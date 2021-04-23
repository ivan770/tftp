#![cfg_attr(not(test), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::convert::{TryFrom, TryInto};

use ascii::{AsAsciiStrError, AsciiStr};
use displaydoc::Display;
use enumn::N;

pub const BLOCK_SIZE: usize = 512;

type Opcode = u16;

pub type BlockId = u16;

/// Error indicating that provided buffer has more than 512 bytes in it.
///
/// Exact buffer len is stored as the only field.
#[derive(Debug)]
pub struct BufLenIsGreaterThan512(pub usize);

/// Buffer, that is at most 512 bytes in size.
///
/// In TFTP terms, a data buffer that is exactly 512 bytes in len
/// means, that client should await for at least one more data block until
/// finally receiving "incomplete" buffer with less than 512 bytes len.
/// You can use [`is_incomplete`] to conveniently check for such a situation.
///
/// [`is_incomplete`]: BufAtMost512::is_incomplete
#[derive(Debug)]
pub struct BufAtMost512<'b>(&'b [u8]);

impl<'b> BufAtMost512<'b> {
    /// Check if buffer is less than 512 bytes in size.
    pub fn is_incomplete(&self) -> bool {
        self.0.len() != BLOCK_SIZE
    }
}

impl<'b> From<&'b [u8; 512]> for BufAtMost512<'b> {
    fn from(buf: &'b [u8; 512]) -> Self {
        Self(&buf[..])
    }
}

impl<'b> TryFrom<&'b [u8]> for BufAtMost512<'b> {
    type Error = BufLenIsGreaterThan512;

    fn try_from(buf: &'b [u8]) -> Result<Self, Self::Error> {
        if buf.len() > BLOCK_SIZE {
            Err(BufLenIsGreaterThan512(buf.len()))
        } else {
            Ok(Self(buf))
        }
    }
}

impl<'b> AsRef<[u8]> for BufAtMost512<'b> {
    fn as_ref(&self) -> &'b [u8] {
        self.0
    }
}

/// TFTP opcodes.
#[derive(N)]
#[repr(u16)]
pub enum Operation {
    Rrq = 1,
    Wrq = 2,
    Data = 3,
    Ack = 4,
    Error = 5,
}

/// A kind of file operation client requested.
#[derive(Debug)]
pub enum FileOperation {
    /// Operation involving server sending blocks of data to client
    Read,

    /// Operation involving server receiving blocks of data from client and writing them to file.
    Write,
}

impl From<FileOperation> for Operation {
    fn from(file_op: FileOperation) -> Self {
        match file_op {
            FileOperation::Read => Operation::Rrq,
            FileOperation::Write => Operation::Wrq,
        }
    }
}

/// Data mode TFTP session is established with
#[derive(Debug)]
pub enum Mode {
    NetAscii,
    Binary,
}

impl From<Mode> for &'static AsciiStr {
    fn from(mode: Mode) -> Self {
        match mode {
            Mode::NetAscii => AsciiStr::from_ascii(b"netascii").unwrap(),
            Mode::Binary => AsciiStr::from_ascii(b"octet").unwrap(),
        }
    }
}

/// A single TFTP message.
#[derive(Debug)]
pub enum Message<'b> {
    /// File operation message.
    ///
    /// By protocol definition, this is the first message of TFTP session.
    File {
        /// Exact file operation client requested.
        operation: FileOperation,

        /// A path of file server should work with (write to it or read it).
        path: &'b AsciiStr,

        /// Data sending mode that client requested
        mode: Mode,
    },

    /// A block of data (max 512 bytes in len).
    Data(BlockId, BufAtMost512<'b>),

    /// Acknowledge of receiving a block of data.
    Ack(BlockId),

    /// Error happened during TFTP session.
    Error(BlockId, &'b AsciiStr),
}

/// `tftp` crate errors.
#[derive(Debug, Display)]
pub enum Error {
    /// Incoming buffer doesn't contain an operation code
    NoOpcode,

    /// Incorrect operation code was provided: {0}
    IncorrectOpcode(Opcode),

    /// Incoming buffer doesn't contain a file path for file operation
    NoPath,

    /// Incoming error doesn't contain an error message
    NoErrorMessage,

    /// Incoming buffer doesn't contain a mode for file operation
    NoMode,

    /// Incoming buffer doesn't contain a block id for file operation
    NoBlockId,

    /// No data buffer was provided in message
    NoBufferProvided,

    /// Data buffer must not exceed 512 bytes, current len: {0}
    BufferTooLarge(usize),

    /// Unable to interpret buffer as ASCII string: {0}
    MalformedAscii(AsAsciiStrError),

    /// Incorrect file operation mode
    IncorrectMode,
}

impl<'b> TryFrom<&'b [u8]> for Message<'b> {
    type Error = Error;

    fn try_from(buf: &'b [u8]) -> Result<Self, Error> {
        let opcode = u16::from_be_bytes(
            buf.get(0..2)
                .ok_or(Error::NoOpcode)?
                .try_into()
                .map_err(|_| Error::NoOpcode)?,
        );
        let operation = Operation::n(opcode).ok_or(Error::IncorrectOpcode(opcode))?;

        Ok(match operation {
            Operation::Rrq => file_operation(&buf[2..], FileOperation::Read)?,
            Operation::Wrq => file_operation(&buf[2..], FileOperation::Write)?,
            Operation::Data => Message::Data(
                u16::from_be_bytes(
                    buf.get(2..4)
                        .ok_or(Error::NoBlockId)?
                        .try_into()
                        .map_err(|_| Error::NoBlockId)?,
                ),
                buf.get(4..)
                    .ok_or(Error::NoBufferProvided)?
                    .try_into()
                    .map_err(|e: BufLenIsGreaterThan512| Error::BufferTooLarge(e.0))?,
            ),
            Operation::Ack => Message::Ack(u16::from_be_bytes(
                buf.get(2..4)
                    .ok_or(Error::NoBlockId)?
                    .try_into()
                    .map_err(|_| Error::NoBlockId)?,
            )),
            Operation::Error => Message::Error(
                u16::from_be_bytes(
                    buf.get(2..4)
                        .ok_or(Error::NoBlockId)?
                        .try_into()
                        .map_err(|_| Error::NoBlockId)?,
                ),
                AsciiStr::from_ascii(buf.get(4..).ok_or(Error::NoErrorMessage)?)
                    .map_err(Error::MalformedAscii)?,
            ),
        })
    }
}

#[cfg(feature = "alloc")]
impl<'b> From<Message<'b>> for alloc::vec::Vec<u8> {
    fn from(message: Message<'b>) -> Self {
        match message {
            Message::File {
                operation,
                path,
                mode,
            } => {
                let mode: &'static AsciiStr = mode.into();

                let mut buf = alloc::vec::Vec::with_capacity(
                    core::mem::size_of::<i16>() + path.len() + mode.len() + 2,
                );

                buf.extend_from_slice(&i16::to_be_bytes(Operation::from(operation) as i16));
                buf.extend_from_slice(path.as_bytes());
                buf.push(0);
                buf.extend_from_slice(mode.as_bytes());
                buf.push(0);

                buf
            }
            Message::Data(block_id, data) => {
                let mut buf =
                    alloc::vec::Vec::with_capacity(core::mem::size_of::<i16>() * 2 + data.0.len());

                buf.extend_from_slice(&i16::to_be_bytes(Operation::Data as i16));
                buf.extend_from_slice(&u16::to_be_bytes(block_id));
                buf.extend_from_slice(data.as_ref());

                buf
            }
            Message::Ack(block_id) => {
                let mut buf = alloc::vec::Vec::with_capacity(core::mem::size_of::<i16>() * 2);

                buf.extend_from_slice(&i16::to_be_bytes(Operation::Ack as i16));
                buf.extend_from_slice(&u16::to_be_bytes(block_id));

                buf
            }
            Message::Error(block_id, error) => {
                let mut buf =
                    alloc::vec::Vec::with_capacity(core::mem::size_of::<i16>() + error.len() + 1);

                buf.extend_from_slice(&i16::to_be_bytes(Operation::Error as i16));
                buf.extend_from_slice(&u16::to_be_bytes(block_id));
                buf.extend_from_slice(error.as_bytes());
                buf.push(0);

                buf
            }
        }
    }
}

fn file_operation(source: &[u8], operation: FileOperation) -> Result<Message<'_>, Error> {
    let mut split = source.split(|b| *b == 0);
    let (path, mode) = (
        split.next().ok_or(Error::NoPath)?,
        split.next().ok_or(Error::NoMode)?,
    );

    Ok(Message::File {
        operation,
        path: AsciiStr::from_ascii(path).map_err(Error::MalformedAscii)?,
        mode: match mode {
            b"netascii" => Mode::NetAscii,
            b"octet" => Mode::Binary,
            _ => return Err(Error::IncorrectMode),
        },
    })
}

#[cfg(test)]
mod tests {
    use core::{array::IntoIter, convert::TryFrom};

    use ascii::AsciiStr;
    use expect_test::{expect, Expect};

    use crate::{BufAtMost512, FileOperation, Mode};

    use super::Message;

    fn accept_test(buf: &[u8], expect: Expect) {
        expect.assert_debug_eq(&Message::try_from(buf));
    }

    fn send_test(message: Message, expect: Expect) {
        expect.assert_debug_eq(&Vec::from(message));
    }

    #[test]
    fn accept_ack() {
        accept_test(
            &[0, 4, 0, 1],
            expect![[r#"
                Ok(
                    Ack(
                        1,
                    ),
                )
            "#]],
        );
    }

    #[test]
    fn accept_rrq_na() {
        accept_test(
            &[
                0, 1, 116, 101, 115, 116, 46, 116, 120, 116, 0, 110, 101, 116, 97, 115, 99, 105,
                105, 0,
            ],
            expect![[r#"
                Ok(
                    File {
                        operation: Read,
                        path: "test.txt",
                        mode: NetAscii,
                    },
                )
            "#]],
        );
    }

    #[test]
    fn accept_rrq_oc() {
        accept_test(
            &[
                0, 1, 116, 101, 115, 116, 46, 116, 120, 116, 0, 111, 99, 116, 101, 116, 0,
            ],
            expect![[r#"
                Ok(
                    File {
                        operation: Read,
                        path: "test.txt",
                        mode: Binary,
                    },
                )
            "#]],
        );
    }

    #[test]
    fn accept_wrq_na() {
        accept_test(
            &[
                0, 2, 116, 101, 115, 116, 46, 116, 120, 116, 0, 110, 101, 116, 97, 115, 99, 105,
                105, 0,
            ],
            expect![[r#"
                Ok(
                    File {
                        operation: Write,
                        path: "test.txt",
                        mode: NetAscii,
                    },
                )
            "#]],
        );
    }

    #[test]
    fn accept_wrq_oc() {
        accept_test(
            &[
                0, 2, 116, 101, 115, 116, 46, 116, 120, 116, 0, 111, 99, 116, 101, 116, 0,
            ],
            expect![[r#"
                Ok(
                    File {
                        operation: Write,
                        path: "test.txt",
                        mode: Binary,
                    },
                )
            "#]],
        );
    }

    #[test]
    fn accept_data() {
        accept_test(
            &[0, 3, 0, 1, 1, 2, 3, 4],
            expect![[r#"
                Ok(
                    Data(
                        1,
                        BufAtMost512(
                            [
                                1,
                                2,
                                3,
                                4,
                            ],
                        ),
                    ),
                )
            "#]],
        );
    }

    #[test]
    fn accept_empty_buf() {
        accept_test(
            &[0, 3, 0, 1],
            expect![[r#"
                Ok(
                    Data(
                        1,
                        BufAtMost512(
                            [],
                        ),
                    ),
                )
            "#]],
        );
    }

    #[test]
    fn accept_big_buf() {
        let msg = IntoIter::new([0, 3, 0, 1])
            .chain(IntoIter::new([0; 513]))
            .collect::<Vec<_>>();

        accept_test(
            &msg,
            expect![[r#"
                Err(
                    BufferTooLarge(
                        513,
                    ),
                )
            "#]],
        );
    }

    #[test]
    fn accept_error() {
        accept_test(
            &[0, 5, 0, 1, 79, 104, 32, 110, 111],
            expect![[r#"
                Ok(
                    Error(
                        1,
                        "Oh no",
                    ),
                )
            "#]],
        );
    }

    #[test]
    fn send_rrq() {
        send_test(
            Message::File {
                operation: FileOperation::Read,
                path: AsciiStr::from_ascii(b"test.txt").unwrap(),
                mode: Mode::NetAscii,
            },
            expect![[r#"
                [
                    0,
                    1,
                    116,
                    101,
                    115,
                    116,
                    46,
                    116,
                    120,
                    116,
                    0,
                    110,
                    101,
                    116,
                    97,
                    115,
                    99,
                    105,
                    105,
                    0,
                ]
            "#]],
        );
    }

    #[test]
    fn send_wrq() {
        send_test(
            Message::File {
                operation: FileOperation::Write,
                path: AsciiStr::from_ascii(b"test.txt").unwrap(),
                mode: Mode::NetAscii,
            },
            expect![[r#"
                [
                    0,
                    2,
                    116,
                    101,
                    115,
                    116,
                    46,
                    116,
                    120,
                    116,
                    0,
                    110,
                    101,
                    116,
                    97,
                    115,
                    99,
                    105,
                    105,
                    0,
                ]
            "#]],
        );
    }

    #[test]
    fn send_rrq_octet() {
        send_test(
            Message::File {
                operation: FileOperation::Read,
                path: AsciiStr::from_ascii(b"test.txt").unwrap(),
                mode: Mode::Binary,
            },
            expect![[r#"
                [
                    0,
                    1,
                    116,
                    101,
                    115,
                    116,
                    46,
                    116,
                    120,
                    116,
                    0,
                    111,
                    99,
                    116,
                    101,
                    116,
                    0,
                ]
            "#]],
        );
    }

    #[test]
    fn send_wrq_octet() {
        send_test(
            Message::File {
                operation: FileOperation::Write,
                path: AsciiStr::from_ascii(b"test.txt").unwrap(),
                mode: Mode::Binary,
            },
            expect![[r#"
                [
                    0,
                    2,
                    116,
                    101,
                    115,
                    116,
                    46,
                    116,
                    120,
                    116,
                    0,
                    111,
                    99,
                    116,
                    101,
                    116,
                    0,
                ]
            "#]],
        );
    }

    #[test]
    fn send_data() {
        send_test(
            Message::Data(123, BufAtMost512::try_from(&[1, 2, 3][..]).unwrap()),
            expect![[r#"
                [
                    0,
                    3,
                    0,
                    123,
                    1,
                    2,
                    3,
                ]
            "#]],
        );
    }

    #[test]
    fn send_ack() {
        send_test(
            Message::Ack(123),
            expect![[r#"
                [
                    0,
                    4,
                    0,
                    123,
                ]
            "#]],
        );
    }

    #[test]
    fn send_error() {
        send_test(
            Message::Error(123, AsciiStr::from_ascii(b"Oh no").unwrap()),
            expect![[r#"
                [
                    0,
                    5,
                    0,
                    123,
                    79,
                    104,
                    32,
                    110,
                    111,
                    0,
                ]
            "#]],
        );
    }
}
