//! - Message format
//!     Field name | Start | Kind |  Size  | Data |
//!     ---       |  ---  | ---  |  ---   | ---  |
//!     Data type |  u8   | u8   | u32    | [u8; Size] |
//!     Value     |  22   | StringValue | xxx    | [..., ...]  |
//!
//!     - Start - Each message starts with SYN (22)
//!     - Kind - The `Kind` of the data stored in the `Data` field, refer to
//!     - Size - The length of the `Data` field in bytes
//!     - Data - Data structured depending on it `Kind`
use crate::data_frame::state::ParserState;
use std::io::Read;
use thiserror::Error;

pub const SYN: u8 = 22;

#[derive(Debug)]
pub struct DataFrame {
    kind: u8,
    size: u32,
    data: Vec<u8>,
}

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Failed to read data at the beginning")]
    MissingSyn,
    #[error("Unexpected SYN at the beginning: expected 22, got {actual:?}")]
    UnexpectedSyn { actual: u8 },
    #[error("Failed to read kind from stream")]
    MissingKind,
    #[error("Failed to read size of data chunk from stream")]
    MissingSize,
    #[error(
        "Insufficient number of bytes in a stream (expected {expected_size:?}, got {actual_size:?})"
    )]
    InsufficientData {
        expected_size: u32,
        actual_size: u32,
    },
    #[error("Stream error")]
    IO(#[from] std::io::Error),
}

impl DataFrame {
    pub fn parse<R: Read>(src: &mut R) -> Result<Self, ParseError> {
        Ok(state::Initial::new()
            .proceed(src)?
            .proceed(src)?
            .proceed(src)?
            .proceed(src)?
            .into())
    }

    pub fn kind(&self) -> u8 {
        self.kind
    }

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn data(&self) -> &[u8] {
        &self.data
    }
}

mod state {
    use crate::data_frame::{DataFrame, ParseError, SYN};
    use std::io::Read;

    pub(super) struct Initial;

    impl Initial {
        pub(super) fn new() -> Self {
            Self {}
        }
    }

    pub(super) struct Start;

    impl Start {
        fn new() -> Self {
            Self {}
        }
    }

    pub(super) struct Kind {
        kind: u8,
    }

    impl Kind {
        fn new(kind: u8) -> Self {
            Self { kind }
        }
    }

    pub(super) struct Size {
        prev: Kind,
        size: u32,
    }

    impl Size {
        fn new(prev: Kind, size: u32) -> Self {
            Self { prev, size }
        }
    }

    pub(super) struct Data {
        prev: Size,
        data: Vec<u8>,
    }

    impl Data {
        fn new(prev: Size, data: Vec<u8>) -> Self {
            Self { prev, data }
        }
    }

    impl From<Data> for DataFrame {
        fn from(value: Data) -> Self {
            DataFrame {
                kind: value.prev.prev.kind,
                size: value.prev.size,
                data: value.data,
            }
        }
    }

    pub(super) trait ParserState {
        type Output;

        fn proceed<R: Read>(self, src: &mut R) -> Result<Self::Output, ParseError>;
    }

    impl ParserState for Initial {
        type Output = Start;

        fn proceed<R: Read>(self, src: &mut R) -> Result<Self::Output, ParseError> {
            let mut buf = [0_u8; 1];
            if src.read(&mut buf)? == 0 {
                Err(ParseError::MissingSyn)
            } else if buf[0] != SYN {
                Err(ParseError::UnexpectedSyn { actual: buf[0] })
            } else {
                Ok(Start::new())
            }
        }
    }

    impl ParserState for Start {
        type Output = Kind;

        fn proceed<R: Read>(self, src: &mut R) -> Result<Self::Output, ParseError> {
            let mut buf = [0_u8; 1];
            if src.read(&mut buf)? == 0 {
                Err(ParseError::MissingKind)
            } else {
                Ok(Kind::new(buf[0]))
            }
        }
    }

    impl ParserState for Kind {
        type Output = Size;

        fn proceed<R: Read>(self, src: &mut R) -> Result<Self::Output, ParseError> {
            let mut buf = [0_u8; size_of::<u32>()];
            if src.read(&mut buf)? != size_of::<u32>() {
                Err(ParseError::MissingSize)
            } else {
                let size = u32::from_le_bytes(buf);
                Ok(Size::new(self, size))
            }
        }
    }

    impl ParserState for Size {
        type Output = Data;

        fn proceed<R: Read>(self, src: &mut R) -> Result<Self::Output, ParseError> {
            let size = self.size as usize;
            let mut data = vec![0_u8; size];
            let bytes_read = src.read(&mut data)?;
            if bytes_read != size {
                Err(ParseError::InsufficientData {
                    expected_size: self.size,
                    actual_size: bytes_read as u32,
                })
            } else {
                Ok(Data::new(self, data))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn success() {
        let mut input = InputBuilder::default()
            .push(SYN)
            .push(1)
            .push_u32(3)
            .push_many(&[0, 1, 2])
            .build();
        let actual = DataFrame::parse(&mut input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        assert_eq!(1, actual.kind);
        assert_eq!(3, actual.size);
        assert_eq!(&[0, 1, 2], &actual.data[..]);
    }

    #[test]
    fn extra_data() {
        let mut input = InputBuilder::default()
            .push(SYN)
            .push(1)
            .push_u32(3)
            .push_many(&[0, 1, 2, 3, 4, 5])
            .build();
        let actual = DataFrame::parse(&mut input);
        assert!(actual.is_ok());
        let actual = actual.unwrap();
        assert_eq!(1, actual.kind);
        assert_eq!(3, actual.size);
        assert_eq!(&[0, 1, 2], &actual.data[..]);

        let mut remaining = vec![];
        assert!(matches!(input.read_to_end(&mut remaining), Ok(3)));
        assert_eq!(&[3, 4, 5], &remaining[..]);
    }

    #[test]
    fn missing_start() {
        let mut input: Cursor<&[u8]> = Cursor::new(&[]);
        let actual = DataFrame::parse(&mut input);
        assert!(actual.is_err());
        let err = actual.unwrap_err();
        assert!(matches!(err, ParseError::MissingSyn));
    }

    #[test]
    fn unexpected_start() {
        let mut input = InputBuilder::default()
            .push(12)
            .push(1)
            .push_u32(3)
            .push_many(&[0, 1, 2])
            .build();
        let actual = DataFrame::parse(&mut input);
        assert!(actual.is_err());
        let err = actual.unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedSyn { actual: 12 }));
    }

    #[test]
    fn missing_kind() {
        let mut input = Cursor::new(&[SYN]);
        let actual = DataFrame::parse(&mut input);
        assert!(actual.is_err());
        let err = actual.unwrap_err();
        assert!(matches!(err, ParseError::MissingKind));
    }

    #[test]
    fn missing_size() {
        let mut input = Cursor::new(&[SYN, 1]);
        let actual = DataFrame::parse(&mut input);
        assert!(actual.is_err());
        let err = actual.unwrap_err();
        assert!(matches!(err, ParseError::MissingSize));
    }

    #[test]
    fn insufficient_data() {
        let mut input = InputBuilder::default()
            .push(SYN)
            .push(1)
            .push_u32(10)
            .push_many(&[0, 0, 0])
            .build();
        let actual = DataFrame::parse(&mut input);
        assert!(actual.is_err());
        let err = actual.unwrap_err();
        assert!(matches!(
            err,
            ParseError::InsufficientData {
                expected_size: 10,
                actual_size: 3,
            }
        ));
    }

    #[derive(Default)]
    struct InputBuilder(Vec<u8>);

    impl InputBuilder {
        fn push(mut self, b: u8) -> Self {
            self.0.push(b);
            self
        }

        fn push_u32(mut self, t: u32) -> Self {
            self.0.extend(t.to_le_bytes());
            self
        }

        fn push_many(mut self, bytes: impl AsRef<[u8]>) -> Self {
            self.0.extend(bytes.as_ref());
            self
        }

        fn build(self) -> Cursor<Vec<u8>> {
            Cursor::new(self.0)
        }
    }
}
