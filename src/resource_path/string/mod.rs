pub mod lexer;
pub mod token;
pub(crate) mod chars;

pub type LocatedSpan<'a> = nom_locate::LocatedSpan<&'a str>;
pub type IResult<'a, T> = nom::IResult<LocatedSpan<'a>, T>;
