use std::ops::Range;

use serde_json::Number;

use crate::resource_path::string::lexer_utils::LocatedSpan;
use crate::resource_path::string::range_ex::AsRange;

#[derive(Clone, Debug)]
pub struct Token<'a> {
    pub span: Span<'a>,
    pub value: TokenValue,
}

#[derive(Clone, Debug)]
pub struct Span<'a> {
    pub range: Range<usize>,
    pub fragment: &'a str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TokenValue {
    Whitespace,
    Scope,
    Wildcard,
    LCurly,
    RCurly,
    LParen,
    RParen,
    Colon,
    Comma,
    LitBool(bool),
    LitNum(Number),
    LitStr(String),
    Ident(String),
}

impl<'a> Token<'a> {
    pub fn new(span: LocatedSpan<'a>, value: TokenValue) -> Self {
        Token {
            span: span.into(),
            value,
        }
    }
}

impl<'a> From<LocatedSpan<'a>> for Span<'a> {
    fn from(s: LocatedSpan<'a>) -> Self {
        Span {
            range: s.as_range(),
            fragment: s.fragment(),
        }
    }
}
