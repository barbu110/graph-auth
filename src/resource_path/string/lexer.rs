use nom::{InputTake, Offset};
use nom::branch::alt;
use nom::bytes::complete::{is_not, tag, take_while, take_while1, take_while_m_n};
use nom::character::complete::{anychar, char, multispace1};
use nom::combinator::{all_consuming, map, map_opt, map_res, recognize, value, verify};
use nom::multi::{fold_many0, many1};
use nom::number::complete::double;
use nom::sequence::{delimited, preceded};
use serde_json::Number;

use crate::resource_path::string::lexer_utils::{IResult, LexerError, LexerState, LocatedSpan};
use crate::resource_path::string::token::{Token, TokenValue};

use super::range_ex::AsRange;

/// Creates a parser function for a token that maps 1:1 with its token value.
macro_rules! tag_token {
    ($name:ident, $repr:literal, $token_value:expr) => {
        fn $name(input: LocatedSpan) -> IResult<Token> {
            map(tag($repr), |span: LocatedSpan| {
                Token::new(span, $token_value)
            })(input)
        }
    };
}

/// A representation of a string fragment used to construct a string literal.
#[derive(Debug, Clone, PartialEq, Eq)]
enum StringFragment<'a> {
    /// A string literal containing no quotes or backslashes.
    Literal(LocatedSpan<'a>),

    /// An escaped character fragment.
    EscapedChar(char),

    /// Whitespace ignored from the string's representation.
    EscapedWhitespace,
}

/// Returns the value of the inner parser if it succeeds. Otherwise, a `LexerError`
/// containing the provided error message is reported to the inner state of the lexer.
fn expect<'a, F, E, T>(
    mut parser: F,
    err_msg: E,
) -> impl FnMut(LocatedSpan<'a>) -> IResult<Option<T>>
where
    F: FnMut(LocatedSpan<'a>) -> IResult<T>,
    E: ToString,
{
    use nom::error::Error as NomError;
    move |input| match parser(input) {
        Ok((remaining, output)) => Ok((remaining, Some(output))),
        Err(nom::Err::Error(NomError { input, code: _ }))
        | Err(nom::Err::Failure(NomError { input, code: _ })) => {
            let err = LexerError(input.as_range(), err_msg.to_string());
            input.extra.report_error(err);

            Ok((input, None))
        }
        Err(err) => Err(err),
    }
}

fn lit_bool(input: LocatedSpan) -> IResult<Token> {
    alt((
        map(tag("false"), |span: LocatedSpan| Token::new(span, TokenValue::LitBool(false))),
        map(tag("true"), |span: LocatedSpan| Token::new(span, TokenValue::LitBool(true))),
    ))(input)
}

/// Parses an identifier.
fn ident(input: LocatedSpan) -> IResult<Token> {
    let first = verify(anychar, |c| c.is_ascii_alphabetic() || *c == '_');
    let rest = take_while(|c: char| c.is_ascii_alphabetic() || c.is_ascii_digit() || c == '_');
    let ident = recognize(preceded(first, rest));
    map(ident, |span: LocatedSpan| {
        let fragment = span.fragment().to_string();
        Token::new(span, TokenValue::Ident(fragment))
    })(input)
}

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals.
fn lit_str_unicode_char(input: LocatedSpan) -> IResult<char> {
    let parse_hex = take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit());
    // FIXME Figure out a way to keep correct span here.
    let parse_delim_hex = preceded(
        char('u'),
        delimited(
            char('{'),
            expect(parse_hex, "expected 1-6 hex digits"),
            expect(char('}'), "expected closing brace"),
        ),
    );
    let parse_u32 = map_res(parse_delim_hex, move |hex| match hex {
        None => Err("cannot parse number"),
        Some(hex) => match u32::from_str_radix(hex.fragment(), 16) {
            Ok(val) => Ok(val),
            Err(_) => Err("invalid number"),
        },
    });
    map_opt(parse_u32, std::char::from_u32)(input)
}

/// Parse an escaped character.
fn lit_str_escaped_char(input: LocatedSpan) -> IResult<char> {
    preceded(
        char('\\'),
        alt((
            lit_str_unicode_char,
            value('\n', char('n')),
            value('\r', char('r')),
            value('\t', char('t')),
            value('\\', char('\\')),
            value('/', char('/')),
            value('"', char('"')),
        )),
    )(input)
}

/// Parse a backslash, followed by any amount of whitespace. This is used later
/// to discard any escaped whitespace.
fn lit_str_escaped_whitespace(input: LocatedSpan) -> IResult<LocatedSpan> {
    preceded(char('\\'), multispace1)(input)
}

/// Parse a non-empty block of text that doesn't include \ or "
fn lit_str_literal(input: LocatedSpan) -> IResult<LocatedSpan> {
    let not_quote_slash = is_not("\"\\");
    verify(not_quote_slash, |s: &LocatedSpan| !s.is_empty())(input)
}

/// Parses a single kind of string fragment as described by the `StringFragment
/// enumeration. This can be a string literal without any quotes or backslashes,
/// an escaped character, or ignored whitespace.
fn lit_str_fragment(input: LocatedSpan) -> IResult<StringFragment> {
    alt((
        map(lit_str_literal, StringFragment::Literal),
        map(lit_str_escaped_char, StringFragment::EscapedChar),
        value(
            StringFragment::EscapedWhitespace,
            lit_str_escaped_whitespace,
        ),
    ))(input)
}

/// Parses and constructs a string literal from its fragments.
///
/// # Notes
///
/// This function uses heap allocation to construct a `String`.
fn lit_str(input: LocatedSpan) -> IResult<Token> {
    let build_string = fold_many0(lit_str_fragment, String::new, |mut string, fragment| {
        match fragment {
            StringFragment::Literal(s) => string.push_str(s.fragment()),
            StringFragment::EscapedChar(c) => string.push(c),
            StringFragment::EscapedWhitespace => {}
        }
        string
    });

    let (remainder, s) = delimited(
        char('"'),
        build_string,
        expect(char('"'), "expected closing quote"),
    )(input.clone())?;
    let span_offset = input.offset(&remainder);
    let span = input.take(span_offset);
    Ok((remainder, Token::new(span, TokenValue::LitStr(s))))
}

/// Parses a numeric literal into either an `f64`, `u64`, or `i64`.
fn lit_num(input: LocatedSpan) -> IResult<Token> {
    let num = map_opt(double, |v: f64| {
        let n = if v == (v as u64) as f64 {
            Some(Number::from(v as u64))
        } else if v < 0.0 && v == (v as i64) as f64 {
            Some(Number::from(v as i64))
        } else {
            Number::from_f64(v)
        };
        n.map(TokenValue::LitNum)
    });

    map(num, |tv: TokenValue| Token::new(input.clone(), tv))(input.clone())
}

/// Parses ASCII whitespace.
fn whitespace(input: LocatedSpan) -> IResult<Token> {
    let ws = take_while1(|c: char| c.is_ascii_whitespace());
    map(ws, |span: LocatedSpan| {
        Token::new(span, TokenValue::Whitespace)
    })(input)
}

tag_token!(scope, "::", TokenValue::Scope);
tag_token!(colon, ":", TokenValue::Colon);
tag_token!(wildcard, "*", TokenValue::Wildcard);
tag_token!(lcurly, "{", TokenValue::LCurly);
tag_token!(rcurly, "}", TokenValue::RCurly);
tag_token!(lparen, "(", TokenValue::LParen);
tag_token!(rparen, ")", TokenValue::RParen);
tag_token!(comma, ",", TokenValue::Comma);

fn expr(input: LocatedSpan) -> IResult<Vec<Token>> {
    let tokens = many1(alt((
        lit_bool, ident, lit_str, lit_num, whitespace, scope, colon, wildcard, lcurly, rcurly, lparen,
        rparen, comma,
    )));
    let (remainder, token_list) = expect(all_consuming(tokens), "expected end-of-file")(input)?;
    Ok((remainder, token_list.unwrap_or_default()))
}

/// Takes a Resource Path string representation and returns a vector of tokens.
///
/// # Notes
///
/// Heap allocation will occur for two token types: identifiers and string
/// literals.
fn tokenize<'a>(raw: &'a str) -> (Vec<Token>, Vec<LexerError>) {
    let input = LocatedSpan::<'a>::new_extra(raw, LexerState::new());
    let (remainder, tokens) = expr(input).expect("parser cannot fail");
    (tokens, remainder.extra.0.into_inner())
}

#[cfg(test)]
mod test {
    use std::ops::Range;

    use rstest::rstest;

    use crate::resource_path::string::lexer::tokenize;
    use crate::resource_path::string::token::TokenValue;

    #[rstest]
    #[case("::", 0..2, TokenValue::Scope)]
    #[case("*", 0..1, TokenValue::Wildcard)]
    #[case("{", 0..1, TokenValue::LCurly)]
    #[case("}", 0..1, TokenValue::RCurly)]
    #[case("(", 0..1, TokenValue::LParen)]
    #[case(")", 0..1, TokenValue::RParen)]
    #[case(",", 0..1, TokenValue::Comma)]
    #[case(":", 0..1, TokenValue::Colon)]
    #[case("false", 0..5, TokenValue::LitBool(false))]
    #[case("true", 0..4, TokenValue::LitBool(true))]
    fn tag_token(#[case] raw: &str, #[case] range: Range<usize>, #[case] tv: TokenValue) {
        let (tokens, errors) = tokenize(raw);
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 1);

        let actual = tokens.first().unwrap();
        assert_eq!(actual.span.range, range, "wrong range for: {}", raw);
        assert_eq!(&actual.value, &tv);
    }

    #[test]
    fn simple() {
        let raw = "account(id: \"123\")::{id, name}";
        let (tokens, _) = tokenize(raw);

        tokens.into_iter().map(|t| t.value).for_each(|t| println!("{:?}", t));
    }
}
