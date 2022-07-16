use std::cell::RefCell;

use nom::{InputTake, Offset};
use nom::branch::alt;
use nom::bytes::complete::{is_not, tag, take_while, take_while1, take_while_m_n};
use nom::character::complete::{anychar, char, multispace1};
use nom::combinator::{all_consuming, map, map_opt, map_res, recognize, value, verify};
use nom::multi::{fold_many0, many1};
use nom::sequence::{delimited, preceded};

use crate::resource_path::string::lexer_utils::{IResult, LexerError, LocatedSpan};
use crate::resource_path::string::token::{Token, TokenValue};

use super::range_ex::AsRange;

fn expect<'a, F, E, T>(mut parser: F, err_msg: E) -> impl FnMut(LocatedSpan<'a>) -> IResult<Option<T>>
    where
        F: FnMut(LocatedSpan<'a>) -> IResult<T>,
        E: ToString
{
    use nom::error::Error as NomError;
    move |input| match parser(input) {
        Ok((remaining, output)) => Ok((remaining, Some(output))),
        Err(nom::Err::Error(NomError { input, code: _ })) | Err(nom::Err::Failure(NomError { input, code: _ })) => {
            let _err = LexerError(input.as_range(), err_msg.to_string());
            //input.extra.report_error(err);

            Ok((input, None))
        }
        Err(err) => Err(err),
    }
}

fn ident(input: LocatedSpan) -> IResult<Token> {
    let first = verify(anychar, |c| c.is_ascii_alphabetic() || *c == '_');
    let rest = take_while(|c: char| c.is_ascii_alphabetic() || c.is_ascii_digit() || c == '_');
    let ident = recognize(preceded(first, rest));
    map(ident, |span: LocatedSpan| {
        let fragment = span.fragment().to_string();
        Token::new(span, TokenValue::Ident(fragment))
    })(input)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum StringFragment<'a> {
    Literal(LocatedSpan<'a>),
    EscapedChar(char),
    EscapedWhitespace,
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
    let parse_u32 = map_res(parse_delim_hex, move |hex| {
        match hex {
            None => Err("cannot parse number"),
            Some(hex) => match u32::from_str_radix(hex.fragment(), 16) {
                Ok(val) => Ok(val),
                Err(_) => Err("invalid number"),
            }
        }
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

fn lit_str_fragment(input: LocatedSpan) -> IResult<StringFragment> {
    alt((
        map(lit_str_literal, StringFragment::Literal),
        map(lit_str_escaped_char, StringFragment::EscapedChar),
        value(StringFragment::EscapedWhitespace, lit_str_escaped_whitespace),
    ))(input)
}

fn lit_str(input: LocatedSpan) -> IResult<Token> {
    let build_string = fold_many0(
        lit_str_fragment,
        String::new,
        |mut string, fragment| {
            match fragment {
                StringFragment::Literal(s) => string.push_str(s.fragment()),
                StringFragment::EscapedChar(c) => string.push(c),
                StringFragment::EscapedWhitespace => {}
            }
            string
        },
    );

    let (remainder, s) = delimited(char('"'), build_string, char('"'))(input.clone())?;
    let span_offset = input.offset(&remainder);
    let span = input.take(span_offset);
    Ok((remainder, Token::new(span, TokenValue::LitStr(s))))
}


fn whitespace(input: LocatedSpan) -> IResult<Token> {
    let ws = take_while1(|c: char| c.is_ascii_whitespace());
    map(ws, |span: LocatedSpan| {
        Token::new(span, TokenValue::Whitespace)
    })(input)
}


macro_rules! tag_token {
    ($name:ident, $repr:literal, $token_value:expr) => {
        fn $name(input: LocatedSpan) -> IResult<Token> {
            map(tag($repr), |span: LocatedSpan| Token::new(span, $token_value))(input)
        }
    };
}

tag_token!(scope, "::", TokenValue::Scope);
tag_token!(colon, ":", TokenValue::Colon);
tag_token!(wildcard, "*", TokenValue::Wildcard);
tag_token!(lcurly, "{", TokenValue::LCurly);
tag_token!(rcurly, "}", TokenValue::RCurly);
tag_token!(lparen, "(", TokenValue::LParen);
tag_token!(rparen, ")", TokenValue::RParen);
tag_token!(comma, ",", TokenValue::Comma);
tag_token!(lit_false, "false", TokenValue::LitFalse);
tag_token!(lit_true, "true", TokenValue::LitTrue);


fn expr(input: LocatedSpan) -> IResult<Vec<Token>> {
    let tokens = many1(alt((
        ident,
        lit_str,
        whitespace,
        scope,
        colon,
        wildcard,
        lcurly, rcurly,
        lparen, rparen,
        comma,
        lit_false, lit_true,
    )));
    let (remainder, token_list) = expect(all_consuming(tokens), "expected end-of-file")(input)?;
    Ok((remainder, token_list.unwrap_or_else(|| Vec::new())))
}

fn tokenize(raw: &str) -> (Vec<Token>, Vec<LexerError>) {
    let errors = RefCell::new(Vec::new());
    let input = LocatedSpan::new_extra(raw, ());
    let (_, tokens) = expr(input).expect("parser cannot fail");
    (tokens, errors.take())
}


#[cfg(test)]
mod test {
    use crate::resource_path::string::lexer::tokenize;

    #[test]
    fn simple() {
        let raw = "{a, b}";
        let result = tokenize(raw);
        println!("{:#?}", result);
    }
}