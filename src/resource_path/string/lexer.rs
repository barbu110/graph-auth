use nom::branch::alt;
use nom::bytes::complete::{take_while, take_while1};
use nom::character::complete::anychar;
use nom::combinator::{eof, map, recognize, verify};
use nom::multi::many1;
use nom::sequence::{preceded, terminated};
use crate::resource_path::string::{IResult, LocatedSpan};
use crate::resource_path::string::token::{Token, TokenValue};

#[derive(Clone, Debug)]
pub struct LexerError<'a>(LocatedSpan<'a>, String);

fn expect<'a, F, E, T>(mut parser: F, err_msg: E) -> impl FnMut(LocatedSpan<'a>) -> IResult<Option<T>>
where
    F: FnMut(LocatedSpan<'a>) -> IResult<T>,
    E: ToString
{
    use nom::error::Error as NomError;
    move |input| match parser(input) {
        Ok((remaining, output)) => Ok((remaining, Some(output))),
        Err(nom::Err::Error(NomError { input, code: _ })) | Err(nom::Err::Failure(NomError { input, code: _ })) => {
            let err = LexerError(input, err_msg.to_string());
            // TODO Report error.
            println!("error: {:?}", err);
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
        Token::new(span, TokenValue::Ident(*span.fragment()))
    })(input)
}

fn whitespace(input: LocatedSpan) -> IResult<Token> {
    let ws = take_while1(|c: char| c.is_ascii_whitespace());
    map(ws, |span: LocatedSpan| {
        Token::new(span, TokenValue::Whitespace)
    })(input)
}

fn expr(input: LocatedSpan) -> IResult<Option<Vec<Token>>> {
    expect(terminated(many1(alt((ident, whitespace))), eof), "expected end-of-file")(input)
}


#[cfg(test)]
mod test {
    use crate::resource_path::string::lexer::{expr, ident};
    use crate::resource_path::string::LocatedSpan;

    #[test]
    fn simple() {
        let raw = "foo bar";
        let span = LocatedSpan::new(raw);
        let result = expr(span);
        println!("{:#?}", result);
    }
}