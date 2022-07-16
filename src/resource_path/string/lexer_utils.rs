use std::cell::RefCell;
use std::ops::Range;

use crate::resource_path::string::range_ex::AsRange;

pub type LocatedSpan<'a> = nom_locate::LocatedSpan<&'a str, LexerState<'a>>;
pub type IResult<'a, T> = nom::IResult<LocatedSpan<'a>, T>;

#[derive(Clone, Debug)]
pub struct LexerState<'a>(pub &'a RefCell<Vec<LexerError>>);

#[derive(Clone, Debug)]
pub struct LexerError(pub Range<usize>, pub String);

impl<'a> LexerState<'a> {
    pub fn report_error(&self, error: LexerError) {
        self.0.borrow_mut().push(error);
    }
}

impl<'a> AsRange for LocatedSpan<'a> {
    fn as_range(&self) -> Range<usize> {
        let start = self.location_offset();
        let end = start + self.fragment().len();
        start..end
    }
}