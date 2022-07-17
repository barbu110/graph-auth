use std::iter::Enumerate;
use std::ops::{Index, Range, RangeFrom, RangeFull, RangeTo};
use std::slice::Iter;


use nom::{InputIter, InputLength, InputTake, Needed, Slice};

use crate::resource_path::string::token::Token;

#[derive(Clone, Debug)]
pub struct TokenSequence<'a> {
    pub(super) tokens: &'a [Token<'a>],
    start: usize,
    end: usize,
}

impl<'a> TokenSequence<'a> {
    pub fn new(tokens: &'a [Token<'a>]) -> Self {
        TokenSequence {
            tokens,
            start: 0,
            end: tokens.len(),
        }
    }
}

impl<'a> Index<usize> for TokenSequence<'a> {
    type Output = Token<'a>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.tokens[index]
    }
}

impl<'a> InputLength for TokenSequence<'a> {
    fn input_len(&self) -> usize {
        1
    }
}

impl<'a> InputTake for TokenSequence<'a> {
    fn take(&self, count: usize) -> Self {
        TokenSequence {
            tokens: &self.tokens[0..count],
            start: 0,
            end: count,
        }
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.tokens.split_at(count);
        let prefix = TokenSequence {
            tokens: prefix,
            start: 0,
            end: prefix.len(),
        };
        let suffix = TokenSequence {
            tokens: suffix,
            start: 0,
            end: suffix.len(),
        };
        (suffix, prefix)
    }
}

impl<'a> InputIter for TokenSequence<'a> {
    type Item = &'a Token<'a>;
    type Iter = Enumerate<Iter<'a, Token<'a>>>;
    type IterElem = Iter<'a, Token<'a>>;

    fn iter_indices(&self) -> Self::Iter {
        self.tokens.iter().enumerate()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.tokens.iter()
    }

    fn position<P>(&self, pred: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.tokens.iter().position(pred)
    }

    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        if self.tokens.len() >= count {
            Ok(count)
        } else {
            Err(Needed::new(self.tokens.len()))
        }
    }
}

impl<'a> Slice<Range<usize>> for TokenSequence<'a> {
    fn slice(&self, range: Range<usize>) -> Self {
        let start = self.start + range.start;
        let end = self.start + range.end;
        let slice = &self.tokens[range];
        TokenSequence {
            tokens: slice,
            start,
            end,
        }
    }
}

impl<'a> Slice<RangeTo<usize>> for TokenSequence<'a> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0..range.end)
    }
}

impl<'a> Slice<RangeFrom<usize>> for TokenSequence<'a> {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        self.slice(range.start..self.end - self.start)
    }
}

impl<'a> Slice<RangeFull> for TokenSequence<'a> {
    fn slice(&self, _: RangeFull) -> Self {
        TokenSequence {
            tokens: self.tokens,
            start: self.start,
            end: self.end,
        }
    }
}
