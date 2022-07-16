use std::ops::Range;

pub(super) trait AsRange {
    fn as_range(&self) -> Range<usize>;
}
