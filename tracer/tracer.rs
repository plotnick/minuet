//! A trivial tracing facility.

use bitmask_enum::bitmask;

#[bitmask]
pub enum Trace {
    All,
    Compile,
    Preprocess,
    Solve,
}

#[macro_export]
macro_rules! trace {
    ($trace:expr, $level:ident, $fmt:literal $(,)? $($arg:expr),* $(,)?) => {
        if $trace.intersects(Trace::$level) {
            eprintln!($fmt, $($arg),*);
        }
    }
}
