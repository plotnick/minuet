//! A trivial tracing facility.

pub type Trace = bool;

macro_rules! trace {
    ($trace:expr, $fmt:literal $(,)? $($arg:expr),* $(,)?) => {
        if $trace {
            eprintln!($fmt, $($arg),*);
        }
    }
}
