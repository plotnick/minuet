//! Test compile-time parsing of Minuet programs.

use minuet_macro::minuet;
use minuet_syntax::*;

#[test]
fn ok() {
    assert_eq!(minuet!(), []);
    assert_eq!(minuet!(if), [minuet_syntax::rule!([])]);
    assert_eq!(minuet!(foo()), [rule!([pos!(foo())])]);
    assert_eq!(minuet!(foo()), minuet!(foo() if));
    assert_eq!(minuet!(if foo()), [rule!([], [pos!(foo())])]);
    assert_eq!(
        minuet!(foo() or bar() if baz()),
        [rule!([pos!(foo()), pos!(bar())], [pos!(baz())])]
    );
    assert_eq!(
        minuet!(foo(x) if x = 0 and not bar(x) and not not bar(baz())),
        [rule!(
            [pos!(foo(x))],
            [rel!(x, Eq, 0), neg!(bar(x)), nneg!(bar(baz()))]
        )]
    );
    assert_eq!(minuet!(p(x) if (x = 0)), minuet!(p(x) if x = 0));
    assert_eq!(
        minuet!(p(x) if x = 0 and x != 0 and x > 0 and x < 0 and x >= 0 and x <= 0),
        [rule!(
            [pos!(p(x))],
            [
                rel!(x, Eq, 0),
                rel!(x, Ne, 0),
                rel!(x, Gt, 0),
                rel!(x, Lt, 0),
                rel!(x, Geq, 0),
                rel!(x, Leq, 0),
            ]
        )]
    );
    assert_eq!(
        minuet!(p(x) if |x| = 0 and -x = 0),
        [rule!(
            [pos!(p(x))],
            [
                rel!(unary!(Abs, x), Eq, 0),
                rel!(unary!(Neg, x), Eq, 0),
                //rel!(unary!(Not, ..), ..),
            ]
        )]
    );
}

#[test]
fn err() {
    trybuild::TestCases::new().compile_fail("tests/err/*.rs");
}
