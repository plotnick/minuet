//! Test compile-time parsing of Minuet programs.
//!
//! TODO: Use [trybuild](https://crates.io/crates/trybuild).

use minuet_macro::minuet;
use minuet_syntax::*;

#[test]
fn test_macro() {
    assert_eq!(minuet!(), []);
    assert_eq!(minuet!(if), [minuet_syntax::rule!([])]);
    assert_eq!(minuet!(foo()), [rule!([pos!(foo)])]);
    assert_eq!(minuet!(foo()), minuet!(foo() if));
    assert_eq!(minuet!(if foo()), [rule!([], [pos!(foo)])]);
    assert_eq!(
        minuet!(foo() or bar() if baz()),
        [rule!([pos!(foo), pos!(bar)], [pos!(baz)])]
    );
    assert_eq!(minuet!((x = 0)), minuet!(x = 0));
    assert_eq!(
        minuet!(x = 0 or x != 0 or x > 0 or x < 0 or x >= 0 or x <= 0),
        [rule!([
            rel!(var!(x), Eq, 0),
            rel!(var!(x), Ne, 0),
            rel!(var!(x), Gt, 0),
            rel!(var!(x), Lt, 0),
            rel!(var!(x), Geq, 0),
            rel!(var!(x), Leq, 0),
        ])]
    );
    assert_eq!(
        minuet!(|x| = 0 or -x = 0),
        [rule!([
            rel!(unary!(Abs, var!(x)), Eq, 0),
            rel!(unary!(Neg, var!(x)), Eq, 0),
            //rel!(unary!(Not, ..), ..),
        ])]
    );
    assert_eq!(
        minuet!(foo() if x = 0 and not bar(x) and not not bar("baz")),
        [rule!(
            [pos!(foo)],
            [rel!(var!(x), Eq, 0), neg!(bar(var!(x))), nneg!(bar("baz"))]
        )]
    );
}
