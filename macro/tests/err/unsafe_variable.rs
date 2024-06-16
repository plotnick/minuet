use minuet_macro::minuet;

fn main() {
    // `x` is safe in the first rule, but unsafe in the second.
    minuet! {
        foo(x) if x = 0;
        foo(x) if x > 0;
    };
}
