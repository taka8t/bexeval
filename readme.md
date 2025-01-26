# bexeval
Bexeval is a Rust crate for evaluating mathematical expressions with integer numeric types written as strings.

## Features

- Parse and evaluate simple mathematical expressions.
    - Basic arithmetic operations: `+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`, `<<`, `>>`, `!`(operator not)
    - Comparison operators (Return 1 if true, 0 if false): `==`, `!=`, `<`, `<=`, `>`, `>=`
    - Parentheses for expression grouping
    - Common mathematical functions (possibility of adding more functions in the future): `pow`, `count_ones`, `abs`...
- Can select primitive integer type as the numeric value type: `u8`, `u16`, `u32`, `u64`, `usize`, `i8`, `i16`, `i32`, `i64`, `isize`
- Support for variables.
- Minimal dependencies (only `num-traits`).

## Usage

Add the `bexeval` crate to your `Cargo.toml` file:

```toml
[dependencies]
bexeval = "<version>"
```

Then, in your Rust code:

```rust
use bexeval::*;

let parser = Parser::<i32>::new();
assert_eq!(parser.eval("1 + 2 * max(3, 4) - (8 ^ 5)").unwrap(), 1 + 2 * 3.max(4) - (8 ^ 5));

assert_eq!(parser.eval_context("1 + x", &[("x", 5)]).unwrap(), 1 + 5);

assert_eq!(parser.eval(&format!("1 + {}", 5)).unwrap(), 1 + 5);
```

The context argument stores information about the variable in array of tuples(&str, T).

Wrapping operations are used for operations that may overflow. (`wrapping_add`, `wrapping_mul`...)

Be careful of overflow.

Dividing by zero causes panic.

You can assign numerical values to variables and evaluate them using `Context`.

```rust
# use bexeval::*;
#
let mut ctx = Context::<u8>::new();

ctx.assign("x", 1);
assert_eq!(ctx.eval("x + 3").unwrap(), 4);
ctx.assign_stmt("y = x + 5").unwrap();
assert_eq!(ctx.eval("y + x * 2").unwrap(), 8);

// wrapping operation
assert_eq!(ctx.eval("y + x * (pow(2, 8) - 1)").unwrap(), 5);
```

### Available function
 - `pow`
 - `abs`
 - `abs_diff` (Available even with rustc versions below 1.60)
 - `count_ones`
 - `count_zeros`
 - `leading_zeros`
 - `trailing_zeros`
 - `rotate_left`
 - `rotate_right`
## API Documentation

Detailed API documentation can be found [here](https://docs.rs/bexeval).

## License

This project is licensed under the MIT license.