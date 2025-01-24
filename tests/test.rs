use bexeval::*;

macro_rules! op_test {
    ($t:ty, $name: ident) => {
        #[test]
        fn $name() {
            let v: Vec<(i32, i32)> = vec![(-5, 3), (5, -3), (3, 3), (-2, -2)];
            let parser = Parser::<$t>::new();
            for &(x_, y_) in &v {
                let (x, y) = (x_ as $t, y_ as $t);
                assert_eq!(parser.eval(&format!("{} + {}", x, y)).unwrap(), x.wrapping_add(y));
                assert_eq!(parser.eval(&format!("{} - {}", x, y)).unwrap(), x.wrapping_sub(y));
                assert_eq!(parser.eval(&format!("{} * {}", x, y)).unwrap(), x.wrapping_mul(y));
                assert_eq!(parser.eval(&format!("{} / {}", x, y)).unwrap(), x / y);
                assert_eq!(parser.eval(&format!("{} % {}", x, y)).unwrap(), x % y);
                assert_eq!(parser.eval(&format!("{} & {}", x, y)).unwrap(), x & y);
                assert_eq!(parser.eval(&format!("{} | {}", x, y)).unwrap(), x | y);
                assert_eq!(parser.eval(&format!("{} ^ {}", x, y)).unwrap(), x ^ y);
                assert_eq!(parser.eval(&format!("{} << {}", x, y)).unwrap(), x.wrapping_shl(y as u32));
                assert_eq!(parser.eval(&format!("{} >> {}", x, y)).unwrap(), x.wrapping_shr(y as u32));
                assert_eq!(parser.eval(&format!("-{}", x)).unwrap(), x.wrapping_neg());
                assert_eq!(parser.eval(&format!("!{}", x)).unwrap(), !x);
            }

            for &(x_, y_) in &v {
                let (x, y) = (x_ as $t, y_ as $t);
                assert_eq!(parser.eval(&format!("{} == {}", x, y)).unwrap(), (x == y) as $t);
                assert_eq!(parser.eval(&format!("{} != {}", x, y)).unwrap(), (x != y) as $t);
                assert_eq!(parser.eval(&format!("{} < {}", x, y)).unwrap(), (x < y) as $t);
                assert_eq!(parser.eval(&format!("{} <= {}", x, y)).unwrap(), (x <= y) as $t);
                assert_eq!(parser.eval(&format!("{} > {}", x, y)).unwrap(), (x > y) as $t);
                assert_eq!(parser.eval(&format!("{} >= {}", x, y)).unwrap(), (x >= y) as $t);
            }

            for &(x_, y_) in &v {
                let (x, y) = (x_ as $t, y_ as $t);
                assert_eq!(parser.eval(&format!("max({}, {})", x, y)).unwrap(), x.max(y));
                assert_eq!(parser.eval(&format!("min({}, {})", x, y)).unwrap(), x.min(y));
                assert_eq!(parser.eval(&format!("pow({}, {})", x, y)).unwrap(), x.wrapping_pow(y as u32));
                assert_eq!(parser.eval(&format!("count_ones({})", x)).unwrap(), x.count_ones() as $t);
                assert_eq!(parser.eval(&format!("count_zeros({})", x)).unwrap(), x.count_zeros() as $t);
            }

            assert_eq!(
                parser.eval("1 + 2 * 3 % 4 << 5 == 96 ^ 6 & 7 | !32").unwrap(),
                ((1 as $t + 2 * 3 % 4).wrapping_shl(5 as u32) == 96) as $t ^ 6 & 7 | !32
            );

            assert_eq!(
                parser.eval_context("-32 + x", &[("x", parser.eval("1 << 5").unwrap())]).unwrap(),
                0
            );
        }
    }
}

op_test!(i8, parser_test_i8);
op_test!(i16, parser_test_i16);
op_test!(i32, parser_test_i32);
op_test!(i64, parser_test_i64);
op_test!(isize, parser_test_isize);
op_test!(u8, parser_test_u8);
op_test!(u16, parser_test_u16);
op_test!(u32, parser_test_u32);
op_test!(u64, parser_test_u64);
op_test!(usize, parser_test_usize);

#[test]
fn context_test() {
    let mut ctx = Context::<i32>::new();
    ctx.assign("x", ctx.eval("2 + 3 * 5").unwrap());
    assert_eq!(ctx.eval("x + 3").unwrap(), 20);
    ctx.assign_stmt("y = x + 5").unwrap();
    assert_eq!(ctx.eval("y + x * 2").unwrap(), 56);

    ctx.assign("y", ctx.eval("y * 2").unwrap());
    assert_eq!(ctx.eval("y + 6").unwrap(), 50);
}