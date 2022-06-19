use anyhow::{ensure, Result};


/// Return `Err` rather than panicking when the assertion fails.
macro_rules! test_assert_eq {
    ($actual:expr, $expected:expr) => {
        ensure!(
            $actual == $expected,
            "equality assertion failed\nactual:\n{actual:#?}\nexpected:\n{expected:#?}",
            actual = $actual,
            expected = $expected,
        );
    }
}

#[test]
fn from_str_works() -> Result<()> {
    use parsel::{FromStr, Parse};
    use parsel::ast::{ident, Ident, Lit};
    use parsel::ast::token::Comma;

    #[derive(PartialEq, Eq, Debug, FromStr, Parse)]
    struct Simple(Ident);


    #[derive(PartialEq, Eq, Debug, FromStr, Parse)]
    enum Generic<A, B> {
        One(A),
        Two(B, Comma, B),
    }

    let actual = Generic::<Lit, Simple>::from_str("key_wrd, supercalifragilisticexpialidocious")?;
    let expected = Generic::<Lit, Simple>::Two(
        Simple(ident("key_wrd")),
        Comma::default(),
        Simple(ident("supercalifragilisticexpialidocious")),
    );

    test_assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn display_works() -> Result<()> {
    use parsel::{quote, Display, ToTokens};
    use parsel::ast::{LitBool, LitInt};
    use parsel::ast::token::{EqEq, Ne, Lt, Le, Gt, Ge};

    #[derive(Display, ToTokens)]
    struct Comparison<L, R> {
        lhs: L,
        op: CmpOp,
        rhs: R,
    }

    #[allow(dead_code)] // some variants are never constructed, and that's OK
    #[derive(Display, ToTokens)]
    enum CmpOp {
        Eq(EqEq),
        Ne(Ne),
        Lt(Lt),
        Le(Le),
        Gt(Gt),
        Ge(Ge),
    }

    let actual_ast = Comparison {
        lhs: LitBool::from(true),
        op: CmpOp::Ge(Ge::default()),
        rhs: LitInt::from(-4356984),
    };
    let actual = actual_ast.to_string();
    let expected_ts = quote::quote!(true >= -4356984);
    let expected = expected_ts.to_string();

    test_assert_eq!(actual, expected);

    Ok(())
}
