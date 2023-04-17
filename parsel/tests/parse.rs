use core::convert::TryFrom;
use anyhow::{ensure, Result};
use parsel::{Parse, Span};
use parsel::ast::{Lit, LitBool, LitUint, LitStr, Ident, Paren};
use parsel::ast::{token, ident, Token};


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
fn parse_struct_named_field() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, Parse)]
    struct Assignment {
        name: Ident,
        eq: Token![=],
        value: Lit,
    }

    let actual: Assignment = parsel::parse_str("foo = 13.37")?;
    let expected = Assignment {
        name: ident("foo"),
        eq: <Token![=]>::default(),
        value: Lit::try_from(13.37).unwrap(),
    };

    test_assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn parse_struct_indexed_field() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, Parse)]
    struct Assignment(Ident, Token![=], Lit);

    let actual: Assignment = parsel::parse_str("quux = 'X'")?;
    let expected = Assignment(
        ident("quux"),
        <Token![=]>::default(),
        Lit::from('X'),
    );

    test_assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn parse_enum() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, Parse)]
    enum Foo {
        Qux {
            first: Lit,
            comma: token::Comma,
            second: Lit,
        },
        Bar(Ident, Lit),
    }

    let f1: Foo = parsel::parse_str("foo1 42")?;
    test_assert_eq!(
        f1,
        Foo::Bar(
            ident("foo1"),
            Lit::from(42_u64),
        )
    );

    let f2: Foo = parsel::parse_str("- 1337, 0.5")?;
    test_assert_eq!(
        f2,
        Foo::Qux {
            first: Lit::from(-1337_i64),
            comma: Default::default(),
            second: Lit::try_from(0.5).unwrap(),
        }
    );

    Ok(())
}

#[test]
fn parse_generic_type() -> Result<()> {
    /// For testing whether generic trait bouds are correctly placed
    /// on field types, and not just blindly on type parameters
    trait Dummy {
        type Assoc;
    }

    /// It must be `Eq + Debug`, though, because `std` derive macros aren't
    /// smart enough, and they do blindly apply bounds to type parameters.
    #[derive(PartialEq, Eq, Debug)]
    struct DoesNotImplParse;

    impl Dummy for DoesNotImplParse {
        type Assoc = LitStr;
    }

    #[derive(PartialEq, Eq, Debug, Parse)]
    struct GenericStruct<T: Dummy, U> {
        namespace: U,
        path_sep: token::PathSep,
        name: T::Assoc,
    }

    let actual_struct: GenericStruct<DoesNotImplParse, Ident>
        = parsel::parse_str(r#"my_ns :: "lorem ipsum""#)?;
    let expected_struct = GenericStruct {
        namespace: ident("my_ns"),
        path_sep: Default::default(),
        name: LitStr::from("lorem ipsum"),
    };
    test_assert_eq!(actual_struct, expected_struct);

    #[derive(PartialEq, Eq, Debug, Parse)]
    enum GenericEnum<X, Y: Dummy, Q> {
        X1(X),
        /// for an ambiguous prefix
        Y2(Y::Assoc, Y::Assoc),
        YQ {
            y: Y::Assoc,
            semi: token::Semi,
            q: Q,
        },
    }

    let actual_enum_1: GenericEnum<LitUint, DoesNotImplParse, Token![=>]>
        = parsel::parse_str("42_usize")?;
    let expected_enum_1 = GenericEnum::X1(LitUint::from(42_u64));
    test_assert_eq!(actual_enum_1, expected_enum_1);

    let actual_enum_2: GenericEnum<LitUint, DoesNotImplParse, Token![=>]>
        = parsel::parse_str(r#""foo bar! #qux"; =>"#)?;
    let expected_enum_2 = GenericEnum::YQ {
        y: LitStr::from("foo bar! #qux"),
        semi: Default::default(),
        q: Default::default(),
    };
    test_assert_eq!(actual_enum_2, expected_enum_2);

    Ok(())
}

#[test]
fn parse_recursive_type() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, Parse)]
    enum Expr {
        Add {
            lhs: MulExpr,
            op: token::Plus,
            rhs: MulExpr,
        },
        Sub {
            lhs: MulExpr,
            op: token::Minus,
            rhs: MulExpr,
        },
        Mul(MulExpr),
    }

    #[derive(PartialEq, Eq, Debug, Parse)]
    enum MulExpr {
        Mul {
            lhs: Term,
            op: token::Star,
            rhs: Term,
        },
        Div {
            lhs: Term,
            op: token::Slash,
            rhs: Term,
        },
        Term(Term),
    }

    #[derive(PartialEq, Eq, Debug, Parse)]
    enum Term {
        Lit(Lit),
        Var(Ident),
        Paren(
            #[parsel(recursive)]
            Box<Paren<Expr>>
        ),
    }

    let actual_expr: Expr = parsel::parse_str("(pq * 3.14) - 738291")?;
    let expected_expr = Expr::Sub {
        lhs: MulExpr::Term(Term::Paren(
            Box::new(Paren::new(
                Expr::Mul(MulExpr::Mul {
                    lhs: Term::Var(ident("pq")),
                    op: Default::default(),
                    rhs: Term::Lit(Lit::try_from(3.14).unwrap()),
                }),
                Span::call_site()
            )),
        )),
        op: Default::default(),
        rhs: MulExpr::Term(Term::Lit(Lit::from(738291_u64))),
    };
    test_assert_eq!(actual_expr, expected_expr);

    #[derive(PartialEq, Eq, Debug, Parse)]
    enum Cond {
        Or {
            lhs: AndExpr,
            op: token::Or,
            rhs: AndExpr,
        },
        And(AndExpr),
    }

    #[derive(PartialEq, Eq, Debug, Parse)]
    enum AndExpr {
        And {
            lhs: Predicate,
            op: token::And,
            rhs: Predicate,
        },
        Term(Predicate),
    }

    #[derive(PartialEq, Eq, Debug, Parse)]
    enum Predicate {
        Lit(LitBool),
        Var(Ident),
        Neg {
            bang: token::Not,
            #[parsel(recursive)]
            subexpr: Box<Predicate>,
        },
        Paren(
            #[parsel(recursive)]
            Box<Paren<Cond>>
        ),
    }

    let actual_cond: Cond = parsel::parse_str("true & (a_var | !false)")?;
    let expected_cond = Cond::And(AndExpr::And {
        lhs: Predicate::Lit(LitBool::from(true)),
        op: Default::default(),
        rhs: Predicate::Paren(Box::new(Paren::new(
            Cond::Or {
                lhs: AndExpr::Term(Predicate::Var(ident("a_var"))),
                op: Default::default(),
                rhs: AndExpr::Term(Predicate::Neg {
                    bang: Default::default(),
                    subexpr: Box::new(Predicate::Lit(LitBool::from(false))),
                }),
            },
            Span::call_site()
        ))),
    });
    test_assert_eq!(actual_cond, expected_cond);

    Ok(())
}
