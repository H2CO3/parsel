use core::convert::TryFrom;
use anyhow::{ensure, Result};
use parsel::quote::quote;
use parsel::{ToTokens, TokenStream};
use parsel::ast::{token, ident, Lit, LitBool, LitUint, LitFloat, Ident};


/// Return `Err` rather than panicking when the assertion fails.
macro_rules! test_assert_eq_token_stream {
    ($actual:expr, $expected:expr) => {
        let actual = $actual.to_token_stream().to_string();
        let expected = $expected.to_string();

        ensure!(
            actual.trim() == expected.trim(),
            "equality assertion failed\nactual:\n{actual}\nexpected:\n{expected}",
            actual = actual,
            expected = expected,
        );
    }
}

#[test]
fn print_struct_named_field() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, ToTokens)]
    struct Conditional {
        condition: Ident,
        qmark: token::Question,
        consequence: Lit,
        colon: token::Colon,
        alternative: Lit,
    }

    let actual = Conditional {
        condition: ident("has_frobnicator"),
        qmark: Default::default(),
        consequence: Lit::from("frobnicate"),
        colon: Default::default(),
        alternative: Lit::from(42_u128),
    };
    let expected = quote!{
        has_frobnicator ? "frobnicate" : 42
    };

    test_assert_eq_token_stream!(actual, expected);

    Ok(())
}

#[test]
fn print_struct_indexed_field() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, ToTokens)]
    struct Conditional(
        Ident,
        token::Question,
        Lit,
        token::Colon,
        Lit,
    );

    let actual = Conditional(
        ident("is_bug"),
        Default::default(),
        Lit::from(13_i128),
        Default::default(),
        Lit::try_from(37.0).unwrap(),
    );
    let expected = quote!{
        is_bug ? 13 : 37.0
    };

    test_assert_eq_token_stream!(actual, expected);

    Ok(())
}

#[test]
fn print_enum() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, ToTokens)]
    enum Expr {
        Literal(Lit),
        Add {
            lhs: Lit,
            op: token::Add,
            rhs: Lit,
        },
    }

    let actual1 = Expr::Add {
        lhs: Lit::from("foo"),
        op: Default::default(),
        rhs: Lit::from(987_i128),
    };
    let expected1 = quote!("foo" + 987);
    test_assert_eq_token_stream!(actual1, expected1);

    let actual2 = Expr::Literal(Lit::try_from(24.99).unwrap());
    let expected2 = quote!(24.99);
    test_assert_eq_token_stream!(actual2, expected2);

    Ok(())
}

#[test]
fn print_generic_type() -> Result<()> {
    /// For testing whether generic trait bouds are correctly placed
    /// on field types, and not just blindly on type parameters
    trait Dummy {
        type Assoc;
    }

    /// It must be `Eq + Debug`, though, because `std` derive macros aren't
    /// smart enough, and they do blindly apply bounds to type parameters.
    #[derive(PartialEq, Eq, Debug)]
    struct DoesNotImplToTokens;

    impl Dummy for DoesNotImplToTokens {
        type Assoc = Lit;
    }

    #[derive(PartialEq, Eq, Debug, ToTokens)]
    struct GenericStruct<T, U: Dummy> {
        key: T,
        eq: token::Eq,
        value: U::Assoc,
    }

    let actual_struct = GenericStruct::<Ident, DoesNotImplToTokens> {
        key: ident("the_key"),
        eq: Default::default(),
        value: Lit::from(true),
    };
    let expected_struct = quote!(the_key = true);
    test_assert_eq_token_stream!(actual_struct, expected_struct);

    #[derive(PartialEq, Eq, Debug, ToTokens)]
    enum GenericEnum<A, B> {
        Tuple(B, token::Comma, B),
        Struct {
            b: B,
            semi: token::Colon,
            a: A,
        },
        Unit,
    }

    let actual_enum_1 = GenericEnum::<Ident, LitFloat>::Tuple(
        LitFloat::try_from(31.42).unwrap(),
        token::Comma::default(),
        LitFloat::try_from(0.7238492).unwrap(),
    );
    let expected_enum_1 = quote!(31.42, 0.7238492);
    test_assert_eq_token_stream!(actual_enum_1, expected_enum_1);

    let actual_enum_2 = GenericEnum::<Ident, LitFloat>::Struct {
        b: LitFloat::try_from(6.789).unwrap(),
        semi: token::Colon::default(),
        a: ident("some_very_long_ident"),
    };
    let expected_enum_2 = quote!(6.789: some_very_long_ident);
    test_assert_eq_token_stream!(actual_enum_2, expected_enum_2);

    let actual_enum_3 = GenericEnum::<Ident, Box<GenericEnum<Lit, LitBool>>>::Unit;
    let expected_enum_3 = TokenStream::new();
    test_assert_eq_token_stream!(actual_enum_3, expected_enum_3);

    Ok(())
}

#[test]
fn print_recursive_type() -> Result<()> {
    #[derive(PartialEq, Eq, Debug, ToTokens)]
    enum Expr {
        Var(Ident),
        Lit(Lit),
        Add {
            #[parsel(recursive)]
            lhs: Box<Expr>,
            op: token::Add,
            #[parsel(recursive)]
            rhs: Box<Expr>,
        },
        Mul {
            #[parsel(recursive)]
            lhs: Box<Expr>,
            op: token::Star,
            #[parsel(recursive)]
            rhs: Box<Expr>,
        },
    }

    let actual_expr = Expr::Add {
        lhs: Box::new(Expr::Mul {
            lhs: Box::new(Expr::Var(ident("xyz"))),
            op: Default::default(),
            rhs: Box::new(Expr::Lit(Lit::from(false))),
        }),
        op: Default::default(),
        rhs: Box::new(Expr::Lit(Lit::from(192837_i128))),
    };
    let expected_expr = quote!(xyz * false + 192837);
    test_assert_eq_token_stream!(actual_expr, expected_expr);

    #[derive(PartialEq, Eq, Debug, ToTokens)]
    struct TokenList<T> {
        token: T,
        comma: token::Comma,
        #[parsel(recursive)]
        next: MyOption<Box<TokenList<T>>>,
    }

    #[derive(PartialEq, Eq, Debug, ToTokens)]
    enum MyOption<T> {
        Some(T),
        None,
    }

    let actual_list: TokenList<Ident> = TokenList {
        token: ident("hey"),
        comma: Default::default(),
        next: MyOption::Some(Box::new(TokenList {
            token: ident("loller_roller"),
            comma: Default::default(),
            next: MyOption::Some(Box::new(TokenList {
                token: ident("last_kw"),
                comma: Default::default(),
                next: MyOption::None,
            })),
        })),
    };
    let expected_list = quote![
        hey,
        loller_roller,
        last_kw,
    ];
    test_assert_eq_token_stream!(actual_list, expected_list);

    #[derive(PartialEq, Eq, Debug, ToTokens)]
    enum MutuallyRecursiveOne {
        Positive(
            token::Add,
            // This doesn't _need_ to be marked as recursive, but it can.
            // It is enough to break the constraint cycle at one single type,
            // but omitting the other constraint doesn't hurt, either.
            MutuallyRecursiveTwo,
        ),
        Negative {
            sign: token::Sub,
            num: MutuallyRecursiveTwo,
        },
        Nothing,
    }

    #[derive(PartialEq, Eq, Debug, ToTokens)]
    struct MutuallyRecursiveTwo {
        number: LitUint,
        #[parsel(recursive)]
        next: Box<MutuallyRecursiveOne>,
    }

    let mutual_actual = MutuallyRecursiveOne::Positive(
        Default::default(),
        MutuallyRecursiveTwo {
            number: LitUint::from(11111_u128),
            next: Box::new(MutuallyRecursiveOne::Negative {
                sign: token::Sub::default(),
                num: MutuallyRecursiveTwo {
                    number: LitUint::from(0_u128),
                    next: Box::new(MutuallyRecursiveOne::Nothing),
                },
            }),
        },
    );
    let mutual_expected = quote!(+11111 -0);
    test_assert_eq_token_stream!(mutual_actual, mutual_expected);

    Ok(())
}
