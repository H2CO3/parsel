use std::iter;
use proc_macro2::{TokenStream, TokenTree, Span};
use proc_macro2::{Ident, Literal, Group, Delimiter, Punct, Spacing};
use quickcheck::{TestResult, Arbitrary, Gen};
use quickcheck_macros::quickcheck;
use parsel::util::TokenStreamFormatter;

#[derive(Clone, Debug)]
struct TokenTreeGen(TokenTree);

impl Arbitrary for TokenTreeGen {
    fn arbitrary(gen: &mut Gen) -> Self {
        #[derive(Clone, Copy)]
        enum Token {
            LitInt,
            LitFloat,
            LitChar,
            LitStr,
            LitByteStr,
            Ident,
            Punct,
            Group,
        }

        let &kind = gen.choose(&[
            Token::LitInt,
            Token::LitFloat,
            Token::LitChar,
            Token::LitStr,
            Token::LitByteStr,
            Token::Ident,
            Token::Punct,
            Token::Group,
        ]).unwrap();

        let token = match kind {
            Token::LitInt => Literal::i64_unsuffixed(i64::arbitrary(gen)).into(),
            Token::LitFloat => {
                loop {
                    let x = f64::arbitrary(&mut *gen);

                    if x.is_finite() {
                        break Literal::f64_unsuffixed(x).into();
                    }
                }
            }
            Token::LitChar => Literal::character(char::arbitrary(gen)).into(),
            Token::LitStr => Literal::string(&String::arbitrary(gen)).into(),
            Token::LitByteStr => Literal::byte_string(&Vec::arbitrary(gen)).into(),
            Token::Ident => {
                let &ident = gen.choose(&["a", "_", "_foo", "multiple_words", "trait"]).unwrap();
                Ident::new(ident, Span::call_site()).into()
            }
            Token::Punct => {
                let &ch = gen.choose(&[
                    '+', '-', '*', '/',
                    '%', '|', '^', '&',
                    '!', '~', '#', '$',
                    '=', '?', '<', '>',
                    ',', ';', '.', '@',
                ]).unwrap();

                // Always generate `Spacing::Alone`, since it's not possible to tell
                // if an individual `Punct` is a punctuation in itself or part of a
                // multi-character string with `Spacing::Joint` characters.
                Punct::new(ch, Spacing::Alone).into()
            },
            Token::Group => {
                let &delimiter = gen.choose(&[
                    Delimiter::Parenthesis,
                    Delimiter::Bracket,
                    Delimiter::Brace,
                ]).unwrap();
                let TokenStreamGen(stream) = TokenStreamGen::arbitrary(gen);
                Group::new(delimiter, stream).into()
            }
        };

        TokenTreeGen(token)
    }
}

#[derive(Clone, Debug)]
struct TokenStreamGen(TokenStream);

impl Arbitrary for TokenStreamGen {
    fn arbitrary(gen: &mut Gen) -> Self {
        /// These only include 2-character operators.
        /// `<<=` and `>>=` are tested in doc-tests.
        static MULTICHAR_OPS: &[&str] = &[
            "==", "!=", "<=", ">=",
            "+=", "-=", "*=", "/=",
            "%=", "&=", "|=", "^=",
            "<<", ">>", "&&", "||",
        ];

        // Manually truncate to a couple of elements, because otherwise the
        // branching process never dies and there will be a stack overflow.
        let size = usize::arbitrary(&mut *gen) % 16;
        let mut tokens: Vec<_> = iter::repeat_with(|| TokenTreeGen::arbitrary(&mut *gen).0)
            .take(size)
            .collect();

        // When allowed pairs of punctuation characters occur, randomly join
        // them with some probability, in order to test multi-character operators.
        // Take care of 3 (or more) punctuations in a row by iterating over
        // disjoint chunks instead of sliding windows.
        for chunk in tokens.chunks_mut(2) {
            if let [TokenTree::Punct(prev), TokenTree::Punct(next)] = chunk {
                let op = format!("{}{}", prev.as_char(), next.as_char());
                if MULTICHAR_OPS.contains(&op.as_str()) {
                    *prev = Punct::new(prev.as_char(), Spacing::Joint);
                }
            }
        }

        let stream = tokens.into_iter().collect();

        TokenStreamGen(stream)
    }
}

#[quickcheck]
fn parse_pretty_printed_is_identity(stream: TokenStreamGen) -> TestResult {
    let TokenStreamGen(stream) = stream;
    let mut pretty = String::new();
    let mut fmt = TokenStreamFormatter::new(&mut pretty);

    if let Err(error) = fmt.write(stream.clone()) {
        return TestResult::error(error.to_string());
    }

    let parsed: TokenStream = match pretty.parse() {
        Ok(ts) => ts,
        Err(error) => return TestResult::error(error.to_string()),
    };

    TestResult::from_bool(stream.to_string() == parsed.to_string())
}
