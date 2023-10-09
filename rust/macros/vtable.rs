// SPDX-License-Identifier: GPL-2.0

use proc_macro::{Delimiter, Group, TokenStream, TokenTree};
use std::collections::HashSet;
use std::fmt::Write;

pub(crate) fn vtable(_attr: TokenStream, ts: TokenStream) -> TokenStream {
    let mut tokens: Vec<_> = ts.into_iter().collect();

    // Scan for the `trait` or `impl` keyword.
    let is_trait = tokens
        .iter()
        .find_map(|token| match token {
            TokenTree::Ident(ident) => match ident.to_string().as_str() {
                "trait" => Some(true),
                "impl" => Some(false),
                _ => None,
            },
            _ => None,
        })
        .expect("#[vtable] attribute should only be applied to trait or impl block");

    // Retrieve the main body. The main body should be the last token tree.
    let body = match tokens.pop() {
        Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Brace => group,
        _ => panic!("cannot locate main body of trait or impl block"),
    };

    let mut body_it = body.stream().into_iter();
    let mut new_body = vec![];
    let mut functions = Vec::new();
    let mut consts = HashSet::new();
    let mut optional_attr = None;
    while let Some(token) = body_it.next() {
        match token {
            TokenTree::Ident(fn_ident) if fn_ident.to_string() == "fn" => {
                let fn_name = match body_it.next() {
                    Some(TokenTree::Ident(ident)) => {
                        new_body.push(TokenTree::Ident(fn_ident));
                        new_body.push(TokenTree::Ident(ident.clone()));
                        ident.to_string()
                    }
                    // Possibly we've encountered a fn pointer type instead.
                    Some(tt) => {
                        if let Some(attr) = optional_attr.take() {
                            // There was a `#[optional]` attribute in front of the `fn` keyword,
                            // which should not happen for function pointers, so add it and let the
                            // compiler complain.
                            new_body.extend(attr);
                        }
                        new_body.push(TokenTree::Ident(fn_ident));
                        new_body.push(tt);
                        continue;
                    }
                    None => continue,
                };
                if optional_attr.take().is_some() {
                    // Scan until we find the `;` at the end of the function declaration and
                    // replace it with `{ ::kernel::build_error("<explanation>") }`.
                    let mut span = None;
                    while let Some(next) = body_it.next() {
                        match next {
                            TokenTree::Punct(punct) if punct.as_char() == ';' => {
                                span = Some(punct.span());
                                // Do not push `;`.
                                break;
                            }
                            tt => new_body.push(tt),
                        }
                    }
                    let Some(span) = span else {
                        panic!("Could not find terminating `;` of function `{fn_name}`.")
                    };
                    new_body.extend(quote_spanned!(span =>
                        {
                            ::kernel::build_error(
                                "Optional `#[vtable]` trait functions must not be called."
                            )
                        }
                    ));
                }
                functions.push(fn_name);
            }
            TokenTree::Ident(ident) if ident.to_string() == "const" => {
                if let Some(attr) = optional_attr.take() {
                    // There was a `#[optional]` attribute in front of this `const` keyword, which
                    // should not happen, so add it and let the compiler complain.
                    new_body.extend(attr);
                }
                new_body.push(TokenTree::Ident(ident));
                let const_name = match body_it.next() {
                    Some(TokenTree::Ident(ident)) => {
                        new_body.push(TokenTree::Ident(ident.clone()));
                        ident.to_string()
                    }
                    // Possibly we've encountered an inline const block instead.
                    Some(tt) => {
                        new_body.push(tt);
                        continue;
                    }
                    None => continue,
                };
                consts.insert(const_name);
            }
            // Search for `#[optional]`.
            TokenTree::Punct(punct) if punct.as_char() == '#' => match body_it.next() {
                Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Bracket => {
                    let contents = group.stream().into_iter().collect::<Vec<_>>();
                    match (contents.len(), contents.get(0)) {
                        (1, Some(TokenTree::Ident(ident))) if ident.to_string() == "optional" => {
                            optional_attr =
                                Some(vec![TokenTree::Punct(punct), TokenTree::Group(group)]);
                        }
                        _ => {
                            new_body.push(TokenTree::Punct(punct));
                            new_body.push(TokenTree::Group(group));
                        }
                    }
                }
                Some(tt) => {
                    new_body.push(TokenTree::Punct(punct));
                    new_body.push(tt);
                }
                None => new_body.push(TokenTree::Punct(punct)),
            },
            tt => new_body.push(tt),
        }
    }

    let mut const_items;
    if is_trait {
        const_items = "
                /// A marker to prevent implementors from forgetting to use [`#[vtable]`](vtable)
                /// attribute when implementing this trait.
                const USE_VTABLE_ATTR: ();
        "
        .to_owned();

        for f in functions {
            let gen_const_name = format!("HAS_{}", f.to_uppercase());
            // Skip if it's declared already -- this allows user override.
            if consts.contains(&gen_const_name) {
                continue;
            }
            // We don't know on the implementation-site whether a method is required or provided
            // so we have to generate a const for all methods.
            write!(
                const_items,
                "/// Indicates if the `{f}` method is overridden by the implementor.
                const {gen_const_name}: bool = false;",
            )
            .unwrap();
            consts.insert(gen_const_name);
        }
    } else {
        const_items = "const USE_VTABLE_ATTR: () = ();".to_owned();

        for f in functions {
            let gen_const_name = format!("HAS_{}", f.to_uppercase());
            if consts.contains(&gen_const_name) {
                continue;
            }
            write!(const_items, "const {gen_const_name}: bool = true;").unwrap();
        }
    }

    let new_body = vec![
        const_items.parse().unwrap(),
        TokenStream::from_iter(new_body),
    ]
    .into_iter()
    .collect();
    tokens.push(TokenTree::Group(Group::new(Delimiter::Brace, new_body)));
    tokens.into_iter().collect()
}
