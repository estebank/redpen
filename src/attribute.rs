use std::collections::{HashMap, HashSet};

use rustc_ast::tokenstream::{self, TokenTree};
use rustc_ast::{ast, token};
use rustc_errors::{DiagnosticBuilder, ErrorGuaranteed};
use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::Ident;
use rustc_span::Span;

#[derive(Debug, PartialEq, Eq)]
pub enum RedpenAttribute {
    Disallow(HashMap<String, HashSet<String>>),
    DontPanic,
    WontPanic,
    WontAllocate,
    WontLeak,
    AssumeSafe,
}

struct Cursor<'a> {
    eof: TokenTree,
    cursor: tokenstream::RefTokenTreeCursor<'a>,
}

impl<'a> Cursor<'a> {
    fn new(cursor: tokenstream::RefTokenTreeCursor<'a>, end_span: Span) -> Self {
        let eof = TokenTree::Token(
            token::Token {
                kind: token::TokenKind::Eof,
                span: end_span,
            },
            tokenstream::Spacing::Alone,
        );
        Cursor { eof, cursor }
    }

    fn is_eof(&self) -> bool {
        self.cursor.look_ahead(0).is_none()
    }

    fn look_ahead(&self, n: usize) -> &TokenTree {
        self.cursor.look_ahead(n).unwrap_or(&self.eof)
    }

    fn next(&mut self) -> &TokenTree {
        self.cursor.next().unwrap_or(&self.eof)
    }
}

struct AttrParser<'tcx> {
    tcx: TyCtxt<'tcx>,
    hir_id: HirId,
}

impl<'tcx> AttrParser<'tcx> {
    fn error(
        &self,
        span: Span,
        decorate: impl for<'a, 'b> FnOnce(
            &'b mut DiagnosticBuilder<'a, ()>,
        ) -> &'b mut DiagnosticBuilder<'a, ()>,
    ) -> Result<!, ErrorGuaranteed> {
        self.tcx.struct_span_lint_hir(
            crate::INCORRECT_ATTRIBUTE,
            self.hir_id,
            span,
            "incorrect usage of `#[kint::preempt_count]`",
            decorate,
        );
        Err(self
            .tcx
            .sess
            .delay_span_bug(span, "incorrect usage of `#[kint::preempt_count]`"))
    }

    fn parse_comma_delimited(
        &self,
        mut cursor: Cursor<'_>,
        mut f: impl for<'a> FnMut(Cursor<'a>) -> Result<Cursor<'a>, ErrorGuaranteed>,
    ) -> Result<(), ErrorGuaranteed> {
        loop {
            if cursor.is_eof() {
                return Ok(());
            }

            cursor = f(cursor)?;

            if cursor.is_eof() {
                return Ok(());
            }

            // Check and skip `,`.
            let comma = cursor.next();
            if !matches!(
                comma,
                TokenTree::Token(
                    token::Token {
                        kind: token::TokenKind::Comma,
                        ..
                    },
                    _
                )
            ) {
                self.error(comma.span(), |diag| {
                    diag.help("`,` expected between property values")
                })?;
            }
        }
    }

    fn parse_eq_delimited<'a>(
        &self,
        mut cursor: Cursor<'a>,
        need_eq: impl FnOnce(Ident) -> Result<bool, ErrorGuaranteed>,
        f: impl FnOnce(Ident, Cursor<'a>) -> Result<Cursor<'a>, ErrorGuaranteed>,
    ) -> Result<Cursor<'a>, ErrorGuaranteed> {
        let prop = cursor.next();
        let invalid_prop = |span| {
            self.error(span, |diag| diag.help("identifier expected"))?;
        };

        let TokenTree::Token(token, _) = prop else {
            return invalid_prop(prop.span());
        };
        let Some((name, _)) = token.ident() else {
            return invalid_prop(token.span);
        };

        let need_eq = need_eq(name)?;

        // Check and skip `=`.
        let eq = cursor.look_ahead(0);
        let is_eq = matches!(
            eq,
            TokenTree::Token(
                token::Token {
                    kind: token::TokenKind::Eq,
                    ..
                },
                _
            )
        );
        if need_eq && !is_eq {
            self.error(eq.span(), |diag| {
                diag.help("`=` expected after property name")
            })?;
        }
        if !need_eq && is_eq {
            self.error(eq.span(), |diag| {
                diag.help("unexpected `=` after property name")
            })?;
        }

        if is_eq {
            cursor.next();
        }

        cursor = f(name, cursor)?;

        Ok(cursor)
    }

    #[allow(unused)]
    fn parse_i32<'a>(&self, mut cursor: Cursor<'a>) -> Result<(i32, Cursor<'a>), ErrorGuaranteed> {
        let expect_int = |span| self.error(span, |diag| diag.help("an integer expected"));

        let negative = if matches!(
            cursor.look_ahead(0),
            TokenTree::Token(
                token::Token {
                    kind: token::TokenKind::BinOp(token::BinOpToken::Minus),
                    ..
                },
                _
            )
        ) {
            cursor.next();
            true
        } else {
            false
        };

        let token = cursor.next();
        let TokenTree::Token(
            token::Token {
                kind: token::TokenKind::Literal(lit),
                ..
            },
            _,
        ) = token
        else {
            expect_int(token.span())?
        };
        if lit.kind != token::LitKind::Integer || lit.suffix.is_some() {
            expect_int(token.span())?;
        }
        let Some(v) = lit.symbol.as_str().parse::<i32>().ok() else {
            expect_int(token.span())?;
        };
        let v = if negative { -v } else { v };

        Ok((v, cursor))
    }

    fn parse_str_literal<'a>(
        &self,
        mut cursor: Cursor<'a>,
    ) -> Result<(String, Cursor<'a>), ErrorGuaranteed> {
        let expect_str = |span| self.error(span, |diag| diag.help("expected a string literal"));
        let token = cursor.next();
        let TokenTree::Token(
            token::Token {
                kind: token::TokenKind::Literal(lit),
                ..
            },
            _,
        ) = token
        else {
            expect_str(token.span())?
        };
        if lit.kind != token::LitKind::Str {
            expect_str(token.span())?;
        }
        Ok((lit.symbol.to_string(), cursor))
    }

    fn parse_disallow(
        &self,
        attr: &ast::Attribute,
        item: &ast::AttrItem,
    ) -> Result<HashMap<String, HashSet<String>>, ErrorGuaranteed> {
        let ast::AttrArgs::Delimited(ast::DelimArgs {
            dspan: delim_span,
            tokens: tts,
            ..
        }) = &item.args
        else {
            self.error(attr.span, |diag| {
                diag.help("correct usage looks like `#[redpen::disallow(...)]`")
            })?;
        };
        let mut map = HashMap::<String, HashSet<String>>::default();
        self.parse_comma_delimited(Cursor::new(tts.trees(), delim_span.close), |cursor| {
            self.parse_eq_delimited(
                cursor,
                |_| Ok(true),
                |name, mut cursor| {
                    let lit;
                    (lit, cursor) = self.parse_str_literal(cursor)?;
                    map.entry(name.to_string()).or_default().insert(lit);
                    Ok(cursor)
                },
            )
        })?;
        Ok(map)
    }

    fn parse(&self, attr: &ast::Attribute) -> Option<RedpenAttribute> {
        let ast::AttrKind::Normal(normal_attr) = &attr.kind else {
            return None;
        };
        let item = &normal_attr.item;
        if item.path.segments[0].ident.name != *crate::symbol::redpen {
            return None;
        };
        if item.path.segments.len() != 2 {
            self.tcx.struct_span_lint_hir(
                crate::INCORRECT_ATTRIBUTE,
                self.hir_id,
                attr.span,
                "invalid redpen attribute",
                |diag| diag,
            );
            return None;
        }
        match item.path.segments[1].ident.name {
            v if v == *crate::symbol::dont_panic => Some(RedpenAttribute::DontPanic),
            v if v == *crate::symbol::wont_panic => Some(RedpenAttribute::WontPanic),
            v if v == *crate::symbol::disallow => Some(RedpenAttribute::Disallow(
                self.parse_disallow(attr, item).ok()?,
            )),
            _ => {
                self.tcx.struct_span_lint_hir(
                    crate::INCORRECT_ATTRIBUTE,
                    self.hir_id,
                    item.path.segments[1].span(),
                    "unrecognized redpen attribute",
                    |diag| diag,
                );
                None
            }
        }
    }
}

pub fn parse_redpen_attribute(
    tcx: TyCtxt<'_>,
    hir_id: HirId,
    attr: &ast::Attribute,
) -> Option<RedpenAttribute> {
    AttrParser { tcx, hir_id }.parse(attr)
}
