use std::ops::ControlFlow::{Break, Continue};

use clippy_utils::diagnostics::{multispan_sugg, span_lint_and_then};
use clippy_utils::paths::{CORE_ITER_ENUMERATE_METHOD, CORE_ITER_ENUMERATE_STRUCT};
use clippy_utils::source::snippet;
use clippy_utils::visitors::{for_each_expr_with_closures, Descend};
use clippy_utils::{expr_or_init, is_trait_method, match_def_path, pat_is_wild, path_to_local_id};
use rustc_hir::{Body, Expr, ExprKind, Param, PatKind};
use rustc_lint::LateContext;
use rustc_middle::ty::AdtDef;
use rustc_span::{sym, Span};

use crate::loops::UNUSED_ENUMERATE_INDEX;

/// Check for the `UNUSED_ENUMERATE_INDEX` lint outside of loops.
///
/// The lint is declared in `clippy_lints/src/loops/mod.rs`. There, the following pattern is
/// checked:
/// ```ignore
/// for (_, x) in some_iter.enumerate() {
///     // Index is ignored
/// }
/// ```
///
/// This `check` function checks for chained method calls constructs where we can detect that the
/// index is unused. Currently, this checks only for the following patterns:
/// ```ignore
/// some_iter.enumerate().map_function(|(_, x)| ..)
/// let x = some_iter.enumerate();
/// x.map_function(|(_, x)| ..)
/// ```
/// where `map_function` is one of `all`, `any`, `filter_map`, `find_map`, `flat_map`, `for_each` or
/// `map`.
///
/// # Preconditons
/// This function must be called not on the `enumerate` call expression itself, but on any of the
/// map functions listed above. It will ensure that `recv` is a `std::iter::Enumerate` instance and
/// that the method call is one of the `std::iter::Iterator` trait.
///
/// * `call_expr`: The map function call expression
/// * `recv`: The receiver of the call
/// * `closure_arg`: The argument to the map function call containing the closure/function to apply
pub(super) fn check(cx: &LateContext<'_>, call_expr: &Expr<'_>, recv: &Expr<'_>, closure_arg: &Expr<'_>) {
    let recv_ty = cx.typeck_results().expr_ty(recv);
    if let Some(recv_ty_defid) = recv_ty.ty_adt_def().map(AdtDef::did)
        // If we call a method on a `std::iter::Enumerate` instance
        && match_def_path(cx, recv_ty_defid, &CORE_ITER_ENUMERATE_STRUCT)
        // If we are calling a method of the `Iterator` trait
        && is_trait_method(cx, call_expr, sym::Iterator)
        // And the map argument is a closure
        && let ExprKind::Closure(closure) = closure_arg.kind
        && let closure_body = cx.tcx.hir().body(closure.body)
        // And that closure has one argument
        && let [closure_param] = closure_body.params
        && let Some(replacement) = index_replacements(cx, closure_param, closure_body)
    {
        // First, try to trigger the lint with our receiver. This will work when chaining methods:
        // ```
        // iter.enumerate().map(|(_, x)| x)
        // ^^^^^^^^^^^^^^^^ `recv`, a call to `std::iter::Iterator::enumerate`
        // ````
        if !trigger_lint(cx, recv, closure_param.span, &replacement) {
            // Otherwise, it may be that we have a binding. Find its initializer:
            // ```
            // let binding = iter.enumerate();
            //               ^^^^^^^^^^^^^^^^ `recv_init_expr`
            // binding.map(|(_, x)| x)
            // ^^^^^^^ `recv`, not a call to `std::iter::Iterator::enumerate`
            let recv_init_expr = expr_or_init(cx, recv);
            trigger_lint(cx, recv_init_expr, closure_param.span, &replacement);

            // Otherwise, the `Enumerate` probably comes from something that we cannot control.
            // This would for instance happen with:
            // ```
            // external_lib::some_function_returning_enumerate().map(|(_, x)| x)
            // ```
        }
    }
}

/// Check if the index of the closure is used. Returns [`Suggestion`] for suggestions if it isn't.
///
/// # Returns
/// If the index is unused, returns location(s) at which the suggestion needs to replace uses of the
/// tuple. If the index is used, returns `None`.
fn index_replacements<'tcx>(cx: &LateContext<'tcx>, param: &Param<'tcx>, body: &'tcx Body<'tcx>) -> Option<Suggestion> {
    match param.pat.kind {
        // If we have a tuple of 2 elements with the first element (the index) is either `_` or unused in the body
        PatKind::Tuple([index, elem], ..) if pat_is_wild(cx, &index.kind, body) => Some(Suggestion::Tuple(elem.span)),
        // If the tuple is bound to an identifier
        PatKind::Binding(_, tup_hir_id, _, _) => {
            // Log each access to `tuple.1` so that we can suggest replacements.
            let mut index_uses = Vec::new();
            let index_is_used = for_each_expr_with_closures(cx, body, |expr| {
                // If we access a field of our tuple
                if let ExprKind::Field(tup, field) = expr.kind
                    && path_to_local_id(tup, tup_hir_id)
                {
                    // If we refer to the index directly, it is used.
                    if field.as_str() == "0" {
                        Break(true)
                    } else {
                        index_uses.push(expr.span);
                        // Otherwise, do not descend so as to not evaluate our tuple expression.
                        Continue(Descend::No)
                    }
                } else if path_to_local_id(expr, tup_hir_id) {
                    // If we refer to the tuple as a whole, we use the index.
                    Break(true)
                } else {
                    Continue(Descend::Yes)
                }
            })
            // If we didn't `Break`, this means we haven't found a use of our index.
            .unwrap_or(false);

            if index_is_used {
                None
            } else {
                Some(Suggestion::Binding(index_uses))
            }
        },
        _ => None,
    }
}

/// Trigger the lint with the suggestion.
///
/// # Returns
/// If the lint was triggered, returns `true`. Otherwise, returns `false`.
fn trigger_lint(cx: &LateContext<'_>, recv: &Expr<'_>, closure_param_span: Span, replacement: &Suggestion) -> bool {
    // Check if our `recv` is a call to `std::iter::Iterator::enumerate`.
    if let ExprKind::MethodCall(_, enumerate_recv, _, enumerate_span) = recv.kind
        && let Some(enumerate_defid) = cx.typeck_results().type_dependent_def_id(recv.hir_id)
        && match_def_path(cx, enumerate_defid, &CORE_ITER_ENUMERATE_METHOD)
    {
        // If it is, we can suggest removing the tuple from the closure and the preceding call to
        // `enumerate`, whose span we can get from the `MethodCall`.
        span_lint_and_then(
            cx,
            UNUSED_ENUMERATE_INDEX,
            enumerate_span,
            "you seem to use `.enumerate()` and immediately discard the index",
            |diag| {
                multispan_sugg(
                    diag,
                    "remove the `.enumerate()` call",
                    std::iter::once((
                        enumerate_span.with_lo(enumerate_recv.span.source_callsite().hi()),
                        String::new(),
                    ))
                    .chain(replacement.to_suggestion_iter(cx, closure_param_span)),
                );
            },
        );
        true
    } else {
        false
    }
}

/// A replacement to be made in the suggestion for the lint.
enum Suggestion {
    /// The closure argument is bound as a tuple `|(_, x)|`. We need only replace it to `|x|`.
    Tuple(Span),
    /// The closure argument is bound as a binding `|t|`.
    ///
    /// In this case, we need to track every use of `t.1` and replace it to just `t`. We must not
    /// change the closure parameter span but every use in the body.
    Binding(Vec<Span>),
}

impl Suggestion {
    /// Create an iterator of suggestions for [`multispan_sugg`].
    fn to_suggestion_iter(
        &self,
        cx: &LateContext<'_>,
        closure_param_span: Span,
    ) -> Box<dyn Iterator<Item = (Span, String)> + '_> {
        match self {
            Suggestion::Tuple(elem_span) => Box::new(std::iter::once((
                closure_param_span,
                snippet(cx, *elem_span, "..").into_owned(),
            ))),
            Suggestion::Binding(use_spans) => {
                let param_str = snippet(cx, closure_param_span, "..");
                Box::new(use_spans.iter().map(move |span| (*span, param_str.to_string())))
            },
        }
    }
}
