use clippy_utils::diagnostics::span_lint_and_then;
use clippy_utils::source::snippet;
use rustc_errors::{Applicability, SuggestionStyle};
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::FnKind;
use rustc_hir::{
    Body, FnDecl, FnRetTy, GenericArg, GenericBound, ImplItem, ImplItemKind, ItemKind, OpaqueTy, TraitBoundModifier,
    TraitItem, TraitItemKind, TyKind, TypeBinding,
};
use rustc_hir_analysis::hir_ty_to_ty;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty::{self, ClauseKind, Generics, Ty, TyCtxt};
use rustc_session::declare_lint_pass;
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

declare_clippy_lint! {
    /// ### What it does
    /// Looks for bounds in `impl Trait` in return position that are implied by other bounds.
    /// This can happen when a trait is specified that another trait already has as a supertrait
    /// (e.g. `fn() -> impl Deref + DerefMut<Target = i32>` has an unnecessary `Deref` bound,
    /// because `Deref` is a supertrait of `DerefMut`)
    ///
    /// ### Why is this bad?
    /// Specifying more bounds than necessary adds needless complexity for the reader.
    ///
    /// ### Limitations
    /// This lint does not check for implied bounds transitively. Meaning that
    /// it does't check for implied bounds from supertraits of supertraits
    /// (e.g. `trait A {} trait B: A {} trait C: B {}`, then having an `fn() -> impl A + C`)
    ///
    /// ### Example
    /// ```no_run
    /// # use std::ops::{Deref,DerefMut};
    /// fn f() -> impl Deref<Target = i32> + DerefMut<Target = i32> {
    /// //             ^^^^^^^^^^^^^^^^^^^ unnecessary bound, already implied by the `DerefMut` trait bound
    ///     Box::new(123)
    /// }
    /// ```
    /// Use instead:
    /// ```no_run
    /// # use std::ops::{Deref,DerefMut};
    /// fn f() -> impl DerefMut<Target = i32> {
    ///     Box::new(123)
    /// }
    /// ```
    #[clippy::version = "1.74.0"]
    pub IMPLIED_BOUNDS_IN_IMPLS,
    complexity,
    "specifying bounds that are implied by other bounds in `impl Trait` type"
}
declare_lint_pass!(ImpliedBoundsInImpls => [IMPLIED_BOUNDS_IN_IMPLS]);

fn emit_lint(
    cx: &LateContext<'_>,
    poly_trait: &rustc_hir::PolyTraitRef<'_>,
    opaque_ty: &rustc_hir::OpaqueTy<'_>,
    index: usize,
    // The bindings that were implied, used for suggestion purposes since removing a bound with associated types
    // means we might need to then move it to a different bound
    implied_bindings: &[rustc_hir::TypeBinding<'_>],
    bound: &ImplTraitBound<'_>,
) {
    let implied_by = snippet(cx, bound.span, "..");

    span_lint_and_then(
        cx,
        IMPLIED_BOUNDS_IN_IMPLS,
        poly_trait.span,
        &format!("this bound is already specified as the supertrait of `{implied_by}`"),
        |diag| {
            // If we suggest removing a bound, we may also need to extend the span
            // to include the `+` token that is ahead or behind,
            // so we don't end up with something like `impl + B` or `impl A + `

            let implied_span_extended = if let Some(next_bound) = opaque_ty.bounds.get(index + 1) {
                poly_trait.span.to(next_bound.span().shrink_to_lo())
            } else if index > 0
                && let Some(prev_bound) = opaque_ty.bounds.get(index - 1)
            {
                prev_bound.span().shrink_to_hi().to(poly_trait.span.shrink_to_hi())
            } else {
                poly_trait.span
            };

            let mut sugg = vec![(implied_span_extended, String::new())];

            // We also might need to include associated type binding that were specified in the implied bound,
            // but omitted in the implied-by bound:
            // `fn f() -> impl Deref<Target = u8> + DerefMut`
            // If we're going to suggest removing `Deref<..>`, we'll need to put `<Target = u8>` on `DerefMut`
            let omitted_assoc_tys: Vec<_> = implied_bindings
                .iter()
                .filter(|binding| !bound.bindings.iter().any(|b| b.ident == binding.ident))
                .collect();

            if !omitted_assoc_tys.is_empty() {
                // `<>` needs to be added if there aren't yet any generic arguments or bindings
                let needs_angle_brackets = bound.args.is_empty() && bound.bindings.is_empty();
                let insert_span = match (bound.args, bound.bindings) {
                    ([.., arg], [.., binding]) => arg.span().max(binding.span).shrink_to_hi(),
                    ([.., arg], []) => arg.span().shrink_to_hi(),
                    ([], [.., binding]) => binding.span.shrink_to_hi(),
                    ([], []) => bound.span.shrink_to_hi(),
                };

                let mut associated_tys_sugg = if needs_angle_brackets {
                    "<".to_owned()
                } else {
                    // If angle brackets aren't needed (i.e., there are already generic arguments or bindings),
                    // we need to add a comma:
                    // `impl A<B, C >`
                    //             ^ if we insert `Assoc=i32` without a comma here, that'd be invalid syntax:
                    // `impl A<B, C Assoc=i32>`
                    ", ".to_owned()
                };

                for (index, binding) in omitted_assoc_tys.into_iter().enumerate() {
                    if index > 0 {
                        associated_tys_sugg += ", ";
                    }
                    associated_tys_sugg += &snippet(cx, binding.span, "..");
                }
                if needs_angle_brackets {
                    associated_tys_sugg += ">";
                }
                sugg.push((insert_span, associated_tys_sugg));
            }

            diag.multipart_suggestion_with_style(
                "try removing this bound",
                sugg,
                Applicability::MachineApplicable,
                SuggestionStyle::ShowAlways,
            );
        },
    );
}

/// Tries to "resolve" a type.
/// The index passed to this function must start with `Self=0`, i.e. it must be a valid
/// type parameter index.
/// If the index is out of bounds, it means that the generic parameter has a default type.
fn try_resolve_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: &'tcx [GenericArg<'tcx>],
    generics: &'tcx Generics,
    index: usize,
) -> Option<Ty<'tcx>> {
    match args.get(index - 1) {
        Some(GenericArg::Type(ty)) => Some(hir_ty_to_ty(tcx, ty)),
        Some(_) => None,
        None => Some(tcx.type_of(generics.params[index].def_id).skip_binder()),
    }
}

/// This function tries to, for all generic type parameters in a supertrait predicate `trait ...<U>:
/// GenericTrait<U>`, check if the substituted type in the implied-by bound matches with what's
/// substituted in the implied bound.
///
/// Consider this example.
/// ```rust,ignore
/// trait GenericTrait<T> {}
/// trait GenericSubTrait<T, U, V>: GenericTrait<U> {}
///                                 ^^^^^^^^^^^^^^^ trait_predicate_args: [Self#0, U#2]
///                                                 (the Self#0 is implicit: `<Self as GenericTrait<U>>`)
/// impl GenericTrait<i32> for () {}
/// impl GenericSubTrait<(), i32, ()> for () {}
/// impl GenericSubTrait<(), i64, ()> for () {}
///
/// fn f() -> impl GenericTrait<i32> + GenericSubTrait<(), i64, ()> {
///                             ^^^ implied_args       ^^^^^^^^^^^ implied_by_args
///                                                                (we are interested in `i64` specifically, as that
///                                                                 is what `U` in `GenericTrait<U>` is substituted with)
/// }
/// ```
/// Here i32 != i64, so this will return false.
fn is_same_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_predicate_args: &'tcx [ty::GenericArg<'tcx>],
    implied_by_args: &'tcx [GenericArg<'tcx>],
    implied_args: &'tcx [GenericArg<'tcx>],
    implied_by_def_id: DefId,
    implied_def_id: DefId,
) -> bool {
    // Get the generics of the two traits to be able to get default generic parameter.
    let implied_by_generics = tcx.generics_of(implied_by_def_id);
    let implied_generics = tcx.generics_of(implied_def_id);

    trait_predicate_args
        .iter()
        .enumerate()
        .skip(1) // skip `Self` implicit arg
        .all(|(arg_index, arg)| {
            if [
                implied_by_generics.host_effect_index,
                implied_generics.host_effect_index,
            ]
            .contains(&Some(arg_index))
            {
                // skip host effect params in determining whether generics are same
                return true;
            }
            if let Some(ty) = arg.as_type() {
                if let &ty::Param(ty::ParamTy { index, .. }) = ty.kind()
                    // `index == 0` means that it's referring to `Self`,
                    // in which case we don't try to substitute it
                    && index != 0
                    && let Some(ty_a) = try_resolve_type(tcx, implied_by_args, implied_by_generics, index as usize)
                    && let Some(ty_b) = try_resolve_type(tcx, implied_args, implied_generics, arg_index)
                {
                    ty_a == ty_b
                } else if let Some(ty_b) = try_resolve_type(tcx, implied_args, implied_generics, arg_index) {
                    ty == ty_b
                } else {
                    false
                }
            } else {
                false
            }
        })
}

struct ImplTraitBound<'tcx> {
    /// The span of the bound in the `impl Trait` type
    span: Span,
    /// The predicates defined in the trait referenced by this bound. This also contains the actual
    /// supertrait bounds
    predicates: &'tcx [(ty::Clause<'tcx>, Span)],
    /// The `DefId` of the trait being referenced by this bound
    trait_def_id: DefId,
    /// The generic arguments on the `impl Trait` bound
    args: &'tcx [GenericArg<'tcx>],
    /// The associated types on this bound
    bindings: &'tcx [TypeBinding<'tcx>],
}

/// Given an `impl Trait` type, gets all the supertraits from each bound ("implied bounds").
///
/// For `impl Deref + DerefMut + Eq` this returns `[Deref, PartialEq]`.
/// The `Deref` comes from `DerefMut` because `trait DerefMut: Deref {}`, and `PartialEq` comes from
/// `Eq`.
fn collect_supertrait_bounds<'tcx>(cx: &LateContext<'tcx>, opaque_ty: &OpaqueTy<'tcx>) -> Vec<ImplTraitBound<'tcx>> {
    opaque_ty
        .bounds
        .iter()
        .filter_map(|bound| {
            if let GenericBound::Trait(poly_trait, TraitBoundModifier::None) = bound
                && let [.., path] = poly_trait.trait_ref.path.segments
                && poly_trait.bound_generic_params.is_empty()
                && let Some(trait_def_id) = path.res.opt_def_id()
                && let predicates = cx.tcx.super_predicates_of(trait_def_id).predicates
                // If the trait has no supertrait, there is no need to collect anything from that bound
                && !predicates.is_empty()
            {
                Some(ImplTraitBound {
                    predicates,
                    args: path.args.map_or([].as_slice(), |p| p.args),
                    bindings: path.args.map_or([].as_slice(), |p| p.bindings),
                    trait_def_id,
                    span: bound.span(),
                })
            } else {
                None
            }
        })
        .collect()
}

/// Given a bound in an `impl Trait` type, looks for a trait in the set of supertraits (previously
/// collected in [`collect_supertrait_bounds`]) that matches (same trait and generic arguments).
fn find_bound_in_supertraits<'a, 'tcx>(
    cx: &LateContext<'tcx>,
    trait_def_id: DefId,
    args: &'tcx [GenericArg<'tcx>],
    bounds: &'a [ImplTraitBound<'tcx>],
) -> Option<&'a ImplTraitBound<'tcx>> {
    bounds.iter().find(|bound| {
        bound.predicates.iter().any(|(clause, _)| {
            if let ClauseKind::Trait(tr) = clause.kind().skip_binder()
                && tr.def_id() == trait_def_id
            {
                is_same_generics(
                    cx.tcx,
                    tr.trait_ref.args,
                    bound.args,
                    args,
                    bound.trait_def_id,
                    trait_def_id,
                )
            } else {
                false
            }
        })
    })
}

fn check(cx: &LateContext<'_>, decl: &FnDecl<'_>) {
    if let FnRetTy::Return(ty) = decl.output
        && let TyKind::OpaqueDef(item_id, ..) = ty.kind
        && let item = cx.tcx.hir().item(item_id)
        && let ItemKind::OpaqueTy(opaque_ty) = item.kind
        // Very often there is only a single bound, e.g. `impl Deref<..>`, in which case
        // we can avoid doing a bunch of stuff unnecessarily.
        && opaque_ty.bounds.len() > 1
    {
        let supertraits = collect_supertrait_bounds(cx, opaque_ty);

        // Lint all bounds in the `impl Trait` type that we've previously also seen in the set of
        // supertraits of each of the bounds.
        // This involves some extra logic when generic arguments are present, since
        // simply comparing trait `DefId`s won't be enough. We also need to compare the generics.
        for (index, bound) in opaque_ty.bounds.iter().enumerate() {
            if let GenericBound::Trait(poly_trait, TraitBoundModifier::None) = bound
                && let [.., path] = poly_trait.trait_ref.path.segments
                && let implied_args = path.args.map_or([].as_slice(), |a| a.args)
                && let implied_bindings = path.args.map_or([].as_slice(), |a| a.bindings)
                && let Some(def_id) = poly_trait.trait_ref.path.res.opt_def_id()
                && let Some(bound) = find_bound_in_supertraits(cx, def_id, implied_args, &supertraits)
            {
                emit_lint(cx, poly_trait, opaque_ty, index, implied_bindings, bound);
            }
        }
    }
}

impl LateLintPass<'_> for ImpliedBoundsInImpls {
    fn check_fn(
        &mut self,
        cx: &LateContext<'_>,
        _: FnKind<'_>,
        decl: &FnDecl<'_>,
        _: &Body<'_>,
        _: Span,
        _: LocalDefId,
    ) {
        check(cx, decl);
    }
    fn check_trait_item(&mut self, cx: &LateContext<'_>, item: &TraitItem<'_>) {
        if let TraitItemKind::Fn(sig, ..) = &item.kind {
            check(cx, sig.decl);
        }
    }
    fn check_impl_item(&mut self, cx: &LateContext<'_>, item: &ImplItem<'_>) {
        if let ImplItemKind::Fn(sig, ..) = &item.kind {
            check(cx, sig.decl);
        }
    }
}
