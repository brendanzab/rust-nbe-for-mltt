use mltt_core::syntax::{core, domain, DbIndex, DbLevel, UniverseLevel};
use mltt_core::validate;
use proptest::arbitrary::any;
use proptest::strategy::{Just, Strategy};
use proptest::{prop_compose, prop_oneof, proptest, proptest_helper};

/// `Γ` is a well-formed context
///
/// ```text
/// ⊢ Γ
/// ```
pub fn arb_context() -> impl Strategy<Value = validate::Context> {
    // ─────
    //  ⊢ •
    Just(validate::Context::new()).prop_recursive(
        8,   // 8 levels deep
        256, // Shoot for maximum size of 256 nodes
        10,  // We put up to 10 items per collection
        |inner| {
            //  ⊢ Γ      Γ ⊢ type T
            // ─────────────────────
            //      ⊢ Γ, x : T
            inner
                .prop_flat_map(|context| (arb_check_term(&context), Just(context)))
                .prop_map(|((term, ann), mut context)| {
                    let term_value = context.eval(&term).unwrap();
                    context.insert_local(term_value, ann);
                    context
                })
        },
    )
}

/// Universe levels
///
/// ```text
/// ul
/// ```
pub fn arb_universe_level() -> impl Strategy<Value = UniverseLevel> {
    any::<u32>().prop_map(UniverseLevel)
}

/// A pair of universe levels, where the first level is less than the second level
///
/// ```text
/// ul₁ < ul₂
/// ```
pub fn arb_universe_levels_lt() -> impl Strategy<Value = (UniverseLevel, UniverseLevel)> {
    any::<u32>().prop_flat_map(|base_level| {
        (
            Just(UniverseLevel(base_level)),
            (base_level..).prop_map(UniverseLevel),
        )
    })
}

/// ```text
/// Type^ul
/// ```
pub fn arb_universe() -> impl Strategy<Value = core::RcTerm> {
    arb_universe_level().prop_map(|level| core::RcTerm::from(core::Term::Universe(level)))
}

/// Looking up a variable `x` in `Γ` yields the type `T`
///
/// ```text
/// Γ ⊢ x lookup ↝ T
/// ```
pub fn arb_var(context: &validate::Context) -> Option<impl Strategy<Value = core::RcTerm>> {
    // ─────────────────────────
    //  Γ, x : T ⊢ x lookup ↝ T
    //
    //  x ≠ y     Γ ⊢ x lookup ↝ T₂
    // ─────────────────────────────
    //   Γ, y : T₁ ⊢ x lookup ↝ T₂

    match context.level() {
        DbLevel(0) => None,
        _ => Some(
            (0..context.level().0)
                .prop_map(|index| core::RcTerm::from(core::Term::Var(DbIndex(index)))),
        ),
    }
}

/// ```text
/// Γ ⊢ t : T
/// ```
pub fn arb_check_term(
    context: &validate::Context,
) -> impl Strategy<Value = (core::RcTerm, domain::RcType)> {
    prop_oneof![
        //         ul₁ < ul₂
        // ─────────────────────────
        //  Γ ⊢ Type^ul₁ : Type^ul₂
        arb_universe_levels_lt().prop_map(|(level1, level2)| (
            core::RcTerm::from(core::Term::Universe(level1)),
            domain::RcValue::from(domain::Value::Universe(level2))
        )),
    ]
    .prop_recursive(
        8,   // 8 levels deep
        256, // Shoot for maximum size of 256 nodes
        10,  // We put up to 10 items per collection
        |inner| {
            prop_oneof![
                inner,
                // TODO: Let
                //
                //  Γ ⊢ t₁ ↝ T₁    Γ, x : T₁ ⊢ t₂ : T₂
                // ────────────────────────────────────
                //      Γ ⊢ let x = t₁ in t₂ : T₂

                // arb_synth_term(context).prop_flat_map(|term| {
                //     let ty = validate::synth_term(context, &term).unwrap();
                //     let term_value = context.eval(&term).unwrap();
                //
                //     let mut body_context = context.clone();
                //     body_context.insert_local(term_value, ty);
                //
                //     arb_check_term(&body_context).prop_map(|(body_term, body_ty)| {
                //         (
                //             core::RcTerm::from(core::Term::Let(term, body_term)),
                //             body_ty,
                //         )
                //     })
                // }),

                // TODO: FunType

                // TODO: FunIntro

                // TODO: PairType

                // TODO: PairIntro

                // TODO: synth_term
                //
                //  Γ ⊢ t ↝ T
                // ───────────
                //  Γ ⊢ t : T
            ]
        },
    )
}

/// ```text
/// Γ ⊢ t ↝ T
/// ```
pub fn arb_synth_term(context: &validate::Context) -> impl Strategy<Value = core::RcTerm> {
    let leaf = prop_oneof![
        // ─────────────────────────────
        //  Γ ⊢ Type^ul ↝ Type^(ul + 1)
        arb_universe(),
    ];

    //  Γ ⊢ x lookup ↝ T
    // ──────────────────
    //    Γ ⊢ x ↝ T
    let leaf = match arb_var(context) {
        None => leaf.boxed(),
        Some(var) => prop_oneof![var, leaf].boxed(),
    };

    leaf.prop_recursive(
        8,   // 8 levels deep
        256, // Shoot for maximum size of 256 nodes
        10,  // We put up to 10 items per collection
        |inner| {
            prop_oneof![
                inner,
                // TODO: Let
                //
                //  Γ ⊢ t₁ ↝ T₁    Γ, x : t₁ ⊢ t₂ ↝ T₂
                // ────────────────────────────────────
                //      Γ ⊢ let x = t₁ in t₂ ↝ T₂

                // inner.clone().prop_flat_map(|term| {
                //     let context = &context;
                //     let ty = validate::synth_term(context, &term).unwrap();
                //     let term_value = context.eval(&term).unwrap();

                //     let mut body_context = context.clone();
                //     body_context.insert_local(term_value, ty);

                //     (Just(term), arb_synth_term(&body_context))
                //         .prop_map(|(term, body_term)| core::RcTerm::from(core::Term::Let(term, body_term)))
                // }),

                // TODO: FunApp
                //
                //   Γ ⊢ t₁ ↝ (x : T₂) → T₃    Γ ⊢ t₂ : T₂
                // ─────────────────────────────────────────
                //             Γ ⊢ t₁ t₂ ↝ T₃

                // TODO: PairFst
                //
                //   Γ ⊢ t ↝ (x : T₁) × T₂
                // ─────────────────────────
                //       Γ ⊢ t.1 ↝ T₁

                // TODO: PairSnd
                //
                //   Γ ⊢ t ↝ (x : T₁) × T₂
                // ─────────────────────────
                //   Γ ⊢ t.2 ↝ [x / t.1] T₂
            ]
        },
    )
}

/// ```text
/// Γ ⊢ type T
/// ```
pub fn arb_check_term_ty(context: &validate::Context) -> impl Strategy<Value = core::RcTerm> {
    prop_oneof![
        // ──────────────────
        //  Γ ⊢ type Type^ul
        arb_universe(),
    ]
    .prop_recursive(
        8,   // 8 levels deep
        256, // Shoot for maximum size of 256 nodes
        10,  // We put up to 10 items per collection
        |inner| {
            prop_oneof![
                inner,
                // TODO: Let

                // TODO: FunType

                // TODO: PairType

                // TODO: synth_term
            ]
        },
    )
}

prop_compose! {
    fn arb_context_check_term()
        (context in arb_context())
        ((term, ty) in arb_check_term(&context), context in Just(context))
        -> (validate::Context, core::RcTerm, domain::RcType)
    {
        (context, term, ty)
    }
}

prop_compose! {
    fn arb_context_synth_term()
        (context in arb_context())
        (term in arb_synth_term(&context), context in Just(context))
        -> (validate::Context, core::RcTerm)
    {
        (context, term)
    }
}

prop_compose! {
    fn arb_context_check_term_ty()
        (context in arb_context())
        (ty in arb_check_term_ty(&context), context in Just(context))
        -> (validate::Context, core::RcTerm)
    {
        (context, ty)
    }
}

proptest! {
    /// We always generate well-typed checkable terms
    #[test]
    fn prop_check_term_well_typed((context, term, ty) in arb_context_check_term()) {
        validate::check_term(&context, &term, &ty)?;
    }

    /// We always generate well-typed synthesizable terms
    #[test]
    fn prop_synth_term_well_typed((context, term) in arb_context_synth_term()) {
        validate::synth_term(&context, &term)?;
    }

    /// We always generate well-typed types
    #[test]
    fn prop_check_term_ty_well_typed((context, ty) in arb_context_check_term_ty()) {
        validate::check_term_ty(&context, &ty)?;
    }

    /// The type of a synthesized term in a context can always be used to check
    /// the term in the same context
    #[test]
    fn prop_check_synth_term((context, term) in arb_context_synth_term()) {
        let synth_ty = validate::synth_term(&context, &term)?;
        validate::check_term(&context, &term, &synth_ty)?;
    }

    // /// The type of a synthesized term in a context should always be checkable
    // /// as a type
    // #[test]
    // fn prop_check_ty_synth_term((context, term) in arb_context_synth_term()) {
    //     let synth_ty = validate::synth_term(&context, &term)?;
    //     validate::check_term_ty(&context, &synth_ty)?;
    // }

    // #[test]
    // fn preservation_check((context, term, ty) in arb_context_check_term()) {
    //     validate::check_term(context, ty)?;
    //     validate::check_term(context, &nbe::normalize(context, term)?, ty)?;
    // }

    // #[test]
    // fn preservation_synth((context, term) in arb_context_synth_term()) {
    //     let synth_ty = validate::synth_term(context, term)?;
    //     let synth_ty_value = nbe::eval(context, term)?;
    //     let norm_synth_ty = validate::synth_term(context, &nbe::normalize(context, term)?)?;
    //     prop_assert_eq!(synth_ty, norm_synth_ty);
    // }
}
