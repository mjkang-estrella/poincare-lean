# M2-deturck-3 blocked: DeTurck field regularity reduced to summand C²

## Outcome

New Lean file:

```text
Poincare/Global/DeTurckFieldRegularity.lean
```

No existing Lean files were edited, and `Poincare.lean` was not changed.

The unconditional target

```lean
theorem deTurckVectorFieldRegularAt_holds
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) :
    DeTurckVectorFieldRegularAt gt bg t
```

was not stated, because the remaining analytic bridge is not currently
available in the imported API.

## Verified partial progress

The new file is general in `n`.

It defines the named trace summand:

```lean
noncomputable def deTurckVectorFieldSummand
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    ∀ x : M, TangentSpace (closedSmoothModelWithCorners n) x
```

It proves that the pointwise connection-difference definition is exactly
Mathlib's tensorial connection difference:

```lean
theorem deTurckConnectionDifferenceAt_eq_difference
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) (u w : TM x) :
    deTurckConnectionDifferenceAt g bg x u w =
      ((g.leviCivita.difference bg.leviCivita) x w) u
```

This also discharges the algebraic bilinearity wrappers:

```lean
deTurckConnectionDifferenceAt_add_left
deTurckConnectionDifferenceAt_smul_left
deTurckConnectionDifferenceAt_add_right
deTurckConnectionDifferenceAt_smul_right
```

It decomposes the field into named summands:

```lean
theorem deTurckVectorFieldAt_eq_sum_summands
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) :
    deTurckVectorFieldAt g bg x =
      ∑ i, deTurckVectorFieldSummand g bg i x
```

It proves the finite-sum regularity reducer:

```lean
theorem deTurckVectorFieldRegularAt_holds_of_summand_regularity
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (hSummand : ∀ i : Fin (Module.finrank ℝ (ClosedSmoothModel n)),
      ClosedC2TangentField
        (deTurckVectorFieldSummand (gt t) bg i)) :
    DeTurckVectorFieldRegularAt gt bg t
```

It also includes the small payoff/glue extractor:

```lean
theorem isDeTurckGaugedFlowAt.deTurckField
    (h : IsDeTurckGaugedFlowAt gt bg t x) :
    DeTurckVectorFieldRegularAt gt bg t
```

This shows the concrete gauged-flow predicate carries exactly the required
`Wt` regularity clause once the DeTurck field regularity is available.

## Single missing statement for the next task

The remaining theorem should be:

```lean
theorem deTurckVectorFieldSummand_closedC2
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    ClosedC2TangentField (deTurckVectorFieldSummand g bg i)
```

Together with
`deTurckVectorFieldRegularAt_holds_of_summand_regularity`, this proves the
original target immediately by applying the theorem to `g := gt t`.

The proof likely needs one genuine regularity bridge not yet present as an
importable lemma:

* `C²` smoothness of the tensorial section
  `x ↦ (g.leviCivita.difference bg.leviCivita) x`, as a bundle section valued
  in `TM x →L[ℝ] TM x →L[ℝ] TM x`, from
  `leviCivita_contMDiff₂ g` and `leviCivita_contMDiff₂ bg`.
* `C²` smoothness of the raised basis field
  `x ↦ metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)`.

The existing files expose the tensorial `difference` and first-order/pointwise
metric-dual algebra, but I did not find an existing closed `C²` global theorem
combining those into the summand field.

## Verification

Required command run:

```text
lake build Poincare.Global.DeTurckFieldRegularity
```

Actual result: success, `Build completed successfully (3079 jobs)`.
The build replayed existing upstream warnings; the new module built.
