# M2-deturck-4 blocked: DeTurck summand C2 reduced to section bridges

## Outcome

New Lean file:

```text
Poincare/Global/DeTurckSummandRegularity.lean
```

No existing Lean files were edited, and `Poincare.lean` was not changed.

The frozen target

```lean
theorem deTurckVectorFieldSummand_closedC2
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    ClosedC2TangentField (deTurckVectorFieldSummand g bg i)
```

was not stated. The unconditional payoff

```lean
theorem deTurckVectorFieldRegularAt_holds
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) :
    DeTurckVectorFieldRegularAt gt bg t
```

was also not stated. The current imports still lack the analytic bridge proving
the needed bundle-section `C²` regularity hypotheses.

## Verified partial progress

The new file is general in `n`.

It names the raw finite-basis field used by the summand:

```lean
noncomputable def deTurckModelBasisField
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    ∀ x : M, TangentSpace (closedSmoothModelWithCorners n) x
```

It names the metric-raised finite-coordinate field:

```lean
noncomputable def deTurckRaisedFinBasisField
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    ∀ x : M, TangentSpace (closedSmoothModelWithCorners n) x
```

It defines the exact `C²` regularity property needed for the tensorial
connection-difference section:

```lean
def ClosedC2ConnectionDifferenceSection
    (g bg : ClosedSmoothRiemannianMetric n M) : Prop
```

It proves the finite-basis definitional reductions:

```lean
deTurckModelBasisField_apply
deTurckModelBasisField_apply_eq_model
deTurck_finBasis_apply_eq_model
deTurck_finBasis_coord_eq_model
```

It imports the existing Gram-inverse machinery into the local shape needed by
this task:

```lean
theorem gramMatrix_inv_entry_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ
      (TangentSpace (closedSmoothModelWithCorners n) x))) :
    ContMDiffAt (closedSmoothModelWithCorners n) 𝓘(ℝ) 2
      (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x
```

It proves that the frozen summand is exactly the tensorial connection
difference applied to the two named fields:

```lean
theorem deTurckVectorFieldSummand_eq_bridge_fields
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    deTurckVectorFieldSummand g bg i =
      fun x : M =>
        ((g.leviCivita.difference bg.leviCivita) x
          (deTurckRaisedFinBasisField g i x))
          (deTurckModelBasisField i x)
```

It proves the conditional summand theorem from the honest regularity bridges:

```lean
theorem deTurckVectorFieldSummand_closedC2_of_bridge_regularities
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n)))
    (hDiff : ClosedC2ConnectionDifferenceSection g bg)
    (hBasis : ClosedC2TangentField (deTurckModelBasisField i))
    (hRaised : ClosedC2TangentField (deTurckRaisedFinBasisField g i)) :
    ClosedC2TangentField (deTurckVectorFieldSummand g bg i)
```

It also proves the conditional whole-field payoff through the existing reducer:

```lean
theorem deTurckVectorFieldRegularAt_holds_of_bridge_regularities
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (hDiff : ClosedC2ConnectionDifferenceSection (gt t) bg)
    (hBasis : ∀ i, ClosedC2TangentField (deTurckModelBasisField i))
    (hRaised : ∀ i, ClosedC2TangentField
      (deTurckRaisedFinBasisField (gt t) i)) :
    DeTurckVectorFieldRegularAt gt bg t
```

## Single missing statement

The next single statement that discharges this file is the bridge package:

```lean
theorem deTurckVectorFieldSummand_bridge_regularities
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    ClosedC2ConnectionDifferenceSection g bg ∧
    ClosedC2TangentField (deTurckModelBasisField i) ∧
    ClosedC2TangentField (deTurckRaisedFinBasisField g i)
```

With this theorem, `deTurckVectorFieldSummand_closedC2` follows immediately by
`deTurckVectorFieldSummand_closedC2_of_bridge_regularities`, and the
unconditional `deTurckVectorFieldRegularAt_holds` follows by
`deTurckVectorFieldRegularAt_holds_of_bridge_regularities`.

This package splits into the two analytic bridges anticipated by the previous
report:

* `C²` smoothness of `x ↦ (g.leviCivita.difference bg.leviCivita) x` as a
  hom-bundle section, from the two `leviCivita_contMDiff₂` facts.
* `C²` smoothness of the raw finite-basis field and the raised finite-coordinate
  field `x ↦ metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)`,
  likely by combining tangent-bundle finite-frame smoothness with the
  Gram-inverse machinery in `Global/ScalarVariation.lean`.

## Verification

Required command run:

```text
lake build Poincare.Global.DeTurckSummandRegularity
```

Actual result: success, `Build completed successfully (3080 jobs)`.
The build replayed existing upstream warnings and produced only linter warnings
in the new module about unused section variables on definitional helper lemmas.
