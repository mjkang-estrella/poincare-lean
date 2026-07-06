Read harness/worker_contract.md first and obey it strictly.

# Task M5-vol-5: GOAL 10 — total and mean scalar curvature

Context: `volumeMeasure g` is defined (`Poincare/Global/VolumeMeasure.lean`) and FINITE on closed manifolds (`volumeMeasure_isFiniteMeasure`, `Poincare/Global/VolumeFinitenessComparison.lean`). `scalarAt` is `MDifferentiableAt` everywhere (`scalarAt_mdifferentiableAt`, `Poincare/Global/ScalarRegularity.lean`) hence continuous; `M` is compact. Everything for integration exists.

Deliverables, in a NEW file `Poincare/Global/ScalarIntegral.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. CONTINUITY: `theorem scalarAt_continuous (g) : Continuous (fun x : M ↦ g.scalarAt x)` (from `MDifferentiableAt.continuousAt` pointwise + `continuous_iff_continuousAt`).
2. INTEGRABILITY: `theorem scalarAt_integrable (g) : MeasureTheory.Integrable (fun x ↦ g.scalarAt x) (volumeMeasure g)` (continuous on compact ⟹ bounded; bounded measurable vs finite measure — mine Mathlib's `Continuous.integrable_of_hasCompactSupport`/`isCompact_univ` + finite-measure integrability lemmas; match `VolumeMeasure.lean`'s measurable-space plumbing exactly).
3. THE FUNCTIONALS: `noncomputable def totalScalar (g) : ℝ := ∫ x, g.scalarAt x ∂(volumeMeasure g)` and `noncomputable def meanScalar (g) : ℝ := totalScalar g / (volumeMeasure g Set.univ).toReal`, with basic lemmas: `totalScalar` of an Einstein-`lam` metric (`∀ x, g.IsEinsteinAt lam x` — scalar ≡ `3·lam` at `n = 3` or `n·lam` general) `= n·lam · (volume)` and `meanScalar = n·lam` when volume ≠ 0 (positivity of the volume of a nonempty closed manifold is likely still open — take `volume ≠ 0` as an explicit hypothesis if so, and note it as the isolated next lemma).
4. Report `harness/reports/M5-vol-5_{done|blocked}.md`: signatures + normalized-flow roadmap (the `−2Ric + (2/n)·meanScalar·g` equation statement is now stateable — sketch it).

No vacuous wrappers. Verify: `lake build Poincare.Global.ScalarIntegral` and report the actual result. Commit your work.
