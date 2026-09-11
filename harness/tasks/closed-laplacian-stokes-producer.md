# Worker contract (plan-and-implement)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/closed-laplacian-stokes-producer`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/closed-laplacian-stokes-producer_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting step and the strongest compiled partial result; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section first.

# Task closed-laplacian-stokes-producer

Read `harness/reports/hamilton-pinching-to-reaction-survey_done.md` sections 3.1 and 3.4, `harness/reports/hamilton-mean-floor-from-energy-domination_done.md`, and the landed modules `Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean` (`ClosedLaplacianStokes`), `Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean` (`FiniteSubordinateHausdorffLaplacianGeometry` and its `localizedClosedLaplacianStokes` / `closedLaplacianStokes` theorems, `localizedScalar`, `fluxComponent`, `coordinateLaplacianDensity_eq_divergence`, `coordinateLaplacianDensity_integrable`), `Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean` (finite genuine chart cover), `Poincare/Global/HamiltonReactionCoreReduction.lean` and `HamiltonChartDensityLocalDomination.lean` (density integrability and domination from joint C³ entries), and Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`.

Module: `Poincare/Global/ClosedLaplacianStokesProducer.lean`. Namespace: `Poincare.ClosedLaplacianStokesProducer`.

Objective: produce the Stokes premise that the pinching-plan cores keep explicit, i.e. prove, for a closed smooth 3-manifold with a `ClosedSmoothRiemannianMetric 3 M` `g` (with the compatible Borel structure of the Hamilton core context) and a scalar function `φ` that is `ContMDiff ... 2`,

```lean
theorem closedLaplacianStokes_of_contMDiff_two
    (g : ClosedSmoothRiemannianMetric 3 M) (φ : M → ℝ)
    (hφ : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 φ) :
    ClosedLaplacianStokes g φ
```

(print the exact definition of `ClosedLaplacianStokes` first and match it: it should say the Riemannian integral of the Laplacian of `φ` vanishes, possibly in the localized chartwise form), and the corollary the cores need, `∀ t ∈ Ici 0, ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)` from a forward normalized flow with joint C³ entries (scalar `C²` on each slice is landed: `scalarAt_contMDiff_two_of_reactionDecayAnalyticData3` in `HamiltonReactionEndpoint.lean` and `scalarAt_contMDiffAt_two_of_normalizedRicciFlow`).

Route: construct a `FiniteSubordinateHausdorffLaplacianGeometry g φ` record from the finite genuine chart cover (chart regions, coordinate domains, inverse charts, densities from the landed area formula and density integrability), a smooth partition of unity subordinate to the chart regions (Mathlib), the coordinate representatives `φ ∘ inverseChart` (C², compact support inside the coordinate domain after multiplying by the partition function), the weight/inverse-metric/Christoffel fields from the chart metric (C¹ from joint regularity or from smoothness of `g` alone, since `g` is a fixed smooth metric here), and the compatibility identities the record asks for (`density_inverseMetric_compatibility`, `intrinsicCoordinateLaplacian_eq`, `localizedLaplacian_aestronglyMeasurable`); then apply the landed `closedLaplacianStokes` theorem of that record. Print the record's fields first (`#print FiniteSubordinateHausdorffLaplacianGeometry`) and audit which fields have landed producers; implement the missing ones. If one field resists (most likely `intrinsicCoordinateLaplacian_eq`, the identification of the intrinsic Laplacian with the coordinate expression), land every other field as separate lemmas and a partial record constructor, and display the exact resisting identity.

Exact stop condition: the displayed theorem and the flow corollary pass the gate; or a blocked report with the exact resisting field and the committed partial constructor.
