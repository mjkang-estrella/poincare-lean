Read harness/worker_contract.md first and obey it strictly.

# Task M5-shrink-1: GOAL 9 — unconditional scalar-curvature regularity + Hamilton-interface shrinkage

Context: `HamiltonConvergencePinchedLimit3` (`Poincare/Global/SphereTheorem.lean:118`) carries three payload conjuncts; the first (`∀ x, MDifferentiableAt … (fun y ↦ g.scalarAt y) x`) should be DERIVABLE for every closed smooth metric now that the C² connection chain is in place: instances `leviCivita_contMDiff` / `leviCivita_contMDiff₂` (`Poincare/Global/Curvature.lean:43/50`), `scalarAt` defined via `CovariantDerivative.scalarCurvatureAt` with `metricBilinAt` (`Curvature.lean:159`), pairing regularity `metric_pairing_contMDiffAt_two` (`Curvature.lean:134`), plus the Gram-matrix/trace regularity machinery from the M3/M4 campaigns (grep `ScalarVariation.lean` / `ScalarEvolution.lean` / `RicciNorm.lean` for `Gram`, `contMDiffAt`, `mdifferentiableAt` helper lemmas around curvature-coefficient functions).

Deliverables:

1. In a NEW file `Poincare/Global/ScalarRegularity.lean`: `theorem scalarAt_mdifferentiableAt (g : ClosedSmoothRiemannianMetric n M) (x : M) : MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (fun y ↦ g.scalarAt y) x` — UNCONDITIONAL (no regularity hypotheses beyond the metric itself; the closed-manifold instance context of `RiemannianContext.lean` is fine; specialize to `n = 3` ONLY if the general case genuinely blocks, and say so in the report).
2. In a NEW file `Poincare/Global/PinchedLimitInterface.lean` (imports SphereTheorem + ScalarRegularity):
   - `def HamiltonConvergencePinchedLimit3Core (M : Type u) … : Prop := ∃ g : ClosedSmoothRiemannianMetric 3 M, (∀ x, g.tracelessRicciNormSqAt x = 0) ∧ (∃ x, 0 < g.scalarAt x)` (same instance context as the original at `SphereTheorem.lean:118`).
   - `theorem hamiltonConvergencePinchedLimit3_iff_core : HamiltonConvergencePinchedLimit3 M ↔ HamiltonConvergencePinchedLimit3Core M`.
   - `theorem poincareConjecture_of_hamiltonConvergenceCore_of_unitRecognition : (∀ N …, HamiltonConvergencePinchedLimit3Core N) → (∀ N …, UnitConstantCurvatureSphereRecognition3 N) → PoincareConjecture.{u}` mirroring `SphereTheorem.lean:333`.

   Do NOT edit existing files (incl. `Poincare.lean`); the orchestrator wires root imports at merge.
3. Report `harness/reports/M5-shrink-1_done.md` (or `_blocked.md`): if deliverable 1 blocks, isolate the exact missing regularity lemma(s) as precisely-stated statements with a decomposition plan — that report is itself valuable. Do NOT ship deliverable 2's `iff` without deliverable 1.

Verify: `lake build Poincare.Global.ScalarRegularity Poincare.Global.PinchedLimitInterface` and report the actual result. Commit your work.
