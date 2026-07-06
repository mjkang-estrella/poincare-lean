Read harness/worker_contract.md first and obey it strictly.

# Task M2-scope-1: GOAL 9 — short-time-existence scoping + honest interface layer

Context: the analytic wall behind `HamiltonConvergencePinchedLimit3Core` (`Poincare/Global/PinchedLimitInterface.lean`) decomposes classically as: (A) short-time existence for Ricci flow on closed 3-manifolds (Hamilton/DeTurck), (B) Hamilton's 1982 a-priori estimates (the repo has the pinching estimates PROVEN: `hamilton_pinching_preserved`, `hamilton_pinching_improvement` in `Poincare/Global/ScalarEvolution.lean`/`ScalarVariation.lean`), (C) normalized-flow convergence to a positive Einstein metric (`PositiveEinsteinMetric3`, `Poincare/Global/EinsteinInterface.lean`). This task begins front (A) as SCOPING + STATEMENT LAYER — no PDE proofs expected.

Deliverables:

1. REPORT `harness/reports/M2-scope-1_assets.md`: inventory the pinned Mathlib for parabolic-PDE prerequisites — Sobolev/Hölder spaces, heat semigroup/kernel, linear parabolic existence/Schauder, second-order elliptic operators, function-space completeness tools (`MeasureTheory.Lp`, `ContDiffBump`, Fourier), ODE-in-Banach (`Mathlib/Analysis/ODE/`). Honest verdict per ingredient: exists / partial / absent. Then map Hamilton 1982 / DeTurck 1983 short-time existence into 5-8 named sub-obligations with exact repo-vocabulary spellings and difficulty ratings.

2. STATEMENT LAYER, in a NEW file `Poincare/Global/ShortTimeInterface.lean` (do NOT edit existing files, incl. `Poincare.lean`):
   - `def RicciFlowShortTimeExistence3 (M : Type u) [context as in SphereTheorem.lean] : Prop` — for every initial metric `g₀ : ClosedSmoothRiemannianMetric 3 M` there exist `T > 0` and a family `gt : ℝ → ClosedSmoothRiemannianMetric 3 M` with `gt 0 = g₀` and `∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x` (`Poincare/Global/RicciFlow.lean:40`). Exact quantifier packaging free; the honest content (every initial closed metric flows for positive time) is frozen.
   - Non-vacuity SHAPE check: the target family type is inhabited — e.g. the constant family of a metric satisfies `gt 0 = g₀`; and cite/reuse the repo's static Ricci-flat instance (`Global/RicciFlow.lean`) to exhibit that the flow-equation clause is satisfiable in the static Ricci-flat case (an `example` or small lemma; do NOT fake a general witness).
   - A consumption theorem proving the interface plugs into the existing evolution layer: e.g. from `RicciFlowShortTimeExistence3 M` and any `g₀`, obtain a family satisfying the hypotheses shape consumed by `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`-style theorems at flow times (state honestly what is and is not derivable — if only the flow clause itself transfers, prove exactly that and say so).

3. Report the final signatures + a 3-5 task roadmap for the DeTurck reduction statement layer (DeTurck vector field, Ricci-DeTurck flow, pullback equivalence) in the same report file.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ShortTimeInterface` and report the actual result. Commit your work.
