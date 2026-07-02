Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-existence: existence of a Levi-Civita connection (exploration + first verified layer)

Context on main: `Poincare/Global/LeviCivita.lean` now has `IsMetricCompatible`, `MDiffAtTangentField`, and `levi_civita_unique` (Koszul/S₃ uniqueness) over `Poincare.ClosedSmoothRiemannianMetric` and Mathlib's `CovariantDerivative`. Goal of this task: make real, verified progress toward
`theorem levi_civita_exists : ∃ cov, IsMetricCompatible g cov ∧ cov.torsion = 0`,
knowing full existence may exceed one session. This is EXPLORATION+FOUNDATION: a verified partial layer plus a precise decomposition is a success outcome.

Two candidate routes — evaluate BOTH against the actual Mathlib API before committing to one (write your route decision as comments / in the report):

Route A (global Koszul): define the candidate ⟪∇_X Y, Z⟫ by the 6-term Koszul formula (three extDerivFun terms of pairings + three bracket/metric terms — Mathlib has `VectorField.mlieBracket`; check `Mathlib/Geometry/Manifold/VectorField/*`). Then recover ∇_X Y from nondegeneracy of g fiberwise. Hard points: showing the result is tensorial in X and a covariant derivative in Y; differentiability side conditions.

Route B (chart transport): build the connection in a chart from the flat model — this repo's `Poincare/ModelChristoffel.lean` + `KoszulExistence.lean` prove Koszul existence in a single flat chart; Mathlib's `IsCovariantDerivativeOn` is set-local, which suggests: define the Christoffel covariant derivative on each chart domain, prove `IsCovariantDerivativeOn` there, and glue (uniqueness on overlaps would come from the chart-local analogue of levi_civita_unique). Hard points: pulling the metric back through `extChartAt`, transporting differentiability.

Deliverables (in order of priority; commit each verified piece separately to `Poincare/Global/LeviCivitaExistence.lean` + root import):
1. The route decision with API evidence (comments or `harness/reports/M1-lc-existence_notes.md`).
2. At least one substantive verified lemma on the chosen route (e.g. Route A: the Koszul candidate is well-defined + ℝ-linear in Z with the fiberwise-nondegeneracy recovery lemma; Route B: chart-domain `IsCovariantDerivativeOn` for the pulled-back Christoffel operator).
3. A decomposition of the remaining work into ≤5 crisply-stated subtasks with the exact Lean statements they must prove, written to `harness/reports/M1-lc-existence_notes.md`.

No sorry/axiom in committed Lean. Build `lake build Poincare.Global.LeviCivitaExistence`, commit, report exact declaration names.
