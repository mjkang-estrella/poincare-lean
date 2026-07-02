Read harness/worker_contract.md first and obey it strictly.

# Task M1-scalar-curvature: canonical curvature quantities for a closed smooth Riemannian metric

Context on main: `Poincare.LeviCivitaExistence.closedLeviCivitaConnection g` is the canonical Levi-Civita connection of `g : ClosedSmoothRiemannianMetric n M` (with `levi_civita_exists`/`levi_civita_unique`). The repo's manifold-level curvature layer (`Poincare/CurvatureTensoriality.lean`, `Poincare/CurvatureConditions.lean`, `Poincare/RicciFlowEquation.lean`) defines `curvatureOp`, `ricciBilinearAt`, `ricciTraceAt`, `scalarCurvatureAt`, `IsEinsteinAt`, ... for a general `CovariantDerivative` + metric. Read those files' actual signatures first.

Deliverable: NEW file `Poincare/Global/Curvature.lean` (+ root import) specializing the curvature layer to the canonical connection:

1. `def ClosedSmoothRiemannianMetric.leviCivita (g : ...) : CovariantDerivative ... := LeviCivitaExistence.closedLeviCivitaConnection g` — the canonical connection, plus restatements of its two characterizing properties and a corollary of `levi_civita_unique`: any torsion-free metric-compatible cov agrees with `g.leviCivita` (pointwise on differentiable fields).
2. Definitions `g.ricciAt x u w : ℝ` and `g.scalarAt x : ℝ` wiring `ricciBilinearAt` / the repo's scalar-curvature-at machinery to `g.leviCivita` and `g.inner` (match the curvature layer's expected argument shapes — whatever regularity data they need, discharge it from `g`'s smoothness like LeviCivitaExistence did via `pairingRegularity`; if a needed regularity piece is genuinely not derivable, carry it as an explicit hypothesis and document).
3. Genuine theorems (as many as fit; each committed separately):
   a. `g.IsEinsteinAt lam x → g.scalarAt x = n * lam` (specialize `scalarCurvatureAt_of_einstein`).
   b. Symmetry/bilinearity access lemmas for `g.ricciAt` (specialize ricciBilinearAt_add_left etc.).
   c. If tractable: the round-metric-on-model or flat-space example — `RicciFlowEquation.lean` has flat_ricciTraceAt_eq_zero; give the ClosedSmoothRiemannianMetric-level statement that a flat metric has scalarAt = 0 IF a clean specialization exists (else skip; do not force).
4. If any wiring is blocked by API mismatch, commit what's green and file `harness/reports/M1-scalar-curvature_blocked.md` with exact obstructions.

No sorry/axiom. `lake build Poincare.Global.Curvature`, commit, report declaration names.
