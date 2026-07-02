Read harness/worker_contract.md first and obey it strictly.

# Task M1-closed-laplacian: scalar Laplacian and covariant Hessian on closed Riemannian manifolds

Context on main: `Poincare/Global/Curvature.lean` shows the working pattern: define objects for `g : ClosedSmoothRiemannianMetric n M` via the canonical `g.leviCivita`, carrying `[CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]` (or whatever regularity is genuinely needed) as an explicit documented hypothesis while the regularity chain is being proven in parallel. The audit report (harness/reports/manifold_assets.md, "will not port cleanly" list) identifies this file as the gateway infrastructure for porting scalar evolution and Bochner from the single-chart model.

Deliverable: NEW file `Poincare/Global/Laplacian.lean` (+ root import):

1. `def g.gradientAt` / gradient vector field of a scalar function f : M → ℝ at x (raise df with g — fiberwise inverse; the nondegeneracy/finite-dimension machinery from LeviCivitaExistence/`metric_nondegenerate` and Mathlib's `extDerivFun` for df). Basic lemmas: g.inner x (grad f x) w = df_x(w).
2. `def g.hessianAt` — covariant Hessian of f at x via `g.leviCivita` applied to the gradient field (or the standard ∇df formulation — pick what the CovariantDerivative API supports; check how the single-chart model defines covariantHessian for guidance on shape). Symmetry theorem if reachable via torsion-freeness (the classical proof: Hess f (X,Y) − Hess f (Y,X) = −df(T(X,Y)) = 0); if the manifold-level symmetry needs second-derivative commutation not yet available, state what's missing in the report.
3. `def g.laplacianAt` — trace of the Hessian w.r.t. g (orthonormal-basis or metric-trace formulation; the fiber is a finite-dim inner product space via g.inner x, so Mathlib's trace machinery applies; check how `ricciTraceAt`/`scalarCurvatureAt` take traces in CurvatureTensoriality.lean and mirror that pattern for consistency).
4. Sanity theorems: linearity of laplacianAt in f; laplacianAt of a constant = 0.
5. Carried hypotheses must each be documented with a comment naming the ledger task that will discharge them. Blocked pieces → commit greens + `harness/reports/M1-closed-laplacian_blocked.md`.

No sorry/axiom. `lake build Poincare.Global.Laplacian`, commit, report declaration names.
