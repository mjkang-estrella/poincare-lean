Read harness/worker_contract.md first and obey it strictly.

# Task M1-hessian-symmetry: symmetry of the covariant Hessian on closed manifolds

Context on main: `Poincare/Global/Laplacian.lean` defines `g.hessianAt` for `g : ClosedSmoothRiemannianMetric n M`; its symmetry was deferred (see `harness/reports/M1-closed-laplacian_blocked.md`) pending (a) gradient-field regularity and (b) scalar second-derivative commutation. BOTH prerequisites may now be dischargeable: the canonical connection is smooth (`leviCivita_contMDiff` instance, `closedLeviCivitaConnection_contMDiff` — NEW since that report) and the transport machinery (Global/LeviCivitaTransport.lean, LeviCivitaRegularity.lean) can push scalar commutation through charts where the model side has Schwarz symmetry (ModelChristoffel/ModelLaplacian have the flat second-derivative symmetry tools; Mathlib has `isSymmSndFDerivAt` machinery).

Deliverable (in Global/Laplacian.lean or new Global/HessianSymmetry.lean + root import):

1. Gradient-field regularity: `g.gradient f` is a differentiable/ContMDiff tangent field at x for f ContMDiff 2 (or the honest order needed) — using the smoothness of the metric inverse (the raising map) + smoothness of df. Check LeviCivitaExistence's `pairingRegularity`/`differentiableAt`-style lemmas and Mathlib's `ContMDiffAt.clm_apply`-family for the raising composition.
2. The classical symmetry theorem:
   `theorem hessianAt_symm (hf : appropriate regularity of f) : g.hessianAt f x v w = g.hessianAt f x w v`
   Route: Hess f (X,Y) − Hess f (Y,X) = −df(Torsion(X,Y)) = 0 via `g.leviCivita_torsionFreeAt`, with the second-derivative commutator handled by the mlieBracket formulation (torsion involves the bracket; the bracket of coordinate/extended fields reduces to flat Schwarz in charts — use `chartTransportedLeviCivitaSection_mlieBracket_apply_chart` if helpful) OR directly via Mathlib's `VectorField.mlieBracket` Leibniz identities. Choose the formulation of hessianAt already in the file and prove symmetry for THAT (statement freeze on hessianAt's definition; if its shape makes symmetry unprovable, blocked-report with the exact issue instead of redefining).
3. Corollary if quick: `laplacianAt` via either slot order agrees.

Commit each green lemma. Blocked → greens + `harness/reports/M1-hessian-symmetry_blocked.md`. No sorry/axiom. `lake build`, report names.
