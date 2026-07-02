Read harness/worker_contract.md first and obey it strictly.

# Task M1-ricci-norm: Ricci endomorphism, |Ric|², and the pinching inequality on closed manifolds

Context on main: `Poincare/Global/Curvature.lean` has `g.ricciAt` (symmetric bilinear) and `g.scalarAt` for `g : ClosedSmoothRiemannianMetric n M`, carrying a documented regularity hypothesis. The single-chart model (`Poincare/ModelLaplacian.lean`) has the full pinching suite (`ricciNormSq_ge_scalar_sq_div`, equality iff Einstein, strict version) proven via general spectral lemmas on operator traces (`trace_comp_self_nonneg`, `trace_sq_le` etc. — find their exact names/locations; they act on endomorphisms of a finite-dim real inner-product space and may be reusable verbatim since fibers `TangentSpace I x` with `g.inner x` are exactly that).

Deliverable: NEW file `Poincare/Global/RicciNorm.lean` (+ root import), the audit's "ports cleanly" item:

1. `def g.ricciEndoAt x : TangentSpace I x →ₗ[ℝ] TangentSpace I x` — the Ricci endomorphism (raise one index of ricciAt via g; fiberwise, using nondegeneracy + finite dimension). Lemma: `g.inner x (g.ricciEndoAt x u) w = g.ricciAt x u w`; self-adjointness from ricciAt_symm.
2. `def g.ricciNormSqAt x : ℝ` — |Ric|² as the trace of ricciEndoAt ∘ ricciEndoAt (mirror the model's coordRicciNormSq_eq_trace shape). Lemma: `g.scalarAt x = trace of ricciEndoAt` (wire to however scalarAt was defined in Curvature.lean — prove the trace identification or, if scalarAt's definition makes this definitional, provide the rfl-lemma).
3. The pinching inequality: `g.scalarAt x ^ 2 ≤ n * g.ricciNormSqAt x` via the model's spectral trace lemmas (import them if they're stated abstractly; re-prove abstractly in this file if they're buried in model-specific form — in that case make them abstract over any finite-dim real inner-product space so both layers can share).
4. Stretch (only if clean): equality iff Einstein at x (`g.ricciEndoAt x = (g.scalarAt x / n) • id`), mirroring the model's iff.
5. Blocked pieces → commit greens + `harness/reports/M1-ricci-norm_blocked.md`.

No sorry/axiom. `lake build Poincare.Global.RicciNorm`, commit, report declaration names.
