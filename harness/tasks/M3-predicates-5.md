Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-5: finish TraceMetricVariationDerivAt — fixed-vector regularity class + cancellation

Read `harness/reports/M3-predicates-4_blocked.md`. On main: the Route A kernel — `traceMetricVariationAt = LinearMap.trace` of the raised endomorphism (fibers = E by rfl), `d(tr A) = tr(dA)` for the fixed-fiber field. Exactly TWO pieces remain, and the blocker names them:

1. **Fixed-vector spatial regularity class** (the hypothesis-shape fix): define `VariationSpatiallyDifferentiableAt (h : ∀ y, TM y → TM y → ℝ) (x : M) : Prop` (name freely) := for all FIXED p q : E, `HasFDerivAt (fun y => h y p q) (...) x` together with whatever derivative-value data is needed (or use `DifferentiableAt` + `fderiv`). This is an HONEST hypothesis (not a renaming of the target — it says nothing about covariant derivatives or traces). Add satisfiability witnesses: (a) h = 0 / static; (b) if reachable, h = timeDerivAt of a family whose inner products are jointly regular (may itself need an honest class field — fine).
2. **The endomorphism derivative + cancellation**: under that class + g's smoothness:
   a. `HasFDerivAt (fun y => raisedEndo h y) D x` with D = (∂♯)∘h♭ + ♯∘(∂h♭) — the spatial raise derivative via the inverse-derivative rule (fibers are E by rfl, so this is plain normed-space calculus: `hasFDerivAt_inverse_raise`-style from ModelLaplacian applies almost verbatim — mine it).
   b. tr(D) = contracted `covTensor2DerivAt` of h: expand covTensor2DerivAt's definition (flat derivative + Christoffel slot corrections); the (∂♯)-term of D equals MINUS the trace of the Christoffel corrections by metric compatibility `leviCivita_metricCompatibleAt` (model: `fderiv_tensorMetricTrace_eq`'s cancellation, mine its algebra).
   c. Combine with the kernel's `d(tr A) = tr(dA)` → **discharge `TraceMetricVariationDerivAt`** (under the new class; provide the adapter from the class to the predicate where consumed).
3. Restate `deltaGamma_innerTrace_eq` and downstream consumers with the discharged predicate; update the notes.

The model file has this entire computation done once (fibers/charts identical since TM y = E by rfl) — the work is careful mining, not new mathematics. No sorry/axiom; partials + report = success. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
