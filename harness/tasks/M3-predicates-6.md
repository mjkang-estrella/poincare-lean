Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-6: TraceMetricVariationDerivAt — native closed-vocabulary computation

Read `harness/reports/M3-predicates-5_blocked.md` and the notes. Do NOT take the closed-to-model transport route (that's what stalled). Prove the cancellation NATIVELY in the closed vocabulary — every ingredient already exists on main. Orchestrator-worked-out route (adjust technical details to the actual definitions, but follow this shape):

Setup: `traceMetricVariationAt h y = Σᵢ h y (eᵢ) (♯_y eⁱ)` (finBasis + y-varying raise; the trace-linearity kernel from predicates-4 gives the LinearMap.trace form too — use whichever contracts cleaner). Under `VariationSpatiallyDifferentiableAt h x` (fixed-vector `HasFDerivAt`, on main with witnesses) + g's smoothness:

1. **Spatial ∂g**: `y ↦ (gt).inner y p q` is differentiable (from `contMDiff_inner`/`ContMDiffRiemannianMetric`); define/obtain the spatial metric-derivative bilinear `(∂_v g)(p,q)`.
2. **Spatial ∂♯**: differentiate `y ↦ ♯_y φ` (fixed covector φ): `∂♯ = −♯(∂g)(♯·)` — the SPATIAL analogue of the proven time-version `metricRaiseDerivAt`; mine `hasFDerivAt_inverse_raise` (ModelLaplacian) since fibers = E by rfl and `metricDualVectorAt_eq_metricRaiseContinuousAt` is on main.
3. **Metric compatibility in fixed-vector form**: from `leviCivita_metricCompatibleAt` (or directly from the canonical connection's Koszul characterization), derive `(∂_v g)(p,q) = g(Γ_v p, q) + g(p, Γ_v q)` at x for fixed vectors — where Γ_v p is the canonical connection's Christoffel action (`g.leviCivita` applied to extend sections; the deltaGammaAt machinery already manipulates exactly these — reuse its extend-section lemmas). If IsMetricCompatible's field-shape needs an extend-section unwrap, that unwrap is `extend`-calculus already done in variation-2's `extend_tangent_add/smul` neighborhood.
4. **Differentiate the trace**: `∂_v (trace) = Σᵢ [(∂_v h)(eᵢ, ♯eⁱ)] + Σᵢ h(eᵢ, ∂♯ eⁱ)`. Substitute 2+3 into the second sum: `Σᵢ h(eᵢ, ∂♯eⁱ) = −Σᵢ h(eᵢ, Γ_v(♯eⁱ)) − Σᵢ h(eᵢ, ♯(g(♯eⁱ, Γ_v ·)))`; the swap machinery (`sum_metricDualVectorAt_contraction_swap`, on main) turns the second term into `−Σᵢ h(Γ_v eᵢ, ♯eⁱ)`-form.
5. **Recognize covTensor2DerivAt**: `Σᵢ covTensor2DerivAt h x v eᵢ ♯eⁱ = Σᵢ [(∂_v h)(eᵢ,♯eⁱ) − h(Γ_v eᵢ, ♯eⁱ) − h(eᵢ, Γ_v ♯eⁱ)]` (per its definition) — exactly matches step 4's result. **Discharge `TraceMetricVariationDerivAt`.**
6. Restate `deltaGamma_innerTrace_eq` modulo classes only; update notes; propagate to the divergence-assembly predicates if they simplify.

Each step its own commit. No sorry/axiom; partials + report = success. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
