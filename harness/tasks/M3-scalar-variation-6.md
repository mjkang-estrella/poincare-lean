Read harness/worker_contract.md first and obey it strictly.

# Task M3-scalar-variation-6: deltaGamma_koszul master identity + discharge hRaiseTrace

Read `harness/reports/M3-scalar-variation_notes.md` (latest status). On main: `scalarVariation_lichnerowicz_shape` holds modulo `hRaiseTrace` and `hDeltaGammaTrace`. This task attacks the FIRST obligation and the master identity feeding the second (scope discipline: hDeltaGammaTrace's full contraction is the next task).

Deliverables, extending Global/ScalarVariation.lean (each its own commit):

1. **`deltaGamma_koszul`** (the master identity): differentiate the Koszul characterization of the canonical connection in time. Target shape: under `MetricFlowRegularAt` + `TimeDifferentiableAt`-style hypotheses,
   `2 * (gt t₀).inner x (deltaGammaAt gt t₀ x v w) z = [∇-of-h 3-term form] − [h(δΓ-slot corrections)]`
   — precisely: d/dt of [2·g_t(Γ_t(v,w),z) = Koszul RHS(g_t)] at t₀. The LHS product rule gives 2h(Γ,z) + 2g(δΓ,z); the RHS differentiates the 6 Koszul terms into ∇h-type derivatives (the derivative of g_t-pairings of extended fields = h-pairings + g-pairings of time-derivatives; the extended fields are t-independent, which kills the bracket terms' variation). Model template: the memory's Koszul route (`g_christoffelDeriv` differentiated). State with honest hypotheses; if the extDerivFun-differentiation-under-d/dt exchange needs a Schwarz-type field in `MetricFlowRegularAt`, extend the class compatibly (keep the const witness updated — non-vacuity).
2. **Discharge `hRaiseTrace`**: the raise-map derivative trace = −⟨h,Ric⟩ pairing. Content: d/dt(g_t⁻¹) = −g⁻¹·h·g⁻¹ (the repo has `hasDerivAt_clm_inverse`-style tools; ModelLaplacian's `fderiv_inverse_raise_apply` is the template), then trace against the Ricci dual gives exactly `−metricVariationRicciPairingAt`. Then restate `scalarVariation_lichnerowicz_shape'` with hRaiseTrace discharged (hDeltaGammaTrace still carried).
3. If momentum: the first contraction of deltaGamma_koszul — the inner trace `Σᵢ g(δΓ(eᵢ,♯eⁱ),w) = (div h)(w) − ½d(tr h)(w)` (model: `deltaGamma_innerTrace_eq`).

No sorry/axiom; blocked → greens + notes. `lake build Poincare.Global.ScalarVariation`, report names.
