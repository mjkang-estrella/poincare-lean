Read harness/worker_contract.md first and obey it strictly.

# Task M3-evolution-ingredients: time-derivative infrastructure for the scalar-evolution port

Goal context: `HamiltonScalarEvolutionProgram` (Global/ScalarEvolution.lean) is the port target of the single-chart `hamilton_scalar_evolution_*` chain (ModelLaplacian.lean). The single-chart proof's skeleton: under the flow ∂g/∂t = −2Ric, (1) the scalar curvature's time derivative decomposes via the metric-variation formula (Lichnerowicz-type: δR = div div h − Δ(tr h) − ⟨h, Ric⟩ at h = −2Ric), (2) contracted second Bianchi + the div div δΓ keystone collapse it to ΔR + 2|Ric|². The closed-manifold port needs TIME-DERIVATIVE objects first. This task builds ONLY that vocabulary + its sanity layer (scope discipline; the variation formula itself is the next task).

Deliverable: NEW file `Poincare/Global/MetricVariation.lean` (+ root import):

1. `def MetricTimeFamily`-style structure or plain functions: for `gt : ℝ → ClosedSmoothRiemannianMetric n M`, the pointwise time-derivative bilinear form `def timeDerivAt (gt) (t₀) (x) : TM x → TM x → ℝ := fun v w => deriv (fun t => (gt t).inner x v w) t₀` with hypotheses class `TimeDifferentiableAt gt t₀ x` (∀ v w, DifferentiableAt ℝ (fun t => (gt t).inner x v w) t₀) — genuine, no certificates. Linearity/symmetry lemmas for timeDerivAt (symmetry from inner_symm + deriv congruence).
2. `theorem isClosedRicciFlowSolutionAt_timeDerivAt`: under `IsClosedRicciFlowSolutionAt gt t₀ x` (Global/RicciFlow.lean), for appropriate section-level inputs, `timeDerivAt gt t₀ x (Z x) w = -2 * ricci-trace-term` — i.e. rewire the flow field of the existing definition into the new timeDerivAt vocabulary (an unfolding/translation theorem, should be mostly definitional given the existing `isClosedRicciFlowSolutionAt_iff`).
3. Static sanity: for constant-in-t families, timeDerivAt = 0 (`deriv_const`).
4. If Mathlib's `deriv`-through-inner needs a differentiability bridge (the inner is fiberwise CLM-applied), prove the small bridging lemmas honestly.

Commit each green piece; blocked → report. No sorry/axiom. `lake build Poincare.Global.MetricVariation`, report names.
