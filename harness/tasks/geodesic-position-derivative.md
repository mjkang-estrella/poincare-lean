# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/geodesic-position-derivative`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; one new file
`Poincare/Global/GeodesicFlowJointDerivative.lean`; no vacuous definitions; report actual command output;
commit each verified lemma on the branch; report to
`harness/reports/geodesic-position-derivative_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md`.

# Task: joint C¹ dependence of the chart geodesic flow on initial position and velocity

Why. HANDOFF.md ("2026-09-08 Repair track") explains that the exponential layer must be re-founded with explicit
uniform constructions on a fixed chart: the anchor-dependent `expAt` is a per-anchor `Classical.choose`. The
first brick is joint differentiability of the fixed-chart geodesic flow in its initial state, which the
repository has only in the velocity slot.

Read first: `Poincare/Global/GeodesicChart.lean` (`geodesicFlowField Γ p = (p.2, -Γ p.1 p.2 p.2)`, Picard–Lindelöf
existence, Grönwall uniqueness), `Poincare/Global/ExponentialFixedTime.lean`
(`exists_uniform_local_geodesic_chart_flow_variableInitialState_continuousOn`: joint continuity in (initial
position, initial velocity, time) on a closed ball times an interval), `Poincare/Global/GeodesicDependence.lean`
and `JacobiOscillator.lean`/`ParameterizedFlowDerivative.lean` (`chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`,
`exists_chartChristoffel_linearizedGeodesicFlow_solution`: the derivative in the initial velocity solves the
linearized (Jacobi) equation), `Poincare/Global/UniformAnchoredSecondVariation.lean` (how first- and second-variation
Grönwall arguments were set up), and Mathlib `Analysis/ODE/Gronwall.lean`, `PicardLindelof.lean`.

Target (frozen). For a chart Christoffel field `Γ : E → E →L[ℝ] E →L[ℝ] E` that is `ContDiffAt ℝ 2` (or `C^1` with
locally Lipschitz derivative — state the minimal hypothesis you actually use, matching the regularity the
repository proves for `chartChristoffelField`) on an open set `U ⊆ E`, and the geodesic flow
`α : (E × E) → ℝ → E × E` produced by the repository's uniform Picard–Lindelöf package on a closed ball
`closedBall (z₀, 0) r ×ˢ Icc (-ε) ε` (reuse the exact package from
`exists_uniform_local_geodesic_chart_flow_variableInitialState_continuousOn` or the strongest existing one):

```lean
theorem geodesic_flow_hasFDerivAt_initialState
    ... : ∀ q ∈ ball (z₀, 0) r, ∀ t ∈ Ioo (-ε) ε,
      HasFDerivAt (fun q' : E × E => α q' t) (Φ q t) q
```

where `Φ q t : E × E →L[ℝ] E × E` is the solution at time `t` of the linearized flow along `α q` with initial value
`id` (the variational equation for BOTH position and velocity perturbations), together with joint continuity of
`(q, t) ↦ Φ q t` on the ball times the interval, and the consequence that `q ↦ α q t` is `C¹` on the ball for
each fixed `t`. Prove it the way the repository proved the velocity derivative (Grönwall estimate on the
difference quotient against the linearized solution), now with a joint perturbation `(δz, δv)`. Commit: (1) the
linearized flow existence with joint initial data; (2) the Grönwall difference-quotient estimate; (3) the
`HasFDerivAt` statement; (4) continuity of `Φ`; (5) if cheap, the specialization giving `HasFDerivAt` of the
joint map `(z, v) ↦ (z, α (z, v) T)` at points `(z, 0)` equal to `id` on the position slot and `T • id` on the
velocity slot (the input to the joint inverse-function argument). Isolate the exact resisting shape if a step
resists.
