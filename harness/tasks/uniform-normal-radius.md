# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/uniform-normal-radius`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; one new file
`Poincare/Global/UniformNormalRadius.lean` is taken — use `Poincare/Global/FixedChartUniformNormalRadius.lean`;
no vacuous definitions; report actual command output; commit each verified lemma on the branch; report to
`harness/reports/uniform-normal-radius_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.

# Task: uniform normal radius of the fixed-chart exponential map via the joint inverse function theorem

Why. HANDOFF.md "2026-09-08 Repair track": the exponential layer must be re-founded with explicit uniform
constructions on a fixed chart. `Poincare/Global/GeodesicFlowJointDerivative.lean` (read fully) now gives, for
the repository's uniform Picard–Lindelöf chart flow `α` on `closedBall (z₀, 0) r ×ˢ Icc (-T) T`, the joint
`C¹` dependence on the initial state `(z, v)` with fundamental solution `Φ`
(`exists_uniform_local_geodesic_chart_flow_initialState_C1`, `geodesic_flow_hasFDerivAt_initialState`,
`exists_flow_initialState_C1`). The fixed-chart exponential of the anchor `z` with velocity `v` at time `T` is
`expChart z v := (α (z, v) T).1`.

Target (frozen). Define `F : E × E → E × E := fun p => (p.1, (α p T).1)` on the state ball and prove:

1. `hasFDerivAt_F_at_zero_velocity`: at every `(z, 0)` in the open ball, `F` has Fréchet derivative
   `(u, w) ↦ (u, u + T • w)` (position derivative is the identity because `α (z, 0) t = (z, 0)` for all `t`
   — prove this from ODE uniqueness with the zero field value, or from the flow package; the velocity
   derivative is `T • id` from `Φ (z, 0) T` applied to `(0, w)`; state exactly what `Φ (z,0) T` is and prove it).
2. `hasStrictFDerivAt_F`: the derivative is strict at `(z, 0)` (use `ContDiffAt` of `F`, which follows from the
   `C¹` conclusion of `exists_flow_initialState_C1`: `contDiffAt_one` gives strict differentiability via
   `ContDiffAt.hasStrictFDerivAt`).
3. `uniform_normal_radius_near`: for each `z₀` in the chart region there are `ρ > 0` and an open set `W` with
   `(z₀, 0) ∈ W` such that `F` restricted to `W` is an `OpenPartialHomeomorph` (from
   `HasStrictFDerivAt.toOpenPartialHomeomorph` applied to the invertible derivative of step 1, which is a
   continuous linear equivalence `(u, w) ↦ (u, u + T • w)` with inverse `(a, b) ↦ (a, T⁻¹ • (b - a))`), and
   consequently: `∀ z ∈ ball z₀ ρ, InjOn (expChart z) (ball 0 ρ) ∧ ball z ρ ⊆ expChart z '' (ball 0 ρ')`
   for some `ρ' > 0` (derive from the product neighborhood contained in `W` and the openness of `F '' W`;
   choose the form that is provable and state it exactly).
4. `exists_uniform_normal_radius_on_compact`: for a compact `K` inside the chart region, one `ρ > 0` serving
   every `z ∈ K` (finite subcover of step 3).

These are statements about the concrete flow `α`, not about the repository's per-anchor `expAt`; do not try
to identify them with `expAt`. Mathlib: `HasStrictFDerivAt.toOpenPartialHomeomorph`,
`HasStrictFDerivAt.to_localInverse`, `ContinuousLinearEquiv`, `HasFDerivAt.prodMk`, `hasFDerivAt_fst`,
`IsCompact.elim_finite_subcover`, `Metric.isOpen_iff`. Commit each step; isolate the exact resisting shape if a
step resists.
