# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/fixed-chart-uniform-source-normal`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/fixed-chart-uniform-source-normal_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/chain-parametrization-inventory.md` (the whole plan; your task is one of its
"First five bounded tasks" and is reproduced below verbatim), then the cited definitions. Task 3 has landed on
`main` as `Poincare/Global/FixedChartEndpointSlices.lean` (namespace and names as specified there); import and
use it.

# Task fixed-chart-uniform-source-normal

### 4. `Poincare/Global/FixedChartUniformSourceNormal.lean`

Use task 3 with the actual product inverse output of `exists_uniform_local_geodesic_chart_flow_normal_neighborhoods`. Define a retained `Patch g x₀` containing the common `r,T,α`, one product inverse `P`, an open anchor neighborhood `A` of `c := extChartAt I x₀ x₀`, and the theorem's ODE/position-control/C¹ hypotheses. Require `A ⊆ ball c r`, `(z,0) ∈ P.source` for `z∈A`, `P = F α T` as forward functions, and position control in a supplied `U` containing `c`. Retain the final theorem's quantified compact `K,R,ρ` clause exactly, without changing the image radius `R` to `ρ`.

The exact retained input structure is below. It was type-checked in `/tmp/chain-patch-contract.lean`; this checks the specification, not inhabitance. The `exists_patch` theorem must construct it from the existing uniform theorem.

```lean
structure Patch (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (U : Set E) where
  r : ℝ≥0
  r_pos : 0 < r
  T : ℝ
  T_pos : 0 < T
  α : (E × E) → ℝ → E × E
  flow_law : ∀ q ∈ closedBall (extChartAt I x₀ x₀, 0) (r : ℝ),
    α q 0 = q ∧ ∀ t ∈ Icc (-T) T, HasDerivWithinAt (α q)
      (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) (α q t))
      (Icc (-T) T) t
  position_mem : ∀ q ∈ closedBall (extChartAt I x₀ x₀, 0) (r : ℝ),
    ∀ t ∈ Icc (-T) T, (α q t).1 ∈ U
  continuous_flow : ContinuousOn (Function.uncurry α)
    (closedBall (extChartAt I x₀ x₀, 0) (r : ℝ) ×ˢ Icc (-T) T)
  endpoint_C1 : ContDiffOn ℝ 1 (fun q => α q T)
    (ball (extChartAt I x₀ x₀, 0) (r : ℝ))
  endpoint_strict : ∀ z ∈ ball (extChartAt I x₀ x₀) (r : ℝ),
    HasStrictFDerivAt (FixedChartUniformNormalRadius.F α T)
      (FixedChartUniformNormalRadius.endpointDerivative T) (z, 0)
  P : OpenPartialHomeomorph (E × E) (E × E)
  P_eq : (P : (E × E) → (E × E)) = FixedChartUniformNormalRadius.F α T
  P_source_subset : P.source ⊆ ball (extChartAt I x₀ x₀, 0) (r : ℝ)
  A : Set E
  A_open : IsOpen A
  center_mem : extChartAt I x₀ x₀ ∈ A
  A_subset : A ⊆ ball (extChartAt I x₀ x₀) (r : ℝ)
  zero_mem_source : ∀ z ∈ A, (z, (0 : E)) ∈ P.source
  stationary : ∀ z ∈ A, P (z, 0) = (z, z)
  compact_radius : ∀ K : Set E, IsCompact K →
    K ⊆ ball (extChartAt I x₀ x₀) (r : ℝ) →
    ∀ R > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ z ∈ K,
      InjOn (FixedChartUniformNormalRadius.expChart α T z) (ball 0 ρ) ∧
      ball z ρ ⊆ FixedChartUniformNormalRadius.expChart α T z '' ball 0 R
```

For `x` in the manifold anchor patch and `v` in the slice source after rescaling, define the endpoint chart by

```lean
v ↦ (extChartAt I x₀).symm
  (FixedChartUniformNormalRadius.expChart α T
    (extChartAt I x₀ x) (T⁻¹ • v))
```

The open partial homeomorphism is the time-rescaling linear equivalence, then task 3's slice, then the inverse fixed manifold chart; its inverse is `normal`. Restrict its composition source/target by the chart domains, rather than extending inverse identities off-source. Exact `exists_patch` target: for every `U ∈ 𝓝 c`, `Nonempty (Patch g x₀ U)` with all retained fields above. Exact `normal_anchor` and `anchor_mem_normal_source` targets: `∀x∈anchors, normal x x = 0` and `∀x∈anchors, x∈(normal x).source`. `rawLocalFamily` must have exactly those anchor sets and the joint source locus of `normal`, with its evaluator equal there to this inverse. Its target is `CartanSourceExponential.LocalFamily g`, without `GenericEndpointAgreement`.

Gate: compile and probe `Patch`, `exists_patch`, `normal`, the two anchor laws and `rawLocalFamily`. Evidence: `FixedChartUniformNormalRadius` theorem at line 315 and `CartanSourceExponentialLocalFamilyTransport.localFamilyOfAnchorEndpoint`. Stop on the exact inability to obtain a jointly open inverse locus or keep position/chart membership. No uniform statement about the old selected exponential belongs in this file.

