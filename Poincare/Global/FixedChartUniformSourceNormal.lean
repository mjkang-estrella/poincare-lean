import Poincare.Global.FixedChartUniformNormalRadius
import Poincare.Global.FixedChartEndpointSlices
import Poincare.Global.CartanSourceExponentialLocalFamilyTransport

/-!
# Normal coordinates from one retained fixed-chart flow

The common flow, product inverse, and compact radii are retained together.
Manifold normal charts use the exact vertical slices and normalize velocity
by the common positive time. All inverse laws retain their chart domains.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology ContDiff NNReal Manifold

namespace Poincare.FixedChartUniformSourceNormal

universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

/-- One common flow and product inverse, with the original quantitative bounds. -/
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

/-- Construct the retained patch from the uniform fixed-chart flow theorem. -/
theorem exists_patch (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {U : Set E} (hU : U ∈ 𝓝 (extChartAt I x₀ x₀)) :
    Nonempty (Patch g x₀ U) := by
  obtain ⟨r, hr, T, hT, α, hflow, hpos, hcont, hC1, hstrict, hlocal, hcompact⟩ :=
    FixedChartUniformNormalRadius.exists_uniform_local_geodesic_chart_flow_normal_neighborhoods
      g x₀ hU
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨ρ, hρ, P, hP, hcenter, hsub, _, _, _⟩ :=
    hlocal (extChartAt I x₀ x₀) (mem_ball_self hr') 1 zero_lt_one
  let A : Set E := {z | (z, (0 : E)) ∈ P.source}
  have hAsub : A ⊆ ball (extChartAt I x₀ x₀) (r : ℝ) := by
    intro z hz
    simpa using hsub hz
  refine ⟨{
    r := r, r_pos := hr, T := T, T_pos := hT, α := α
    flow_law := hflow, position_mem := hpos, continuous_flow := hcont
    endpoint_C1 := hC1, endpoint_strict := hstrict
    P := P, P_eq := hP, P_source_subset := hsub
    A := A
    A_open := P.open_source.preimage (continuous_id.prodMk continuous_const)
    center_mem := hcenter, A_subset := hAsub
    zero_mem_source := fun _ hz => hz
    stationary := ?_
    compact_radius := hcompact }⟩
  intro z hz
  have hzball := ball_subset_closedBall (hsub hz)
  have hstat := FixedChartUniformNormalRadius.flow_zero_velocity
    (contDiff_geodesicFlowField (GeodesicTransport.chartChristoffelField_contDiff g x₀))
    hT (hflow (z, 0) hzball).1 (hflow (z, 0) hzball).2 T
    (by constructor <;> linarith)
  rw [congrFun hP]
  exact Prod.ext rfl (congrArg Prod.fst hstat)

end Poincare.FixedChartUniformSourceNormal
