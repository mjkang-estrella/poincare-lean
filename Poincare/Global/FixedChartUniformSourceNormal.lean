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

namespace Patch

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
variable (C : Patch g x₀ U)

/-- The retained product map preserves the anchor coordinate. -/
theorem preserves_fst : ∀ q ∈ C.P.source, (C.P q).1 = q.1 := by
  intro q _
  rw [congrFun C.P_eq]
  rfl

/-- Time normalization, from time-one velocities to the common flow time. -/
def timeRescaling : E ≃L[ℝ] E :=
  { LinearEquiv.smulOfNeZero ℝ E C.T⁻¹ (inv_ne_zero C.T_pos.ne') with
    continuous_toFun := continuous_const.smul continuous_id
    continuous_invFun := continuous_const.smul continuous_id }

/-- Exact endpoint slice followed by the inverse fixed manifold chart. -/
def endpoint (x : M) : OpenPartialHomeomorph E M :=
  (C.timeRescaling.toHomeomorph.toOpenPartialHomeomorph.trans
    (FixedChartEndpointSlices.slice C.P C.preserves_fst (extChartAt I x₀ x))).trans
      (chartAt E x₀).symm

/-- Normal vectors in the fixed chart's time-one velocity frame. -/
def normal (x : M) : OpenPartialHomeomorph M E := (C.endpoint x).symm

/-- Anchors retained in both the fixed manifold chart and the product patch. -/
def anchors : Set M :=
  CartanSourceExponentialLocalFamilyTransport.anchorSet x₀ C.A

/-- The manifold anchor set is open. -/
theorem isOpen_anchors : IsOpen C.anchors :=
  CartanSourceExponentialLocalFamilyTransport.isOpen_anchorSet x₀ C.A_open

/-- The central manifold point is retained. -/
theorem center_mem_anchors : x₀ ∈ C.anchors :=
  ⟨mem_extChartAt_source x₀, C.center_mem⟩

/-- The forward chart is exactly the specified time-normalized endpoint. -/
theorem endpoint_apply (x : M) (v : E) :
    C.endpoint x v = (extChartAt I x₀).symm
      (FixedChartUniformNormalRadius.expChart C.α C.T
        (extChartAt I x₀ x) (C.T⁻¹ • v)) := by
  change (chartAt E x₀).symm
    (C.P (extChartAt I x₀ x, C.T⁻¹ • v)).2 = _
  rw [congrFun C.P_eq]
  rfl

/-- Zero belongs to the composed endpoint source at every retained anchor. -/
theorem zero_mem_endpoint_source : ∀ x ∈ C.anchors, 0 ∈ (C.endpoint x).source := by
  intro x hx
  change (0 ∈ (C.timeRescaling.toHomeomorph.toOpenPartialHomeomorph.trans
    (FixedChartEndpointSlices.slice C.P C.preserves_fst (extChartAt I x₀ x))).source) ∧ _
  constructor
  · change (0 ∈ (Set.univ : Set E)) ∧ (extChartAt I x₀ x, C.T⁻¹ • (0 : E)) ∈ C.P.source
    exact ⟨mem_univ _, by simpa using C.zero_mem_source _ hx.2⟩
  · change (C.P (extChartAt I x₀ x, C.T⁻¹ • (0 : E))).2 ∈ (chartAt E x₀).target
    rw [smul_zero, C.stationary _ hx.2]
    exact (chartAt E x₀).map_source (by simpa only [extChartAt_source] using hx.1)

/-- The endpoint at zero is the retained anchor. -/
theorem endpoint_zero : ∀ x ∈ C.anchors, C.endpoint x 0 = x := by
  intro x hx
  change (chartAt E x₀).symm (C.P (extChartAt I x₀ x, C.T⁻¹ • (0 : E))).2 = x
  rw [smul_zero, C.stationary _ hx.2]
  exact (chartAt E x₀).left_inv (by simpa only [extChartAt_source] using hx.1)

/-- Each retained anchor lies in its normal source. -/
theorem anchor_mem_normal_source : ∀ x ∈ C.anchors, x ∈ (C.normal x).source := by
  intro x hx
  simpa only [C.endpoint_zero x hx] using
    (C.endpoint x).map_source (C.zero_mem_endpoint_source x hx)

/-- Normal coordinates send each retained anchor to zero. -/
theorem normal_anchor : ∀ x ∈ C.anchors, C.normal x x = 0 := by
  intro x hx
  simpa only [C.endpoint_zero x hx] using
    (C.endpoint x).left_inv (C.zero_mem_endpoint_source x hx)

end Patch
end Poincare.FixedChartUniformSourceNormal
