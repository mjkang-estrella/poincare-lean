import Poincare.Global.FixedChartLocalSuccessorExistence

/-!
# Uniform differentials of retained fixed-chart exponentials

The endpoint derivatives are constructed from the retained joint C1 flow.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartUniformDifferentialPullback
open CartanSuppliedDifferentialSuccessor FixedChartLocalSuccessorExistence

/-- The position endpoint, with the retained time normalized to velocity time one. -/
def normalizedEndpoint {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) (q : E × E) : E :=
  (C.α (q.1, C.T⁻¹ • q.2) C.T).1

/-- The velocity derivative at zero is the identity at every retained anchor. -/
theorem normalizedEndpoint_hasStrictFDerivAt_zero {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (hx : x ∈ C.anchors) :
    HasStrictFDerivAt (fun v => normalizedEndpoint C (extChartAt I x₀ x, v))
      (ContinuousLinearMap.id ℝ E) 0 := by
  have hd := (C.endpoint_strict _ (C.A_subset hx.2)).snd
  have hi := (hasStrictFDerivAt_const (extChartAt I x₀ x) (0 : E)).prodMk
    C.timeRescaling.hasStrictFDerivAt
  have hd' : HasStrictFDerivAt (fun q => (FixedChartUniformNormalRadius.F C.α C.T q).2)
      ((ContinuousLinearMap.snd ℝ E E).comp (FixedChartUniformNormalRadius.endpointDerivative C.T))
      (extChartAt I x₀ x, C.timeRescaling 0) := by simpa using hd
  have h := hd'.comp 0 hi
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  change 0 + C.T • (C.T⁻¹ • w) = w
  simp [smul_smul, C.T_pos.ne']

/-- The supplied coordinate endpoint cancels the fixed chart on its actual source. -/
theorem coordinateEndpoint_eq_normalizedEndpoint {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (v : E) (hv : v ∈ (C.endpoint x).source) :
    (C.endpoint x).trans (chartAt E x₀) v =
      normalizedEndpoint C (extChartAt I x₀ x, v) := by
  change (chartAt E x₀) ((chartAt E x₀).symm
    (C.P (extChartAt I x₀ x, C.T⁻¹ • v)).2) = _
  have ht : (C.P (extChartAt I x₀ x, C.T⁻¹ • v)).2 ∈ (chartAt E x₀).target := hv.2
  rw [(chartAt E x₀).right_inv ht, congrFun C.P_eq]
  rfl

/-- Invertible velocity derivatives persist jointly in position and velocity. -/
theorem normalizedEndpoint_eventually_equiv {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (hx : x ∈ C.anchors) :
    ∀ᶠ q : E × E in 𝓝 (extChartAt I x₀ x, 0),
      ∃ A : E ≃L[ℝ] E,
        HasStrictFDerivAt (fun v => normalizedEndpoint C (q.1, v))
          (A : E →L[ℝ] E) q.2 := by
  let q₀ : E × E := (extChartAt I x₀ x, 0)
  have hmem : (extChartAt I x₀ x, (0 : E)) ∈
      ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) := by
    simpa using C.A_subset hx.2
  have hc : ContDiffAt ℝ 1 (normalizedEndpoint C) q₀ := by
    have h := (C.endpoint_C1.contDiffAt (isOpen_ball.mem_nhds hmem)).fst
    have hi : ContDiffAt ℝ 1 (fun q : E × E => (q.1, C.T⁻¹ • q.2)) q₀ :=
      contDiffAt_fst.prodMk ((contDiffAt_const (c := C.T⁻¹)).smul contDiffAt_snd)
    have h' : ContDiffAt ℝ 1 (fun q => (C.α q C.T).1)
        (q₀.1, C.T⁻¹ • q₀.2) := by simpa [q₀] using h
    exact h'.comp q₀ (f := fun q : E × E => (q.1, C.T⁻¹ • q.2)) hi
  let d : E × E → E →L[ℝ] E := fun q =>
    (fderiv ℝ (normalizedEndpoint C) q).comp (ContinuousLinearMap.inr ℝ E E)
  have hd : ContinuousAt d q₀ :=
    (hc.continuousAt_fderiv one_ne_zero).clm_comp continuousAt_const
  have hslice : ∀ q, ContDiffAt ℝ 1 (normalizedEndpoint C) q →
      HasStrictFDerivAt (fun v => normalizedEndpoint C (q.1, v)) (d q) q.2 := by
    intro q hq
    exact (hq.hasStrictFDerivAt one_ne_zero).comp q.2
      ((hasStrictFDerivAt_const q.1 q.2).prodMk (hasStrictFDerivAt_id q.2))
  have hd0 : d q₀ = ContinuousLinearMap.id ℝ E :=
    (hslice q₀ hc).hasFDerivAt.unique
      (normalizedEndpoint_hasStrictFDerivAt_zero C x hx).hasFDerivAt
  have hunit : IsUnit (d q₀) := by rw [hd0]; exact isUnit_one
  have he : ∀ᶠ q in 𝓝 q₀, IsUnit (d q) := hd (Units.isOpen.mem_nhds hunit)
  filter_upwards [he, hc.eventually (by norm_num)] with q hq hCq
  rcases hq with ⟨a, ha⟩
  refine ⟨ContinuousLinearEquiv.ofUnit a, ?_⟩
  simpa only [← ha] using hslice q hCq

end FixedChartUniformDifferentialPullback
end Poincare
