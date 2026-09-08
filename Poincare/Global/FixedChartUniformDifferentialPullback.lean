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

end FixedChartUniformDifferentialPullback
end Poincare
