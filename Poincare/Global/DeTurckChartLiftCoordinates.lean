import Poincare.Global.DeTurckChartLiftDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
universe u

namespace Poincare.DeTurckChartLift

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]

/-- The forward differential acts in both tensor slots of the local pullback. -/
theorem localPullback_apply (anchor : M) (F : E → Bilin) (x : M)
    (v w : TangentSpace I x) :
    localPullback anchor F x v w =
      F (extChartAt I anchor x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x w) :=
  rfl

/-- On the genuine source, the global lift is its actual local pullback. -/
theorem chartLift_eq_localPullback (anchor : M) (F : E → Bilin) {x : M}
    (hx : x ∈ (extChartAt I anchor).source) :
    chartLift anchor F x = localPullback anchor F x := by
  classical
  simp only [chartLift, if_pos hx]

/-- Inverse-chart transport recovers the whole coefficient tensor on the target. -/
theorem chartMetric_chartLift (anchor : M) (F : E → Bilin) (z : E)
    (hz : z ∈ (extChartAt I anchor).target) :
    _root_.CovariantDerivative.chartMetric (I := I) (chartLift anchor F) anchor z = F z := by
  ext v w
  rw [_root_.CovariantDerivative.chartMetric_apply,
    chartLift_eq_localPullback anchor F ((extChartAt I anchor).map_target hz),
    localPullback_apply, (extChartAt I anchor).right_inv hz]
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := I) (x := anchor) hz
  have hv :
      mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) ((extChartAt I anchor).symm z)
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor).symm) (range I) z v) = v :=
    congrArg (fun A => A v) hcomp
  have hw :
      mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) ((extChartAt I anchor).symm z)
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor).symm) (range I) z w) = w :=
    congrArg (fun A => A w) hcomp
  exact congrArg₂ (fun a b : E => F z a b) hv hw

/-- Symmetry passes through both differential slots and the off-source zero tensor. -/
theorem chartLift_symmetric (anchor : M) (F : E → Bilin)
    (hF : ∀ z v w : E, F z v w = F z w v)
    (x : M) (v w : TangentSpace I x) :
    chartLift anchor F x v w = chartLift anchor F x w v := by
  classical
  by_cases hx : x ∈ (extChartAt I anchor).source
  · rw [chartLift_eq_localPullback anchor F hx, localPullback_apply, localPullback_apply]
    exact hF _ _ _
  · simp only [chartLift, if_neg hx, ContinuousLinearMap.zero_apply]

/-- The actual nested Hom trivialization reads the lift as the original coefficients. -/
theorem chartLift_coordinates (anchor : M) (F : E → Bilin) (x : M)
    (hx : x ∈ (extChartAt I anchor).source) :
    let e := trivializationAt E (TangentSpace I) anchor
    let eR := trivializationAt ℝ (fun _ : M => ℝ) anchor
    ((e.continuousLinearMap (RingHom.id ℝ)
      (e.continuousLinearMap (RingHom.id ℝ) eR))
      ⟨x, chartLift anchor F x⟩).2 = F (extChartAt I anchor x) := by
  dsimp only
  let e := trivializationAt E (TangentSpace I) anchor
  let eR := trivializationAt ℝ (fun _ : M => ℝ) anchor
  let eHom := e.continuousLinearMap (RingHom.id ℝ) eR
  have hxChart : x ∈ (chartAt E anchor).source := by
    rwa [← extChartAt_source (I := I)]
  have hxBase : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hxChart
  have hxHom : x ∈ eHom.baseSet := by simpa [eHom, eR] using hxBase
  have hA : e.continuousLinearMapAt ℝ x =
      mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x :=
    TangentBundle.continuousLinearMapAt_trivializationAt hxChart
  have hcancel (a : E) :
      mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x (e.symmL ℝ x a) = a := by
    rw [← hA]
    exact Trivialization.continuousLinearMapAt_symmL e hxBase a
  ext a b
  simp only [Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ eHom hxHom]
  simp only [eHom, Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply]
  change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x
    (chartLift anchor F x (e.symmL ℝ x a) (e.symmL ℝ x b)) =
      F (extChartAt I anchor x) a b
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization]
  simp only [ContinuousLinearMap.id_apply]
  rw [chartLift_eq_localPullback anchor F hx, localPullback_apply]
  exact congrArg₂ (fun v w : E => F (extChartAt I anchor x) v w) (hcancel a) (hcancel b)

end Poincare.DeTurckChartLift
