import Poincare.Global.CartanSuppliedDifferentialSuccessor
import Poincare.Global.DifferentialSuccessorIntervalNaturality

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
namespace CartanSuppliedDifferentialTransfer
variable [T2Space M]
open CartanSuppliedDifferentialSuccessor

private theorem reverse_chartTransitionMFDeriv_comp_forward_eq_id
    (p₀ y₀ : RoundSphere3)
    (hy : y₀ ∈ (extChartAt I p₀).source) :
    (GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)).comp
      (GeodesicTransport.chartTransitionMFDeriv
        (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)) =
      ContinuousLinearMap.id ℝ E := by
  let zT : E := extChartAt I y₀ y₀
  let DT : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := y₀) (y₀ := p₀) zT
  let Drev : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)
  have hzT : zT ∈ (extChartAt I y₀).target :=
    (extChartAt I y₀).map_source (mem_extChartAt_source y₀)
  have hxT : (extChartAt I y₀).symm zT = y₀ :=
    (extChartAt I y₀).left_inv (mem_extChartAt_source y₀)
  apply ContinuousLinearMap.ext
  intro w
  let Dnew : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I y₀).symm) (range I) zT
  let Cold : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p₀) y₀
  let Iold : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I p₀).symm) (range I) (extChartAt I p₀ y₀)
  let Cnew : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I y₀) y₀
  have holdCLM : Iold.comp Cold = ContinuousLinearMap.id ℝ E := by
    simpa [Iold, Cold] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy)
  have hnewCLM : Cnew.comp Dnew = ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hzT
    rw [hxT] at h
    simpa [Cnew, Dnew] using h
  change Drev (DT w) = w
  dsimp [Drev, DT, GeodesicTransport.chartTransitionMFDeriv]
  have hxT' : (chartAt E y₀).symm zT = y₀ := by
    simpa [extChartAt_coe] using hxT
  have hold' :
      (chartAt E p₀).symm ((chartAt E p₀) y₀) = y₀ :=
    (chartAt E p₀).left_inv (by
      simpa [extChartAt_source] using hy)
  rw [hxT', hold']
  change Cnew (Iold (Cold (Dnew w))) = w
  calc
    Cnew (Iold (Cold (Dnew w))) = Cnew (Dnew w) := by
      have hw := congrArg (fun L : E →L[ℝ] E => L (Dnew w)) holdCLM
      simpa [ContinuousLinearMap.comp_apply] using congrArg Cnew hw
    _ = w := by
      have hw := congrArg (fun L : E →L[ℝ] E => L w) hnewCLM
      simpa [ContinuousLinearMap.comp_apply] using hw

private theorem reverse_chartTransitionMFDeriv_eq_symm
    (p₀ y₀ : RoundSphere3)
    (hy : y₀ ∈ (extChartAt I p₀).source)
    (T : E ≃L[ℝ] E)
    (hTco : (T : E →L[ℝ] E) =
      GeodesicTransport.chartTransitionMFDeriv
        (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)) :
    GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀) =
      (T.symm : E →L[ℝ] E) := by
  let DT : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)
  let Drev : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)
  have hcomp : Drev.comp DT = ContinuousLinearMap.id ℝ E := by
    simpa [Drev, DT] using
      reverse_chartTransitionMFDeriv_comp_forward_eq_id p₀ y₀ hy
  apply ContinuousLinearMap.ext
  intro w
  calc
    Drev w = Drev (T (T.symm w)) := by rw [T.apply_symm_apply]
    _ = (Drev.comp DT) (T.symm w) := by
      rw [ContinuousLinearMap.comp_apply]
      have hTco' : (T : E →L[ℝ] E) = DT := by
        simpa [DT] using hTco
      rw [← hTco']
      rfl
    _ = T.symm w := by rw [hcomp]; rfl

end CartanSuppliedDifferentialTransfer
end Poincare
