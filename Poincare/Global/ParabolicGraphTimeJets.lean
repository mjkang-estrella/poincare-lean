import Poincare.Global.DeTurckCoupledForcingDefinitions
import Poincare.Global.DeTurckChartIndependentPullback
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Time jets of the original parabolic Graph carriers. The interval remains
closed, so derivative uniqueness covers both endpoints when `0 < T`.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators

universe u v
namespace Poincare.ParabolicGraphTimeJets
open ParabolicSolutionGraph DeTurckPrincipalSecondJet DeTurckCoupledForcing

/-- A static finite value reconstruction determines its within-interval time jet. -/
theorem finite_time_transfer :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ι : Type v) [Fintype ι] (α T : ℝ)
    (G : ParabolicSolutionGraph.Graph (E := E) α T)
    (W : ι → ParabolicSolutionGraph.Graph (E := E) α T)
    (a : ι → ℝ) (x : E) (xs : ι → E), 0 < T →
    (∀ s ∈ Set.Icc 0 T, G.u (s,x) = ∑ i, a i * (W i).u (s,xs i)) →
    ∀ t ∈ Set.Icc 0 T, G.ut (t,x) = ∑ i, a i * (W i).ut (t,xs i) := by
  intro E _ _ ι _ α T G W a x xs hT hvalue t ht
  classical
  have hsum : HasDerivWithinAt (fun s : ℝ => ∑ i, a i * (W i).u (s,xs i))
      (∑ i, a i * (W i).ut (t,xs i)) (Icc 0 T) t :=
    HasDerivWithinAt.fun_sum (fun i _ =>
      ((W i).hasDeriv_time t ht (xs i)).const_mul (a i))
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv (Icc 0 T)
    (G.hasDeriv_time t ht x) (hsum.congr_of_mem hvalue ht)

/-- Static whole-tensor value covariance transfers to the actual Graph time entries. -/
theorem tensor_time_covariance :
    ∀ (α T : ℝ) (U V : DeTurckCoupledForcing.Inputs α T)
    (phi : ClosedSmoothModel 3 → ClosedSmoothModel 3)
    (J : ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3)
    (z : ClosedSmoothModel 3) (t : ℝ),
    0 < T → t ∈ Set.Icc 0 T →
    Filter.Eventually
      (fun s => DeTurckCoupledForcing.tensorValue U (s,z) =
        pullbackBilinearForm (DeTurckCoupledForcing.tensorValue V (s,phi z)) J)
      (nhdsWithin t (Set.Icc 0 T)) →
    let TT := fun (W : DeTurckCoupledForcing.Inputs α T)
      (p : ℝ × ClosedSmoothModel 3) =>
        ∑ a : Fin 3, ∑ b : Fin 3,
          (W (a,b)).ut p • DeTurckTensorBasis.tensor a b
    TT U (t,z) = pullbackBilinearForm (TT V (t,phi z)) J := by
  intro α T U V phi J z t hT ht hvalue
  let TT := fun (W : Inputs α T) (p : ℝ × ClosedSmoothModel 3) =>
    ∑ a : Fin 3, ∑ b : Fin 3, (W (a,b)).ut p • DeTurckTensorBasis.tensor a b
  change TT U (t,z) = pullbackBilinearForm (TT V (t,phi z)) J
  ext v w
  have hU : HasDerivWithinAt (fun s : ℝ => tensorValue U (s,z) v w)
      (TT U (t,z) v w) (Icc 0 T) t := by
    simpa only [tensorValue, TT, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] using
      (HasDerivWithinAt.fun_sum (fun a (_ : a ∈ Finset.univ) =>
        HasDerivWithinAt.fun_sum (fun b (_ : b ∈ Finset.univ) =>
          ((U (a,b)).hasDeriv_time t ht z).mul_const
            (DeTurckTensorBasis.tensor a b v w))))
  have hV : HasDerivWithinAt (fun s : ℝ => tensorValue V (s,phi z) (J v) (J w))
      (TT V (t,phi z) (J v) (J w)) (Icc 0 T) t := by
    simpa only [tensorValue, TT, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] using
      (HasDerivWithinAt.fun_sum (fun a (_ : a ∈ Finset.univ) =>
        HasDerivWithinAt.fun_sum (fun b (_ : b ∈ Finset.univ) =>
          ((V (a,b)).hasDeriv_time t ht (phi z)).mul_const
            (DeTurckTensorBasis.tensor a b (J v) (J w)))))
  have heq : (fun s : ℝ => tensorValue U (s,z) v w) =ᶠ[𝓝[Icc 0 T] t]
      (fun s : ℝ => tensorValue V (s,phi z) (J v) (J w)) := by
    filter_upwards [hvalue] with s hs
    exact congrArg (fun B : Bilin => B v w) hs
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv (Icc 0 T) hU
    (hV.congr_of_eventuallyEq_of_mem heq ht)

end Poincare.ParabolicGraphTimeJets
