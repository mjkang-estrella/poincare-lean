import Poincare.Global.DeTurckBUCCoefficientIdentification
import Poincare.Global.MovingBUCEvaluation

/-!
# Moving spatial evaluation of coordinate BUC metrics

This file specializes the generic moving-evaluation chain rule to the
Riesz-operator representation of coordinate metrics.  Postcomposition with
the inner product is made into a continuous linear map both on tensor targets
and on intrinsic `BUC` spaces.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open Filter Set Function
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

section TensorToBilinearBUC

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "BilinearTarget" => E →L[ℝ] E →L[ℝ] ℝ
/-- Postcompose a Riesz operator with the real inner product, continuously
and linearly in the operator. -/
def coordinateTensorBilinearFormCLM :
    CoordinateTwoTensor E →L[ℝ] BilinearTarget :=
  ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) (innerSL ℝ)

@[simp]
theorem coordinateTensorBilinearFormCLM_apply
    (B : CoordinateTwoTensor E) (v w : E) :
    coordinateTensorBilinearFormCLM B v w = ⟪B v, w⟫_ℝ := by
  rfl

/-- Moving-base chain rule for a tensor-valued `BUC` path, expressed directly
as a path of coordinate bilinear forms.  The spatial derivative is supplied
in the Riesz-operator representation and then postcomposed with the inner
product. -/
theorem hasDerivWithinAt_coordinateBilinearFormAt_moving_of_tensor_fderiv
    {g : ℝ → CoordinateBUCTensor E} {g' : CoordinateBUCTensor E}
    {phi : ℝ → E} {phi' : E}
    {s : Set ℝ} {t₀ : ℝ}
    {D : E →L[ℝ] CoordinateTwoTensor E}
    (hg : HasDerivWithinAt g g' s t₀)
    (hphi : HasDerivWithinAt phi phi' s t₀)
    (hspace : HasFDerivAt
      (fun x : E ↦ (g t₀).1 x)
      D (phi t₀)) :
    HasDerivWithinAt
      (fun t : ℝ ↦ coordinateBilinearFormAt (g t) (phi t))
      (coordinateBilinearFormAt g' (phi t₀) +
        coordinateTensorBilinearFormCLM (D phi')) s t₀ := by
  have hmoving : HasDerivWithinAt
      (fun t : ℝ ↦ (g t).1 (phi t))
      (g'.1 (phi t₀) + D phi') s t₀ :=
    hasDerivWithinAt_buc_apply_moving hg hphi hspace
  let L : CoordinateTwoTensor E →L[ℝ] BilinearTarget :=
    coordinateTensorBilinearFormCLM (E := E)
  have hpost : HasDerivWithinAt
      (fun t : ℝ ↦ L ((g t).1 (phi t)))
      (L (g'.1 (phi t₀) + D phi')) s t₀ := by
    have hL : HasFDerivAt
        (fun B : CoordinateTwoTensor E ↦ L B) L
        ((g t₀).1 (phi t₀)) :=
      L.hasFDerivAt
    have hcomp :=
      HasFDerivAt.comp_hasDerivWithinAt
        (𝕜 := ℝ) (F := CoordinateTwoTensor E) (E := BilinearTarget)
        (f := fun t : ℝ ↦ (g t).1 (phi t))
        (f' := g'.1 (phi t₀) + D phi') (x := t₀) (s := s)
        (l := fun B : CoordinateTwoTensor E ↦ L B) (l' := L)
        hL hmoving
    simpa [Function.comp_def] using hcomp
  simpa [L, Function.comp_def, coordinateBilinearFormAt,
    ContinuousLinearMap.map_add] using hpost

/-- Moving-base chain rule stated directly for the bilinear-form-valued
coefficient.  This form consumes an honest smooth metric germ without first
choosing a Riesz representative for its spatial derivative. -/
theorem hasDerivWithinAt_coordinateBilinearFormAt_moving
    {g : ℝ → CoordinateBUCTensor E} {g' : CoordinateBUCTensor E}
    {phi : ℝ → E} {phi' : E}
    {s : Set ℝ} {t₀ : ℝ}
    {D : E →L[ℝ] BilinearTarget}
    (hg : HasDerivWithinAt g g' s t₀)
    (hphi : HasDerivWithinAt phi phi' s t₀)
    (hspace : HasFDerivAt
      (fun x : E ↦ coordinateBilinearFormAt (g t₀) x)
      D (phi t₀)) :
    HasDerivWithinAt
      (fun t : ℝ ↦ coordinateBilinearFormAt (g t) (phi t))
      (coordinateBilinearFormAt g' (phi t₀) + D phi') s t₀ := by
  apply (hasDerivWithinAt_iff_tendsto_slope
    (𝕜 := ℝ) (F := BilinearTarget)
    (f := fun t : ℝ ↦ coordinateBilinearFormAt (g t) (phi t))
    (f' := coordinateBilinearFormAt g' (phi t₀) + D phi')
    (s := s) (x := t₀)).2
  let l : Filter ℝ := nhdsWithin t₀ (s \ {t₀})
  have hgSlope : Tendsto (slope g t₀) l (nhds g') := by
    simpa only [l] using
      (hasDerivWithinAt_iff_tendsto_slope.mp hg)
  have hphiT : Tendsto phi l (nhds (phi t₀)) := by
    exact hphi.continuousWithinAt.mono_left
      (nhdsWithin_mono t₀ Set.diff_subset)
  have hgSlopeBCF : Tendsto
      (fun t : ℝ ↦ (slope g t₀ t).1)
      l (nhds g'.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hgSlope
  have htimeTensor : Tendsto
      (fun t : ℝ ↦ ((slope g t₀ t).1 : E →ᵇ CoordinateTwoTensor E)
        (phi t))
      l (nhds ((g'.1 : E →ᵇ CoordinateTwoTensor E) (phi t₀))) := by
    exact (continuous_eval.tendsto (g'.1, phi t₀)).comp
      (hgSlopeBCF.prodMk_nhds hphiT)
  let L : CoordinateTwoTensor E →L[ℝ] BilinearTarget :=
    coordinateTensorBilinearFormCLM (E := E)
  have htime : Tendsto
      (fun t : ℝ ↦ L (((slope g t₀ t).1 :
        E →ᵇ CoordinateTwoTensor E) (phi t)))
      l (nhds (L ((g'.1 : E →ᵇ CoordinateTwoTensor E) (phi t₀)))) :=
    L.continuous.continuousAt.tendsto.comp htimeTensor
  have hspatial : HasDerivWithinAt
      (fun t : ℝ ↦ coordinateBilinearFormAt (g t₀) (phi t))
      (D phi') s t₀ := by
    have hcomp :=
      HasFDerivAt.comp_hasDerivWithinAt
        (𝕜 := ℝ) (F := E) (E := BilinearTarget)
        (f := phi) (f' := phi') (x := t₀) (s := s)
        (l := fun x : E ↦ coordinateBilinearFormAt (g t₀) x)
        (l' := D) hspace hphi
    simpa [Function.comp_def] using hcomp
  have hspatialSlope : Tendsto
      (slope (fun t : ℝ ↦
        coordinateBilinearFormAt (g t₀) (phi t)) t₀)
      l (nhds (D phi')) := by
    have hslope := (hasDerivWithinAt_iff_tendsto_slope
      (𝕜 := ℝ) (F := BilinearTarget)
      (f := fun t : ℝ ↦ coordinateBilinearFormAt (g t₀) (phi t))
      (f' := D phi') (s := s) (x := t₀)).mp hspatial
    simpa only [l] using
      hslope
  have hsum := htime.add hspatialSlope
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change
    L (((slope g t₀ t).1 : E →ᵇ CoordinateTwoTensor E) (phi t)) +
        slope (fun r : ℝ ↦ L ((g t₀).1 (phi r))) t₀ t =
      slope (fun r : ℝ ↦ L ((g r).1 (phi r))) t₀ t
  simp only [slope]
  change
    L ((t - t₀)⁻¹ •
          ((g t).1 (phi t) - (g t₀).1 (phi t))) +
        (t - t₀)⁻¹ •
          (L ((g t₀).1 (phi t)) - L ((g t₀).1 (phi t₀))) =
      (t - t₀)⁻¹ •
        (L ((g t).1 (phi t)) - L ((g t₀).1 (phi t₀)))
  rw [L.map_smul, L.map_sub, ← smul_add]
  congr 1
  abel

end TensorToBilinearBUC

end Poincare
