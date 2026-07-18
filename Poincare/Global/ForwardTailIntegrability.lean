import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# From an integrable forward tail to the whole forward half-line

For eventual curvature-pinching arguments, coercive decay may begin only
after a finite time.  Continuity makes the omitted compact initial interval
integrable, while translation invariance identifies a shifted `Ici 0` tail
with `Ici T`.
-/

noncomputable section

open Function MeasureTheory Set
open scoped MeasureTheory Topology

namespace Poincare

/-- Translation identifies integrability on `Ici T` with integrability of the
shifted function on `Ici 0`. -/
theorem integrableOn_Ici_iff_integrableOn_comp_const_add_Ici_zero
    (f : ℝ → ℝ) (T : ℝ) :
    IntegrableOn f (Ici T) ↔
      IntegrableOn (fun s : ℝ ↦ f (T + s)) (Ici 0) := by
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addLeft T
  have h :=
    (measurePreserving_add_left volume T).integrableOn_image
      e.measurableEmbedding (f := f) (s := Ici (0 : ℝ))
  simpa [e, MeasurableEquiv.coe_addLeft, Function.comp_def] using h

/-- A continuous forward function with an integrable tail is integrable on
the whole forward half-line. -/
theorem integrableOn_Ici_zero_of_continuousOn_of_integrableOn_tail
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hContinuous : ContinuousOn f (Ici 0))
    (hTail : IntegrableOn f (Ici T)) :
    IntegrableOn f (Ici 0) := by
  rw [← Ico_union_Ici_eq_Ici hT, integrableOn_union]
  refine ⟨?_, hTail⟩
  exact
    (hContinuous.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set
      Ico_subset_Icc_self

/-- Shifted-tail form of the preceding gluing theorem. -/
theorem integrableOn_Ici_zero_of_continuousOn_of_integrableOn_shifted_tail
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hContinuous : ContinuousOn f (Ici 0))
    (hShiftedTail :
      IntegrableOn (fun s : ℝ ↦ f (T + s)) (Ici 0)) :
    IntegrableOn f (Ici 0) := by
  apply integrableOn_Ici_zero_of_continuousOn_of_integrableOn_tail
    hT hContinuous
  exact
    (integrableOn_Ici_iff_integrableOn_comp_const_add_Ici_zero f T).2
      hShiftedTail

end Poincare
