import Poincare.Global.PointFlowVariationalSelectorTower

/-!
# Three-level selector tower for the inverse-gauge point ODE

A locally joint `C⁴` time-dependent coordinate field gives a `C⁴`
autonomous time--point extension.  The generic selector-tower construction
then supplies genuine controlled continuous flows for the base equation and
all three iterated variational systems.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Poincare

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local joint `C⁴` regularity is preserved by the autonomous inverse-gauge
time--point extension. -/
theorem contDiffAt_four_inverseGaugePointExtendedField
    (W : ℝ → E → E) (t : ℝ) (x : E)
    (hW : ContDiffAt ℝ 4 (Function.uncurry W) (t, x)) :
    ContDiffAt ℝ 4 (inverseGaugePointExtendedField W) (t, x) := by
  have htx : ContDiffAt ℝ 4 (fun q : ℝ × E ↦ (q.1, q.2)) (t, x) :=
    contDiffAt_fst.prodMk contDiffAt_snd
  have hWq : ContDiffAt ℝ 4 (fun q : ℝ × E ↦ W q.1 q.2) (t, x) := by
    simpa only [Function.uncurry] using hW.comp (t, x) htx
  simpa only [inverseGaugePointExtendedField] using
    contDiffAt_const.prodMk hWq.neg

/-- A locally joint `C⁴` inverse-gauge coordinate field admits genuine
controlled continuous selectors for its base autonomous point flow and all
three variational augmentations. -/
theorem exists_inverseGaugePoint_threeLevelVariationalSelectorTower
    (W : ℝ → E → E) (t : ℝ) (x : E)
    (J : (ℝ × E) →L[ℝ] (ℝ × E))
    (K : FirstVariationalState (ℝ × E) →L[ℝ]
      FirstVariationalState (ℝ × E))
    (L : SecondVariationalState (ℝ × E) →L[ℝ]
      SecondVariationalState (ℝ × E))
    (hW : ContDiffAt ℝ 4 (Function.uncurry W) (t, x)) :
    Nonempty (ThreeLevelVariationalSelectorTower
      (inverseGaugePointExtendedField W) (t, x) J K L) :=
  exists_threeLevelVariationalSelectorTower_of_contDiffAt_four
    (inverseGaugePointExtendedField W) (t, x) J K L
    (contDiffAt_four_inverseGaugePointExtendedField W t x hW)

end Poincare
