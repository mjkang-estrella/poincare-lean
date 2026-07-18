import Poincare.Global.DeTurckBUCPointFlowVariationalSmoothDependence

/-!
# Generic variational fields for the autonomous DeTurck point flow

For an autonomous field `F`, the first variational augmented field is

`(z,J) ↦ (F z, D F(z) ∘ J)`.

Iterating this construction packages the second and third variational
systems.  A `C³` base field makes the first augmented field `C²`, the second
`C¹`, and the third `C⁰`.  These are the precise field-regularity inputs for
the residual/endpoint tower needed to prove smooth dependence of the selected
Picard--Lindelof family.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Poincare

section GenericVariationalFields

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- State space of a point and its first linear variation. -/
abbrev FirstVariationalState (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  X × (X →L[ℝ] X)

/-- State space obtained after two variational augmentations. -/
abbrev SecondVariationalState (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  FirstVariationalState X ×
    (FirstVariationalState X →L[ℝ] FirstVariationalState X)

/-- State space obtained after three variational augmentations. -/
abbrev ThirdVariationalState (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  SecondVariationalState X ×
    (SecondVariationalState X →L[ℝ] SecondVariationalState X)

/-- The point flow together with its continuous-linear initial-state
variation. -/
def firstVariationalAugmentedField (F : X → X) :
    (X × (X →L[ℝ] X)) → (X × (X →L[ℝ] X)) :=
  fun z ↦ (F z.1, (fderiv ℝ F z.1).comp z.2)

/-- The variational augmentation iterated twice. -/
def secondVariationalAugmentedField (F : X → X) :=
  firstVariationalAugmentedField (firstVariationalAugmentedField F)

/-- The variational augmentation iterated three times. -/
def thirdVariationalAugmentedField (F : X → X) :=
  firstVariationalAugmentedField (secondVariationalAugmentedField F)

/-- A local `C⁴` field has a locally `C³` first variational augmented
field.  This one-extra-derivative version makes every level of a three-stage
variational selector tower locally Lipschitz and hence directly accessible to
Picard--Lindelof. -/
theorem firstVariationalAugmentedField_contDiffAt_three_of_contDiffAt_four
    (F : X → X) (x : X) (J : X →L[ℝ] X)
    (hF : ContDiffAt ℝ 4 F x) :
    ContDiffAt ℝ 3 (firstVariationalAugmentedField F) (x, J) := by
  have hbase : ContDiffAt ℝ 3
      (fun z : X × (X →L[ℝ] X) ↦ F z.1) (x, J) :=
    (hF.of_le (by norm_num)).comp (x, J) contDiffAt_fst
  have hDf : ContDiffAt ℝ 3
      (fun z : X × (X →L[ℝ] X) ↦ fderiv ℝ F z.1) (x, J) :=
    (hF.fderiv_right (m := 3) (by norm_num)).comp (x, J) contDiffAt_fst
  have hcompFamily : ContDiffAt ℝ 3
      (fun z : X × (X →L[ℝ] X) ↦
        (ContinuousLinearMap.compL ℝ X X X) (fderiv ℝ F z.1)) (x, J) :=
    contDiffAt_const.clm_apply hDf
  have hvariation : ContDiffAt ℝ 3
      (fun z : X × (X →L[ℝ] X) ↦ (fderiv ℝ F z.1).comp z.2)
      (x, J) := by
    simpa using hcompFamily.clm_apply contDiffAt_snd
  simpa only [firstVariationalAugmentedField] using hbase.prodMk hvariation

/-- A local `C³` field has a locally `C²` first variational augmented
field at every prescribed linear initial variation. -/
theorem firstVariationalAugmentedField_contDiffAt_two_of_contDiffAt_three
    (F : X → X) (x : X) (J : X →L[ℝ] X)
    (hF : ContDiffAt ℝ 3 F x) :
    ContDiffAt ℝ 2 (firstVariationalAugmentedField F) (x, J) := by
  have hbase : ContDiffAt ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦ F z.1) (x, J) :=
    (hF.of_le (by norm_num)).comp (x, J) contDiffAt_fst
  have hDf : ContDiffAt ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦ fderiv ℝ F z.1) (x, J) :=
    (hF.fderiv_right (m := 2) (by norm_num)).comp (x, J) contDiffAt_fst
  have hcompFamily : ContDiffAt ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦
        (ContinuousLinearMap.compL ℝ X X X) (fderiv ℝ F z.1)) (x, J) :=
    contDiffAt_const.clm_apply hDf
  have hvariation : ContDiffAt ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦ (fderiv ℝ F z.1).comp z.2)
      (x, J) := by
    simpa using hcompFamily.clm_apply contDiffAt_snd
  simpa only [firstVariationalAugmentedField] using hbase.prodMk hvariation

/-- A local `C²` field has a locally `C¹` first variational augmented
field. -/
theorem firstVariationalAugmentedField_contDiffAt_one_of_contDiffAt_two
    (F : X → X) (x : X) (J : X →L[ℝ] X)
    (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 1 (firstVariationalAugmentedField F) (x, J) := by
  have hbase : ContDiffAt ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦ F z.1) (x, J) :=
    (hF.of_le (by norm_num)).comp (x, J) contDiffAt_fst
  have hDf : ContDiffAt ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦ fderiv ℝ F z.1) (x, J) :=
    (hF.fderiv_right (m := 1) (by norm_num)).comp (x, J) contDiffAt_fst
  have hcompFamily : ContDiffAt ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦
        (ContinuousLinearMap.compL ℝ X X X) (fderiv ℝ F z.1)) (x, J) :=
    contDiffAt_const.clm_apply hDf
  have hvariation : ContDiffAt ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦ (fderiv ℝ F z.1).comp z.2)
      (x, J) := by
    simpa using hcompFamily.clm_apply contDiffAt_snd
  simpa only [firstVariationalAugmentedField] using hbase.prodMk hvariation

/-- A local `C¹` field has a continuous first variational augmented field. -/
theorem firstVariationalAugmentedField_contDiffAt_zero_of_contDiffAt_one
    (F : X → X) (x : X) (J : X →L[ℝ] X)
    (hF : ContDiffAt ℝ 1 F x) :
    ContDiffAt ℝ 0 (firstVariationalAugmentedField F) (x, J) := by
  have hbase : ContDiffAt ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦ F z.1) (x, J) :=
    (hF.of_le (by norm_num)).comp (x, J) contDiffAt_fst
  have hDf : ContDiffAt ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦ fderiv ℝ F z.1) (x, J) :=
    (hF.fderiv_right (m := 0) (by norm_num)).comp (x, J) contDiffAt_fst
  have hcompFamily : ContDiffAt ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦
        (ContinuousLinearMap.compL ℝ X X X) (fderiv ℝ F z.1)) (x, J) :=
    contDiffAt_const.clm_apply hDf
  have hvariation : ContDiffAt ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦ (fderiv ℝ F z.1).comp z.2)
      (x, J) := by
    simpa using hcompFamily.clm_apply contDiffAt_snd
  simpa only [firstVariationalAugmentedField] using hbase.prodMk hvariation

/-- Local version of the complete `C³ → C²/C¹/C⁰` variational-field
cascade, at arbitrary prescribed initial states in the three augmented
spaces. -/
theorem variationalAugmentedFields_regularities_of_contDiffAt_three
    (F : X → X) (x : X) (J : X →L[ℝ] X)
    (K : FirstVariationalState X →L[ℝ] FirstVariationalState X)
    (L : SecondVariationalState X →L[ℝ] SecondVariationalState X)
    (hF : ContDiffAt ℝ 3 F x) :
    ContDiffAt ℝ 2 (firstVariationalAugmentedField F) (x, J) ∧
      ContDiffAt ℝ 1 (secondVariationalAugmentedField F) ((x, J), K) ∧
      ContDiffAt ℝ 0 (thirdVariationalAugmentedField F) (((x, J), K), L) := by
  have hfirst : ContDiffAt ℝ 2
      (firstVariationalAugmentedField F) (x, J) :=
    firstVariationalAugmentedField_contDiffAt_two_of_contDiffAt_three
      F x J hF
  have hsecond : ContDiffAt ℝ 1
      (secondVariationalAugmentedField F) ((x, J), K) := by
    exact firstVariationalAugmentedField_contDiffAt_one_of_contDiffAt_two
      (firstVariationalAugmentedField F) (x, J) K hfirst
  have hthird : ContDiffAt ℝ 0
      (thirdVariationalAugmentedField F) (((x, J), K), L) := by
    exact firstVariationalAugmentedField_contDiffAt_zero_of_contDiffAt_one
      (secondVariationalAugmentedField F) ((x, J), K) L hsecond
  exact ⟨hfirst, hsecond, hthird⟩

/-- With one spare derivative, all three iterated augmented fields remain at
least `C¹`, so each admits a controlled continuous Picard--Lindelof
selector. -/
theorem variationalAugmentedFields_lipschitzRegularities_of_contDiffAt_four
    (F : X → X) (x : X) (J : X →L[ℝ] X)
    (K : FirstVariationalState X →L[ℝ] FirstVariationalState X)
    (L : SecondVariationalState X →L[ℝ] SecondVariationalState X)
    (hF : ContDiffAt ℝ 4 F x) :
    ContDiffAt ℝ 3 (firstVariationalAugmentedField F) (x, J) ∧
      ContDiffAt ℝ 2 (secondVariationalAugmentedField F) ((x, J), K) ∧
      ContDiffAt ℝ 1 (thirdVariationalAugmentedField F) (((x, J), K), L) := by
  have hfirst : ContDiffAt ℝ 3
      (firstVariationalAugmentedField F) (x, J) :=
    firstVariationalAugmentedField_contDiffAt_three_of_contDiffAt_four
      F x J hF
  have hsecond : ContDiffAt ℝ 2
      (secondVariationalAugmentedField F) ((x, J), K) :=
    firstVariationalAugmentedField_contDiffAt_two_of_contDiffAt_three
      (firstVariationalAugmentedField F) (x, J) K hfirst
  have hthird : ContDiffAt ℝ 1
      (thirdVariationalAugmentedField F) (((x, J), K), L) :=
    firstVariationalAugmentedField_contDiffAt_one_of_contDiffAt_two
      (secondVariationalAugmentedField F) ((x, J), K) L hsecond
  exact ⟨hfirst, hsecond, hthird⟩

/-- A `C³` field has a `C²` first variational augmented field. -/
theorem firstVariationalAugmentedField_contDiff_two_of_contDiff_three
    (F : X → X) (hF : ContDiff ℝ 3 F) :
    ContDiff ℝ 2 (firstVariationalAugmentedField F) := by
  have hbase : ContDiff ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦ F z.1) :=
    (hF.of_le (by norm_num)).comp contDiff_fst
  have hDf : ContDiff ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦ fderiv ℝ F z.1) :=
    (hF.fderiv_right (m := 2) (by norm_num)).comp contDiff_fst
  have hcompFamily : ContDiff ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦
        (ContinuousLinearMap.compL ℝ X X X) (fderiv ℝ F z.1)) :=
    contDiff_const.clm_apply hDf
  have hJ : ContDiff ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦ z.2) := contDiff_snd
  have hvariation : ContDiff ℝ 2
      (fun z : X × (X →L[ℝ] X) ↦ (fderiv ℝ F z.1).comp z.2) := by
    simpa using hcompFamily.clm_apply hJ
  simpa only [firstVariationalAugmentedField] using
    hbase.prodMk hvariation

/-- A `C²` field has a `C¹` first variational augmented field. -/
theorem firstVariationalAugmentedField_contDiff_one_of_contDiff_two
    (F : X → X) (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (firstVariationalAugmentedField F) := by
  have hbase : ContDiff ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦ F z.1) :=
    (hF.of_le (by norm_num)).comp contDiff_fst
  have hDf : ContDiff ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦ fderiv ℝ F z.1) :=
    (hF.fderiv_right (m := 1) (by norm_num)).comp contDiff_fst
  have hcompFamily : ContDiff ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦
        (ContinuousLinearMap.compL ℝ X X X) (fderiv ℝ F z.1)) :=
    contDiff_const.clm_apply hDf
  have hJ : ContDiff ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦ z.2) := contDiff_snd
  have hvariation : ContDiff ℝ 1
      (fun z : X × (X →L[ℝ] X) ↦ (fderiv ℝ F z.1).comp z.2) := by
    simpa using hcompFamily.clm_apply hJ
  simpa only [firstVariationalAugmentedField] using
    hbase.prodMk hvariation

/-- A `C¹` field has a continuous first variational augmented field. -/
theorem firstVariationalAugmentedField_contDiff_zero_of_contDiff_one
    (F : X → X) (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 0 (firstVariationalAugmentedField F) := by
  have hbase : ContDiff ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦ F z.1) :=
    (hF.of_le (by norm_num)).comp contDiff_fst
  have hDf : ContDiff ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦ fderiv ℝ F z.1) :=
    (hF.fderiv_right (m := 0) (by norm_num)).comp contDiff_fst
  have hcompFamily : ContDiff ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦
        (ContinuousLinearMap.compL ℝ X X X) (fderiv ℝ F z.1)) :=
    contDiff_const.clm_apply hDf
  have hJ : ContDiff ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦ z.2) := contDiff_snd
  have hvariation : ContDiff ℝ 0
      (fun z : X × (X →L[ℝ] X) ↦ (fderiv ℝ F z.1).comp z.2) := by
    simpa using hcompFamily.clm_apply hJ
  simpa only [firstVariationalAugmentedField] using
    hbase.prodMk hvariation

/-- The complete three-level field-regularity cascade from a `C³` base
field. -/
theorem variationalAugmentedFields_regularities_of_contDiff_three
    (F : X → X) (hF : ContDiff ℝ 3 F) :
    ContDiff ℝ 2 (firstVariationalAugmentedField F) ∧
      ContDiff ℝ 1 (secondVariationalAugmentedField F) ∧
      ContDiff ℝ 0 (thirdVariationalAugmentedField F) := by
  have hfirst : ContDiff ℝ 2 (firstVariationalAugmentedField F) :=
    firstVariationalAugmentedField_contDiff_two_of_contDiff_three F hF
  have hsecond : ContDiff ℝ 1 (secondVariationalAugmentedField F) := by
    exact firstVariationalAugmentedField_contDiff_one_of_contDiff_two
      (firstVariationalAugmentedField F) hfirst
  have hthird : ContDiff ℝ 0 (thirdVariationalAugmentedField F) := by
    exact firstVariationalAugmentedField_contDiff_zero_of_contDiff_one
      (secondVariationalAugmentedField F) hsecond
  exact ⟨hfirst, hsecond, hthird⟩

end GenericVariationalFields

section InverseGaugeExtendedFieldRegularity

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local joint `C³` regularity of the inverse-gauge coordinate field gives
local `C³` regularity of its autonomous time--point extension. -/
theorem contDiffAt_three_inverseGaugePointExtendedField
    (W : ℝ → E → E) (t : ℝ) (x : E)
    (hW : ContDiffAt ℝ 3 (Function.uncurry W) (t, x)) :
    ContDiffAt ℝ 3 (inverseGaugePointExtendedField W) (t, x) := by
  have htx : ContDiffAt ℝ 3 (fun q : ℝ × E ↦ (q.1, q.2)) (t, x) :=
    contDiffAt_fst.prodMk contDiffAt_snd
  have hWq : ContDiffAt ℝ 3 (fun q : ℝ × E ↦ W q.1 q.2) (t, x) := by
    simpa only [Function.uncurry] using hW.comp (t, x) htx
  simpa only [inverseGaugePointExtendedField] using
    contDiffAt_const.prodMk hWq.neg

/-- Local joint `C³` regularity of `W` supplies the complete local
regularity cascade for the first three variational fields of the autonomous
inverse-gauge point ODE. -/
theorem inverseGaugePoint_variationalAugmentedFields_regularitiesAt
    (W : ℝ → E → E) (t : ℝ) (x : E)
    (J : (ℝ × E) →L[ℝ] (ℝ × E))
    (K : FirstVariationalState (ℝ × E) →L[ℝ]
      FirstVariationalState (ℝ × E))
    (L : SecondVariationalState (ℝ × E) →L[ℝ]
      SecondVariationalState (ℝ × E))
    (hW : ContDiffAt ℝ 3 (Function.uncurry W) (t, x)) :
    ContDiffAt ℝ 2
        (firstVariationalAugmentedField (inverseGaugePointExtendedField W))
        ((t, x), J) ∧
      ContDiffAt ℝ 1
        (secondVariationalAugmentedField (inverseGaugePointExtendedField W))
        (((t, x), J), K) ∧
      ContDiffAt ℝ 0
        (thirdVariationalAugmentedField (inverseGaugePointExtendedField W))
        ((((t, x), J), K), L) :=
  variationalAugmentedFields_regularities_of_contDiffAt_three
    (inverseGaugePointExtendedField W) (t, x) J K L
    (contDiffAt_three_inverseGaugePointExtendedField W t x hW)

/-- Joint `C³` regularity of the inverse-gauge coordinate field gives a
`C³` autonomous time--point extension. -/
theorem contDiff_three_inverseGaugePointExtendedField
    (W : ℝ → E → E)
    (hW : ContDiff ℝ 3 (Function.uncurry W)) :
    ContDiff ℝ 3 (inverseGaugePointExtendedField W) := by
  have htx : ContDiff ℝ 3 (fun q : ℝ × E ↦ (q.1, q.2)) :=
    contDiff_fst.prodMk contDiff_snd
  have hWq : ContDiff ℝ 3 (fun q : ℝ × E ↦ W q.1 q.2) := by
    simpa only [Function.uncurry] using hW.comp htx
  simpa only [inverseGaugePointExtendedField] using
    contDiff_const.prodMk hWq.neg

/-- The first three variational augmented fields of a jointly `C³`
inverse-gauge point field have the regularities required by the variational
endpoint tower. -/
theorem inverseGaugePoint_variationalAugmentedFields_regularities
    (W : ℝ → E → E)
    (hW : ContDiff ℝ 3 (Function.uncurry W)) :
    ContDiff ℝ 2
        (firstVariationalAugmentedField (inverseGaugePointExtendedField W)) ∧
      ContDiff ℝ 1
        (secondVariationalAugmentedField (inverseGaugePointExtendedField W)) ∧
      ContDiff ℝ 0
        (thirdVariationalAugmentedField (inverseGaugePointExtendedField W)) :=
  variationalAugmentedFields_regularities_of_contDiff_three
    (inverseGaugePointExtendedField W)
    (contDiff_three_inverseGaugePointExtendedField W hW)

end InverseGaugeExtendedFieldRegularity

end Poincare
