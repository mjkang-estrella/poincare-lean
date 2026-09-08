import Poincare.Global.CurvatureInstanceTransport

/-!
# Differential naturality across compatible chart instances

The identity map from the new atlas to the original atlas has derivative `J`.
-/

noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.ConnectionInstanceNaturality
open RiemannianMetricInstanceTransportGeometric CurvatureInstanceTransport
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M]
variable (inst' : ChartedSpace E M)
  (h : inst'.atlas ⊆ @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I))

include h in
/-- The identity between the two atlas choices is smooth, with its direction explicit. -/
theorem contMDiffAt_identity (x : M) :
    @ContMDiffAt ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst ∞ id x := by
  letI := inst
  have hc := contMDiffAt_extChartAt («I» := I) (n := ∞) (x := x)
  have hc' := (modelContMDiffAt_iff (inst := inst) inst' h _ x).1 hc
  apply (@contMDiffAt_iff ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst ∞ id x).2
  letI := inst'
  exact ⟨continuousAt_id, (contMDiffAt_iff.mp hc').2⟩

/-- The derivative of the identity from the new atlas to the old one is `J`. -/
theorem mfderiv_identity (x : M) :
    @mfderiv ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst id x =
      (J (inst := inst) inst' h x).toContinuousLinearMap := by
  letI := inst
  have hd := @ContMDiffAt.mdifferentiableAt ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst id x ∞
    (contMDiffAt_identity (inst := inst) inst' h x) (by simp)
  ext v
  rw [mfderiv, if_pos hd]
  change _ = J (inst := inst) inst' h x v
  rw [J_apply]
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    mfld_simps, fderivWithin_univ, Function.id_comp]
  rfl

/-- Scalar exterior derivatives transform by the new-to-old tangent identification. -/
theorem extDerivFun_naturality (f : M → ℝ) (x : M)
    (hf : letI := inst; MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (v : E) :
    (letI := inst'; extDerivFun («I» := I) f x v) =
      (letI := inst; extDerivFun («I» := I) f x (J (inst := inst) inst' h x v)) := by
  letI := inst
  have hd := @ContMDiffAt.mdifferentiableAt ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst id x ∞
    (contMDiffAt_identity (inst := inst) inst' h x) (by simp)
  have he := @mfderiv_comp ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst
    ℝ _ _ ℝ _ 𝓘(ℝ, ℝ) ℝ _ _ id x f hf hd
  rw [mfderiv_identity (inst := inst) inst' h] at he
  exact congrArg (fun L ↦ L v) he

/-- Field transport is pullback by the identity between the two chart instances. -/
theorem mpullback_identity (X : M → E) :
    @VectorField.mpullback ℝ _ E _ E _ _ I M _ inst' E _ E _ _ I M _ inst id X =
      transportField (inst := inst) inst' h X := by
  funext x
  rw [VectorField.mpullback, mfderiv_identity (inst := inst) inst' h]
  change (J (inst := inst) inst' h x).toContinuousLinearMap.inverse (X x) =
    (J (inst := inst) inst' h x).symm (X x)
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

/-- Lie brackets commute with transport at points where both fields are differentiable. -/
theorem mlieBracket_transportField (X Y : M → E) (x : M)
    (hX : letI := inst; MDiffAtTangentField (n := 3) X x)
    (hY : letI := inst; MDiffAtTangentField (n := 3) Y x) :
    (letI := inst';
      VectorField.mlieBracket I (transportField (inst := inst) inst' h X)
        (transportField (inst := inst) inst' h Y) x) =
      transportField (inst := inst) inst' h
        (letI := inst; VectorField.mlieBracket I X Y) x := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  have hs' : (letI := inst'; IsManifold I (minSmoothness ℝ 2) M) := by
    letI := inst'
    letI : IsManifold I ∞ M := hs
    exact IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hb := @VectorField.mpullback_mlieBracket ℝ _ E _ E _ _ I M _ inst'
    E _ E _ _ I M _ inst hs' (IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) inferInstance ∞ id X Y x hX hY
    (contMDiffAt_identity (inst := inst) inst' h x) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [mpullback_identity (inst := inst) inst' h,
    mpullback_identity (inst := inst) inst' h,
    mpullback_identity (inst := inst) inst' h] at hb
  exact hb.symm

/-- The same identity respects the zero value of the derivative at nondifferentiable points. -/
theorem extDerivFun_naturality_total (f : M → ℝ) (x : M) (v : E) :
    (letI := inst'; extDerivFun («I» := I) f x v) =
      (letI := inst; extDerivFun («I» := I) f x (J (inst := inst) inst' h x v)) := by
  letI := inst
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · exact extDerivFun_naturality (inst := inst) inst' h f x hf v
  · have hf' : ¬ (letI := inst'; MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :=
      fun hf' ↦ hf ((modelMDifferentiableAt_iff (inst := inst) inst' h f x).2 hf')
    simp only [extDerivFun, mfderiv, if_neg hf, if_neg hf', ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]

section Connection
variable [T2Space M]

/-- The raw conjugated derivative satisfies Leibniz without a naturality premise. -/
theorem conjugatedDerivative_leibniz
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (X : M → E) (f : M → ℝ) (x : M)
    (hX : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      MDiffAtTangentField (n := 3) X x)
    (hf : letI := inst'; MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (v : E) :
    conjugatedDerivative (inst := inst) inst' h g (f • X) x v =
      f x • conjugatedDerivative (inst := inst) inst' h g X x v +
        (letI := inst'; extDerivFun («I» := I) f x v) • X x := by
  letI := inst
  have hXold := inverseTransportField_mdiffAt (inst := inst) inst' h X x hX
  have hfold := (modelMDifferentiableAt_iff (inst := inst) inst' h f x).2 hf
  have hsmul : inverseTransportField (inst := inst) inst' h (f • X) =
      f • inverseTransportField (inst := inst) inst' h X := by
    funext y
    exact (J (inst := inst) inst' h y).map_smul (f y) (X y)
  unfold conjugatedDerivative
  rw [hsmul, g.leviCivita.isCovariantDerivativeOnUniv.leibniz hXold hfold]
  change (J (inst := inst) inst' h x).symm
      (f x • (show E from g.leviCivita (inverseTransportField (inst := inst) inst' h X) x
        (J (inst := inst) inst' h x v)) +
        extDerivFun («I» := I) f x (J (inst := inst) inst' h x v) •
          J (inst := inst) inst' h x (X x)) = _
  rw [map_add, map_smul, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  congr 1
  exact congrArg (fun r : ℝ ↦ r • X x)
    (extDerivFun_naturality (inst := inst) inst' h f x hfold v).symm

/-- Scalar naturality and additivity bundle the conjugated connection unconditionally. -/
theorem conjugatedDerivative_isCovariantDerivativeOn
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    IsCovariantDerivativeOn («I» := I) (V := TangentSpace I) E
      (conjugatedDerivative (inst := inst) inst' h g) univ := by
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  constructor
  · intro X Y x hX hY _
    exact conjugatedDerivative_add (inst := inst) inst' h g X Y x hX hY
  · intro X f x hX hf _
    apply ContinuousLinearMap.ext
    intro v
    exact conjugatedDerivative_leibniz (inst := inst) inst' h g X f x hX hf v

/-- The conjugated operator as a covariant derivative, with its laws proved. -/
def conjugatedConnection (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    CovariantDerivative I E (TangentSpace I : M → Type _) := by
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  exact ⟨conjugatedDerivative (inst := inst) inst' h g,
    conjugatedDerivative_isCovariantDerivativeOn (inst := inst) inst' h g⟩

end Connection
end Poincare.ConnectionInstanceNaturality
