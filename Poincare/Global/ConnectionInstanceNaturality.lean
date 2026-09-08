import Poincare.Global.CurvatureInstanceTransport

/-!
# Differential naturality across compatible chart instances

The identity map from the new atlas to the original atlas has derivative `J`.
-/

noncomputable section
open Bundle Filter Set FiberBundle
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

/-- Inverse field transport preserves local section regularity, including that of local extensions. -/
theorem inverseTransportField_contMDiffAt {n : ℕ∞ω} (hn : n ≤ ∞)
    (X : M → E) (a : M)
    (hX : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) n
        (fun x : M ↦ (⟨x, X x⟩ : TotalSpace E (TangentSpace I))) a) :
    letI := inst
    ContMDiffAt I ((I).prod 𝓘(ℝ, E)) n
      (fun x : M ↦ (⟨x, inverseTransportField (inst := inst) inst' h X x⟩ :
        TotalSpace E (TangentSpace I))) a := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  have hcoord : letI := inst'
      ContMDiffAt I 𝓘(ℝ, E) n
        (fun x ↦ tangentCoordinates inst' hs a x (X x)) a := by
    letI := inst'
    letI : IsManifold I ∞ M := hs
    exact (Bundle.contMDiffAt_section (IB := I) (F := E) («E» := TangentSpace I) a).1 hX
  have hXold := (modelContMDiffAt_iff_of_le (inst := inst) inst' h hn _ a).2 hcoord
  apply (Bundle.contMDiffAt_section (IB := I) (F := E) («E» := TangentSpace I) a).2
  have hD := (contMDiffAt_D (newChart (inst := inst) inst' h a)
    (oldChart (inst := inst) a) a
    (inst'.mem_chart_source a) (inst.mem_chart_source a)).of_le hn
  apply (hD.clm_apply hXold).congr_of_eventuallyEq
  filter_upwards [(inst.chartAt a).open_source.mem_nhds (inst.mem_chart_source a),
    (inst'.chartAt a).open_source.mem_nhds (inst'.mem_chart_source a)] with x hx hx'
  exact tangentCoordinates_transport (inst := inst) inst' h a x hx hx' (X x)

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

/-- Pullback of the metric pairing makes the conjugated connection metric compatible. -/
theorem conjugatedConnection_metricCompatible
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    IsMetricCompatible (transport (inst := inst) inst' h g)
      (conjugatedConnection (inst := inst) inst' h g) := by
  letI := inst
  intro x X Y hX hY v
  have hXold := inverseTransportField_mdiffAt (inst := inst) inst' h X x hX
  have hYold := inverseTransportField_mdiffAt (inst := inst) inst' h Y x hY
  have hc := g.leviCivita_metricCompatible hXold hYold (J (inst := inst) inst' h x v)
  have hd := extDerivFun_naturality_total (inst := inst) inst' h
    (fun y ↦ g.inner y (inverseTransportField (inst := inst) inst' h X y)
      (inverseTransportField (inst := inst) inst' h Y y)) x v
  change _ = g.inner x
    (J (inst := inst) inst' h x ((J (inst := inst) inst' h x).symm
      (g.leviCivita (inverseTransportField (inst := inst) inst' h X) x
        (J (inst := inst) inst' h x v))))
    (inverseTransportField (inst := inst) inst' h Y x) +
    g.inner x (inverseTransportField (inst := inst) inst' h X x)
      (J (inst := inst) inst' h x ((J (inst := inst) inst' h x).symm
        (g.leviCivita (inverseTransportField (inst := inst) inst' h Y) x
          (J (inst := inst) inst' h x v))))
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact hd.trans hc

/-- Lie-bracket naturality transfers zero torsion to the conjugated connection. -/
theorem conjugatedConnection_torsion
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    (conjugatedConnection (inst := inst) inst' h g).torsion = 0 := by
  letI := inst
  have ht := g.leviCivita_torsion
  rw [CovariantDerivative.torsion_eq_zero_iff] at ht
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  have hXold := inverseTransportField_mdiffAt (inst := inst) inst' h X x hX
  have hYold := inverseTransportField_mdiffAt (inst := inst) inst' h Y x hY
  have ho := ht hXold hYold
  have hb := mlieBracket_transportField (inst := inst) inst' h
    (inverseTransportField (inst := inst) inst' h X)
    (inverseTransportField (inst := inst) inst' h Y) x hXold hYold
  have hr (Z : M → E) : transportField (inst := inst) inst' h
      (inverseTransportField (inst := inst) inst' h Z) = Z := by
    funext y
    exact (J (inst := inst) inst' h y).symm_apply_apply (Z y)
  rw [hr X, hr Y] at hb
  change (J (inst := inst) inst' h x).symm _ -
    (J (inst := inst) inst' h x).symm _ = _
  rw [← map_sub]
  exact (congrArg (J (inst := inst) inst' h x).symm ho).trans hb.symm

/-- The conjugated connection agrees with the new Levi-Civita connection on differentiable fields. -/
theorem conjugatedConnection_eq_leviCivita
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    ∀ (X : M → E) (x : M), MDiffAtTangentField X x →
      conjugatedDerivative (inst := inst) inst' h g X x =
        (transport (inst := inst) inst' h g).leviCivita X x := by
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  intro X x hX
  exact (transport (inst := inst) inst' h g).eq_leviCivita_of_metricCompatible_torsion
    (conjugatedConnection_metricCompatible (inst := inst) inst' h g)
    (conjugatedConnection_torsion (inst := inst) inst' h g) hX

/-- Pointwise connection naturality, oriented from the new connection to the old one. -/
theorem leviCivita_naturality_apply
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (X : M → E) (x : M)
    (hX : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      MDiffAtTangentField (n := 3) X x) (v : E) :
    (letI := inst';
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1;
      J (inst := inst) inst' h x ((transport (inst := inst) inst' h g).leviCivita X x v)) =
      (letI := inst; g.leviCivita (inverseTransportField (inst := inst) inst' h X) x
        (J (inst := inst) inst' h x v)) := by
  have he := conjugatedConnection_eq_leviCivita (inst := inst) inst' h g X x hX
  rw [← he]
  exact (J (inst := inst) inst' h x).apply_symm_apply _

/-- Nested covariant derivatives transform using germ locality of the inner section. -/
theorem leviCivita_naturality_twice
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (Z W : M → E) (x : M)
    (hZ : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
        (fun y : M ↦ (⟨y, Z y⟩ : TotalSpace E (TangentSpace I))) x)
    (hW : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      MDiffAtTangentField (n := 3) W x) (v : E) :
    (letI := inst';
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1;
      let cov := (transport (inst := inst) inst' h g).leviCivita;
      J (inst := inst) inst' h x (cov (fun y ↦ cov Z y (W y)) x v)) =
    (letI := inst;
      g.leviCivita (fun y ↦ g.leviCivita (inverseTransportField (inst := inst) inst' h Z) y
        (inverseTransportField (inst := inst) inst' h W y)) x
        (J (inst := inst) inst' h x v)) := by
  letI := inst
  have hZold := inverseTransportField_contMDiffAt (inst := inst) inst' h
    (show (2 : ℕ∞ω) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) Z x hZ
  have hWold := inverseTransportField_mdiffAt (inst := inst) inst' h W x hW
  have hinnerOld := CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
    g.leviCivita hZold hWold
  let innerOld := fun y ↦ g.leviCivita (inverseTransportField (inst := inst) inst' h Z) y
    (inverseTransportField (inst := inst) inst' h W y)
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  let cov := (transport (inst := inst) inst' h g).leviCivita
  let innerNew := fun y ↦ cov Z y (W y)
  have hinnerNew := CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt cov hZ hW
  have hinnerInv := inverseTransportField_mdiffAt (inst := inst) inst' h innerNew x hinnerNew
  have hev : inverseTransportField (inst := inst) inst' h innerNew =ᶠ[𝓝 x] innerOld := by
    obtain ⟨s, hs, hZs⟩ := (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
    filter_upwards [eventually_mem_nhds_iff.mpr hs] with y hy
    exact leviCivita_naturality_apply (inst := inst) inst' h g Z y
      ((hZs.contMDiffAt hy).mdifferentiableAt two_ne_zero) (W y)
  have he := leviCivita_naturality_apply (inst := inst) inst' h g innerNew x hinnerNew v
  letI := inst
  have heq := g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hinnerInv hinnerOld univ_mem hev
  exact he.trans (congrArg (fun L ↦ L (J (inst := inst) inst' h x v)) heq)

/-- Curvature of local fields transforms by `J`; no global smoothness is required. -/
theorem curvatureOp_naturality
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (X Y Z : M → E) (x : M)
    (hX : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      MDiffAtTangentField (n := 3) X x)
    (hY : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      MDiffAtTangentField (n := 3) Y x)
    (hZ : letI := inst'
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
        (fun y : M ↦ (⟨y, Z y⟩ : TotalSpace E (TangentSpace I))) x) :
    (letI := inst';
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1;
      J (inst := inst) inst' h x
        (CovariantDerivative.curvatureOp (transport (inst := inst) inst' h g).leviCivita X Y Z x)) =
    (letI := inst; CovariantDerivative.curvatureOp g.leviCivita
      (inverseTransportField (inst := inst) inst' h X)
      (inverseTransportField (inst := inst) inst' h Y)
      (inverseTransportField (inst := inst) inst' h Z) x) := by
  letI := inst
  have hXold := inverseTransportField_mdiffAt (inst := inst) inst' h X x hX
  have hYold := inverseTransportField_mdiffAt (inst := inst) inst' h Y x hY
  have hb := mlieBracket_transportField (inst := inst) inst' h
    (inverseTransportField (inst := inst) inst' h X)
    (inverseTransportField (inst := inst) inst' h Y) x hXold hYold
  have hr (W : M → E) : transportField (inst := inst) inst' h
      (inverseTransportField (inst := inst) inst' h W) = W := by
    funext y
    exact (J (inst := inst) inst' h y).symm_apply_apply (W y)
  rw [hr X, hr Y] at hb
  have hbJ := congrArg (J (inst := inst) inst' h x) hb
  simp only [transportField, ContinuousLinearEquiv.apply_symm_apply] at hbJ
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  have hZd : MDiffAtTangentField (n := 3) Z x := hZ.mdifferentiableAt two_ne_zero
  have hthird := leviCivita_naturality_apply (inst := inst) inst' h g Z x hZd
    (VectorField.mlieBracket I X Y x)
  rw [hbJ] at hthird
  let cov := (transport (inst := inst) inst' h g).leviCivita
  change J (inst := inst) inst' h x
    ((show E from cov (fun y ↦ cov Z y (Y y)) x (X x)) -
      (show E from cov (fun y ↦ cov Z y (X y)) x (Y x)) -
      (show E from cov Z x (VectorField.mlieBracket I X Y x))) = _
  rw [(J (inst := inst) inst' h x).map_sub, (J (inst := inst) inst' h x).map_sub]
  rw [leviCivita_naturality_twice (inst := inst) inst' h g Z Y x hZ hY (X x),
    leviCivita_naturality_twice (inst := inst) inst' h g Z X x hZ hX (Y x), hthird]
  rfl

/-- Curvature values on the canonical extensions conjugate by `J`. -/
theorem curvatureValue_naturality
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (x : M) (u w a : E) :
    (letI := inst';
      letI : IsManifold I ∞ M :=
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1;
      J (inst := inst) inst' h x
        (curvatureValue (transport (inst := inst) inst' h g) x u w a)) =
    curvatureValue (inst := inst) g x (J (inst := inst) inst' h x u)
      (J (inst := inst) inst' h x w) (J (inst := inst) inst' h x a) := by
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  let X : Π y : M, TangentSpace I y := FiberBundle.extend E (x := x) u
  let Y : Π y : M, TangentSpace I y := FiberBundle.extend E (x := x) w
  let Z : Π y : M, TangentSpace I y := FiberBundle.extend E (x := x) a
  have hX : MDiffAtTangentField (n := 3) X x := mdifferentiableAt_extend I E (V := TangentSpace I) (x := x) u
  have hY : MDiffAtTangentField (n := 3) Y x := mdifferentiableAt_extend I E (V := TangentSpace I) (x := x) w
  have hZ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
      (fun y : M ↦ (⟨y, Z y⟩ : TotalSpace E (TangentSpace I))) x :=
    contMDiffAt_extend' I E (V := TangentSpace I) (x := x) a
  have hR := curvatureOp_naturality (inst := inst) inst' h g X Y Z x hX hY hZ
  have hXold := inverseTransportField_mdiffAt (inst := inst) inst' h X x hX
  have hYold := inverseTransportField_mdiffAt (inst := inst) inst' h Y x hY
  have hZold := inverseTransportField_contMDiffAt (inst := inst) inst' h
    (show (2 : ℕ∞ω) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) Z x hZ
  letI := inst
  let X' := inverseTransportField (inst := inst) inst' h X
  let Y' := inverseTransportField (inst := inst) inst' h Y
  let Z' := inverseTransportField (inst := inst) inst' h Z
  let U : Π y : M, TangentSpace I y := FiberBundle.extend E (x := x) (J (inst := inst) inst' h x u)
  let W : Π y : M, TangentSpace I y := FiberBundle.extend E (x := x) (J (inst := inst) inst' h x w)
  let A : Π y : M, TangentSpace I y := FiberBundle.extend E (x := x) (J (inst := inst) inst' h x a)
  have hU : MDiffAtTangentField (n := 3) U x := mdifferentiableAt_extend I E (V := TangentSpace I) (x := x) _
  have hW : MDiffAtTangentField (n := 3) W x := mdifferentiableAt_extend I E (V := TangentSpace I) (x := x) _
  have hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z' x :=
    fun V hV ↦ CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt g.leviCivita hZold hV
  have hxy : CovariantDerivative.curvatureOp g.leviCivita X' Y' Z' x =
      CovariantDerivative.curvatureOp g.leviCivita U W Z' x := by
    rw [← CovariantDerivative.curvatureTensorAt_apply g.leviCivita hreg hXold hYold,
      ← CovariantDerivative.curvatureTensorAt_apply g.leviCivita hreg hU hW]
    simp only [inverseTransportField, X, Y, U, W, FiberBundle.extend_apply_self]
  have hz : CovariantDerivative.curvatureOp g.leviCivita U W Z' x =
      CovariantDerivative.curvatureOp g.leviCivita U W A x :=
    CovariantDerivative.curvatureOp_congr_of_value_eq g.leviCivita hZold
      (contMDiffAt_extend' I E (V := TangentSpace I) (x := x) _) (by simp only [Z', inverseTransportField, Z, A,
        FiberBundle.extend_apply_self]) hU hW
  exact hR.trans (hxy.trans hz)

/-- Connection and curvature naturality across compatible chart instances. -/
theorem connectionCurvatureNaturality
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    CurvatureInstanceTransport.ConnectionCurvatureNaturality (inst := inst) inst' h g :=
  ⟨conjugatedConnection_eq_leviCivita (inst := inst) inst' h g,
    curvatureValue_naturality (inst := inst) inst' h g⟩

section Recognition
variable [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M]

/-- Recognition on the compatible controlled instance implies recognition on the original instance. -/
theorem unitConstantCurvatureSphereRecognition3_of_controlled
    (hrec : @UnitConstantCurvatureSphereRecognition3 M _ _ _ inst'
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1 _ _ _) :
    @UnitConstantCurvatureSphereRecognition3 M _ _ _ inst _ _ _ _ :=
  target_of_ConnectionCurvatureNaturality (inst := inst) inst' h
    (connectionCurvatureNaturality (inst := inst) inst' h) hrec

end Recognition
end Connection
end Poincare.ConnectionInstanceNaturality
