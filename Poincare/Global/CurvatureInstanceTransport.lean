import Poincare.Global.RiemannianMetricInstanceTransportGeometric
import Poincare.Global.SphereTheorem

/-!
# Tangent fields across compatible chart instances

The geometric identification `J` maps new fibers to old fibers. Its inverse
therefore transports old vector fields to the new tangent bundle.
-/

noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.CurvatureInstanceTransport
open RiemannianMetricInstanceTransportGeometric
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M]

/-- Tangent-section regularity with the chart instance explicit. -/
def fieldContMDiff (charts : ChartedSpace E M)
    (hs : letI := charts; IsManifold I ∞ M) (n : ℕ∞ω) (X : M → E) : Prop :=
  letI := charts
  letI : IsManifold I ∞ M := hs
  ContMDiff I ((I).prod 𝓘(ℝ, E)) n
    (fun x : M ↦ (⟨x, X x⟩ : TotalSpace E (TangentSpace I)))

/-- Preferred tangent trivializations detect section regularity. -/
theorem fieldContMDiff_iff (n : ℕ∞ω) (X : M → E) :
    fieldContMDiff inst inferInstance n X ↔
      ∀ a, ContMDiffAt I 𝓘(ℝ, E) n
        (fun x ↦ tangentCoordinates inst inferInstance a x (X x)) a := by
  exact forall_congr' fun a ↦ Bundle.contMDiffAt_section
    (IB := I) (F := E) («E» := TangentSpace I) (s := X) a

variable (inst' : ChartedSpace E M)
  (h : inst'.atlas ⊆ @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I))

/-- Transport from the old tangent fibers to the new ones. -/
def transportField (X : Π x : M, TangentSpace I x) : M → E :=
  fun x ↦ (J (inst := inst) inst' h x).symm (X x)

/-- Transport from the new tangent fibers back to the old ones. -/
def inverseTransportField (X : M → E) : Π x : M, TangentSpace I x :=
  fun x ↦ J (inst := inst) inst' h x (X x)

/-- New tangent coordinates are related to old ones by a fixed-anchor derivative. -/
theorem tangentCoordinates_transportField (X : M → E) (a x : M)
    (ha : x ∈ (inst.chartAt a).source) (ha' : x ∈ (inst'.chartAt a).source) :
    tangentCoordinates inst'
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
        a x (transportField (inst := inst) inst' h X x) =
      D (inst := inst) (oldChart (inst := inst) a) (newChart (inst := inst) inst' h a) x
        (tangentCoordinates inst inferInstance a x (X x)) := by
  letI := inst
  have hb := tangentCoordinates_transport (inst := inst) inst' h a x ha ha'
    (transportField (inst := inst) inst' h X x)
  simp only [transportField, ContinuousLinearEquiv.apply_symm_apply] at hb
  rw [hb, D_comp _ _ _ x ha' ha ha', D_self _ x ha']
  rfl

include h in
/-- Source chart independence for model-valued maps at every finite or smooth order. -/
theorem modelContMDiffAt_iff_of_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} (hn : n ≤ ∞) (f : M → F) (x : M) :
    (letI := inst; ContMDiffAt I 𝓘(ℝ, F) n f x) ↔
      (letI := inst'; ContMDiffAt I 𝓘(ℝ, F) n f x) := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  letI : IsManifold I n M := IsManifold.of_le hn
  let e := inst'.chartAt x
  have he : e ∈ IsManifold.maximalAtlas I n M :=
    StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le hn)
      (h (inst'.chart_mem_atlas x))
  have hx : x ∈ e.source := inst'.mem_chart_source x
  have hold := contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    (I' := 𝓘(ℝ, F)) (f := f) (s := univ) he hx
  letI := inst'
  letI : IsManifold I ∞ M := hs
  letI : IsManifold I n M := IsManifold.of_le hn
  have he' : e ∈ IsManifold.maximalAtlas I n M := IsManifold.chart_mem_maximalAtlas x
  have hnew := contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    (I' := 𝓘(ℝ, F)) (f := f) (s := univ) he' hx
  exact hold.trans hnew.symm

/-- The inverse-J transport preserves tangent-section regularity. -/
theorem transportField_contMDiff {n : ℕ∞ω} (hn : n ≤ ∞) (X : M → E)
    (hX : fieldContMDiff inst inferInstance n X) :
    fieldContMDiff inst'
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1 n
      (transportField (inst := inst) inst' h X) := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  apply (@fieldContMDiff_iff M _ inst' hs n _).2
  intro a
  apply (modelContMDiffAt_iff_of_le (inst := inst) inst' h hn _ a).1
  have hX' := (fieldContMDiff_iff n X).1 hX a
  have hD := (contMDiffAt_D (oldChart (inst := inst) a)
    (newChart (inst := inst) inst' h a) a
    (inst.mem_chart_source a) (inst'.mem_chart_source a)).of_le hn
  apply (hD.clm_apply hX').congr_of_eventuallyEq
  filter_upwards [(inst.chartAt a).open_source.mem_nhds (inst.mem_chart_source a),
    (inst'.chartAt a).open_source.mem_nhds (inst'.mem_chart_source a)] with x hx hx'
  exact tangentCoordinates_transportField inst' h X a x hx hx'

/-- Transport back by J preserves tangent-section regularity. -/
theorem inverseTransportField_contMDiff {n : ℕ∞ω} (hn : n ≤ ∞) (X : M → E)
    (hX : fieldContMDiff inst'
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1 n X) :
    fieldContMDiff inst inferInstance n (inverseTransportField (inst := inst) inst' h X) := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  apply (fieldContMDiff_iff n _).2
  intro a
  have hX' := (@fieldContMDiff_iff M _ inst' hs n X).1 hX a
  have hXold := (modelContMDiffAt_iff_of_le (inst := inst) inst' h hn _ a).2 hX'
  have hD := (contMDiffAt_D (newChart (inst := inst) inst' h a)
    (oldChart (inst := inst) a) a
    (inst'.mem_chart_source a) (inst.mem_chart_source a)).of_le hn
  apply (hD.clm_apply hXold).congr_of_eventuallyEq
  filter_upwards [(inst.chartAt a).open_source.mem_nhds (inst.mem_chart_source a),
    (inst'.chartAt a).open_source.mem_nhds (inst'.mem_chart_source a)] with x hx hx'
  exact tangentCoordinates_transport (inst := inst) inst' h a x hx hx' (X x)

/-- Tangent sections have the same regularity after geometric transport. -/
theorem transportField_contMDiff_iff {n : ℕ∞ω} (hn : n ≤ ∞) (X : M → E) :
    fieldContMDiff inst'
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1 n
        (transportField (inst := inst) inst' h X) ↔
      fieldContMDiff inst inferInstance n X := by
  letI := inst
  constructor
  · intro hX
    have hback := inverseTransportField_contMDiff inst' h hn _ hX
    have he : inverseTransportField (inst := inst) inst' h
        (transportField (inst := inst) inst' h X) = X :=
      funext fun x ↦ (J (inst := inst) inst' h x).apply_symm_apply (X x)
    rw [he] at hback
    exact hback
  · exact transportField_contMDiff inst' h hn X

section Connection
variable [T2Space M]

/-- Conjugate the old Levi-Civita operator, including its direction argument. -/
def conjugatedDerivative (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    (M → E) → M → E →L[ℝ] E :=
  letI := inst
  fun X x ↦ (J (inst := inst) inst' h x).symm.toContinuousLinearMap.comp
    ((g.leviCivita (inverseTransportField (inst := inst) inst' h X) x).comp
      (J (inst := inst) inst' h x).toContinuousLinearMap)

/-- The conjugated operator has the required vector-field formula. -/
theorem conjugatedDerivative_apply (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
    (X : M → E) (x : M) (v : E) :
    conjugatedDerivative (inst := inst) inst' h g X x v =
      (letI := inst
       (J (inst := inst) inst' h x).symm
         (g.leviCivita (inverseTransportField (inst := inst) inst' h X) x
           (J (inst := inst) inst' h x v))) := rfl

/-- The actual curvature operator evaluated on the repository's local extensions. -/
def curvatureValue (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
    (x : M) (u w a : E) : E :=
  letI := inst
  CovariantDerivative.curvatureOp g.leviCivita
    (FiberBundle.extend E (x := x) u) (FiberBundle.extend E (x := x) w)
    (FiberBundle.extend E (x := x) a) x

/-- Remaining differential naturality identities. The first is required only
on differentiable sections, as in Levi-Civita uniqueness. The second compares
the actual curvature tensors, independently of any constant-curvature premise.
Neither identity is proved by the tangent-section regularity results above. -/
def ConnectionCurvatureNaturality (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) : Prop :=
  let R := curvatureValue (inst := inst) g
  let cov := conjugatedDerivative (inst := inst) inst' h g
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  let g' := transport (inst := inst) inst' h g
  (∀ (X : M → E) (x : M), MDiffAtTangentField X x → cov X x = g'.leviCivita X x) ∧
    (∀ (x : M) (u w a : E),
      J (inst := inst) inst' h x (curvatureValue g' x u w a) =
        R x (J (inst := inst) inst' h x u) (J (inst := inst) inst' h x w)
          (J (inst := inst) inst' h x a))

/-- Differential naturality suffices to bundle the raw conjugated operator. -/
theorem conjugatedDerivative_isCovariantDerivativeOn
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
    (hN : ConnectionCurvatureNaturality (inst := inst) inst' h g) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    IsCovariantDerivativeOn («I» := I) (V := TangentSpace I) E (conjugatedDerivative (inst := inst) inst' h g) univ := by
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  let g' := transport (inst := inst) inst' h g
  have he := hN.1
  constructor
  · intro X Y x hX hY _
    rw [he (X + Y) x (mdifferentiableAt_add_section hX hY), he X x hX, he Y x hY]
    exact g'.leviCivita.isCovariantDerivativeOnUniv.add hX hY
  · intro X f x hX hf _
    rw [he (f • X) x (hf.smul_section hX), he X x hX]
    exact g'.leviCivita.isCovariantDerivativeOnUniv.leibniz hX hf

/-- The conjugated connection, conditional on the differential naturality boundary. -/
def conjugatedConnection (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
    (hN : ConnectionCurvatureNaturality (inst := inst) inst' h g) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    CovariantDerivative I E (TangentSpace I : M → Type _) := by
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  exact ⟨conjugatedDerivative (inst := inst) inst' h g,
    conjugatedDerivative_isCovariantDerivativeOn (inst := inst) inst' h g hN⟩

/-- The conditional conjugated connection is metric compatible and torsion free. -/
theorem conjugatedConnection_metricCompatible_torsion
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
    (hN : ConnectionCurvatureNaturality (inst := inst) inst' h g) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    IsMetricCompatible (transport (inst := inst) inst' h g)
        (conjugatedConnection (inst := inst) inst' h g hN) ∧
      (conjugatedConnection (inst := inst) inst' h g hN).torsion = 0 := by
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  let g' := transport (inst := inst) inst' h g
  have he : ∀ (X : M → E) (x : M), MDiffAtTangentField X x →
      conjugatedConnection (inst := inst) inst' h g hN X x = g'.leviCivita X x := hN.1
  constructor
  · intro x X Y hX hY v
    rw [he X x hX, he Y x hY]
    exact g'.leviCivita_metricCompatible hX hY v
  · rw [CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x hX hY
    rw [he Y x hY, he X x hX]
    exact (CovariantDerivative.torsion_eq_zero_iff _).1 g'.leviCivita_torsion hX hY

end Connection
end Poincare.CurvatureInstanceTransport
