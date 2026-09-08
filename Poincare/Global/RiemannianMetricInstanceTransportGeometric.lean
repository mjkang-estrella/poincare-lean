import Poincare.Global.RiemannianMetricInstanceTransport
import Poincare.Global.ControlledChartInstance

/-!
# Geometric metric transport between compatible preferred charts

Every comparison of tangent fibers uses the derivative from the new preferred
chart to the old preferred chart. A common maximal atlas supplies the cocycle
law even when the two preferred-chart selections are unrelated.
-/

noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.RiemannianMetricInstanceTransportGeometric
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M]

/-- Enlarge only the atlas, keeping the original preferred charts. -/
@[implicit_reducible]
def commonCharts : ChartedSpace E M where
  atlas := IsManifold.maximalAtlas I ∞ M
  chartAt := inst.chartAt
  mem_chart_source := inst.mem_chart_source
  chart_mem_atlas := IsManifold.chart_mem_maximalAtlas

instance commonCharts_isManifold :
    (letI := commonCharts (inst := inst); IsManifold I ∞ M) :=
  (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) commonCharts (Subset.refl _)).1

/-- Derivative of a transition between any two charts in the common atlas. -/
def D (i j : IsManifold.maximalAtlas I ∞ M) (x : M) : E →L[ℝ] E :=
  letI := commonCharts (inst := inst)
  (tangentBundleCore I M).coordChange i j x

theorem D_comp (i j k : IsManifold.maximalAtlas I ∞ M) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (hk : x ∈ k.1.source) (v : E) :
    D j k x (D i j x v) = D i k x v := by
  letI := commonCharts (inst := inst)
  exact (tangentBundleCore I M).coordChange_comp i j k x ⟨⟨hi, hj⟩, hk⟩ v

theorem D_self (i : IsManifold.maximalAtlas I ∞ M) (x : M)
    (hi : x ∈ i.1.source) (v : E) : D i i x v = v := by
  letI := commonCharts (inst := inst)
  exact (tangentBundleCore I M).coordChange_self i x hi v

/-- The original preferred chart as a member of the common atlas. -/
def oldChart (x : M) : IsManifold.maximalAtlas I ∞ M :=
  ⟨inst.chartAt x, IsManifold.chart_mem_maximalAtlas x⟩

local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

/-- Pull back a bilinear form in both arguments by a continuous linear map. -/
def pull (b : Bilin) (L : E →L[ℝ] E) : Bilin :=
  (L.precomp ℝ).comp (b.comp L)

/-- Coefficients of a bilinear-form section for an explicitly selected atlas. -/
def coefficients (charts : ChartedSpace E M)
    (hs : letI := charts; IsManifold I ∞ M) (s : M → Bilin) (a x : M) : Bilin :=
  letI := charts
  letI : IsManifold I ∞ M := hs
  (trivializationAt Bilin
    (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) a ⟨x, s x⟩).2

set_option backward.isDefEq.respectTransparency false in
/-- The hom-bundle coefficient formula holds for any bilinear section. -/
theorem coefficients_apply (s : M → Bilin) {a x : M}
    (hx : x ∈ (inst.chartAt a).source) (v w : E) :
    coefficients inst inferInstance s a x v w =
      s x (D (oldChart a) (oldChart x) x v) (D (oldChart a) (oldChart x) x w) := by
  unfold coefficients
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem]
  · rw [hom_trivializationAt_apply]
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [TangentBundle.symmL_trivializationAt_eq_core hx]
    simp [D, tangentBundleCore_coordChange, oldChart, mfld_simps]
    rfl
  · simpa using hx

/-- In the boundaryless model the common-core transition is an ordinary derivative. -/
theorem D_eq_fderiv (i j : IsManifold.maximalAtlas I ∞ M) (x : M) :
    D i j x = fderiv ℝ (j.1 ∘ i.1.symm) (i.1 x) := by
  simp only [D, tangentBundleCore_coordChange, OpenPartialHomeomorph.extend,
    mfld_simps, fderivWithin_univ]

/-- A transition derivative between fixed smooth charts is smooth on their overlap. -/
theorem contMDiffAt_D (i j : IsManifold.maximalAtlas I ∞ M) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (D i j) x := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (j.1 ∘ i.1.symm))
      (i.1.symm.trans j.1).source := by
    letI := commonCharts (inst := inst)
    haveI : IsManifold I (∞ + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    have hd := contDiffOn_fderiv_coord_change («I» := I) (n := ∞) i j
    simpa only [OpenPartialHomeomorph.extend, mfld_simps, fderivWithin_univ] using hd
  have hx : i.1 x ∈ (i.1.symm.trans j.1).source :=
    ⟨i.1.map_source hi, by
      change i.1.symm (i.1 x) ∈ j.1.source
      simpa only [i.1.left_inv hi] using hj⟩
  have hderiv := (hd.contDiffAt ((i.1.symm.trans j.1).open_source.mem_nhds hx)).contMDiffAt
  have hchart := contMDiffAt_of_mem_maximalAtlas i.2 hi
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ D i j y) x
  simp_rw [D_eq_fderiv]
  exact hderiv.comp x hchart

omit [IsManifold I ∞ M] in
/-- Pullback of bilinear forms by a smooth family of linear maps is smooth. -/
theorem contMDiffAt_pull {b : M → Bilin} {L : M → E →L[ℝ] E} {x : M}
    (hb : ContMDiffAt I 𝓘(ℝ, Bilin) ∞ b x)
    (hL : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ L x) :
    ContMDiffAt I 𝓘(ℝ, Bilin) ∞ (fun y ↦ pull (b y) (L y)) x :=
  (hL.clm_precomp (F₃ := ℝ)).clm_comp (hb.clm_comp hL)

/-- Smoothness of a tensor section with its bundle atlas specified explicitly. -/
def sectionContMDiff (charts : ChartedSpace E M)
    (hs : letI := charts; IsManifold I ∞ M) (s : M → Bilin) : Prop :=
  letI := charts
  letI : IsManifold I ∞ M := hs
  ContMDiff I ((I).prod 𝓘(ℝ, Bilin)) ∞
    (fun x : M ↦ (⟨x, s x⟩ : TotalSpace Bilin
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)))

/-- Smoothness of tensor sections is detected by the preferred trivializations. -/
theorem sectionContMDiff_iff (s : M → Bilin) :
    sectionContMDiff inst inferInstance s ↔
      ∀ a, ContMDiffAt I 𝓘(ℝ, Bilin) ∞ (coefficients inst inferInstance s a) a := by
  exact forall_congr' fun a ↦ Bundle.contMDiffAt_section
    (IB := I) (F := Bilin)
    («E» := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (s := s) a

/-- Tangent coordinates with the bundle instance specified explicitly. -/
def tangentCoordinates (charts : ChartedSpace E M)
    (hs : letI := charts; IsManifold I ∞ M) (a x : M) (v : E) : E :=
  letI := charts
  letI : IsManifold I ∞ M := hs
  (trivializationAt E (TangentSpace I) a ⟨x, v⟩).2

variable (inst' : ChartedSpace E M)
  (h : inst'.atlas ⊆ @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I))

/-- The new preferred chart as a member of the original maximal atlas. -/
def newChart (x : M) : @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I) :=
  ⟨inst'.chartAt x, h (inst'.chart_mem_atlas x)⟩

/-- The geometric identification from new tangent coordinates to old ones. -/
def J (x : M) : E ≃L[ℝ] E :=
  { D (inst := inst) (newChart (inst := inst) inst' h x) (oldChart (inst := inst) x) x with
    invFun := D (inst := inst) (oldChart (inst := inst) x) (newChart (inst := inst) inst' h x) x
    left_inv := fun v ↦ by
      change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = v
      rw [D_comp (inst := inst) _ _ _ x (inst'.mem_chart_source x) (inst.mem_chart_source x)
        (inst'.mem_chart_source x), D_self (inst := inst) _ x (inst'.mem_chart_source x)]
    right_inv := fun v ↦ by
      change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = v
      rw [D_comp (inst := inst) _ _ _ x (inst.mem_chart_source x) (inst'.mem_chart_source x)
        (inst.mem_chart_source x), D_self (inst := inst) _ x (inst.mem_chart_source x)] }

/-- The identification is exactly the ordinary derivative of the chart transition. -/
theorem J_apply (x : M) (v : E) :
    J (inst := inst) inst' h x v =
      fderiv ℝ (inst.chartAt x ∘ (inst'.chartAt x).symm) (inst'.chartAt x x) v := by
  change fderivWithin ℝ _ _ _ v = _
  simp only [OpenPartialHomeomorph.extend, mfld_simps, fderivWithin_univ]
  rfl

/-- Inverse tangent trivializations intertwine through the fixed-anchor transition. -/
theorem J_inverse_trivialization (a x : M)
    (ha : x ∈ (inst.chartAt a).source) (ha' : x ∈ (inst'.chartAt a).source) (v : E) :
    J (inst := inst) inst' h x (D (inst := inst) (newChart (inst := inst) inst' h a) (newChart (inst := inst) inst' h x) x v) =
      D (inst := inst) (oldChart (inst := inst) a) (oldChart (inst := inst) x) x
        (D (inst := inst) (newChart (inst := inst) inst' h a) (oldChart (inst := inst) a) x v) := by
  change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = D (inst := inst) _ _ x (D (inst := inst) _ _ x v)
  rw [D_comp (inst := inst) _ _ _ x ha' (inst'.mem_chart_source x) (inst.mem_chart_source x),
    D_comp (inst := inst) _ _ _ x ha' ha (inst.mem_chart_source x)]

/-- Forward tangent trivializations satisfy the same change-of-anchor law. -/
theorem J_trivialization (a x : M)
    (ha : x ∈ (inst.chartAt a).source) (ha' : x ∈ (inst'.chartAt a).source) (v : E) :
    D (inst := inst) (oldChart (inst := inst) x) (oldChart (inst := inst) a) x (J (inst := inst) inst' h x v) =
      D (inst := inst) (newChart (inst := inst) inst' h a) (oldChart (inst := inst) a) x
        (D (inst := inst) (newChart (inst := inst) inst' h x) (newChart (inst := inst) inst' h a) x v) := by
  change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = D (inst := inst) _ _ x (D (inst := inst) _ _ x v)
  rw [D_comp (inst := inst) _ _ _ x (inst'.mem_chart_source x) (inst.mem_chart_source x) ha,
    D_comp (inst := inst) _ _ _ x (inst'.mem_chart_source x) ha' ha]

/-- The candidate transported metric tensor, with no smoothness assumption. -/
def transportedInner (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (x : M) : Bilin :=
  letI := inst
  pull (g.inner x) (J (inst := inst) inst' h x).toContinuousLinearMap

/-- Hom-bundle coefficients transform by the smooth fixed-anchor transition. -/
theorem coefficients_transportedInner
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (a x : M)
    (ha : x ∈ (inst.chartAt a).source) (ha' : x ∈ (inst'.chartAt a).source) :
    letI := inst
    coefficients inst'
        (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
        (transportedInner (inst := inst) inst' h g) a x =
      pull (coefficients inst inferInstance g.inner a x)
        (D (inst := inst) (newChart (inst := inst) inst' h a)
          (oldChart (inst := inst) a) x) := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  ext v w
  have hnew := @coefficients_apply M _ inst' hs
    (transportedInner (inst := inst) inst' h g) a x ha' v w
  rw [hnew]
  change g.inner x (J (inst := inst) inst' h x
      (D (inst := inst) (newChart (inst := inst) inst' h a)
        (newChart (inst := inst) inst' h x) x v))
    (J (inst := inst) inst' h x
      (D (inst := inst) (newChart (inst := inst) inst' h a)
        (newChart (inst := inst) inst' h x) x w)) = _
  rw [J_inverse_trivialization inst' h a x ha ha',
    J_inverse_trivialization inst' h a x ha ha']
  exact (coefficients_apply (inst := inst) g.inner ha _ _).symm

include h in
/-- Source chart independence for maps into a normed vector space. -/
theorem modelContMDiffAt_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (x : M) :
    (letI := inst; ContMDiffAt I 𝓘(ℝ, F) ∞ f x) ↔
      (letI := inst'; ContMDiffAt I 𝓘(ℝ, F) ∞ f x) := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  let e := inst'.chartAt x
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := h (inst'.chart_mem_atlas x)
  have hx : x ∈ e.source := inst'.mem_chart_source x
  have hold := contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    (I' := 𝓘(ℝ, F)) (f := f) (s := univ) he hx
  letI := inst'
  letI : IsManifold I ∞ M := hs
  have he' : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hnew := contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    (I' := 𝓘(ℝ, F)) (f := f) (s := univ) he' hx
  exact hold.trans hnew.symm

/-- The geometrically pulled-back tensor is smooth for the new bundle instance. -/
theorem transportedInner_contMDiff (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    sectionContMDiff inst'
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
      (transportedInner (inst := inst) inst' h g) := by
  letI := inst
  have hs := (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) inst' h).1
  apply (@sectionContMDiff_iff M _ inst' hs _).2
  intro a
  apply (modelContMDiffAt_iff (inst := inst) inst' h _ a).1
  have hg := (sectionContMDiff_iff g.inner).1 g.contMDiff a
  have hD := contMDiffAt_D (newChart (inst := inst) inst' h a) (oldChart a) a
    (inst'.mem_chart_source a) (inst.mem_chart_source a)
  apply (contMDiffAt_pull hg hD).congr_of_eventuallyEq
  filter_upwards [(inst.chartAt a).open_source.mem_nhds (inst.mem_chart_source a),
    (inst'.chartAt a).open_source.mem_nhds (inst'.mem_chart_source a)] with x hx hx'
  exact coefficients_transportedInner inst' h g a x hx hx'

/-- Transport a smooth Riemannian metric using the geometric tangent identification. -/
def transport (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    @ClosedSmoothRiemannianMetric 3 M _ inst'
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1 := by
  letI := inst
  let b := transportedInner (inst := inst) inst' h g
  have hsymm : ∀ x v w, b x v w = b x w v :=
    fun x v w ↦ g.symm x (J inst' h x v) (J inst' h x w)
  have hpos : ∀ x v, v ≠ 0 → 0 < b x v v := by
    intro x v hv
    exact g.pos x (J inst' h x v) ((J inst' h x).map_ne_zero_iff.mpr hv)
  have hbounded : ∀ x, Bornology.IsVonNBounded ℝ {v | b x v v < 1} := by
    intro x
    apply ((g.isVonNBounded x).image (J inst' h x).symm.toContinuousLinearMap).subset
    intro v hv
    exact ⟨J inst' h x v, hv, (J inst' h x).symm_apply_apply v⟩
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  exact ⟨b, hsymm, hpos, hbounded, transportedInner_contMDiff (inst := inst) inst' h g⟩

/-- The transported inner product is the pullback by the new-to-old derivative. -/
theorem transport_inner (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
    (x : M) (v w : E) :
    letI := inst'
    letI : IsManifold I ∞ M :=
      (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
    (transport (inst := inst) inst' h g).inner x v w =
      (letI := inst; g.inner x (J inst' h x v) (J inst' h x w)) := by
  rfl

/-- The pointwise bridge stated with the actual tangent-bundle trivializations. -/
theorem tangentCoordinates_transport (a x : M)
    (ha : x ∈ (inst.chartAt a).source) (ha' : x ∈ (inst'.chartAt a).source) (v : E) :
    tangentCoordinates inst inferInstance a x (J (inst := inst) inst' h x v) =
      D (inst := inst) (newChart (inst := inst) inst' h a) (oldChart (inst := inst) a) x
        (tangentCoordinates inst'
          (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
          a x v) :=
  J_trivialization (inst := inst) inst' h a x ha ha' v

/-- Optional remaining distance comparison, stated using the actual induced metrics.
A proof must transport curve derivatives and lengths through `J`. -/
def InducedDistanceAgreement [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) : Prop :=
  letI := inst
  let d := g.toMetricSpace
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  let d' := (transport (inst := inst) inst' h g).toMetricSpace
  ∀ x y : M, @dist M d'.toDist x y = @dist M d.toDist x y

end Poincare.RiemannianMetricInstanceTransportGeometric
