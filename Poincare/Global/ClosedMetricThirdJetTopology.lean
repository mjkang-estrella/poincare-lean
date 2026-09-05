import Mathlib.Topology.CompactOpen
import Poincare.Global.MetricFamilyEntryThirdJetCovRicciContinuity

/-!
# A compact-open scalar third-jet topology for closed metrics

This module equips `ClosedSmoothRiemannianMetric n M` with an explicit
topology induced by all scalar components of the cutoff-blended metric and
its first three spatial derivatives.  Each component is a continuous map on
the model space, and its codomain carries the compact-open topology.

The topology is used only through local instances.  It records convergence
of the tagged scalar jets on compact subsets of the model space.  It does not
make an arbitrary set or family of closed metrics compact; compactness still
has to be proved separately.
-/

noncomputable section

open Bundle Filter Function
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M

/-- A tag for one scalar component of a cutoff-blended metric's spatial jets
through order three.  The manifold point fixes the blended chart anchor; the
remaining vectors select one scalar component. -/
inductive MetricEntryThirdJetSlot (n : ℕ) (M : Type u)
  | value (x : M) (i j : ClosedSmoothModel n)
  | first (x : M) (u i j : ClosedSmoothModel n)
  | second (x : M) (u a i j : ClosedSmoothModel n)
  | third (x : M) (u a b i j : ClosedSmoothModel n)

/-- Product of compact-open continuous-map spaces containing every tagged
scalar cutoff-blended metric jet through order three. -/
abbrev MetricEntryThirdJetProfileTarget (n : ℕ) (M : Type u) :=
  MetricEntryThirdJetSlot n M → C(ClosedSmoothModel n, ℝ)

private noncomputable def metricEntryThirdJetValueMap
    (g : G) (x : M) (i j : E) : C(E, ℝ) where
  toFun z := anchorBlendedMetricFamily (fun h : G ↦ h) x g z i j
  continuous_toFun := by
    exact (((anchorBlendedMetricFamily_contDiff_four
      (fun h : G ↦ h) x g).clm_apply contDiff_const).clm_apply
        contDiff_const).continuous

private noncomputable def metricEntryThirdJetFirstMap
    (g : G) (x : M) (u i j : E) : C(E, ℝ) where
  toFun z := fderiv ℝ
    (anchorBlendedMetricFamily (fun h : G ↦ h) x g) z u i j
  continuous_toFun := by
    let A := anchorBlendedMetricFamily (fun h : G ↦ h) x g
    have hA : ContDiff ℝ 4 A :=
      anchorBlendedMetricFamily_contDiff_four (fun h : G ↦ h) x g
    have hD : ContDiff ℝ 3 (fun z ↦ fderiv ℝ A z u) := by
      simpa [A] using (hA.contDiff_fderiv_apply (m := 3) (by norm_num)).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 3 (fun _ : E ↦ u)))
    exact ((hD.clm_apply contDiff_const).clm_apply contDiff_const).continuous

private noncomputable def metricEntryThirdJetSecondMap
    (g : G) (x : M) (u a i j : E) : C(E, ℝ) where
  toFun z := fderiv ℝ
    (fun y ↦ fderiv ℝ
      (anchorBlendedMetricFamily (fun h : G ↦ h) x g) y u) z a i j
  continuous_toFun := by
    let A := anchorBlendedMetricFamily (fun h : G ↦ h) x g
    have hA : ContDiff ℝ 4 A :=
      anchorBlendedMetricFamily_contDiff_four (fun h : G ↦ h) x g
    have hD₁ : ContDiff ℝ 3 (fun z ↦ fderiv ℝ A z u) := by
      simpa [A] using (hA.contDiff_fderiv_apply (m := 3) (by norm_num)).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 3 (fun _ : E ↦ u)))
    have hD₂ : ContDiff ℝ 2
        (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ A y u) z a) := by
      simpa [A] using (hD₁.contDiff_fderiv_apply (m := 2) (by norm_num)).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 2 (fun _ : E ↦ a)))
    exact ((hD₂.clm_apply contDiff_const).clm_apply contDiff_const).continuous

private noncomputable def metricEntryThirdJetThirdMap
    (g : G) (x : M) (u a b i j : E) : C(E, ℝ) where
  toFun z := fderiv ℝ
    (fun y ↦ fderiv ℝ
      (fun w ↦ fderiv ℝ
        (anchorBlendedMetricFamily (fun h : G ↦ h) x g) w u) y a) z b i j
  continuous_toFun := by
    let A := anchorBlendedMetricFamily (fun h : G ↦ h) x g
    have hA : ContDiff ℝ 4 A :=
      anchorBlendedMetricFamily_contDiff_four (fun h : G ↦ h) x g
    have hD₁ : ContDiff ℝ 3 (fun z ↦ fderiv ℝ A z u) := by
      simpa [A] using (hA.contDiff_fderiv_apply (m := 3) (by norm_num)).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 3 (fun _ : E ↦ u)))
    have hD₂ : ContDiff ℝ 2
        (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ A y u) z a) := by
      simpa [A] using (hD₁.contDiff_fderiv_apply (m := 2) (by norm_num)).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 2 (fun _ : E ↦ a)))
    have hD₃ : ContDiff ℝ 1
        (fun z ↦ fderiv ℝ
          (fun y ↦ fderiv ℝ (fun w ↦ fderiv ℝ A w u) y a) z b) := by
      simpa [A] using (hD₂.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 1 (fun _ : E ↦ b)))
    exact ((hD₃.clm_apply contDiff_const).clm_apply contDiff_const).continuous

/-- The profile of all scalar cutoff-blended metric entries and their first
three spatial derivatives, each regarded as a continuous function of the
model-space coordinate. -/
noncomputable def metricEntryThirdJetProfile (g : G) :
    MetricEntryThirdJetProfileTarget n M
  | .value x i j => metricEntryThirdJetValueMap g x i j
  | .first x u i j => metricEntryThirdJetFirstMap g x u i j
  | .second x u a i j => metricEntryThirdJetSecondMap g x u a i j
  | .third x u a b i j => metricEntryThirdJetThirdMap g x u a b i j

/-- The value slot at its own chart center recovers the intrinsic metric
pairing.  This makes the profile faithful already at order zero. -/
theorem metricEntryThirdJetProfile_value_anchor
    (g : G) (x : M) (i j : E) :
    metricEntryThirdJetProfile g (.value x i j)
        (extChartAt (closedSmoothModelWithCorners n) x x) =
      g.inner x i j := by
  have hblend :=
    (anchorBlendedMetricFlow_eventuallyEq_anchorChartMetricFlow
      (fun _ : ℝ ↦ g) 0 x).self_of_nhds
  have hchart := CovariantDerivative.chartMetric_apply_chart
    g.inner x (mem_extChartAt_source x) i j
  rw [mfderiv_extChartAt_self] at hchart
  change anchorBlendedMetricFlow (fun _ : ℝ ↦ g) x 0
      (extChartAt (closedSmoothModelWithCorners n) x x) i j = _
  calc
    _ = anchorChartMetricFlow (fun _ : ℝ ↦ g) x 0
        (extChartAt (closedSmoothModelWithCorners n) x x) i j :=
      congrArg (fun A ↦ A i j) hblend
    _ = g.inner x i j := by
      simpa [anchorChartMetricFlow] using hchart

/-- Distinct closed smooth metrics have distinct scalar third-jet profiles.
The proof uses only the value slots at their chart centers. -/
theorem metricEntryThirdJetProfile_injective :
    Function.Injective
      (metricEntryThirdJetProfile (n := n) (M := M)) := by
  intro g h hprofile
  have hinner : g.inner = h.inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro i
    apply ContinuousLinearMap.ext
    intro j
    have hp := congrArg
      (fun f : C(E, ℝ) ↦
        f (extChartAt (closedSmoothModelWithCorners n) x x))
      (congrFun hprofile (.value x i j))
    simpa only [metricEntryThirdJetProfile_value_anchor] using hp
  cases g with
  | mk ginner gsymm gpos gbdd gsmooth =>
      cases h with
      | mk hinner' hsymm hpos hbdd hsmooth =>
          dsimp only at hinner
          cases hinner
          rfl

/-- Full joint continuity of every scalar profile slot on `K × E`.
This is stronger than continuity only at a parameter and the corresponding
chart center used by `MetricFamilyBlendedMetricEntryThirdJetContinuousAt`. -/
def MetricFamilyEntryThirdJetProfileJointContinuous
    {K : Type v} [TopologicalSpace K] (metric : K → G) : Prop :=
  ∀ slot : MetricEntryThirdJetSlot n M,
    Continuous (fun p : K × E ↦
      metricEntryThirdJetProfile (metric p.1) slot p.2)

/-- The topology on closed smooth metrics induced by the complete scalar
third-jet profile.  This definition is reducible so callers can install it as
a local instance without creating a competing global metric topology. -/
@[reducible] noncomputable def closedSmoothRiemannianMetricEntryThirdJetTopology :
    TopologicalSpace G :=
  TopologicalSpace.induced (metricEntryThirdJetProfile (n := n) (M := M))
    inferInstance

section EntryThirdJetTopology

local instance : TopologicalSpace G :=
  closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)

private theorem metricEntryThirdJetProfile_continuous :
    Continuous (metricEntryThirdJetProfile (n := n) (M := M)) :=
  continuous_induced_dom

/-- The scalar third-jet profile is a topological embedding for the locally
installed induced topology. -/
theorem metricEntryThirdJetProfile_isEmbedding :
    Topology.IsEmbedding
      (metricEntryThirdJetProfile (n := n) (M := M)) :=
  metricEntryThirdJetProfile_injective.isEmbedding_induced

/-- Joint continuity of every complete scalar profile slot makes a metric
family continuous into the explicit scalar third-jet topology.  The premise
is global on `K × E`, not merely local at each chart center. -/
theorem continuous_closedMetricFamily_of_entryThirdJetProfileJointContinuous
    {K : Type v} [TopologicalSpace K] {metric : K → G}
    (hmetric : MetricFamilyEntryThirdJetProfileJointContinuous metric) :
    Continuous metric := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro slot
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa only [Function.uncurry_apply_pair, Function.comp_apply] using
    hmetric slot

private theorem metricEntryThirdJetProfile_component_continuous
    (s : MetricEntryThirdJetSlot n M) :
    Continuous (fun g : G ↦ metricEntryThirdJetProfile g s) :=
  (continuous_apply s).comp metricEntryThirdJetProfile_continuous

/-- A family continuous into the scalar third-jet topology has jointly
continuous cutoff-blended metric entries and spatial derivatives through
order three at every parameter and manifold anchor. -/
theorem metricFamilyBlendedMetricEntryThirdJetContinuousAt_of_continuous
    {K : Type v} [TopologicalSpace K] {g : K → G}
    (hg : Continuous g) (k₀ : K) (x : M) :
    MetricFamilyBlendedMetricEntryThirdJetContinuousAt g k₀ x := by
  refine
    { value := ?_
      firstSpatial := ?_
      secondSpatial := ?_
      thirdSpatial := ?_ }
  · intro i j
    have h :=
      (metricEntryThirdJetProfile_component_continuous (.value x i j)).comp hg
    simpa [metricEntryThirdJetProfile, metricEntryThirdJetValueMap] using
      ((h.comp continuous_fst).eval continuous_snd).continuousAt
  · intro u i j
    have h :=
      (metricEntryThirdJetProfile_component_continuous (.first x u i j)).comp hg
    simpa [metricEntryThirdJetProfile, metricEntryThirdJetFirstMap] using
      ((h.comp continuous_fst).eval continuous_snd).continuousAt
  · intro u a i j
    have h :=
      (metricEntryThirdJetProfile_component_continuous (.second x u a i j)).comp hg
    simpa [metricEntryThirdJetProfile, metricEntryThirdJetSecondMap] using
      ((h.comp continuous_fst).eval continuous_snd).continuousAt
  · intro u a b i j
    have h :=
      (metricEntryThirdJetProfile_component_continuous (.third x u a b i j)).comp hg
    simpa [metricEntryThirdJetProfile, metricEntryThirdJetThirdMap] using
      ((h.comp continuous_fst).eval continuous_snd).continuousAt

/-- The identity family has scalar cutoff-blended third-jet continuity for
the explicit scalar third-jet topology. -/
theorem metricFamilyBlendedMetricEntryThirdJetContinuousAt_identity
    (g₀ : G) (x : M) :
    MetricFamilyBlendedMetricEntryThirdJetContinuousAt
      (fun g : G ↦ g) g₀ x :=
  metricFamilyBlendedMetricEntryThirdJetContinuousAt_of_continuous
    continuous_id g₀ x

/-- Inclusion of any subtype of closed metrics has scalar cutoff-blended
third-jet continuity for the induced subtype topology.  No compactness of
the subtype is asserted. -/
theorem metricFamilyBlendedMetricEntryThirdJetContinuousAt_subtype
    (s : Set G) (g₀ : s) (x : M) :
    MetricFamilyBlendedMetricEntryThirdJetContinuousAt
      (fun g : s ↦ (g : G)) g₀ x :=
  metricFamilyBlendedMetricEntryThirdJetContinuousAt_of_continuous
    continuous_subtype_val g₀ x

end EntryThirdJetTopology

end Poincare
