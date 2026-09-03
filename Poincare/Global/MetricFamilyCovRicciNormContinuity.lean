import Poincare.Global.MetricFlowJointCovRicciNormContinuity

/-!
# Joint continuity of the covariant Ricci norm for metric families

This module packages a sufficient chartwise continuity interface for a family
of metrics over an arbitrary topological parameter space.  It does not derive
that interface from the real-time regularity hypotheses used for metric flows.
-/

noncomputable section

open Bundle Filter Function
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- An inverse-metric coefficient for a metric family, defined by viewing one
family member as a constant real-parameter flow. -/
noncomputable def anchorChartInverseMetricCoeffFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z : E) (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  anchorChartInverseMetricCoeffFlow (fun _ : ℝ ↦ g k) x 0 z i j

/-- The cutoff-blended chart metric for a metric family, obtained by viewing
one family member as a constant real-parameter flow. -/
noncomputable def anchorBlendedMetricFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M) :
    K → E → E →L[ℝ] E →L[ℝ] ℝ := fun k z ↦
  anchorBlendedMetricFlow (fun _ : ℝ ↦ g k) x 0 z

omit [T2Space M] in
/-- Every member of the cutoff-blended family is an invertible metric
operator. -/
theorem anchorBlendedMetricFamily_isInvertible
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z : E) :
    (anchorBlendedMetricFamily g x k z).IsInvertible := by
  exact anchorBlendedMetricFlow_isInvertible
    (fun _ : ℝ ↦ g k) x 0 z

omit [T2Space M] in
/-- Joint continuity of the blended metric operator supplies continuity of
every inverse-metric coefficient used by the family norm contraction. -/
theorem anchorChartInverseMetricCoeffFamily_continuousAt_of_blendedMetric
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartInverseMetricCoeffFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x) := by
  let q : E := extChartAt I x x
  let b := Module.finBasis ℝ E
  have hInvMap : ContinuousAt ContinuousLinearMap.inverse
      (anchorBlendedMetricFamily g x k₀ q) :=
    ((anchorBlendedMetricFamily_isInvertible g x k₀ q)
      |>.contDiffAt_map_inverse (n := 0)).continuousAt
  have hInv : ContinuousAt
      (fun p : K × E ↦
        (anchorBlendedMetricFamily g x p.1 p.2).inverse)
      (k₀, q) := by
    simpa [Function.comp_def, q] using hInvMap.comp_of_eq hG rfl
  have hcoordI : ContinuousAt
      (fun _ : K × E ↦
        LinearMap.toContinuousLinearMap (b.coord i))
      (k₀, q) := continuousAt_const
  have hraised := hInv.clm_apply hcoordI
  have hcoordJ : ContinuousAt
      (fun _ : K × E ↦
        LinearMap.toContinuousLinearMap (b.coord j))
      (k₀, q) := continuousAt_const
  simpa [anchorChartInverseMetricCoeffFamily,
    anchorBlendedMetricFamily, anchorChartInverseMetricCoeffFlow, b, q]
    using hcoordJ.clm_apply hraised

/-- A coordinate covariant-Ricci entry for a metric family, defined by viewing
one family member as a constant real-parameter flow. -/
noncomputable def anchorChartCovRicciEntryFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z a i j : E) : ℝ :=
  anchorChartCovRicciEntryFlow (fun _ : ℝ ↦ g k) x 0 z a i j

/-- The coordinate contraction representing the squared covariant Ricci norm
for a metric family. -/
noncomputable def anchorChartCovRicciNormSqFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z : E) : ℝ :=
  anchorChartCovRicciNormSqFlow (fun _ : ℝ ↦ g k) x 0 z

/-- A sufficient chartwise continuity interface for a metric family at one
parameter-space point and one manifold anchor. -/
structure MetricFamilyCovRicciChartContinuousAt
    {K : Type v} [TopologicalSpace K]
    (g : K → ClosedSmoothRiemannianMetric n M) (k₀ : K) (x : M) : Prop where
  inverseCoeff : ∀ i j : Fin (Module.finrank ℝ E),
    ContinuousAt
      (fun p : K × E ↦
        anchorChartInverseMetricCoeffFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x)
  covRicciEntry : ∀ a i j : E,
    ContinuousAt
      (fun p : K × E ↦
        anchorChartCovRicciEntryFamily g x p.1 p.2 a i j)
      (k₀, extChartAt I x x)

private theorem continuousAt_finset_sum_family
    {X ι : Type*} [TopologicalSpace X] {p : X}
    (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ r ∈ s, ContinuousAt (f r) p) :
    ContinuousAt (fun q ↦ ∑ r ∈ s, f r q) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℝ)) p)
  | @insert r s hr ih =>
      have hrCont : ContinuousAt (f r) p :=
        hf r (Finset.mem_insert_self r s)
      have hsCont : ContinuousAt (fun q ↦ ∑ k ∈ s, f k q) p :=
        ih (fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert hr] using hrCont.add hsCont

omit [T2Space M] in
/-- The chartwise coefficient interface makes the finite coordinate
contraction jointly continuous at the family-space anchor. -/
theorem anchorChartCovRicciNormSqFamily_continuousAt
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyCovRicciChartContinuousAt g k₀ x) :
    ContinuousAt
      (Function.uncurry (anchorChartCovRicciNormSqFamily g x))
      (k₀, extChartAt I x x) := by
  classical
  let e := Module.finBasis ℝ E
  unfold anchorChartCovRicciNormSqFamily anchorChartCovRicciNormSqFlow
  dsimp only
  apply continuousAt_finset_sum_family Finset.univ
  intro a _ha
  apply continuousAt_finset_sum_family Finset.univ
  intro i _hi
  apply continuousAt_finset_sum_family Finset.univ
  intro j _hj
  apply continuousAt_finset_sum_family Finset.univ
  intro b _hb
  apply continuousAt_finset_sum_family Finset.univ
  intro k _hk
  apply continuousAt_finset_sum_family Finset.univ
  intro l _hl
  have hab := h.inverseCoeff a b
  have hik := h.inverseCoeff i k
  have hjl := h.inverseCoeff j l
  have hbkl := h.covRicciEntry (e b) (e k) (e l)
  have haij := h.covRicciEntry (e a) (e i) (e j)
  simpa only [anchorChartInverseMetricCoeffFamily,
    anchorChartCovRicciEntryFamily, Function.uncurry] using
    ((((hab.mul hik).mul hjl).mul hbkl).mul haij)

/-- On the cutoff-one chart zone, the family coordinate contraction is the
intrinsic squared norm for the selected family member. -/
theorem anchorChartCovRicciNormSqFamily_eq_covRicciNormSqAt_zone
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M)
    (x : M) (k : K) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1) :
    anchorChartCovRicciNormSqFamily g x k z =
      covRicciNormSqAt (g k) ((extChartAt I x).symm z) := by
  simpa only [anchorChartCovRicciNormSqFamily] using
    anchorChartCovRicciNormSqFlow_eq_covRicciNormSqAt_zone
      (fun _ : ℝ ↦ g k) x 0 hz hχone

/-- The chartwise family interface transfers to joint continuity of the
intrinsic norm at one parameter-manifold point. -/
theorem continuousAt_covRicciNormSqAt_joint_of_chartContinuous
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M}
    {k₀ : K} {x : M}
    (h : MetricFamilyCovRicciChartContinuousAt g k₀ x) :
    ContinuousAt
      (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) (k₀, x) := by
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ nhds (extChartAt I x x) := by
    apply hopen.mem_nhds
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hchart :
      ContinuousAt (fun p : K × M ↦ extChartAt I x p.2) (k₀, x) :=
    ContinuousAt.comp'
      (f := fun p : K × M ↦ p.2)
      (g := fun y : M ↦ extChartAt I x y)
      (x := (k₀, x)) (continuousAt_extChartAt x) continuousAt_snd
  have hchartPair :
      ContinuousAt
        (fun p : K × M ↦ (p.1, extChartAt I x p.2)) (k₀, x) :=
    continuousAt_fst.prodMk hchart
  have hcoord :
      ContinuousAt
        (Function.uncurry (anchorChartCovRicciNormSqFamily g x))
        (k₀, extChartAt I x x) :=
    anchorChartCovRicciNormSqFamily_continuousAt h
  have hchartNorm :
      ContinuousAt
        (fun p : K × M ↦
          anchorChartCovRicciNormSqFamily g x p.1
            (extChartAt I x p.2))
        (k₀, x) :=
    ContinuousAt.comp'
      (f := fun p : K × M ↦ (p.1, extChartAt I x p.2))
      (g := Function.uncurry (anchorChartCovRicciNormSqFamily g x))
      (x := (k₀, x)) hcoord hchartPair
  have hsource :
      ∀ᶠ p : K × M in nhds (k₀, x),
        p.2 ∈ (extChartAt I x).source :=
    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
  have hone :
      ∀ᶠ p : K × M in nhds (k₀, x),
        extChartAt I x p.2 ∈ oneLocus :=
    hchart.eventually hone_mem
  have hEq :
      (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2)
        =ᶠ[nhds (k₀, x)]
      (fun p : K × M ↦
        anchorChartCovRicciNormSqFamily g x p.1
          (extChartAt I x p.2)) := by
    filter_upwards [hsource, hone] with p hpSource hpOne
    have hz : extChartAt I x p.2 ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hpSource
    have hχone :
        ∀ᶠ z' in nhds (extChartAt I x p.2),
          GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    symm
    calc
      anchorChartCovRicciNormSqFamily g x p.1
          (extChartAt I x p.2) =
          covRicciNormSqAt (g p.1)
            ((extChartAt I x).symm (extChartAt I x p.2)) :=
        anchorChartCovRicciNormSqFamily_eq_covRicciNormSqAt_zone
          g x p.1 hz hχone
      _ = covRicciNormSqAt (g p.1) p.2 := by
        rw [(extChartAt I x).left_inv hpSource]
  exact hchartNorm.congr_of_eventuallyEq hEq

/-- Chartwise continuity at every parameter-manifold point gives global joint
continuity of the intrinsic squared covariant Ricci norm. -/
theorem continuous_covRicciNormSqAt_joint_of_chartContinuous
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M}
    (h : ∀ k : K, ∀ x : M,
      MetricFamilyCovRicciChartContinuousAt g k x) :
    Continuous (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨k, x⟩
  exact continuousAt_covRicciNormSqAt_joint_of_chartContinuous (h k x)

end Poincare
