import Mathlib.Topology.MetricSpace.ProperSpace
import Poincare.Global.MetricEntryThirdJetFormalInvertibility
import Poincare.Global.MetricEntryThirdJetProfileLimitAlgebra

/-!
# Positive lower bounds on compact fixed-chart sets

A genuine cutoff-blended metric is positive definite at every model-space
point.  On a compact coordinate set, continuity and compactness of the unit
sphere turn that pointwise fact into one positive Euclidean quadratic-form
lower bound.  This is the fixed-chart nondegeneration input used by the formal
profile closure.
-/

noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [Nontrivial (ClosedSmoothModel n)]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M

omit [Nontrivial E] in
/-- An intrinsic lower comparison with a reference metric passes to the two
cutoff-blended metrics in every fixed anchor.  Truncating the factor at one
keeps the shared Euclidean background term monotone. -/
theorem anchorBlendedMetricFamily_lower_of_closedMetricLowerComparison
    {J : Type*} (gref : G) (gt : J → G) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref gt c)
    (x : M) (t : J) (z w : E) :
    min c 1 *
        anchorBlendedMetricFamily (fun _ : Unit => gref) x () z w w ≤
      anchorBlendedMetricFamily gt x t z w w := by
  let c₀ : ℝ := min c 1
  let χ : ℝ := GeodesicTransport.cutoff (n := n) x z
  let G₀ : E →L[ℝ] E →L[ℝ] ℝ :=
    GeodesicTransport.backgroundMetric (n := n)
  let A := mfderivWithin 𝓘(ℝ, E) (closedSmoothModelWithCorners n)
    ((extChartAt (closedSmoothModelWithCorners n) x).symm)
    (Set.range (closedSmoothModelWithCorners n)) z w
  have hc₀c : c₀ ≤ c := min_le_left c 1
  have hc₀one : c₀ ≤ 1 := min_le_right c 1
  have hrefNonneg : 0 ≤ gref.inner
      ((extChartAt (closedSmoothModelWithCorners n) x).symm z) A A :=
    gref.inner_nonneg _ _
  have hchart : c₀ *
      CovariantDerivative.chartMetric gref.inner x z w w ≤
      CovariantDerivative.chartMetric (gt t).inner x z w w := by
    rw [CovariantDerivative.chartMetric_apply,
      CovariantDerivative.chartMetric_apply]
    exact (mul_le_mul_of_nonneg_right hc₀c hrefNonneg).trans
      (hLower.2 t _ A)
  have hbackground : 0 ≤ G₀ w w := by
    dsimp [G₀, GeodesicTransport.backgroundMetric]
    change 0 ≤ inner ℝ w w
    exact real_inner_self_nonneg
  have hχnonneg : 0 ≤ χ :=
    GeodesicTransport.cutoff_nonneg (n := n) x z
  have hχle : χ ≤ 1 :=
    GeodesicTransport.cutoff_le_one (n := n) x z
  have hchartWeighted : χ *
      (c₀ * CovariantDerivative.chartMetric gref.inner x z w w) ≤
      χ * CovariantDerivative.chartMetric (gt t).inner x z w w :=
    mul_le_mul_of_nonneg_left hchart hχnonneg
  have hbackgroundScaled : c₀ * (G₀ w w) ≤ G₀ w w := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc₀one hbackground
  have hbackgroundWeighted : (1 - χ) * (c₀ * (G₀ w w)) ≤
      (1 - χ) * (G₀ w w) :=
    mul_le_mul_of_nonneg_left hbackgroundScaled (sub_nonneg.mpr hχle)
  change c₀ *
      (χ * CovariantDerivative.chartMetric gref.inner x z w w +
        (1 - χ) * G₀ w w) ≤
    χ * CovariantDerivative.chartMetric (gt t).inner x z w w +
      (1 - χ) * G₀ w w
  nlinarith [hchartWeighted, hbackgroundWeighted]

/-- A single genuine metric has a uniform positive Euclidean lower bound on
every compact set in one fixed cutoff-blended chart. -/
theorem exists_uniformAnchorBlendedMetricLowerComparison_const
    (g : G) (x : M) {Q : Set E} (hQ : IsCompact Q) :
    ∃ c : ℝ,
      UniformAnchorBlendedMetricLowerComparison
        (fun _ : Unit => g) x Q c := by
  classical
  by_cases hQne : Q.Nonempty
  · let B : E → E →L[ℝ] E →L[ℝ] ℝ :=
      anchorBlendedMetricFamily (fun _ : Unit => g) x ()
    let F : E × E → ℝ := fun q => B q.1 q.2 q.2
    have hB : Continuous B :=
      (anchorBlendedMetricFamily_contDiff_four
        (fun _ : Unit => g) x ()).continuous
    have hF : Continuous F := by
      exact ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply
        continuous_snd
    have hSphereCompact : IsCompact (Metric.sphere (0 : E) 1) :=
      isCompact_sphere 0 1
    have hSphereNonempty : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr (by norm_num)
    obtain ⟨q, hq, hqmin⟩ :=
      (hQ.prod hSphereCompact).exists_isMinOn
        (hQne.prod hSphereNonempty) hF.continuousOn
    have hqnorm : ‖q.2‖ = 1 := by
      simpa [Metric.mem_sphere] using hq.2
    have hqzero : q.2 ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hqnorm
      norm_num at hqnorm
    have hqpos : 0 < F q := by
      exact anchorBlendedMetricFamily_pos
        (fun _ : Unit => g) x () q.1 hqzero
    refine ⟨F q, hqpos, ?_⟩
    intro _t z hz w
    by_cases hw : w = 0
    · subst w
      simp
    · let normalized : E := ‖w‖⁻¹ • w
      have hwnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      have hnormalizedNorm : ‖normalized‖ = 1 := by
        simp [normalized, norm_smul, hwnorm]
      have hnormalizedSphere : normalized ∈ Metric.sphere (0 : E) 1 := by
        simpa [Metric.mem_sphere] using hnormalizedNorm
      have hpair : (z, normalized) ∈
          Q ×ˢ Metric.sphere (0 : E) 1 :=
        ⟨hz, hnormalizedSphere⟩
      have hmin := hqmin hpair
      change F q ≤ B z normalized normalized at hmin
      have hreconstruct : ‖w‖ • normalized = w := by
        simp [normalized, smul_smul, hwnorm]
      calc
        F q * ‖w‖ ^ 2 ≤ B z normalized normalized * ‖w‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖w‖)
        _ = B z (‖w‖ • normalized) (‖w‖ • normalized) := by
          simp [map_smul, smul_eq_mul]
          ring
        _ = B z w w := by rw [hreconstruct]
        _ = anchorBlendedMetricFamily
            (fun _ : Unit => g) x () z w w := rfl
  · refine ⟨1, zero_lt_one, ?_⟩
    intro _t z hz _w
    exact False.elim (hQne ⟨z, hz⟩)

/-- A uniform intrinsic lower comparison with one reference metric yields a
uniform Euclidean lower comparison for the whole family on every compact
fixed-chart coordinate set. -/
theorem exists_uniformAnchorBlendedMetricLowerComparison_of_closedMetricLowerComparison
    {J : Type*} (gref : G) (gt : J → G) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref gt c)
    (x : M) {Q : Set E} (hQ : IsCompact Q) :
    ∃ d : ℝ, UniformAnchorBlendedMetricLowerComparison gt x Q d := by
  obtain ⟨dref, hdref⟩ :=
    exists_uniformAnchorBlendedMetricLowerComparison_const gref x hQ
  have hcpos : 0 < min c 1 := lt_min hLower.1 zero_lt_one
  refine ⟨min c 1 * dref, mul_pos hcpos hdref.1, ?_⟩
  intro t z hz w
  calc
    (min c 1 * dref) * ‖w‖ ^ 2 =
        min c 1 * (dref * ‖w‖ ^ 2) := by ring
    _ ≤ min c 1 *
        anchorBlendedMetricFamily (fun _ : Unit => gref) x () z w w :=
      mul_le_mul_of_nonneg_left (hdref.2 () z hz w) hcpos.le
    _ ≤ anchorBlendedMetricFamily gt x t z w w :=
      anchorBlendedMetricFamily_lower_of_closedMetricLowerComparison
        gref gt c hLower x t z w

end Poincare
