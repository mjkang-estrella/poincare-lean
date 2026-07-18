import Poincare.Global.GeodesicDependence
import Poincare.Global.RoundSphereCanonicalExponential

/-!
# Local anchor-independence of the generic round-sphere exponential

The fixed-time exponential map is chosen separately at every base point.  On
the round sphere those choices nevertheless have the same coordinate germ.
Indeed, the fixed-time package exposes a Picard--Lindelof chart trajectory on
a closed interval.  Two anchor packages start at the same chart state because
every anchor is the origin of its own stereographic chart, and their ODE
fields are literally equal because the round-sphere chart Christoffel field
is anchor-independent.  ODE uniqueness on a common subinterval therefore
identifies their endpoints.

The radii below are pairwise rather than uniform over all anchors.  This is
the strongest conclusion available from the current generic fixed-time API:
its independently chosen time and velocity radii have no continuity in the
anchor parameter.  In particular, this file does not identify the chosen
partial-homeomorphism source sets globally; it identifies the underlying map
germs at zero.
-/

noncomputable section

open Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace RoundSphereGenericExponentialAnchorIndependence

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/-- The chart-coordinate generic exponential maps at two round-sphere anchors
agree on a positive ball about zero. -/
theorem exists_pairwise_chart_expAt_eq_on_ball (p q : RoundSphere3) :
    ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
      extChartAt I p
          (GeodesicTransport.expAt roundSphereMetric3 p v) =
        extChartAt I q
          (GeodesicTransport.expAt roundSphereMetric3 q v) := by
  rcases
      GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc
        (g := roundSphereMetric3) p with
    ⟨τp, hτp, δp, hδp, εp, hεp, ap, αp, hαp, hexp_p⟩
  rcases
      GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc
        (g := roundSphereMetric3) q with
    ⟨τq, hτq, δq, hδq, εq, hεq, aq, αq, hαq, hexp_q⟩
  let T : ℝ := min (min τp τq) (min εp εq)
  let δ : ℝ := min δp δq
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min (lt_min hτp hτq) (lt_min hεp hεq)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδp hδq
  have hT_le_τp : T ≤ τp :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hT_le_τq : T ≤ τq :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hT_le_εp : T ≤ εp :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hT_le_εq : T ≤ εq :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨T * δ, mul_pos hT hδ, ?_⟩
  intro w hw
  let v : E := T⁻¹ • w
  have hv : ‖v‖ < δ := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
    calc
      T⁻¹ * ‖w‖ < T⁻¹ * (T * δ) :=
        mul_lt_mul_of_pos_left hw (inv_pos.mpr hT)
      _ = δ := by field_simp [ne_of_gt hT]
  have hvp : ‖v‖ < δp :=
    hv.trans_le (by dsimp [δ]; exact min_le_left _ _)
  have hvq : ‖v‖ < δq :=
    hv.trans_le (by dsimp [δ]; exact min_le_right _ _)
  have hscale : T • v = w := by
    simp [v, smul_smul, ne_of_gt hT]
  rcases hαp v hvp with
    ⟨hαp_zero, hαp_deriv, hαp_mem, hαp_target, hαp_hom⟩
  rcases hαq v hvq with
    ⟨hαq_zero, hαq_deriv, hαq_mem, hαq_target, hαq_hom⟩
  let F : E × E → E × E :=
    geodesicFlowField
      (GeodesicTransport.chartChristoffelField roundSphereMetric3 p)
  let γp : ℝ → E × E :=
    αp (extChartAt I p p, v)
  let γq : ℝ → E × E :=
    αq (extChartAt I q q, v)
  let c : E × E := ((0 : E), (0 : E))
  let R : ℝ := max (ap : ℝ) (aq : ℝ)
  have hΓ :=
    RoundSphereTargetAnchorUniformity.chartChristoffelField_roundSphere_anchor_independent
      p q
  have hIp : Icc (0 : ℝ) T ⊆ Icc (-εp) εp := by
    intro t ht
    exact ⟨by linarith [hεp, ht.1], ht.2.trans hT_le_εp⟩
  have hIq : Icc (0 : ℝ) T ⊆ Icc (-εq) εq := by
    intro t ht
    exact ⟨by linarith [hεq, ht.1], ht.2.trans hT_le_εq⟩
  have hγp_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt γp (F (γp t)) (Icc (0 : ℝ) T) t := by
    intro t ht
    simpa [γp, F] using (hαp_deriv t (hIp ht)).mono hIp
  have hγq_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt γq (F (γq t)) (Icc (0 : ℝ) T) t := by
    intro t ht
    have hraw := (hαq_deriv t (hIq ht)).mono hIq
    rw [← hΓ] at hraw
    simpa [γq, F] using hraw
  have hγp_mem : ∀ t ∈ Icc (0 : ℝ) T,
      γp t ∈ closedBall c R := by
    intro t ht
    have hsmall := hαp_mem t (hIp ht)
    have hself : extChartAt I p p = (0 : E) :=
      RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero p
    rw [hself] at hsmall
    have hsmall' : γp t ∈ closedBall c (ap : ℝ) := by
      change αp (extChartAt I p p, v) t ∈ closedBall c (ap : ℝ)
      rw [hself]
      simpa [c] using hsmall
    exact closedBall_subset_closedBall
      (by dsimp [R]; exact le_max_left _ _) hsmall'
  have hγq_mem : ∀ t ∈ Icc (0 : ℝ) T,
      γq t ∈ closedBall c R := by
    intro t ht
    have hsmall := hαq_mem t (hIq ht)
    have hself : extChartAt I q q = (0 : E) :=
      RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero q
    rw [hself] at hsmall
    have hsmall' : γq t ∈ closedBall c (aq : ℝ) := by
      change αq (extChartAt I q q, v) t ∈ closedBall c (aq : ℝ)
      rw [hself]
      simpa [c] using hsmall
    exact closedBall_subset_closedBall
      (by dsimp [R]; exact le_max_right _ _) hsmall'
  rcases
      GeodesicTransport.geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
        roundSphereMetric3 p c R with
    ⟨K, hLip⟩
  have hγp_cont : ContinuousOn γp (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn hγp_deriv
  have hγq_cont : ContinuousOn γq (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn hγq_deriv
  have hzero : γp 0 = γq 0 := by
    rw [show γp 0 = (extChartAt I p p, v) by simpa [γp] using hαp_zero]
    rw [show γq 0 = (extChartAt I q q, v) by simpa [γq] using hαq_zero]
    rw [RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero,
      RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero]
  have hγ_eq : EqOn γp γq (Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ : ℝ ↦ F) (s := fun _ : ℝ ↦ closedBall c R)
      (K := K) ?_ hγp_cont ?_ ?_ hγq_cont ?_ ?_ hzero
    · intro t ht
      simpa [F] using hLip
    · intro t ht
      exact
        (hγp_deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
    · intro t ht
      exact hγp_mem t (Ico_subset_Icc_self ht)
    · intro t ht
      exact
        (hγq_deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
    · intro t ht
      exact hγq_mem t (Ico_subset_Icc_self ht)
  have hT_mem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hstate_T : γp T = γq T := hγ_eq hT_mem
  have hT_mem_p : T ∈ Icc (0 : ℝ) τp := ⟨hT.le, hT_le_τp⟩
  have hT_mem_q : T ∈ Icc (0 : ℝ) τq := ⟨hT.le, hT_le_τq⟩
  have hT_full_p : T ∈ Icc (-εp) εp := hIp hT_mem
  have hT_full_q : T ∈ Icc (-εq) εq := hIq hT_mem
  have hchart_p :
      extChartAt I p
          (GeodesicTransport.expAt roundSphereMetric3 p w) =
        (γp T).1 := by
    rw [← hscale, hexp_p v hvp T hT_mem_p]
    apply (extChartAt I p).right_inv
    simpa [γp] using hαp_target T hT_full_p
  have hchart_q :
      extChartAt I q
          (GeodesicTransport.expAt roundSphereMetric3 q w) =
        (γq T).1 := by
    rw [← hscale, hexp_q v hvq T hT_mem_q]
    apply (extChartAt I q).right_inv
    simpa [γq] using hαq_target T hT_full_q
  calc
    extChartAt I p
        (GeodesicTransport.expAt roundSphereMetric3 p w) =
        (γp T).1 := hchart_p
    _ = (γq T).1 := congrArg Prod.fst hstate_T
    _ = extChartAt I q
        (GeodesicTransport.expAt roundSphereMetric3 q w) := hchart_q.symm

/-- The generic chart-coordinate exponential at any anchor has the same germ
as the reference-anchor coordinate exponential. -/
theorem exists_chart_expAt_eq_coordinateLocalHomeomorph_on_ball
    (p : RoundSphere3) :
    ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
      extChartAt I p
          (GeodesicTransport.expAt roundSphereMetric3 p v) =
        RoundSphereCanonicalExponential.coordinateLocalHomeomorph v := by
  rcases exists_pairwise_chart_expAt_eq_on_ball p
      RoundSphereCanonicalExponential.referenceAnchor with ⟨r, hr, h⟩
  refine ⟨r, hr, ?_⟩
  intro v hv
  simpa [RoundSphereCanonicalExponential.coordinateLocalHomeomorph,
    GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using h v hv

/-- Equivalently, the two chart-coordinate maps are eventually equal at
zero. -/
theorem chart_expAt_eventuallyEq_coordinateLocalHomeomorph
    (p : RoundSphere3) :
    (fun v : E ↦
      extChartAt I p (GeodesicTransport.expAt roundSphereMetric3 p v))
      =ᶠ[𝓝 (0 : E)]
        (RoundSphereCanonicalExponential.coordinateLocalHomeomorph : E → E) := by
  rcases exists_chart_expAt_eq_coordinateLocalHomeomorph_on_ball p with
    ⟨r, hr, h⟩
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with v hv
  apply h v
  simpa [Metric.mem_ball, dist_eq_norm] using hv

/-- The sphere-valued generic exponential itself has the same germ as the
reference-normalized exponential at the supplied anchor. -/
theorem exists_expAt_eq_canonical_expAt_on_ball (p : RoundSphere3) :
    ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
      GeodesicTransport.expAt roundSphereMetric3 p v =
        RoundSphereCanonicalExponential.expAt p v := by
  rcases exists_chart_expAt_eq_coordinateLocalHomeomorph_on_ball p with
    ⟨rChart, hrChart, hChart⟩
  rcases GeodesicTransport.expAt_mem_source_of_norm_lt
      roundSphereMetric3 p with ⟨rSource, hrSource, hSource⟩
  refine ⟨min rChart rSource, lt_min hrChart hrSource, ?_⟩
  intro v hv
  have hvChart : ‖v‖ < rChart := hv.trans_le (min_le_left _ _)
  have hvSource : ‖v‖ < rSource := hv.trans_le (min_le_right _ _)
  calc
    GeodesicTransport.expAt roundSphereMetric3 p v =
        (extChartAt I p).symm
          (extChartAt I p
            (GeodesicTransport.expAt roundSphereMetric3 p v)) :=
      ((extChartAt I p).left_inv (hSource v hvSource)).symm
    _ = (extChartAt I p).symm
        (RoundSphereCanonicalExponential.coordinateLocalHomeomorph v) := by
      rw [hChart v hvChart]
    _ = RoundSphereCanonicalExponential.expAt p v := rfl

/-- Germ formulation of the sphere-valued comparison. -/
theorem expAt_eventuallyEq_canonical_expAt (p : RoundSphere3) :
    GeodesicTransport.expAt roundSphereMetric3 p
      =ᶠ[𝓝 (0 : E)] RoundSphereCanonicalExponential.expAt p := by
  rcases exists_expAt_eq_canonical_expAt_on_ball p with ⟨r, hr, h⟩
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with v hv
  apply h v
  simpa [Metric.mem_ball, dist_eq_norm] using hv

end RoundSphereGenericExponentialAnchorIndependence
end Poincare
