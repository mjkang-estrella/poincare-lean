import Poincare.Global.DeTurckCoordinateJointRegularity
import Poincare.Global.DeTurckChartOverlapCovariance

/-!
# Joint DeTurck regularity in an overlapping preferred chart

Metric-entry regularity is most naturally stated in the preferred chart
centered at the point under consideration.  Inverse-gauge reconstruction may
use a different preferred chart containing that point.  This file transports
the joint coordinate-field regularity across the honest chart overlap, using
the intrinsic DeTurck field's exact covariance law.
-/

noncomputable section

open Filter Function Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DeTurckCoordinateJointRegularityOverlap

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "𝓘" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- An honest preferred-chart transition is `C³` at every point of its
overlap source. -/
theorem chartTransition_contDiffAt_three_of_mem_source
    (sourceAnchor targetAnchor : M) {z : E}
    (hz : z ∈
      ((extChartAt 𝓘 sourceAnchor).symm ≫ extChartAt 𝓘 targetAnchor).source) :
    ContDiffAt ℝ 3
      (GeodesicTransport.chartTransition sourceAnchor targetAnchor) z := by
  have h := contDiffWithinAt_ext_coord_change
    (I := 𝓘) (n := 3) targetAnchor sourceAnchor hz
  have hAt : ContDiffAt ℝ 3
      ((extChartAt 𝓘 targetAnchor) ∘
        (extChartAt 𝓘 sourceAnchor).symm) z := by
    simpa [ModelWithCorners.range_eq_univ] using h
  simpa [GeodesicTransport.chartTransition] using hAt

/-- The differential of an honest preferred-chart transition is `C²`. -/
theorem chartTransitionDeriv_contDiffAt_two_of_mem_source
    (sourceAnchor targetAnchor : M) {z : E}
    (hz : z ∈
      ((extChartAt 𝓘 sourceAnchor).symm ≫ extChartAt 𝓘 targetAnchor).source) :
    ContDiffAt ℝ 2
      (GeodesicTransport.chartTransitionDeriv sourceAnchor targetAnchor) z := by
  have h := chartTransition_contDiffAt_three_of_mem_source
    sourceAnchor targetAnchor hz
  simpa [GeodesicTransport.chartTransitionDeriv] using
    h.fderiv_right (m := 2) (by norm_num)

/-- Joint `C³` metric entries at `y` give joint `C²` regularity of the
intrinsic DeTurck field in every preferred chart whose source contains `y`.
This removes the artificial requirement that the coordinate chart be
centered at the point where regularity is supplied. -/
theorem deTurckChartCoordinateField_jointContDiffAt_two_of_metricEntries_of_mem_source
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {anchor y : M}
    (hy : y ∈ (extChartAt 𝓘 anchor).source)
    (hgt : MetricEntriesJointContDiffAt gt t₀ y 3) :
    ContDiffAt ℝ 2
      (Function.uncurry (fun t z ↦
        chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z))
      (t₀, extChartAt 𝓘 anchor y) := by
  let qa : E := extChartAt 𝓘 anchor y
  let qy : E := extChartAt 𝓘 y y
  let tau : E → E :=
    GeodesicTransport.chartTransition anchor y
  let sigma : E → E :=
    GeodesicTransport.chartTransition y anchor
  let Wy : ℝ → E → E := fun t z ↦
    chartCoordinateTangentField y (deTurckVectorField gt bg t) z
  let Wa : ℝ → E → E := fun t z ↦
    chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z
  let candidate : ℝ × E → E := fun p ↦
    GeodesicTransport.chartTransitionDeriv y anchor (tau p.2)
      (Wy p.1 (tau p.2))
  have hqaTarget : qa ∈ (extChartAt 𝓘 anchor).target := by
    simpa [qa] using (extChartAt 𝓘 anchor).map_source hy
  have hqaSymm : (extChartAt 𝓘 anchor).symm qa = y := by
    simpa [qa] using (extChartAt 𝓘 anchor).left_inv hy
  have hqaOverlap : qa ∈
      ((extChartAt 𝓘 anchor).symm ≫ extChartAt 𝓘 y).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hqaTarget, by
      change (extChartAt 𝓘 anchor).symm qa ∈
        (extChartAt 𝓘 y).source
      rw [hqaSymm]
      exact mem_extChartAt_source y⟩
  have hqyTarget : qy ∈ (extChartAt 𝓘 y).target := by
    exact mem_extChartAt_target y
  have hqySymm : (extChartAt 𝓘 y).symm qy = y := by
    simpa [qy] using
      (extChartAt 𝓘 y).left_inv (mem_extChartAt_source y)
  have hqyOverlap : qy ∈
      ((extChartAt 𝓘 y).symm ≫ extChartAt 𝓘 anchor).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hqyTarget, by
      change (extChartAt 𝓘 y).symm qy ∈
        (extChartAt 𝓘 anchor).source
      rw [hqySymm]
      exact hy⟩
  have htauValue : tau qa = qy := by
    change extChartAt 𝓘 y ((extChartAt 𝓘 anchor).symm qa) = qy
    rw [hqaSymm]
  have htauC2 : ContDiffAt ℝ 2 tau qa :=
    (chartTransition_contDiffAt_three_of_mem_source
      anchor y hqaOverlap).of_le (by norm_num)
  have hsigmaDC2 : ContDiffAt ℝ 2
      (GeodesicTransport.chartTransitionDeriv y anchor) qy :=
    chartTransitionDeriv_contDiffAt_two_of_mem_source y anchor hqyOverlap
  have hWyC2 : ContDiffAt ℝ 2 (Function.uncurry Wy) (t₀, qy) := by
    simpa [Wy, qy] using
      DeTurckCoordinateJointRegularity.deTurckChartCoordinateField_jointContDiffAt_two_of_metricEntries
        (bg := bg) hgt
  have htauSpace : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ tau p.2) (t₀, qa) := by
    have hsnd : ContDiffAt ℝ 2 (Prod.snd : ℝ × E → E) (t₀, qa) :=
      contDiffAt_snd
    exact ContDiffAt.fun_comp (g := tau) (f := Prod.snd)
      (t₀, qa) htauC2 hsnd
  have htauPair : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ (p.1, tau p.2)) (t₀, qa) :=
    contDiffAt_fst.prodMk htauSpace
  have hWyComp : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ Wy p.1 (tau p.2)) (t₀, qa) := by
    have hWyC2' : ContDiffAt ℝ 2 (Function.uncurry Wy)
        (t₀, tau qa) := by
      simpa [htauValue] using hWyC2
    simpa [Function.uncurry] using
      (ContDiffAt.fun_comp
        (g := Function.uncurry Wy)
        (f := fun p : ℝ × E ↦ (p.1, tau p.2))
        (t₀, qa) hWyC2' htauPair)
  have hDComp : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦
        GeodesicTransport.chartTransitionDeriv y anchor (tau p.2))
      (t₀, qa) := by
    have hsigmaDC2' : ContDiffAt ℝ 2
        (GeodesicTransport.chartTransitionDeriv y anchor) (tau qa) := by
      simpa [htauValue] using hsigmaDC2
    exact ContDiffAt.fun_comp
      (g := GeodesicTransport.chartTransitionDeriv y anchor)
      (f := fun p : ℝ × E ↦ tau p.2)
      (t₀, qa) hsigmaDC2' htauSpace
  have hcandidate : ContDiffAt ℝ 2 candidate (t₀, qa) := by
    simpa [candidate] using hDComp.clm_apply hWyComp
  have hoverlapMem :
      ((extChartAt 𝓘 anchor).symm ≫ extChartAt 𝓘 y).source ∈ nhds qa :=
    by
      have htarget : (extChartAt 𝓘 anchor).target ∈ nhds qa :=
        extChartAt_target_mem_nhds' hqaTarget
      have hpreimage :
          (extChartAt 𝓘 anchor).symm ⁻¹' (extChartAt 𝓘 y).source ∈
            nhds qa := by
        simpa [qa] using
          (extChartAt_preimage_mem_nhds' (I := 𝓘) hy
            (extChartAt_source_mem_nhds (I := 𝓘) y))
      simpa [PartialEquiv.trans_source, PartialEquiv.symm_source] using
        inter_mem htarget hpreimage
  have hoverlapPair : ∀ᶠ p : ℝ × E in nhds (t₀, qa),
      p.2 ∈ ((extChartAt 𝓘 anchor).symm ≫ extChartAt 𝓘 y).source :=
    continuousAt_snd.eventually hoverlapMem
  have heq : Function.uncurry Wa =ᶠ[nhds (t₀, qa)] candidate := by
    filter_upwards [hoverlapPair] with p hp
    let m : M := (extChartAt 𝓘 anchor).symm p.2
    have hp' : p.2 ∈ (extChartAt 𝓘 anchor).target ∧
        m ∈ (extChartAt 𝓘 y).source := by
      simpa [m, PartialEquiv.trans_source'', PartialEquiv.symm_target] using hp
    have hmAnchor : m ∈ (extChartAt 𝓘 anchor).source :=
      (extChartAt 𝓘 anchor).symm.map_source hp'.1
    have htau : tau p.2 = extChartAt 𝓘 y m := rfl
    have htauTarget : tau p.2 ∈ (extChartAt 𝓘 y).target := by
      rw [htau]
      exact (extChartAt 𝓘 y).map_source hp'.2
    have htauSymm : (extChartAt 𝓘 y).symm (tau p.2) = m := by
      rw [htau]
      exact (extChartAt 𝓘 y).left_inv hp'.2
    have hreverse : tau p.2 ∈
        ((extChartAt 𝓘 y).symm ≫ extChartAt 𝓘 anchor).source := by
      rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
      exact ⟨htauTarget, by
        change (extChartAt 𝓘 y).symm (tau p.2) ∈
          (extChartAt 𝓘 anchor).source
        rw [htauSymm]
        exact hmAnchor⟩
    have hsigmaTau : sigma (tau p.2) = p.2 := by
      change extChartAt 𝓘 anchor
          ((extChartAt 𝓘 y).symm (tau p.2)) = p.2
      rw [htauSymm]
      exact (extChartAt 𝓘 anchor).right_inv hp'.1
    have hcov := deTurckChartCoordinateField_covariant
      gt bg p.1 y anchor hreverse
    rw [show GeodesicTransport.chartTransition y anchor (tau p.2) = p.2 by
      exact hsigmaTau] at hcov
    simpa [Wa, Wy, candidate, Function.uncurry] using hcov.symm
  exact hcandidate.congr_of_eventuallyEq heq

end DeTurckCoordinateJointRegularityOverlap
end Poincare
