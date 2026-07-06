import Poincare.Global.GeodesicGerm

/-!
# Constant speed for chart geodesics

This module proves the first metric invariant for the chart geodesic ODE:
the blended chart metric used to define `chartChristoffelField` has constant
velocity pairing along first-order chart geodesic solutions.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

open Bundle Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The exact blended chart metric whose Christoffel one-form is `chartChristoffelField`. -/
abbrev chartGeodesicMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    E → E →L[ℝ] E →L[ℝ] ℝ :=
  CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
    (backgroundMetric (n := n)) g.inner x₀

omit [T2Space M] in
private theorem chartGeodesicMetric_contDiff_two
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ContDiff ℝ 2 (chartGeodesicMetric g x₀) := by
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  simpa [chartGeodesicMetric] using
    (CovariantDerivative.contDiff_blendedChartMetric
      (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
      htwo_add_one_le_top (cutoff_contDiff (n := n) x₀)
      (cutoff_tsupport (n := n) x₀) hg2)

omit [T2Space M] in
private theorem chartGeodesicMetric_differentiable
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    Differentiable ℝ (chartGeodesicMetric g x₀) :=
  (chartGeodesicMetric_contDiff_two g x₀).differentiable (by norm_num)

omit [T2Space M] in
theorem chartGeodesicMetric_symm
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (z v w : E) :
    chartGeodesicMetric g x₀ z v w =
      chartGeodesicMetric g x₀ z w v := by
  simpa [chartGeodesicMetric] using
    CovariantDerivative.blendedChartMetric_symm
      (cutoff (n := n) x₀) (backgroundMetric (n := n))
      (backgroundMetric_symm (n := n)) g.inner
      (fun y v w => g.inner_symm y v w) x₀ z v w

omit [T2Space M] in
/--
The Christoffel pairing identity for the exact blended chart metric used by
`chartChristoffelField`.
-/
theorem chartChristoffelField_pairing_eq_blendedChartMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z u v w : E) :
    chartGeodesicMetric g x₀ z ((chartChristoffelField g x₀ z) u v) w =
      (1 / 2 : ℝ) *
        (((fderiv ℝ (chartGeodesicMetric g x₀) z v) u w) +
          ((fderiv ℝ (chartGeodesicMetric g x₀) z u) v w) -
            ((fderiv ℝ (chartGeodesicMetric g x₀) z w) v u)) := by
  rw [show
      chartGeodesicMetric g x₀ z ((chartChristoffelField g x₀ z) u v) w =
        CovariantDerivative.chartBilin (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀ z
          ((chartChristoffelField g x₀ z) u v) w from rfl]
  change
      CovariantDerivative.chartBilin (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀ z
        (CovariantDerivative.christoffelAt
          (chartGeodesicMetric g x₀) z
          (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀ z)
          (CovariantDerivative.chartBilin_nondegenerate
            (cutoff (n := n) x₀) (backgroundMetric (n := n))
            (backgroundMetric_pos (n := n)) g.inner
            (fun y u hu => g.inner_pos y (v := u) hu) x₀
            (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
            (cutoff_support_invertible (n := n) x₀) z)
          v u) w =
        (1 / 2 : ℝ) *
          ((((fderiv ℝ (chartGeodesicMetric g x₀) z) v) u) w +
            (((fderiv ℝ (chartGeodesicMetric g x₀) z) u) v) w -
              (((fderiv ℝ (chartGeodesicMetric g x₀) z) w) v) u)
  rw [CovariantDerivative.b_christoffelAt]

omit [T2Space M] in
/--
Pointwise constant-speed derivative identity for a chart geodesic solution.
The scalar speed is measured by the same blended chart metric used to build
`chartChristoffelField`.
-/
theorem chart_geodesic_speed_hasDerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {γ : ℝ → E × E} {t : ℝ}
    (hγ : HasDerivAt γ
      (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t) :
    HasDerivAt
      (fun τ : ℝ =>
        chartGeodesicMetric g x₀ (γ τ).1 (γ τ).2 (γ τ).2)
      0 t := by
  set z : E := (γ t).1
  set v : E := (γ t).2
  set Γ : E := (chartChristoffelField g x₀ z) v v
  set A : ℝ := (((fderiv ℝ (chartGeodesicMetric g x₀) z) v) v) v
  have hpos : HasDerivAt (fun τ : ℝ => (γ τ).1) v t := by
    simpa [v] using
      (geodesic_position_hasDerivAt
        (Γ := chartChristoffelField g x₀) (γ := γ) hγ)
  have hvel : HasDerivAt (fun τ : ℝ => (γ τ).2) (-Γ) t := by
    simpa [z, v, Γ] using
      (geodesic_velocity_hasDerivAt
        (Γ := chartChristoffelField g x₀) (γ := γ) hγ)
  have hGpath :
      HasDerivAt
        (fun τ : ℝ => chartGeodesicMetric g x₀ (γ τ).1)
        ((fderiv ℝ (chartGeodesicMetric g x₀) z) v) t := by
    have hGdiffAt :
        DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ t).1 :=
      chartGeodesicMetric_differentiable g x₀ (γ t).1
    have hcomp :
        HasDerivAt
          ((chartGeodesicMetric g x₀) ∘ fun τ : ℝ => (γ τ).1)
          ((fderiv ℝ (chartGeodesicMetric g x₀) (γ t).1) v) t :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := E)
        (f := fun τ : ℝ => (γ τ).1) (f' := v) (x := t)
        (l := chartGeodesicMetric g x₀)
        (l' := fderiv ℝ (chartGeodesicMetric g x₀) (γ t).1)
        hGdiffAt.hasFDerivAt hpos
    simpa [Function.comp_def, z] using hcomp
  have hGv :
      HasDerivAt
        (fun τ : ℝ => chartGeodesicMetric g x₀ (γ τ).1 (γ τ).2)
        (((fderiv ℝ (chartGeodesicMetric g x₀) z) v) v +
          chartGeodesicMetric g x₀ z (-Γ)) t := by
    simpa [z, v] using hGpath.clm_apply hvel
  have hspeed :
      HasDerivAt
        (fun τ : ℝ =>
          chartGeodesicMetric g x₀ (γ τ).1 (γ τ).2 (γ τ).2)
        ((((fderiv ℝ (chartGeodesicMetric g x₀) z) v) v +
            chartGeodesicMetric g x₀ z (-Γ)) v +
          chartGeodesicMetric g x₀ z v (-Γ)) t := by
    simpa [z, v] using hGv.clm_apply hvel
  have hΓpair : chartGeodesicMetric g x₀ z Γ v = (1 / 2 : ℝ) * A := by
    have h :=
      chartChristoffelField_pairing_eq_blendedChartMetric
        (g := g) (x₀ := x₀) z v v v
    simpa [Γ, A] using h
  have hsymmΓ : chartGeodesicMetric g x₀ z v Γ =
      chartGeodesicMetric g x₀ z Γ v :=
    chartGeodesicMetric_symm g x₀ z v Γ
  have hcancel :
      A + chartGeodesicMetric g x₀ z (-Γ) v +
          chartGeodesicMetric g x₀ z v (-Γ) = 0 := by
    simp only [map_neg, ContinuousLinearMap.neg_apply]
    rw [hsymmΓ, hΓpair]
    ring_nf
  convert hspeed using 1
  symm
  simpa [A, ContinuousLinearMap.add_apply, map_neg,
    ContinuousLinearMap.neg_apply] using hcancel

omit [T2Space M] in
/-- The blended-metric speed is constant on any open preconnected interval of solution. -/
theorem chart_geodesic_speed_constantOn
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {s : Set ℝ} (hs_open : IsOpen s) (hs_pre : IsPreconnected s)
    {γ : ℝ → E × E}
    (hγ : ∀ t ∈ s,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    {t u : ℝ} (ht : t ∈ s) (hu : u ∈ s) :
    chartGeodesicMetric g x₀ (γ t).1 (γ t).2 (γ t).2 =
      chartGeodesicMetric g x₀ (γ u).1 (γ u).2 (γ u).2 := by
  let speed : ℝ → ℝ :=
    fun τ : ℝ => chartGeodesicMetric g x₀ (γ τ).1 (γ τ).2 (γ τ).2
  have hspeed : ∀ τ ∈ s, HasDerivAt speed 0 τ := by
    intro τ hτ
    exact chart_geodesic_speed_hasDerivAt_zero
      (g := g) (x₀ := x₀) (γ := γ) (t := τ) (hγ τ hτ)
  have hdiff : DifferentiableOn ℝ speed s :=
    fun τ hτ => (hspeed τ hτ).differentiableAt.differentiableWithinAt
  have hderiv : s.EqOn (deriv speed) 0 :=
    fun τ hτ => (hspeed τ hτ).deriv
  exact hs_open.is_const_of_deriv_eq_zero hs_pre hdiff hderiv ht hu

omit [T2Space M] in
/-- The blended-metric speed is constant on an open interval of chart geodesic solution. -/
theorem chart_geodesic_speed_constantOn_Ioo
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {a b : ℝ} {γ : ℝ → E × E}
    (hγ : ∀ t ∈ Ioo a b,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    {t u : ℝ} (ht : t ∈ Ioo a b) (hu : u ∈ Ioo a b) :
    chartGeodesicMetric g x₀ (γ t).1 (γ t).2 (γ t).2 =
      chartGeodesicMetric g x₀ (γ u).1 (γ u).2 (γ u).2 :=
  chart_geodesic_speed_constantOn (g := g) (x₀ := x₀)
    (s := Ioo a b) isOpen_Ioo isPreconnected_Ioo hγ ht hu

omit [T2Space M] in
/--
The chosen chart solution defining `geodesicGermAt` has its blended-metric
speed equal to its initial speed as a germ at `0`.
-/
theorem geodesicGermChartSolution_speed_eventually_eq_initial
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      chartGeodesicMetric g x₀
          (geodesicGermChartSolution g x₀ v₀ t).1
          (geodesicGermChartSolution g x₀ v₀ t).2
          (geodesicGermChartSolution g x₀ v₀ t).2 =
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀ := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  have hε := geodesicGermRadius_pos g x₀ v₀
  have hI :
      Ioo (-(geodesicGermRadius g x₀ v₀))
          (geodesicGermRadius g x₀ v₀) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hI] with t ht
  have hzero :
      (0 : ℝ) ∈
        Ioo (-(geodesicGermRadius g x₀ v₀))
          (geodesicGermRadius g x₀ v₀) := by
    constructor <;> linarith
  have hconst :=
    chart_geodesic_speed_constantOn_Ioo
      (g := g) (x₀ := x₀)
      (a := -(geodesicGermRadius g x₀ v₀))
      (b := geodesicGermRadius g x₀ v₀)
      (γ := geodesicGermChartSolution g x₀ v₀)
      hspec.2.1 ht hzero
  simpa [hspec.1] using hconst

end GeodesicTransport
end Poincare
