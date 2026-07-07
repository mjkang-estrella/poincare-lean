import Poincare.Global.JacobiIntegrated

/-!
# Cartan isometry assembly: integrated Jacobi scalars

This module records the first honest assembly step from the pointwise
cutoff-one Jacobi norm bridge to the integrated scalar identities used by the
normal-coordinate Cartan route.
-/

noncomputable section

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanIsometryTheorem

universe u

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3

open GeodesicTransport

/--
Interval assembly of the actual corrected Jacobi scalars.

At every time in the cutoff-one interval, the pointwise bridge
`JacobiNormClose.chart_linearized_state_feeds_norm_system_at` supplies the
closed norm system for the corrected chart-linearized state.  The scalar
Picard-Lindelöf theorem from `JacobiIntegrated` then pins the actual scalars
to the sine/cosine solution on the same interval.
-/
theorem actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3}
    {tmin tmax q : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : ℝ), (0 : ℝ), q) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hunit : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 = 1)
    (horth : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA q s,
        JacobiNormSystem.pinnedB q s,
        JacobiNormSystem.pinnedC q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    JacobiNormSystem.normA g x₀
        (fun τ : ℝ => (γ τ).1)
        (fun τ : ℝ => (Ψ τ).1) t = Real.sin t ^ 2 * q ∧
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) t =
        (Real.sin t * Real.cos t) * q ∧
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) t =
        Real.cos t ^ 2 * q := by
  let z : ℝ → E3 := fun τ => (γ τ).1
  let J : ℝ → E3 := fun τ => (Ψ τ).1
  let D : ℝ → E3 :=
    fun τ => (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1
  let a : ℝ → ℝ := JacobiNormSystem.normA g x₀ z J
  let b : ℝ → ℝ := JacobiNormSystem.normB g x₀ z J D
  let c : ℝ → ℝ := JacobiNormSystem.normC g x₀ z D
  have ha : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt a (2 * b s) (Icc tmin tmax) s := by
    intro s hs
    have hfeed :=
      JacobiNormClose.chart_linearized_state_feeds_norm_system_at
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
        (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
        (hunit s hs) (horth s hs) (hGd s hs)
    simpa [a, b, z, J, D] using hfeed.1.hasDerivWithinAt
  have hb : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt b (c s - a s) (Icc tmin tmax) s := by
    intro s hs
    have hfeed :=
      JacobiNormClose.chart_linearized_state_feeds_norm_system_at
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
        (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
        (hunit s hs) (horth s hs) (hGd s hs)
    simpa [a, b, c, z, J, D] using hfeed.2.1.hasDerivWithinAt
  have hc : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt c (-2 * b s) (Icc tmin tmax) s := by
    intro s hs
    have hfeed :=
      JacobiNormClose.chart_linearized_state_feeds_norm_system_at
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
        (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
        (hunit s hs) (horth s hs) (hGd s hs)
    simpa [b, c, z, J, D] using hfeed.2.2.hasDerivWithinAt
  have hmem' : ∀ s ∈ Icc tmin tmax,
      (a s, b s, c s) ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius := by
    intro s hs
    simpa [a, b, c, z, J, D] using hmem s hs
  have ha0' : a 0 = 0 := by
    simpa [a, z, J] using ha0
  have hb0' : b 0 = 0 := by
    simpa [b, z, J, D] using hb0
  have hc0' : c 0 = q := by
    simpa [c, z, D] using hc0
  have hpinned :=
    JacobiIntegrated.closed_norm_system_eq_pinned_on_Icc
      (tmin := tmin) (tmax := tmax) (q := q) hzero Aop
      (hpl := hpl) hAop
      (a := a) (b := b) (c := c)
      ha hb hc hmem' hpinnedmem ha0' hb0' hc0' ht
  simpa [a, b, c, z, J, D] using hpinned

end CartanIsometryTheorem
end Poincare
