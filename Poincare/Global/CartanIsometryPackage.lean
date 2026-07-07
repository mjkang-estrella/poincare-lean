import Poincare.Global.CartanIsometryTheorem

/-!
# Cartan isometry package: polarized Jacobi pairing

This module records the next strict partial after the cutoff-one scalar
assembly.  It proves the interval linearity needed for polarization from the
linearized-flow uniqueness theorem, then specializes the existing polarization
algebra to the chart Jacobi endpoint pairing.
-/

noncomputable section

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanIsometryPackage

universe u

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3

open GeodesicTransport

/--
Polarize the cutoff-one Jacobi endpoint norm identity.

The hypotheses `hquad_w`, `hquad_w'`, and `hquad_add` are exactly the three
quadratic `normA` conclusions supplied by
`CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc` for
initial directions `w`, `w'`, and `w + w'`.  The theorem proves the missing
linearity statement `J_{w+w'} = J_w + J_{w'}` on the interval by applying the
linear ODE uniqueness theorem to the linearized geodesic flow, then feeds that
linearity into the chart-metric polarization algebra.
-/
theorem actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ Ψw Ψw' Ψadd : ℝ → E3 × E3}
    {w w' : E3} {tmin tmax : ℝ}
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E3 × E3 =>
        linearizedGeodesicFlowOperator
          (chartChristoffelField g x₀) (γ s) ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E3), w + w') a r L K)
    (hΨw : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψw
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψw s)) s)
    (hΨw' : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψw'
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψw' s)) s)
    (hΨadd : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψadd
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψadd s)) s)
    (hmem_add : ∀ s ∈ Icc tmin tmax,
      Ψadd s ∈ closedBall ((0 : E3), w + w') a)
    (hmem_sum : ∀ s ∈ Icc tmin tmax,
      Ψw s + Ψw' s ∈ closedBall ((0 : E3), w + w') a)
    (hΨw0 : Ψw 0 = ((0 : E3), w))
    (hΨw'0 : Ψw' 0 = ((0 : E3), w'))
    (hΨadd0 : Ψadd 0 = ((0 : E3), w + w'))
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    (hquad_w :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw τ).1) t =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w)
    (hquad_w' :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw' τ).1) t =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w' w')
    (hquad_add :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψadd τ).1) t =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) (w + w') (w + w')) :
    chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw' t).1 =
      Real.sin t ^ 2 *
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w' := by
  let A : ℝ → (E3 × E3) →L[ℝ] (E3 × E3) :=
    fun s => linearizedGeodesicFlowOperator
      (chartChristoffelField g x₀) (γ s)
  have hder_add : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd (A s (Ψadd s)) (Icc tmin tmax) s := by
    intro s hs
    simpa [A, linearizedGeodesicFlowFieldAlong] using
      (hΨadd s hs).hasDerivWithinAt
  have hder_sum : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (fun τ : ℝ => Ψw τ + Ψw' τ)
        (A s ((fun τ : ℝ => Ψw τ + Ψw' τ) s)) (Icc tmin tmax) s := by
    intro s hs
    have hder := (hΨw s hs).add (hΨw' s hs)
    simpa [A, linearizedGeodesicFlowFieldAlong] using hder.hasDerivWithinAt
  have hinitial :
      Ψadd (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
        (fun τ : ℝ => Ψw τ + Ψw' τ)
          (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
    change Ψadd 0 = Ψw 0 + Ψw' 0
    rw [hΨadd0, hΨw0, hΨw'0]
    simp
  have hEqOn :
      EqOn Ψadd (fun τ : ℝ => Ψw τ + Ψw' τ) (Icc tmin tmax) :=
    linearODE_solution_uniqueOn_Icc
      (A := A) (t₀ := ⟨(0 : ℝ), hzero⟩)
      (x₀ := ((0 : E3), w + w')) (a := a) (r := r) (L := L) (K := K)
      hpl hder_add hmem_add hder_sum hmem_sum hinitial
  have hJadd : (Ψadd t).1 = (Ψw t).1 + (Ψw' t).1 := by
    have hstate := hEqOn ht
    exact congrArg Prod.fst hstate
  have hww :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw t).1 =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w := by
    simpa [JacobiNormSystem.normA] using hquad_w
  have hww' :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw' t).1 (Ψw' t).1 =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w' w' := by
    simpa [JacobiNormSystem.normA] using hquad_w'
  have hadd :
      chartGeodesicMetric g x₀ (γ t).1 (Ψadd t).1 (Ψadd t).1 =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) (w + w') (w + w') := by
    simpa [JacobiNormSystem.normA] using hquad_add
  exact
    JacobiNormSystem.polarize_endpoint_pairing_of_quadratic
      (B := chartGeodesicMetric g x₀ (γ t).1)
      (A := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀))
      (S := Real.sin t ^ 2)
      (fun u v => chartGeodesicMetric_symm (g := g) (x₀ := x₀) (γ t).1 u v)
      (fun u v => chartGeodesicMetric_symm
        (g := g) (x₀ := x₀) (extChartAt I3 x₀ x₀) u v)
      (w := w) (w' := w') (Jw := (Ψw t).1) (Jw' := (Ψw' t).1)
      (Jadd := (Ψadd t).1) hJadd hww hww' hadd

end CartanIsometryPackage
end Poincare
