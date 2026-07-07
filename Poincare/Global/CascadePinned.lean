import Poincare.Global.EqualityChain
import Poincare.Global.CartanIsometryPackage

/-!
# Cascade pinned endpoint pairings

This module isolates the last non-vacuous upstream algebra needed before the
hosted endpoint equality chain can consume cascade-produced Jacobi families.

The first theorem is the polarized Jacobi pairing theorem with
`HasDerivWithinAt` hypotheses, matching the shape exported by the hosted
cascade.  The second theorem converts the resulting blended
`chartGeodesicMetric` endpoint pairing to the genuine transported chart metric
on a cutoff-one endpoint.  The final theorem packages these two steps for the
rescaled hosted family shape whose initial data is `T⁻¹ • w`.
-/

noncomputable section

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CascadePinned

universe u

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/--
Polarized cutoff-one endpoint pairing with derivative hypotheses already in
the `Icc`-restricted form exported by the hosted cascade.
-/
theorem actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ Ψw Ψw' Ψadd : ℝ → E × E}
    {w w' : E} {tmin tmax : ℝ}
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E × E =>
        linearizedGeodesicFlowOperator
          (chartChristoffelField g x₀) (γ s) ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E), w + w') a r L K)
    (hΨw : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψw s))
        (Icc tmin tmax) s)
    (hΨw' : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw'
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψw' s))
        (Icc tmin tmax) s)
    (hΨadd : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψadd s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ s ∈ Icc tmin tmax,
      Ψadd s ∈ closedBall ((0 : E), w + w') a)
    (hmem_sum : ∀ s ∈ Icc tmin tmax,
      Ψw s + Ψw' s ∈ closedBall ((0 : E), w + w') a)
    (hΨw0 : Ψw 0 = ((0 : E), w))
    (hΨw'0 : Ψw' 0 = ((0 : E), w'))
    (hΨadd0 : Ψadd 0 = ((0 : E), w + w'))
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    (hquad_w :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw τ).1) t =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) w w)
    (hquad_w' :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw' τ).1) t =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) w' w')
    (hquad_add :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψadd τ).1) t =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) (w + w') (w + w')) :
    chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw' t).1 =
      Real.sin t ^ 2 *
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) w w' := by
  let A : ℝ → (E × E) →L[ℝ] (E × E) :=
    fun s => linearizedGeodesicFlowOperator
      (chartChristoffelField g x₀) (γ s)
  have hder_add : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd (A s (Ψadd s)) (Icc tmin tmax) s := by
    intro s hs
    simpa [A, linearizedGeodesicFlowFieldAlong] using hΨadd s hs
  have hder_sum : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (fun τ : ℝ => Ψw τ + Ψw' τ)
        (A s ((fun τ : ℝ => Ψw τ + Ψw' τ) s)) (Icc tmin tmax) s := by
    intro s hs
    have hder := (hΨw s hs).add (hΨw' s hs)
    simpa [A, linearizedGeodesicFlowFieldAlong] using hder
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
      (x₀ := ((0 : E), w + w')) (a := a) (r := r) (L := L) (K := K)
      hpl hder_add hmem_add hder_sum hmem_sum hinitial
  have hJadd : (Ψadd t).1 = (Ψw t).1 + (Ψw' t).1 := by
    have hstate := hEqOn ht
    exact congrArg Prod.fst hstate
  have hww :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw t).1 =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) w w := by
    simpa [JacobiNormSystem.normA] using hquad_w
  have hww' :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw' t).1 (Ψw' t).1 =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) w' w' := by
    simpa [JacobiNormSystem.normA] using hquad_w'
  have hadd :
      chartGeodesicMetric g x₀ (γ t).1 (Ψadd t).1 (Ψadd t).1 =
        Real.sin t ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) (w + w') (w + w') := by
    simpa [JacobiNormSystem.normA] using hquad_add
  exact
    JacobiNormSystem.polarize_endpoint_pairing_of_quadratic
      (B := chartGeodesicMetric g x₀ (γ t).1)
      (A := chartGeodesicMetric g x₀ (extChartAt I x₀ x₀))
      (S := Real.sin t ^ 2)
      (fun u v => chartGeodesicMetric_symm (g := g) (x₀ := x₀) (γ t).1 u v)
      (fun u v => chartGeodesicMetric_symm
        (g := g) (x₀ := x₀) (extChartAt I x₀ x₀) u v)
      (w := w) (w' := w') (Jw := (Ψw t).1) (Jw' := (Ψw' t).1)
      (Jadd := (Ψadd t).1) hJadd hww hww' hadd

/--
Convert a cutoff-one endpoint pairing stated for the blended
`chartGeodesicMetric` into the genuine transported chart metric at the endpoint
and at the anchor.
-/
theorem chartMetric_pairing_eq_pinned_of_blended_pairing
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {z J J' w w' : E} {S : ℝ}
    (hcut : cutoff (n := 3) x₀ z = 1)
    (hPair :
      chartGeodesicMetric g x₀ z J J' =
        S * chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) w w') :
    CovariantDerivative.chartMetric g.inner x₀ z J J' =
      S * CartanMap.sourceAnchorChartMetric g x₀ w w' := by
  have hzMetric :
      chartGeodesicMetric g x₀ z =
        CovariantDerivative.chartMetric g.inner x₀ z := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := x₀) hcut)
  have hanchorCut : cutoff (n := 3) x₀ (extChartAt I x₀ x₀) = 1 :=
    (cutoff_eventuallyEq_one (n := 3) x₀).self_of_nhds
  have hanchorMetric :
      chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) =
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀) := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := x₀) hanchorCut)
  have hPair' := hPair
  rw [hzMetric, hanchorMetric] at hPair'
  simpa [CartanMap.sourceAnchorChartMetric] using hPair'

/--
Endpoint pinned formula for a rescaled hosted family.  This matches the
cascade export shape `Ψ w 0 = (0, T⁻¹ • w)`; consequently the pinned anchor
pairing is also evaluated on the rescaled initial directions.
-/
theorem hosted_rescaled_endpoint_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {Ψ : E → ℝ → E × E}
    {v : E} {T tmin tmax : ℝ}
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : ∀ w w' : E,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E × E =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField g x₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E), T⁻¹ • (w + w')) a r L K)
    (hΨder : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E), T⁻¹ • (w + w')) a)
    (hmem_sum : ∀ w w' : E, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E), T⁻¹ • (w + w')) a)
    (hΨ0 : ∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hcutT : cutoff (n := 3) x₀ (γ T).1 = 1)
    (hendpoint :
      (γ T).1 =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (hquad : ∀ w : E,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) T =
        Real.sin T ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ w T).1 (Ψ w' T).1 =
        Real.sin T ^ 2 *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  intro w w'
  have hΨadd0 :
      Ψ (w + w') 0 = ((0 : E), T⁻¹ • w + T⁻¹ • w') := by
    rw [hΨ0 (w + w')]
    simp [smul_add]
  have hPairBlended :
      chartGeodesicMetric g x₀ (γ T).1 (Ψ w T).1 (Ψ w' T).1 =
        Real.sin T ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w') :=
    actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc
      (g := g) (x₀ := x₀) (γ := γ)
      (Ψw := Ψ w) (Ψw' := Ψ w') (Ψadd := Ψ (w + w'))
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (tmin := tmin) (tmax := tmax) hzero
      (a := a) (r := r) (L := L) (K := K)
      (hpl := by simpa [smul_add] using hpl w w')
      (hΨw := hΨder w) (hΨw' := hΨder w') (hΨadd := hΨder (w + w'))
      (hmem_add := by simpa [smul_add] using hmem_add w w')
      (hmem_sum := by simpa [smul_add] using hmem_sum w w')
      (hΨw0 := hΨ0 w) (hΨw'0 := hΨ0 w') (hΨadd0 := hΨadd0)
      (ht := hT) (hquad_w := hquad w) (hquad_w' := hquad w')
      (hquad_add := by simpa [smul_add] using hquad (w + w'))
  have hPairChart :
      CovariantDerivative.chartMetric g.inner x₀ (γ T).1
          (Ψ w T).1 (Ψ w' T).1 =
        Real.sin T ^ 2 *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') :=
    chartMetric_pairing_eq_pinned_of_blended_pairing
      (g := g) (x₀ := x₀) (z := (γ T).1)
      (J := (Ψ w T).1) (J' := (Ψ w' T).1)
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (S := Real.sin T ^ 2) hcutT hPairBlended
  simpa [hendpoint] using hPairChart

end CascadePinned
end Poincare
