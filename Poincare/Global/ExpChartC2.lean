import Poincare.Global.ContDiffTwo

/-!
# C² exponential-chart handoff

This module isolates the last chart-side regularity handoff.  A `C¹`
derivative field for each fixed-time exponential chart gives `C²` regularity
of the chart by `contDiffAt_succ_iff_hasFDerivAt`; the source inverse then
gets `C²` regularity from the inverse-function theorem for
`OpenPartialHomeomorph`s.  The resulting chart-side inputs feed the existing
Cartan-map composition assembly from `ContDiffTwo`.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace ExpChartC2

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Derivative-field regularity for the two exponential charts supplies the
`ContDiffAt ℝ 2` Cartan chart map input.

The source inverse is not assumed `C²`: it is derived from the source
exponential chart's `C²` regularity and an invertible derivative via
`OpenPartialHomeomorph.contDiffAt_symm`.
-/
theorem cartanChartMap_contDiffAt_two_of_expChart_derivative_fields
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    (p0 : RoundSphere3) (L : CartanMap.TangentAlignment g x0 p0)
    {v : E3}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0).source)
    {sourceD targetD : E3 → E3 →L[ℝ] E3}
    {sourceIso : E3 ≃L[ℝ] E3}
    (hsource_deriv :
      ∃ U ∈ 𝓝 v, ∀ q ∈ U,
        HasFDerivAt
          (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0)
          (sourceD q) q)
    (hsourceD_c1 : ContDiffAt ℝ 1 sourceD v)
    (hsourceIso_deriv :
      HasFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0)
        (sourceIso : E3 →L[ℝ] E3) v)
    (htarget_deriv :
      ∃ U ∈ 𝓝 (L v), ∀ q ∈ U,
        HasFDerivAt
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0)
          (targetD q) q)
    (htargetD_c1 : ContDiffAt ℝ 1 targetD (L v)) :
    ContDiffAt ℝ 2 (CartanDifferential.cartanChartMap g x0 p0 L)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v) := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p0
  have hsourceC2 : ContDiffAt ℝ 2 eM v := by
    exact
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)
        (f := eM) (x := v)).2
        ⟨sourceD, by simpa [eM] using hsource_deriv, hsourceD_c1⟩
  have htargetC2 : ContDiffAt ℝ 2 eS (L v) := by
    exact
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)
        (f := eS) (x := L v)).2
        ⟨targetD, by simpa [eS] using htarget_deriv, htargetD_c1⟩
  have hsourceInvC2 : ContDiffAt ℝ 2 eM.symm (eM v) := by
    have htarget_mem : eM v ∈ eM.target := eM.map_source hvsrc
    have hleft : eM.symm (eM v) = v := eM.left_inv hvsrc
    have hsourceIso_deriv_at_symm :
        HasFDerivAt eM (sourceIso : E3 →L[ℝ] E3) (eM.symm (eM v)) := by
      rw [hleft]
      simpa [eM] using hsourceIso_deriv
    have hsourceC2_at_symm :
        ContDiffAt ℝ 2 eM (eM.symm (eM v)) := by
      rw [hleft]
      exact hsourceC2
    exact
      eM.contDiffAt_symm (f₀' := sourceIso) (a := eM v) htarget_mem
        hsourceIso_deriv_at_symm hsourceC2_at_symm
  exact
    ContDiffTwo.cartanChartMap_contDiffAt_two_of_expChart_contDiffAt_two
      (g := g) (x₀ := x0) (p₀ := p0) (L := L) (v := v)
      hvsrc hsourceInvC2 htargetC2

end ExpChartC2
end Poincare
