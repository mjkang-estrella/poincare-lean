import Poincare.Global.CartanDifferential

/-!
# C² assembly for the Cartan chart map

This module isolates the final chart-composition step for the producer
`ContDiffAt ℝ 2 F (eM v)`, where
`F = CartanDifferential.cartanChartMap g x₀ p₀ L`.

The theorem below is intentionally not a substitute for the missing
smooth-dependence theorem for the exponential charts.  It records the exact
non-circular assembly once the source inverse exponential chart and target
exponential chart are known to be `C²` at the relevant points.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace ContDiffTwo

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The chart-composition step for the Cartan chart map.

If the inverse source exponential chart is `C²` at `eM v` and the target
exponential chart is `C²` at `L v`, then the Cartan chart map
`eS ∘ L ∘ eM.symm` is `C²` at `eM v`.  These are precisely the chart-side
regularity facts needed to produce the `ContDiffAt ℝ 2 F (eM v)` input
consumed by `EndpointBridge`.
-/
theorem cartanChartMap_contDiffAt_two_of_expChart_contDiffAt_two
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsource :
      ContDiffAt ℝ 2
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).symm
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v))
    (htarget :
      ContDiffAt ℝ 2
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (L v)) :
    ContDiffAt ℝ 2 (CartanDifferential.cartanChartMap g x₀ p₀ L)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀
  have hleft : eM.symm (eM v) = v := eM.left_inv hvsrc
  have hL : ContDiffAt ℝ 2 (fun z : E3 => L z) (eM.symm (eM v)) := by
    simpa using (L.toContinuousLinearEquiv.contDiff (n := (2 : ℕ∞))).contDiffAt
  have hinner : ContDiffAt ℝ 2 (fun y : E3 => L (eM.symm y)) (eM v) := by
    simpa [Function.comp_def] using ContDiffAt.comp (eM v) hL hsource
  have htarget' : ContDiffAt ℝ 2 eS (L (eM.symm (eM v))) := by
    simpa [hleft] using htarget
  have hcomp : ContDiffAt ℝ 2 (fun y : E3 => eS (L (eM.symm y))) (eM v) := by
    simpa [Function.comp_def] using ContDiffAt.comp (eM v) htarget' hinner
  simpa [CartanDifferential.cartanChartMap, eM, eS] using hcomp

end ContDiffTwo
end Poincare
