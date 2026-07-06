import Poincare.Global.GeodesicSpeed
import Poincare.Global.ExponentialRayLaw

/-!
# Radial-radial Gauss lemma input

This module records the part of the Gauss lemma that does not need a
two-parameter variation theorem.  Along the geodesic germ ray, the chart
velocity is the derivative of the chart position and its blended-metric norm is
constant by `Poincare.Global.GeodesicSpeed`.  The fixed-time exponential map is
then tied to the same ray by the exported `expAt`/`geodesicGermAt` germ law.

The transverse Gauss lemma would require differentiating geodesic solutions
with respect to the initial velocity.  The concrete missing ODE-dependence
package is isolated below as
`ChartGeodesicInitialVelocitySmoothDependence`; it is an explicit hypothesis
interface, not a postulate and not used to manufacture a theorem in this file.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Near `0`, the velocity component of the chosen first-order chart geodesic is
the derivative of its chart-position component.
-/
theorem geodesicGermChartSolution_position_hasDerivAt_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
        (fun τ : ℝ => (geodesicGermChartSolution g x₀ v₀ τ).1)
        (geodesicGermChartSolution g x₀ v₀ t).2 t := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  have hε := geodesicGermRadius_pos g x₀ v₀
  have hI :
      Ioo (-(geodesicGermRadius g x₀ v₀))
          (geodesicGermRadius g x₀ v₀) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hI] with t ht
  exact
    geodesic_position_hasDerivAt
      (Γ := chartChristoffelField g x₀)
      (γ := geodesicGermChartSolution g x₀ v₀)
      (hspec.2.1 t ht)

/--
Radial-radial Gauss identity for the chosen geodesic germ in the anchor chart:
the chart ray has derivative equal to its velocity component, and the
blended-metric speed of that derivative equals the initial speed.
-/
theorem geodesicGermChart_radialRadial_gauss_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
          (fun τ : ℝ => (geodesicGermChartSolution g x₀ v₀ τ).1)
          (geodesicGermChartSolution g x₀ v₀ t).2 t ∧
        chartGeodesicMetric g x₀
            (geodesicGermChartSolution g x₀ v₀ t).1
            (geodesicGermChartSolution g x₀ v₀ t).2
            (geodesicGermChartSolution g x₀ v₀ t).2 =
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀ := by
  filter_upwards
    [geodesicGermChartSolution_position_hasDerivAt_eventually
      (g := g) (x₀ := x₀) (v₀ := v₀),
     geodesicGermChartSolution_speed_eventually_eq_initial
      (g := g) (x₀ := x₀) (v₀ := v₀)] with t hder hspeed
  exact ⟨hder, hspeed⟩

/--
Radial-radial Gauss identity on the honest right-hand `expAt` ray germ.

For sufficiently small initial velocities, the fixed-time exponential ray
`t ↦ expAt g x₀ (t • v₀)` agrees with `geodesicGermAt g x₀ v₀ t` as a
right-germ at `0`; on that same germ, the chart representative has constant
blended-metric speed equal to the initial speed at the anchor.
-/
theorem expAt_radialRadial_gauss_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ v₀ : E, ‖v₀‖ < δ →
      ∀ᶠ t in 𝓝[Icc (0 : ℝ) τ] (0 : ℝ),
        expAt g x₀ (t • v₀) = geodesicGermAt g x₀ v₀ t ∧
          HasDerivAt
              (fun σ : ℝ => (geodesicGermChartSolution g x₀ v₀ σ).1)
              (geodesicGermChartSolution g x₀ v₀ t).2 t ∧
            chartGeodesicMetric g x₀
                (geodesicGermChartSolution g x₀ v₀ t).1
                (geodesicGermChartSolution g x₀ v₀ t).2
                (geodesicGermChartSolution g x₀ v₀ t).2 =
              chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀ := by
  rcases expAt_eventually_eq_geodesicGermAt (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, hray⟩
  refine ⟨τ, hτ, δ, hδ, fun v₀ hv₀ => ?_⟩
  have hradial :
      ∀ᶠ t in 𝓝[Icc (0 : ℝ) τ] (0 : ℝ),
        HasDerivAt
            (fun σ : ℝ => (geodesicGermChartSolution g x₀ v₀ σ).1)
            (geodesicGermChartSolution g x₀ v₀ t).2 t ∧
          chartGeodesicMetric g x₀
              (geodesicGermChartSolution g x₀ v₀ t).1
              (geodesicGermChartSolution g x₀ v₀ t).2
              (geodesicGermChartSolution g x₀ v₀ t).2 =
            chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀ :=
    (geodesicGermChart_radialRadial_gauss_eventually
      (g := g) (x₀ := x₀) (v₀ := v₀)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hray v₀ hv₀, hradial] with t hExp hGauss
  exact ⟨hExp, hGauss⟩

/--
Concrete ODE-dependence interface needed for the transverse Gauss lemma.

It asks for one chart-flow family, smooth in the initial velocity and time on
a common small velocity ball and time interval, whose time slices solve the
first-order chart geodesic equation with the expected initial state.  This is
the missing ingredient for differentiating the constant-speed identity in the
initial-velocity parameter and commuting the time/parameter derivatives.
-/
def ChartGeodesicInitialVelocitySmoothDependence
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : Prop :=
  ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E → ℝ → E × E,
    (∀ v₀ : E, ‖v₀‖ < δ →
      Φ v₀ 0 = (extChartAt I x₀ x₀, v₀)) ∧
    (∀ v₀ : E, ‖v₀‖ < δ →
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (Φ v₀)
          (geodesicFlowField (chartChristoffelField g x₀) (Φ v₀ t)) t) ∧
    ContDiffOn ℝ 2 (Function.uncurry Φ)
      (Metric.ball (0 : E) δ ×ˢ Ioo (-ε) ε)

end GeodesicTransport
end Poincare
