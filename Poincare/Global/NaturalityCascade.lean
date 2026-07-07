import Poincare.Global.CartanChain
import Poincare.Global.ChainRuleInput

/-!
# Naturality cascade input from the unconditional re-anchor law

This module records the strict noncircular consequence now available from
`ChainRuleInput`: a Cartan chain state can re-anchor the source geodesic germ
and the aligned target geodesic germ in parallel, with no remaining velocity
chain-rule hypothesis.

The statement is deliberately one-dimensional.  Upgrading this paired germ
re-anchoring to `RigidStepCompatibleWith` still requires a separate theorem
showing that these shifted rays cover the full common normal-coordinate source
of the old and re-anchored Cartan germs.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace NaturalityCascade

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Parallel source/target re-anchoring for a Cartan chain state.

The source side is the old chain state's geodesic through `x₁`.  The target
side is the aligned round-sphere geodesic through `s.map x₁`.  Both conclusions
are direct uses of the unconditional re-anchor law, so the previous
velocity-chain-rule input is no longer part of the cascade surface.
-/
theorem source_target_shifted_geodesicGermAt_eventuallyEq_reanchored_unconditional
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (v₀ : E) (t₀ : ℝ)
    (ht_source :
      t₀ ∈ Ioo
        (-(GeodesicTransport.geodesicGermRadius g s.anchor v₀))
        (GeodesicTransport.geodesicGermRadius g s.anchor v₀))
    (hx₁ : GeodesicTransport.geodesicGermAt g s.anchor v₀ t₀ = x₁)
    (hsource_x_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          g s.anchor v₀ (t₀ + t)).1,
        q ∈ (extChartAt I s.anchor).target)
    (hsource_y_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          g s.anchor v₀ (t₀ + t)).1,
        (extChartAt I s.anchor).symm q ∈ (extChartAt I x₁).source)
    (hsource_cutoff_x : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          g s.anchor v₀ (t₀ + t)).1,
        GeodesicTransport.cutoff (n := 3) s.anchor q = 1)
    (hsource_cutoff_y : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          g s.anchor v₀ (t₀ + t)).1,
        GeodesicTransport.cutoff (n := 3) x₁
          (GeodesicTransport.chartTransition s.anchor x₁ q) = 1)
    (ht_target :
      t₀ ∈ Ioo
        (-(GeodesicTransport.geodesicGermRadius
          roundSphereMetric3 s.target (s.alignment v₀)))
        (GeodesicTransport.geodesicGermRadius
          roundSphereMetric3 s.target (s.alignment v₀)))
    (hp₁ :
      GeodesicTransport.geodesicGermAt
        roundSphereMetric3 s.target (s.alignment v₀) t₀ = s.map x₁)
    (htarget_x_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          roundSphereMetric3 s.target (s.alignment v₀) (t₀ + t)).1,
        q ∈ (extChartAt I s.target).target)
    (htarget_y_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          roundSphereMetric3 s.target (s.alignment v₀) (t₀ + t)).1,
        (extChartAt I s.target).symm q ∈
          (extChartAt I (s.map x₁)).source)
    (htarget_cutoff_x : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          roundSphereMetric3 s.target (s.alignment v₀) (t₀ + t)).1,
        GeodesicTransport.cutoff (n := 3) s.target q = 1)
    (htarget_cutoff_y : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in
        𝓝 (GeodesicTransport.geodesicGermChartSolution
          roundSphereMetric3 s.target (s.alignment v₀) (t₀ + t)).1,
        GeodesicTransport.cutoff (n := 3) (s.map x₁)
          (GeodesicTransport.chartTransition s.target (s.map x₁) q) = 1) :
    ((fun τ : ℝ =>
        GeodesicTransport.geodesicGermAt g s.anchor v₀ (t₀ + τ))
        =ᶠ[𝓝 (0 : ℝ)]
      GeodesicTransport.geodesicGermAt g x₁
        (GeodesicTransport.reanchoredVelocity g s.anchor x₁ v₀ t₀)) ∧
      ((fun τ : ℝ =>
          GeodesicTransport.geodesicGermAt
            roundSphereMetric3 s.target (s.alignment v₀) (t₀ + τ))
          =ᶠ[𝓝 (0 : ℝ)]
        GeodesicTransport.geodesicGermAt roundSphereMetric3 (s.map x₁)
          (GeodesicTransport.reanchoredVelocity
            roundSphereMetric3 s.target (s.map x₁) (s.alignment v₀) t₀)) := by
  constructor
  · exact
      GeodesicTransport.shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one_unconditional
        (g := g) (x₀ := s.anchor) (y₀ := x₁) (v₀ := v₀) (t₀ := t₀)
        ht_source hx₁ hsource_x_chart hsource_y_chart hsource_cutoff_x
        hsource_cutoff_y
  · exact
      GeodesicTransport.shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one_unconditional
        (g := roundSphereMetric3) (x₀ := s.target) (y₀ := s.map x₁)
        (v₀ := s.alignment v₀) (t₀ := t₀)
        ht_target hp₁ htarget_x_chart htarget_y_chart htarget_cutoff_x
        htarget_cutoff_y

end NaturalityCascade
end Poincare
