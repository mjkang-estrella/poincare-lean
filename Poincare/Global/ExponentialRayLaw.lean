import Poincare.Global.ExponentialFixedTime

/-!
# Ray-law consequences for the fixed-time exponential map

This file records what follows downstream from the currently exported
fixed-time package for `expAt`: the right-neighborhood ray law at the origin
and the corresponding chart right derivative for small velocities.

The closed-interval ray law needs a stronger exported package tying the chosen
`expAt` witness to a full-interval PL-flow/germ identification; see the
M5-geo-12 report.
-/

noncomputable section

open Filter Set
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
The exported `Icc`-within eventual ray law is a genuine right-neighborhood
ray law at `0`.
-/
theorem expAt_eventually_eq_geodesicGermAt_nhdsGE
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ v : E, ‖v‖ < δ →
        (fun t : ℝ => expAt g x₀ (t • v))
          =ᶠ[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
        (fun t : ℝ => geodesicGermAt g x₀ v t) := by
  rcases expAt_eventually_eq_geodesicGermAt (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, hray⟩
  refine ⟨τ, hτ, δ, hδ, fun v hv ↦ ?_⟩
  have hIcc_mem :
      Set.Icc (0 : ℝ) τ ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) := by
    simpa using (Icc_mem_nhdsGE hτ)
  have hle :
      𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) ≤
        𝓝[Set.Icc (0 : ℝ) τ] (0 : ℝ) := by
    exact (nhdsWithin_le_iff).2 hIcc_mem
  exact (hray v hv).filter_mono hle

/--
For small chart velocities, `expAt` has the expected right derivative at the
anchor after applying the anchor chart.
-/
theorem expAt_chart_hasDerivWithinAt_of_norm_lt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ v : E, ‖v‖ < δ →
        HasDerivWithinAt
          (fun t : ℝ => extChartAt I x₀ (expAt g x₀ (t • v)))
          v (Set.Ici (0 : ℝ)) (0 : ℝ) := by
  rcases expAt_eventually_eq_geodesicGermAt_nhdsGE
      (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, hray⟩
  refine ⟨τ, hτ, δ, hδ, fun v hv ↦ ?_⟩
  have hchart :
      (fun t : ℝ => extChartAt I x₀ (expAt g x₀ (t • v)))
        =ᶠ[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
      (fun t : ℝ => extChartAt I x₀ (geodesicGermAt g x₀ v t)) := by
    filter_upwards [hray v hv] with t ht
    rw [ht]
  have hgerm :
      HasDerivWithinAt
        (fun t : ℝ => extChartAt I x₀ (geodesicGermAt g x₀ v t))
        v (Set.Ici (0 : ℝ)) (0 : ℝ) :=
    (geodesicGermAt_chart_hasDerivAt (g := g) (x₀ := x₀) (v₀ := v)).hasDerivWithinAt
  refine hgerm.congr_of_eventuallyEq hchart ?_
  simp

end GeodesicTransport
end Poincare
