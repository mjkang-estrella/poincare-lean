import Poincare.Global.CartanCascade
import Poincare.Global.CartanHomogeneity
import Poincare.Global.SourcePackage

/-!
# Cartan isometry instantiation boundary

This module records the reusable interval/germ conversions needed by the final
source/target feed instantiation.  They are deliberately small: the remaining
blocked package field is documented in `harness/reports/M5-rigid-64_blocked.md`.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace IsometryInstantiate

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The chart points where the geodesic-transport cutoff is germ-equal to one. -/
def cutoffOneLocus (x₀ : M) : Set E :=
  {z | ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1}

omit [T2Space M] in
/-- The cutoff-one locus is available at the anchor as a neighborhood. -/
theorem cutoffOneLocus_mem_nhds_anchor (x₀ : M) :
    cutoffOneLocus x₀ ∈ 𝓝 (extChartAt I x₀ x₀) := by
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hanchor : (extChartAt I x₀ x₀) ∈ oneLocus := by
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x₀)
  simpa [cutoffOneLocus, oneLocus] using hopen.mem_nhds hanchor

omit [T2Space M] in
/-- Membership in the cutoff-one locus is exactly the germ hypothesis packages need. -/
theorem cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
    {x₀ : M} {z : E} (hz : z ∈ cutoffOneLocus x₀) :
    ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1 :=
  hz

/--
Upgrade a within-derivative on a larger closed interval to an ordinary
derivative at a point lying in the interior of that interval.
-/
theorem hasDerivAt_of_hasDerivWithinAt_larger_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {a b t : ℝ}
    (hder : HasDerivWithinAt f f' (Icc a b) t)
    (ha : a < t) (hb : t < b) :
    HasDerivAt f f' t :=
  hder.hasDerivAt (Icc_mem_nhds ha hb)

/--
Family form of `hasDerivAt_of_hasDerivWithinAt_larger_Icc`, for a whole
closed interval strictly contained in the larger interval.
-/
theorem hasDerivAt_on_Icc_of_hasDerivWithinAt_on_larger_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : ℝ → F} {a b c d : ℝ}
    (hac : a < c) (hdb : d < b)
    (hder : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t) :
    ∀ t ∈ Icc c d, HasDerivAt f (f' t) t := by
  intro t ht
  exact
    hasDerivAt_of_hasDerivWithinAt_larger_Icc
      (hder t ⟨hac.le.trans ht.1, ht.2.trans hdb.le⟩)
      (lt_of_lt_of_le hac ht.1) (lt_of_le_of_lt ht.2 hdb)

omit [T2Space M] in
/-- Source-side geodesic-flow derivative upgrade on a strictly smaller interval. -/
theorem geodesicFlow_hasDerivAt_on_shrunk_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {a b c d : ℝ}
    (hac : a < c) (hdb : d < b)
    (hγ : ∀ t ∈ Icc a b,
      HasDerivWithinAt γ
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x₀) (γ t))
        (Icc a b) t) :
    ∀ t ∈ Icc c d,
      HasDerivAt γ
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x₀) (γ t)) t :=
  hasDerivAt_on_Icc_of_hasDerivWithinAt_on_larger_Icc hac hdb hγ

omit [T2Space M] in
/-- Source-side linearized-flow derivative upgrade on a strictly smaller interval. -/
theorem linearizedFlow_hasDerivAt_on_shrunk_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {Ψ : E → ℝ → E × E} {a b c d : ℝ}
    (hac : a < c) (hdb : d < b)
    (hΨ : ∀ w : E, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t (Ψ w t))
        (Icc a b) t) :
    ∀ w : E, ∀ t ∈ Icc c d,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t (Ψ w t)) t := by
  intro w
  exact hasDerivAt_on_Icc_of_hasDerivWithinAt_on_larger_Icc hac hdb (hΨ w)

end IsometryInstantiate
end Poincare
