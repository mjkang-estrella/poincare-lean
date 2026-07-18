import Poincare.Global.CartanCanonicalFamilyLocalDataTransfer

/-!
# Germ comparison for the canonical round-sphere exponential family

The reference-normalized target exponential is used to obtain genuine joint
target-anchor regularity.  The classical Cartan continuation and rigidity
modules, however, are written using the generic round-sphere exponential.

The two target coordinate exponentials agree on a ball about zero at every
fixed target anchor.  Since the source normal coordinate tends to zero at its
anchor, every canonical-family Cartan map therefore agrees with the generic
Cartan map on a neighborhood of that source anchor.  This module records that
germ-level bridge without claiming global equality of the independently
constructed partial homeomorphisms.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanCanonicalFamilyGermComparison

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential

/-- Forget the canonical target-family tag while retaining the three
geometric fields of a Cartan state. -/
def canonicalToGenericState
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState canonicalFamily g) : CartanChain.ChainState g where
  anchor := s.anchor
  target := s.target
  alignment := s.alignment

@[simp]
theorem canonicalToGenericState_anchor
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState canonicalFamily g) :
    (canonicalToGenericState s).anchor = s.anchor :=
  rfl

@[simp]
theorem canonicalToGenericState_target
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState canonicalFamily g) :
    (canonicalToGenericState s).target = s.target :=
  rfl

/-- A canonical-target Cartan map and the corresponding generic Cartan map
agree on a neighborhood of their common source anchor. -/
theorem cartanMap_canonical_eventuallyEq_generic
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3)
    (L : CartanMap.TangentAlignment g x p) :
    cartanMap canonicalFamily g x p L =ᶠ[nhds x]
      CartanMap.cartanMap g x p L := by
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
  let sourceNormal : M → E := fun z ↦ eM.symm ((chartAt E x) z)
  let alignedNormal : M → E := fun z ↦ L (sourceNormal z)
  have htarget : (chartAt E x) x ∈ eM.target := by
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  have hchart : ContinuousAt (fun z : M ↦ (chartAt E x) z) x := by
    simpa [extChartAt_coe] using
      continuousAt_extChartAt («I» := I) x
  have hsourceContinuous : ContinuousAt sourceNormal x := by
    exact (eM.continuousAt_symm htarget).comp hchart
  have hsourceZero : sourceNormal x = (0 : E) := by
    simpa [sourceNormal, eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x
  have halignedContinuous : ContinuousAt alignedNormal x := by
    exact L.toContinuousLinearEquiv.continuous.continuousAt.comp
      hsourceContinuous
  have halignedZero : alignedNormal x = (0 : E) := by
    change L (sourceNormal x) = 0
    rw [hsourceZero, map_zero]
  rcases
      CartanCanonicalFamilyLocalDataTransfer.exists_genericFamily_chart_eq_canonicalFamily_on_ball
        p with
    ⟨radius, hradius, hcharts⟩
  have hnear : alignedNormal ⁻¹' Metric.ball (0 : E) radius ∈ nhds x := by
    apply halignedContinuous.preimage_mem_nhds
    rw [halignedZero]
    exact Metric.ball_mem_nhds (0 : E) hradius
  filter_upwards [hnear] with z hz
  have hnorm : ‖alignedNormal z‖ < radius := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have heq := hcharts (alignedNormal z) hnorm
  change
    (chartAt E p).symm (canonicalFamily.chart p (alignedNormal z)) =
      (chartAt E p).symm (genericFamily.chart p (alignedNormal z))
  rw [heq]

/-- State form of the canonical/generic germ comparison. -/
theorem canonicalState_map_eventuallyEq_genericState
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState canonicalFamily g) :
    s.map =ᶠ[nhds s.anchor] (canonicalToGenericState s).map := by
  simpa [ChainState.map, CartanChain.ChainState.map,
    canonicalToGenericState] using
    cartanMap_canonical_eventuallyEq_generic
      g s.anchor s.target s.alignment

/-- In particular, the canonical and generic maps have the same value at the
anchor, stated through the germ comparison rather than recomputed. -/
theorem canonicalState_map_anchor_eq_genericState
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState canonicalFamily g) :
    s.map s.anchor = (canonicalToGenericState s).map s.anchor :=
  (canonicalState_map_eventuallyEq_genericState s).self_of_nhds

end CartanCanonicalFamilyGermComparison
end Poincare
