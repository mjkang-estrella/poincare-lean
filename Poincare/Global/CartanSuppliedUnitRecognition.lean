import Poincare.Global.CartanSuppliedRestrictedDevelopment
import Poincare.Global.ConnectionInstanceNaturality
import Poincare.Global.CartanTwoNeighborhoodDevelopment

/-!
# Unit-curvature recognition from supplied Cartan development

The supplied patch construction gives a total local homeomorphism to the round
sphere. Recognition transfers through a finite controlled atlas to the original
smooth structure. The final Poincare implication retains Hamilton convergence.
-/

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

namespace CartanSuppliedUnitRecognition
open CartanSuppliedFinitePatchCover CartanSuppliedUniformPatchSwitch
open CartanSuppliedWholeCellRealization CartanSuppliedRestrictedDevelopment
variable [SecondCountableTopology M] [SimplyConnectedSpace M]

/-- Supplied rooted endpoints discharge the controlled developing-map interface.
The finite patch refinement itself works for every smooth chart instance. -/
theorem controlled_globalLocalDevelopment : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitRecognitionNext.UnitCurvatureGlobalLocalDevelopment3 (M := M) := by
  intro _d _hd _hcontrolled g hcurv
  obtain ⟨B⟩ := exists_quantitativeCover hcurv
  obtain ⟨switch⟩ := exists_switchControl hcurv B
  let S : System g := ⟨B, switch⟩
  obtain ⟨sk⟩ := CartanAtlasRootedPathSkeleton.nonempty_rootedCartanPathSkeleton g
  obtain ⟨R⟩ := exists_rootedRealization_with_wholeCellMesh S sk
  exact ⟨development R, isLocalHomeomorph_development S sk R⟩

end CartanSuppliedUnitRecognition
end Poincare
