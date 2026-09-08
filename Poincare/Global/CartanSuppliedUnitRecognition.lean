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

/-- Compact covering recognition applies to the supplied developing map. -/
theorem controlled_unitRecognition : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitConstantCurvatureSphereRecognition3 M := by
  intro d hd hc
  exact RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment
    (controlled_globalLocalDevelopment d hd hc)

/-- Recognition on a compatible controlled atlas transfers to the original atlas. -/
theorem unitRecognition : UnitConstantCurvatureSphereRecognition3 M := by
  intro g hcurv
  let d : MetricSpace M := g.toMetricSpace
  have hd : d.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M) := rfl
  obtain ⟨charts, δ, hδ, hball, hfinite, _hsub, hs, hrecognition⟩ :=
    ConnectionInstanceNaturality.exists_controlled_recognition_reduction' (inst := inst) d hd
  letI : ChartedSpace E M := charts
  letI : IsManifold I ∞ M := hs
  have hc : Controlled charts (d.replaceTopology hd.symm) :=
    ⟨hfinite, δ, hδ, hball⟩
  have hunit : UnitConstantCurvatureSphereRecognition3 M :=
    controlled_unitRecognition (d.replaceTopology hd.symm) rfl hc
  exact hrecognition hunit g hcurv

/-- Unit-curvature recognition holds over every closed simply connected smooth 3-manifold. -/
theorem universal_unitRecognition :
  CartanTwoNeighborhoodDevelopment.UniversalUnitConstantCurvatureSphereRecognitionStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  exact unitRecognition (M := N)

/-- Hamilton convergence is the remaining premise of this Poincare implication. -/
theorem poincare_of_hamiltonConvergence :
  (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonConvergencePinchedLimit3 N) → PoincareConjecture.{u} := by
  intro hHamilton
  exact poincareConjecture_of_hamiltonConvergence_of_unitRecognition
    hHamilton universal_unitRecognition

end CartanSuppliedUnitRecognition
end Poincare
