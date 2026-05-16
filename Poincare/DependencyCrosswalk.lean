/-
Crosswalk between the milestone ledger and the executable dependency package.

The milestone ledger is intentionally data-only. This module records, in Lean,
which concrete package layer is intended to discharge each milestone.
-/

import Poincare.Dependencies
import Poincare.Milestones

universe u

open scoped Manifold ContDiff

namespace Poincare

/-- Concrete dependency-package layer associated to a milestone. -/
inductive DependencyPackageLayer where
  /-- `Poincare.AnalyticFoundation`: curvature and PDE foundations for Ricci flow. -/
  | analyticFoundationPackage
  /-- `Poincare.Surgery`: surgery construction and Perelman control interfaces. -/
  | surgeryPackage
  /-- `Poincare.Surgery`: finite-extinction derivation and conclusion. -/
  | finiteExtinctionPackage
  /-- `Poincare.TopologyExtraction`: post-extinction recognition and homeomorphism extraction. -/
  | topologyPackage
  /-- `Poincare.Smoothability`: topological-to-smooth bridge for the surgery model. -/
  | smoothabilityPackage
  deriving DecidableEq, Repr

/--
The three aggregate component slots carried by `PoincareProofDependencies`.
Several package layers are implemented inside the same aggregate component.
-/
inductive DependencyComponentSlot where
  /-- The smoothability component of the aggregate dependency package. -/
  | smoothabilityComponent
  /-- The target-family surgery component, including analytic and Perelman inputs. -/
  | surgeryComponent
  /-- The post-extinction topology extraction component. -/
  | topologyComponent
  deriving DecidableEq, Repr

/-- Map each milestone to the concrete package layer intended to discharge it. -/
def dependencyLayerForMilestone : DependencyMilestone → DependencyPackageLayer
  | DependencyMilestone.smoothabilityBridge =>
      DependencyPackageLayer.smoothabilityPackage
  | DependencyMilestone.ricciFlowAnalyticFoundation =>
      DependencyPackageLayer.analyticFoundationPackage
  | DependencyMilestone.ricciFlowWithSurgery =>
      DependencyPackageLayer.surgeryPackage
  | DependencyMilestone.perelmanSingularityControl =>
      DependencyPackageLayer.surgeryPackage
  | DependencyMilestone.finiteExtinction =>
      DependencyPackageLayer.finiteExtinctionPackage
  | DependencyMilestone.extinctionToSphereHomeomorphism =>
      DependencyPackageLayer.topologyPackage

/-- The milestone-to-package-layer map is exactly the explicit six-case ledger map. -/
theorem dependencyLayerForMilestone_eq :
    dependencyLayerForMilestone =
      (fun
        | DependencyMilestone.smoothabilityBridge =>
            DependencyPackageLayer.smoothabilityPackage
        | DependencyMilestone.ricciFlowAnalyticFoundation =>
            DependencyPackageLayer.analyticFoundationPackage
        | DependencyMilestone.ricciFlowWithSurgery =>
            DependencyPackageLayer.surgeryPackage
        | DependencyMilestone.perelmanSingularityControl =>
            DependencyPackageLayer.surgeryPackage
        | DependencyMilestone.finiteExtinction =>
            DependencyPackageLayer.finiteExtinctionPackage
        | DependencyMilestone.extinctionToSphereHomeomorphism =>
            DependencyPackageLayer.topologyPackage) :=
  rfl

/-- Map each package layer to the aggregate dependency component that carries it. -/
def dependencyComponentForPackageLayer :
    DependencyPackageLayer → DependencyComponentSlot
  | DependencyPackageLayer.smoothabilityPackage =>
      DependencyComponentSlot.smoothabilityComponent
  | DependencyPackageLayer.analyticFoundationPackage =>
      DependencyComponentSlot.surgeryComponent
  | DependencyPackageLayer.surgeryPackage =>
      DependencyComponentSlot.surgeryComponent
  | DependencyPackageLayer.finiteExtinctionPackage =>
      DependencyComponentSlot.surgeryComponent
  | DependencyPackageLayer.topologyPackage =>
      DependencyComponentSlot.topologyComponent

/-- The package-layer-to-component map is exactly the explicit five-case fold. -/
theorem dependencyComponentForPackageLayer_eq :
    dependencyComponentForPackageLayer =
      (fun
        | DependencyPackageLayer.smoothabilityPackage =>
            DependencyComponentSlot.smoothabilityComponent
        | DependencyPackageLayer.analyticFoundationPackage =>
            DependencyComponentSlot.surgeryComponent
        | DependencyPackageLayer.surgeryPackage =>
            DependencyComponentSlot.surgeryComponent
        | DependencyPackageLayer.finiteExtinctionPackage =>
            DependencyComponentSlot.surgeryComponent
        | DependencyPackageLayer.topologyPackage =>
            DependencyComponentSlot.topologyComponent) :=
  rfl

/-- Map each milestone directly to the aggregate component slot that carries it. -/
def dependencyComponentForMilestone :
    DependencyMilestone → DependencyComponentSlot :=
  fun milestone =>
    dependencyComponentForPackageLayer (dependencyLayerForMilestone milestone)

/--
The direct milestone-to-component map is exactly the composition of the
milestone-to-layer and layer-to-component maps.
-/
theorem dependencyComponentForMilestone_eq :
    dependencyComponentForMilestone =
      fun milestone =>
        dependencyComponentForPackageLayer (dependencyLayerForMilestone milestone) :=
  rfl

/-- The smoothability package layer is carried by the smoothability component. -/
theorem dependencyComponentForPackageLayer_smoothabilityPackage :
    dependencyComponentForPackageLayer DependencyPackageLayer.smoothabilityPackage =
      DependencyComponentSlot.smoothabilityComponent :=
  rfl

/-- The analytic-foundation package layer is carried by the surgery component. -/
theorem dependencyComponentForPackageLayer_analyticFoundationPackage :
    dependencyComponentForPackageLayer DependencyPackageLayer.analyticFoundationPackage =
      DependencyComponentSlot.surgeryComponent :=
  rfl

/-- The surgery package layer is carried by the surgery component. -/
theorem dependencyComponentForPackageLayer_surgeryPackage :
    dependencyComponentForPackageLayer DependencyPackageLayer.surgeryPackage =
      DependencyComponentSlot.surgeryComponent :=
  rfl

/-- The finite-extinction package layer is carried by the surgery component. -/
theorem dependencyComponentForPackageLayer_finiteExtinctionPackage :
    dependencyComponentForPackageLayer DependencyPackageLayer.finiteExtinctionPackage =
      DependencyComponentSlot.surgeryComponent :=
  rfl

/-- The topology package layer is carried by the topology component. -/
theorem dependencyComponentForPackageLayer_topologyPackage :
    dependencyComponentForPackageLayer DependencyPackageLayer.topologyPackage =
      DependencyComponentSlot.topologyComponent :=
  rfl

/-- The smoothability package-layer component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForPackageLayer_smoothabilityPackage_eq :
    dependencyComponentForPackageLayer_smoothabilityPackage =
      (rfl :
        dependencyComponentForPackageLayer DependencyPackageLayer.smoothabilityPackage =
          DependencyComponentSlot.smoothabilityComponent) :=
  rfl

/-- The analytic package-layer component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForPackageLayer_analyticFoundationPackage_eq :
    dependencyComponentForPackageLayer_analyticFoundationPackage =
      (rfl :
        dependencyComponentForPackageLayer
            DependencyPackageLayer.analyticFoundationPackage =
          DependencyComponentSlot.surgeryComponent) :=
  rfl

/-- The surgery package-layer component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForPackageLayer_surgeryPackage_eq :
    dependencyComponentForPackageLayer_surgeryPackage =
      (rfl :
        dependencyComponentForPackageLayer DependencyPackageLayer.surgeryPackage =
          DependencyComponentSlot.surgeryComponent) :=
  rfl

/-- The finite-extinction package-layer component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForPackageLayer_finiteExtinctionPackage_eq :
    dependencyComponentForPackageLayer_finiteExtinctionPackage =
      (rfl :
        dependencyComponentForPackageLayer
            DependencyPackageLayer.finiteExtinctionPackage =
          DependencyComponentSlot.surgeryComponent) :=
  rfl

/-- The topology package-layer component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForPackageLayer_topologyPackage_eq :
    dependencyComponentForPackageLayer_topologyPackage =
      (rfl :
        dependencyComponentForPackageLayer DependencyPackageLayer.topologyPackage =
          DependencyComponentSlot.topologyComponent) :=
  rfl

/-- The smoothability milestone is carried by the smoothability component. -/
theorem dependencyComponentForMilestone_smoothabilityBridge :
    dependencyComponentForMilestone DependencyMilestone.smoothabilityBridge =
      DependencyComponentSlot.smoothabilityComponent :=
  rfl

/-- The analytic-foundation milestone is carried by the surgery component. -/
theorem dependencyComponentForMilestone_ricciFlowAnalyticFoundation :
    dependencyComponentForMilestone DependencyMilestone.ricciFlowAnalyticFoundation =
      DependencyComponentSlot.surgeryComponent :=
  rfl

/-- The Ricci-flow-with-surgery milestone is carried by the surgery component. -/
theorem dependencyComponentForMilestone_ricciFlowWithSurgery :
    dependencyComponentForMilestone DependencyMilestone.ricciFlowWithSurgery =
      DependencyComponentSlot.surgeryComponent :=
  rfl

/-- The Perelman-control milestone is carried by the surgery component. -/
theorem dependencyComponentForMilestone_perelmanSingularityControl :
    dependencyComponentForMilestone DependencyMilestone.perelmanSingularityControl =
      DependencyComponentSlot.surgeryComponent :=
  rfl

/-- The finite-extinction milestone is carried by the surgery component. -/
theorem dependencyComponentForMilestone_finiteExtinction :
    dependencyComponentForMilestone DependencyMilestone.finiteExtinction =
      DependencyComponentSlot.surgeryComponent :=
  rfl

/-- The post-extinction topology milestone is carried by the topology component. -/
theorem dependencyComponentForMilestone_extinctionToSphereHomeomorphism :
    dependencyComponentForMilestone DependencyMilestone.extinctionToSphereHomeomorphism =
      DependencyComponentSlot.topologyComponent :=
  rfl

/-- The smoothability milestone component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForMilestone_smoothabilityBridge_eq :
    dependencyComponentForMilestone_smoothabilityBridge =
      (rfl :
        dependencyComponentForMilestone DependencyMilestone.smoothabilityBridge =
          DependencyComponentSlot.smoothabilityComponent) :=
  rfl

/-- The analytic-foundation milestone component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForMilestone_ricciFlowAnalyticFoundation_eq :
    dependencyComponentForMilestone_ricciFlowAnalyticFoundation =
      (rfl :
        dependencyComponentForMilestone
            DependencyMilestone.ricciFlowAnalyticFoundation =
          DependencyComponentSlot.surgeryComponent) :=
  rfl

/-- The Ricci-flow-with-surgery milestone component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForMilestone_ricciFlowWithSurgery_eq :
    dependencyComponentForMilestone_ricciFlowWithSurgery =
      (rfl :
        dependencyComponentForMilestone DependencyMilestone.ricciFlowWithSurgery =
          DependencyComponentSlot.surgeryComponent) :=
  rfl

/-- The Perelman-control milestone component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForMilestone_perelmanSingularityControl_eq :
    dependencyComponentForMilestone_perelmanSingularityControl =
      (rfl :
        dependencyComponentForMilestone
            DependencyMilestone.perelmanSingularityControl =
          DependencyComponentSlot.surgeryComponent) :=
  rfl

/-- The finite-extinction milestone component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForMilestone_finiteExtinction_eq :
    dependencyComponentForMilestone_finiteExtinction =
      (rfl :
        dependencyComponentForMilestone DependencyMilestone.finiteExtinction =
          DependencyComponentSlot.surgeryComponent) :=
  rfl

/-- The topology-extraction milestone component theorem is the direct `rfl` proof. -/
theorem dependencyComponentForMilestone_extinctionToSphereHomeomorphism_eq :
    dependencyComponentForMilestone_extinctionToSphereHomeomorphism =
      (rfl :
        dependencyComponentForMilestone
            DependencyMilestone.extinctionToSphereHomeomorphism =
          DependencyComponentSlot.topologyComponent) :=
  rfl

/-- The proposition represented by each aggregate dependency component slot. -/
def dependencyComponentRequirement : DependencyComponentSlot → Prop
  | DependencyComponentSlot.smoothabilityComponent =>
      SmoothabilityPackage.{u}
  | DependencyComponentSlot.surgeryComponent =>
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)
  | DependencyComponentSlot.topologyComponent =>
      ExtinctionTopologyExtractionPackage.{u}

/-- The component-slot requirement map is exactly the explicit three-case map. -/
theorem dependencyComponentRequirement_eq :
    dependencyComponentRequirement.{u} =
      (fun
        | DependencyComponentSlot.smoothabilityComponent =>
            SmoothabilityPackage.{u}
        | DependencyComponentSlot.surgeryComponent =>
            ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
              [ChartedSpace ThreeManifoldModel M]
              [SimplyConnectedSpace M] [CompactSpace M]
              [IsManifold ThreeManifoldModelWithCorners 1 M],
                Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)
        | DependencyComponentSlot.topologyComponent =>
            ExtinctionTopologyExtractionPackage.{u}) :=
  rfl

/-- The smoothability component requirement is the smoothability package. -/
theorem dependencyComponentRequirement_smoothabilityComponent :
    dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent =
      SmoothabilityPackage.{u} :=
  rfl

/-- The surgery component requirement is the target-family surgery package. -/
theorem dependencyComponentRequirement_surgeryComponent :
    dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :=
  rfl

/-- The topology component requirement is the topology extraction package. -/
theorem dependencyComponentRequirement_topologyComponent :
    dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent =
      ExtinctionTopologyExtractionPackage.{u} :=
  rfl

/-- The smoothability component requirement theorem is the direct `rfl` proof. -/
theorem dependencyComponentRequirement_smoothabilityComponent_eq :
    dependencyComponentRequirement_smoothabilityComponent.{u} =
      (rfl :
        dependencyComponentRequirement.{u}
            DependencyComponentSlot.smoothabilityComponent =
          SmoothabilityPackage.{u}) := by
  apply Subsingleton.elim

/-- The surgery component requirement theorem is the direct `rfl` proof. -/
theorem dependencyComponentRequirement_surgeryComponent_eq :
    dependencyComponentRequirement_surgeryComponent.{u} =
      (rfl :
        dependencyComponentRequirement.{u}
            DependencyComponentSlot.surgeryComponent =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              Nonempty (Σ n : ℕ∞ω,
                FiniteExtinctionSurgeryPackage n M))) := by
  apply Subsingleton.elim

/-- The topology component requirement theorem is the direct `rfl` proof. -/
theorem dependencyComponentRequirement_topologyComponent_eq :
    dependencyComponentRequirement_topologyComponent.{u} =
      (rfl :
        dependencyComponentRequirement.{u}
            DependencyComponentSlot.topologyComponent =
          ExtinctionTopologyExtractionPackage.{u}) := by
  apply Subsingleton.elim

/-- A completed aggregate dependency package supplies every component-slot requirement. -/
theorem dependencyComponentRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (slot : DependencyComponentSlot) :
    dependencyComponentRequirement.{u} slot := by
  cases slot
  · exact dependencies.smoothability
  · exact dependencies.surgery
  · exact dependencies.topology

/--
The generic component-slot projection from dependencies is exactly the
destructor that returns the stored field for the requested component slot.
-/
theorem dependencyComponentRequirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyComponentRequirement_of_dependencies dependencies =
      (fun
        | DependencyComponentSlot.smoothabilityComponent =>
            dependencies.smoothability
        | DependencyComponentSlot.surgeryComponent =>
            dependencies.surgery
        | DependencyComponentSlot.topologyComponent =>
            dependencies.topology) := by
  funext slot
  cases slot <;> apply Subsingleton.elim

/--
The generic smoothability component projection is the stored smoothability
field.
-/
theorem dependencyComponentRequirement_of_dependencies_smoothabilityComponent_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyComponentRequirement_of_dependencies dependencies
      DependencyComponentSlot.smoothabilityComponent =
      dependencies.smoothability :=
  rfl

/-- The generic surgery component projection is the stored surgery field. -/
theorem dependencyComponentRequirement_of_dependencies_surgeryComponent_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyComponentRequirement_of_dependencies dependencies
      DependencyComponentSlot.surgeryComponent =
      dependencies.surgery :=
  rfl

/-- The generic topology component projection is the stored topology field. -/
theorem dependencyComponentRequirement_of_dependencies_topologyComponent_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyComponentRequirement_of_dependencies dependencies
      DependencyComponentSlot.topologyComponent =
      dependencies.topology :=
  rfl

/-- Aggregate dependencies supply the smoothability component requirement. -/
theorem smoothabilityComponent_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyComponentRequirement.{u}
      DependencyComponentSlot.smoothabilityComponent := by
  exact dependencyComponentRequirement_of_dependencies dependencies
    DependencyComponentSlot.smoothabilityComponent

/-- Aggregate dependencies supply the surgery component requirement. -/
theorem surgeryComponent_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent := by
  exact dependencyComponentRequirement_of_dependencies dependencies
    DependencyComponentSlot.surgeryComponent

/-- Aggregate dependencies supply the topology component requirement. -/
theorem topologyComponent_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent := by
  exact dependencyComponentRequirement_of_dependencies dependencies
    DependencyComponentSlot.topologyComponent

/--
The smoothability component projection is the generic component-slot projection
at the smoothability component.
-/
theorem smoothabilityComponent_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothabilityComponent_requirement_of_dependencies dependencies =
      dependencyComponentRequirement_of_dependencies dependencies
        DependencyComponentSlot.smoothabilityComponent :=
  rfl

/--
The surgery component projection is the generic component-slot projection at the
surgery component.
-/
theorem surgeryComponent_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgeryComponent_requirement_of_dependencies dependencies =
      dependencyComponentRequirement_of_dependencies dependencies
        DependencyComponentSlot.surgeryComponent :=
  rfl

/--
The topology component projection is the generic component-slot projection at
the topology component.
-/
theorem topologyComponent_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topologyComponent_requirement_of_dependencies dependencies =
      dependencyComponentRequirement_of_dependencies dependencies
        DependencyComponentSlot.topologyComponent :=
  rfl

/-- The named smoothability component projection is the stored smoothability field. -/
theorem smoothabilityComponent_requirement_of_dependencies_to_field_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothabilityComponent_requirement_of_dependencies dependencies =
      dependencies.smoothability :=
  rfl

/-- The named surgery component projection is the stored surgery field. -/
theorem surgeryComponent_requirement_of_dependencies_to_field_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgeryComponent_requirement_of_dependencies dependencies =
      dependencies.surgery :=
  rfl

/-- The named topology component projection is the stored topology field. -/
theorem topologyComponent_requirement_of_dependencies_to_field_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topologyComponent_requirement_of_dependencies dependencies =
      dependencies.topology :=
  rfl

/--
A completed aggregate dependency package supplies the requirements for exactly
the three aggregate component slots.
-/
theorem dependency_component_requirements_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _smoothability :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent := by
  exact
    ⟨ smoothabilityComponent_requirement_of_dependencies dependencies
    , surgeryComponent_requirement_of_dependencies dependencies
    , topologyComponent_requirement_of_dependencies dependencies
    ⟩

/--
The aggregate dependency component-slot payload is the tuple of the stored
component fields under the component-slot requirement aliases.
-/
theorem dependency_component_requirements_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_component_requirements_payload_of_dependencies dependencies =
      ⟨dependencies.smoothability, dependencies.surgery,
        dependencies.topology⟩ := by
  apply Subsingleton.elim

/--
The aggregate dependency component-slot payload is also the tuple of the named
component-slot projections.
-/
theorem dependency_component_requirements_payload_of_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_component_requirements_payload_of_dependencies dependencies =
      ⟨ smoothabilityComponent_requirement_of_dependencies dependencies
      , surgeryComponent_requirement_of_dependencies dependencies
      , topologyComponent_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies supply every existing component-slot
requirement after forgetting the explicit equation-boundary data.
-/
theorem dependencyComponentRequirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (slot : DependencyComponentSlot) :
    dependencyComponentRequirement.{u} slot :=
  dependencyComponentRequirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies) slot

/--
The strengthened dependency component-slot projection is the ordinary
component-slot projection applied to the forgetful dependency package.
-/
theorem dependencyComponentRequirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyComponentRequirement_of_equation_boundary_dependencies
        dependencies =
      dependencyComponentRequirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  funext slot
  apply Subsingleton.elim

/-- Strengthened dependencies supply the smoothability component requirement. -/
theorem smoothabilityComponent_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyComponentRequirement.{u}
      DependencyComponentSlot.smoothabilityComponent :=
  smoothabilityComponent_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the ordinary surgery component requirement
after forgetting equation-boundary data.
-/
theorem surgeryComponent_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent :=
  surgeryComponent_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/-- Strengthened dependencies supply the topology component requirement. -/
theorem topologyComponent_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent :=
  topologyComponent_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened smoothability component projection is the ordinary projection
of the forgetful dependency package.
-/
theorem smoothabilityComponent_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    smoothabilityComponent_requirement_of_equation_boundary_dependencies
        dependencies =
      smoothabilityComponent_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened surgery component projection is the ordinary projection of
the forgetful dependency package.
-/
theorem surgeryComponent_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgeryComponent_requirement_of_equation_boundary_dependencies
        dependencies =
      surgeryComponent_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened topology component projection is the ordinary projection of
the forgetful dependency package.
-/
theorem topologyComponent_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topologyComponent_requirement_of_equation_boundary_dependencies
        dependencies =
      topologyComponent_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies supply the three existing component
requirements after forgetting equation-boundary data.
-/
theorem dependency_component_requirements_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _smoothability :
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.topologyComponent :=
  dependency_component_requirements_payload_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened dependency component payload is the ordinary component payload
of the forgetful dependency package.
-/
theorem dependency_component_requirements_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependency_component_requirements_payload_of_equation_boundary_dependencies
        dependencies =
      dependency_component_requirements_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency component payload is also the tuple of the named
strengthened component projections.
-/
theorem dependency_component_requirements_payload_of_equation_boundary_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependency_component_requirements_payload_of_equation_boundary_dependencies
        dependencies =
      ⟨ smoothabilityComponent_requirement_of_equation_boundary_dependencies
          dependencies
      , surgeryComponent_requirement_of_equation_boundary_dependencies
          dependencies
      , topologyComponent_requirement_of_equation_boundary_dependencies
          dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The aggregate dependency package is equivalent to exactly the three component
requirements named by the dependency crosswalk.
-/
theorem poincareProofDependencies_iff_component_requirements :
    PoincareProofDependencies.{u} ↔
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent := by
  constructor
  · exact dependency_component_requirements_payload_of_dependencies
  · rintro ⟨smoothability, surgery, topology⟩
    exact ⟨smoothability, surgery, topology⟩

/--
The component-slot requirement payload reconstructs the aggregate dependency
package.
-/
theorem poincareProofDependencies_of_component_requirements_payload :
    (∃ _smoothability :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) →
      PoincareProofDependencies.{u} := by
  rintro ⟨smoothability, surgery, topology⟩
  exact ⟨smoothability, surgery, topology⟩

/--
The component-slot payload constructor is exactly the payload destructor that
keeps the smoothability, surgery, and topology component fields.
-/
theorem poincareProofDependencies_of_component_requirements_payload_eq :
    poincareProofDependencies_of_component_requirements_payload.{u} =
      (by
        rintro ⟨smoothability, surgery, topology⟩
        exact ⟨smoothability, surgery, topology⟩) := by
  apply Subsingleton.elim

/--
Projecting component-slot requirements from the aggregate dependencies
reconstructed from that payload returns the original payload.
-/
theorem dependency_component_requirements_payload_of_component_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
      ∃ _surgery :
        dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
        dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) :
    dependency_component_requirements_payload_of_dependencies
      (poincareProofDependencies_of_component_requirements_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The component-slot requirements constructor recovers any aggregate dependency
package from its projected component-slot payload.
-/
theorem poincareProofDependencies_of_component_requirements_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincareProofDependencies_of_component_requirements_payload
      (dependency_component_requirements_payload_of_dependencies dependencies) =
      dependencies := by
  apply Subsingleton.elim

/--
The ordinary aggregate dependency reconstructed from the strengthened
component-slot payload is exactly the forgetful aggregate dependency package.
-/
theorem poincareProofDependencies_of_component_requirements_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincareProofDependencies_of_component_requirements_payload
      (dependency_component_requirements_payload_of_equation_boundary_dependencies
        dependencies) =
      dependencies_of_equation_boundary_dependencies dependencies := by
  apply Subsingleton.elim

/--
The component-slot equivalence is exactly the named forward payload projection
paired with the named reverse constructor.
-/
theorem poincareProofDependencies_iff_component_requirements_eq :
    poincareProofDependencies_iff_component_requirements.{u} =
      ⟨dependency_component_requirements_payload_of_dependencies,
        poincareProofDependencies_of_component_requirements_payload⟩ := by
  apply Subsingleton.elim

/-- The proposition represented by each concrete dependency package layer. -/
def dependencyPackageLayerRequirement : DependencyPackageLayer → Prop
  | DependencyPackageLayer.smoothabilityPackage =>
      SmoothabilityPackage.{u}
  | DependencyPackageLayer.analyticFoundationPackage =>
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω,
            RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M)
  | DependencyPackageLayer.surgeryPackage =>
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
              PerelmanSingularityControlPackage (n := n) (M := M) flow
  | DependencyPackageLayer.finiteExtinctionPackage =>
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)
  | DependencyPackageLayer.topologyPackage =>
      ExtinctionTopologyExtractionPackage.{u}

/-- The package-layer requirement map is exactly the explicit five-case map. -/
theorem dependencyPackageLayerRequirement_eq :
    dependencyPackageLayerRequirement.{u} =
      (fun
        | DependencyPackageLayer.smoothabilityPackage =>
            SmoothabilityPackage.{u}
        | DependencyPackageLayer.analyticFoundationPackage =>
            ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
              [ChartedSpace ThreeManifoldModel M]
              [SimplyConnectedSpace M] [CompactSpace M]
              [IsManifold ThreeManifoldModelWithCorners 1 M],
                Nonempty (Σ n : ℕ∞ω,
                  RicciFlowAnalyticFoundationPackage
                    ThreeManifoldModelWithCorners n M)
        | DependencyPackageLayer.surgeryPackage =>
            ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
              [ChartedSpace ThreeManifoldModel M]
              [SimplyConnectedSpace M] [CompactSpace M]
              [IsManifold ThreeManifoldModelWithCorners 1 M],
                ∃ n : ℕ∞ω,
                ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
                    RicciFlowWithSurgeryConstructionPackage
                      (n := n) (M := M) flow ∧
                    PerelmanSingularityControlPackage (n := n) (M := M) flow
        | DependencyPackageLayer.finiteExtinctionPackage =>
            ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
              [ChartedSpace ThreeManifoldModel M]
              [SimplyConnectedSpace M] [CompactSpace M]
              [IsManifold ThreeManifoldModelWithCorners 1 M],
                Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)
        | DependencyPackageLayer.topologyPackage =>
            ExtinctionTopologyExtractionPackage.{u}) :=
  rfl

/-- The smoothability package-layer requirement is the smoothability package. -/
theorem dependencyPackageLayerRequirement_smoothabilityPackage :
    dependencyPackageLayerRequirement.{u} DependencyPackageLayer.smoothabilityPackage =
      SmoothabilityPackage.{u} :=
  rfl

/-- The analytic package-layer requirement is the target-family analytic package. -/
theorem dependencyPackageLayerRequirement_analyticFoundationPackage :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω,
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M)) :=
  rfl

/--
The surgery package-layer requirement is the target-family construction plus
Perelman-control package.
-/
theorem dependencyPackageLayerRequirement_surgeryPackage :
    dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
              PerelmanSingularityControlPackage (n := n) (M := M) flow) :=
  rfl

/-- The finite-extinction package-layer requirement is the target-family surgery package. -/
theorem dependencyPackageLayerRequirement_finiteExtinctionPackage :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :=
  rfl

/-- The topology package-layer requirement is the topology extraction package. -/
theorem dependencyPackageLayerRequirement_topologyPackage :
    dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage =
      ExtinctionTopologyExtractionPackage.{u} :=
  rfl

/-- The smoothability package-layer requirement theorem is the direct `rfl` proof. -/
theorem dependencyPackageLayerRequirement_smoothabilityPackage_eq :
    dependencyPackageLayerRequirement_smoothabilityPackage.{u} =
      (rfl :
        dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.smoothabilityPackage =
          SmoothabilityPackage.{u}) := by
  apply Subsingleton.elim

/-- The analytic package-layer requirement theorem is the direct `rfl` proof. -/
theorem dependencyPackageLayerRequirement_analyticFoundationPackage_eq :
    dependencyPackageLayerRequirement_analyticFoundationPackage.{u} =
      (rfl :
        dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.analyticFoundationPackage =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              Nonempty (Σ n : ℕ∞ω,
                RicciFlowAnalyticFoundationPackage
                  ThreeManifoldModelWithCorners n M))) := by
  apply Subsingleton.elim

/-- The surgery package-layer requirement theorem is the direct `rfl` proof. -/
theorem dependencyPackageLayerRequirement_surgeryPackage_eq :
    dependencyPackageLayerRequirement_surgeryPackage.{u} =
      (rfl :
        dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.surgeryPackage =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              ∃ n : ℕ∞ω,
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
                  RicciFlowWithSurgeryConstructionPackage
                    (n := n) (M := M) flow ∧
                  PerelmanSingularityControlPackage
                    (n := n) (M := M) flow)) := by
  apply Subsingleton.elim

/-- The finite-extinction package-layer requirement theorem is the direct `rfl` proof. -/
theorem dependencyPackageLayerRequirement_finiteExtinctionPackage_eq :
    dependencyPackageLayerRequirement_finiteExtinctionPackage.{u} =
      (rfl :
        dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.finiteExtinctionPackage =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              Nonempty (Σ n : ℕ∞ω,
                FiniteExtinctionSurgeryPackage n M))) := by
  apply Subsingleton.elim

/-- The topology package-layer requirement theorem is the direct `rfl` proof. -/
theorem dependencyPackageLayerRequirement_topologyPackage_eq :
    dependencyPackageLayerRequirement_topologyPackage.{u} =
      (rfl :
        dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.topologyPackage =
          ExtinctionTopologyExtractionPackage.{u}) := by
  apply Subsingleton.elim

/-- A completed aggregate dependency package supplies every package-layer requirement. -/
theorem dependencyPackageLayerRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (layer : DependencyPackageLayer) :
    dependencyPackageLayerRequirement.{u} layer := by
  cases layer
  · intro M _ _ _ _ _ _
    rcases dependencies.surgery M with ⟨⟨n, package⟩⟩
    exact ⟨⟨n, analytic_foundation_of_surgery_package package⟩⟩
  · intro M _ _ _ _ _ _
    rcases dependencies.surgery M with ⟨⟨n, package⟩⟩
    let flow := ricci_flow_data_of_surgery_package package
    let constructionPackage :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
      surgery_construction_package_of_surgery_package package
    let controlPackage :
        PerelmanSingularityControlPackage (n := n) (M := M) flow :=
      perelman_control_package_of_surgery_package package
    exact ⟨n, flow, constructionPackage, controlPackage⟩
  · exact dependencies.surgery
  · exact dependencies.topology
  · exact dependencies.smoothability

/--
The aggregate component requirement carrying a package layer is enough to
discharge that concrete package-layer requirement.  For the surgery-carried
layers, the finite-extinction surgery package projects to the analytic,
construction, and Perelman-control packages.
-/
theorem dependencyPackageLayerRequirement_of_componentRequirement
    (layer : DependencyPackageLayer) :
    dependencyComponentRequirement.{u}
        (dependencyComponentForPackageLayer layer) →
      dependencyPackageLayerRequirement.{u} layer := by
  cases layer
  · intro surgeryRequirement M _ _ _ _ _ _
    rcases surgeryRequirement M with ⟨⟨n, package⟩⟩
    exact ⟨⟨n, analytic_foundation_of_surgery_package package⟩⟩
  · intro surgeryRequirement M _ _ _ _ _ _
    rcases surgeryRequirement M with ⟨⟨n, package⟩⟩
    let flow := ricci_flow_data_of_surgery_package package
    let constructionPackage :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
      surgery_construction_package_of_surgery_package package
    let controlPackage :
        PerelmanSingularityControlPackage (n := n) (M := M) flow :=
      perelman_control_package_of_surgery_package package
    exact ⟨n, flow, constructionPackage, controlPackage⟩
  · intro surgeryRequirement
    exact surgeryRequirement
  · intro topologyRequirement
    exact topologyRequirement
  · intro smoothabilityRequirement
    exact smoothabilityRequirement

/--
The component-to-package-layer requirement bridge is exactly the case split
that projects package-layer data from the carrying component.
-/
theorem dependencyPackageLayerRequirement_of_componentRequirement_eq :
    dependencyPackageLayerRequirement_of_componentRequirement.{u} =
      (by
        intro layer
        cases layer
        · intro surgeryRequirement M _ _ _ _ _ _
          rcases surgeryRequirement M with ⟨⟨n, package⟩⟩
          exact ⟨⟨n, analytic_foundation_of_surgery_package package⟩⟩
        · intro surgeryRequirement M _ _ _ _ _ _
          rcases surgeryRequirement M with ⟨⟨n, package⟩⟩
          let flow := ricci_flow_data_of_surgery_package package
          let constructionPackage :
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
            surgery_construction_package_of_surgery_package package
          let controlPackage :
              PerelmanSingularityControlPackage (n := n) (M := M) flow :=
            perelman_control_package_of_surgery_package package
          exact ⟨n, flow, constructionPackage, controlPackage⟩
        · intro surgeryRequirement
          exact surgeryRequirement
        · intro topologyRequirement
          exact topologyRequirement
        · intro smoothabilityRequirement
          exact smoothabilityRequirement) := by
  funext layer
  cases layer <;> apply Subsingleton.elim

/--
The generic package-layer projection from dependencies is exactly the five-case
destructor that projects the requested layer from the stored aggregate fields.
-/
theorem dependencyPackageLayerRequirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement_of_dependencies dependencies =
      (fun
        | DependencyPackageLayer.analyticFoundationPackage =>
            by
              intro M _ _ _ _ _ _
              rcases dependencies.surgery M with ⟨⟨n, package⟩⟩
              exact ⟨⟨n, analytic_foundation_of_surgery_package package⟩⟩
        | DependencyPackageLayer.surgeryPackage =>
            by
              intro M _ _ _ _ _ _
              rcases dependencies.surgery M with ⟨⟨n, package⟩⟩
              let flow := ricci_flow_data_of_surgery_package package
              let constructionPackage :
                  RicciFlowWithSurgeryConstructionPackage
                    (n := n) (M := M) flow :=
                surgery_construction_package_of_surgery_package package
              let controlPackage :
                  PerelmanSingularityControlPackage
                    (n := n) (M := M) flow :=
                perelman_control_package_of_surgery_package package
              exact ⟨n, flow, constructionPackage, controlPackage⟩
        | DependencyPackageLayer.finiteExtinctionPackage =>
            dependencies.surgery
        | DependencyPackageLayer.topologyPackage =>
            dependencies.topology
        | DependencyPackageLayer.smoothabilityPackage =>
            dependencies.smoothability) := by
  funext layer
  cases layer <;> apply Subsingleton.elim

/--
The generic analytic package-layer projection is obtained from the stored
surgery family by projecting each surgery package's analytic-foundation package.
-/
theorem dependencyPackageLayerRequirement_of_dependencies_analyticFoundationPackage_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.analyticFoundationPackage =
      (by
        intro M _ _ _ _ _ _
        rcases dependencies.surgery M with ⟨⟨n, package⟩⟩
        exact ⟨⟨n, analytic_foundation_of_surgery_package package⟩⟩) := by
  apply Subsingleton.elim

/--
The generic surgery package-layer projection is obtained from the stored
surgery family by unpacking each surgery package into construction and
Perelman-control packages.
-/
theorem dependencyPackageLayerRequirement_of_dependencies_surgeryPackage_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.surgeryPackage =
      (by
        intro M _ _ _ _ _ _
        rcases dependencies.surgery M with ⟨⟨n, package⟩⟩
        let flow := ricci_flow_data_of_surgery_package package
        let constructionPackage :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
          surgery_construction_package_of_surgery_package package
        let controlPackage :
            PerelmanSingularityControlPackage (n := n) (M := M) flow :=
          perelman_control_package_of_surgery_package package
        exact ⟨n, flow, constructionPackage, controlPackage⟩) := by
  apply Subsingleton.elim

/-- The generic finite-extinction package-layer projection is the stored surgery field. -/
theorem dependencyPackageLayerRequirement_of_dependencies_finiteExtinctionPackage_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.finiteExtinctionPackage =
      dependencies.surgery :=
  rfl

/-- The generic topology package-layer projection is the stored topology field. -/
theorem dependencyPackageLayerRequirement_of_dependencies_topologyPackage_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.topologyPackage =
      dependencies.topology :=
  rfl

/-- The generic smoothability package-layer projection is the stored smoothability field. -/
theorem dependencyPackageLayerRequirement_of_dependencies_smoothabilityPackage_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.smoothabilityPackage =
      dependencies.smoothability :=
  rfl

/-- Aggregate dependencies supply the smoothability package-layer requirement. -/
theorem smoothabilityPackage_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage := by
  exact dependencyPackageLayerRequirement_of_dependencies dependencies
    DependencyPackageLayer.smoothabilityPackage

/-- Aggregate dependencies supply the analytic package-layer requirement. -/
theorem analyticFoundationPackage_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.analyticFoundationPackage := by
  exact dependencyPackageLayerRequirement_of_dependencies dependencies
    DependencyPackageLayer.analyticFoundationPackage

/-- Aggregate dependencies supply the surgery package-layer requirement. -/
theorem surgeryPackage_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage := by
  exact dependencyPackageLayerRequirement_of_dependencies dependencies
    DependencyPackageLayer.surgeryPackage

/-- Aggregate dependencies supply the finite-extinction package-layer requirement. -/
theorem finiteExtinctionPackage_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage := by
  exact dependencyPackageLayerRequirement_of_dependencies dependencies
    DependencyPackageLayer.finiteExtinctionPackage

/-- Aggregate dependencies supply the topology package-layer requirement. -/
theorem topologyPackage_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage := by
  exact dependencyPackageLayerRequirement_of_dependencies dependencies
    DependencyPackageLayer.topologyPackage

/--
The smoothability package-layer projection is the generic package-layer
projection at the smoothability layer.
-/
theorem smoothabilityPackage_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothabilityPackage_requirement_of_dependencies dependencies =
      dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.smoothabilityPackage :=
  rfl

/--
The analytic package-layer projection is the generic package-layer projection at
the analytic-foundation layer.
-/
theorem analyticFoundationPackage_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    analyticFoundationPackage_requirement_of_dependencies dependencies =
      dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.analyticFoundationPackage :=
  rfl

/--
The surgery package-layer projection is the generic package-layer projection at
the surgery layer.
-/
theorem surgeryPackage_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgeryPackage_requirement_of_dependencies dependencies =
      dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.surgeryPackage :=
  rfl

/--
The finite-extinction package-layer projection is the generic package-layer
projection at the finite-extinction layer.
-/
theorem finiteExtinctionPackage_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finiteExtinctionPackage_requirement_of_dependencies dependencies =
      dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.finiteExtinctionPackage :=
  rfl

/--
The topology package-layer projection is the generic package-layer projection at
the topology layer.
-/
theorem topologyPackage_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topologyPackage_requirement_of_dependencies dependencies =
      dependencyPackageLayerRequirement_of_dependencies dependencies
        DependencyPackageLayer.topologyPackage :=
  rfl

/--
A completed aggregate dependency package supplies the concrete package-layer
requirements in package-layer order.
-/
theorem dependency_package_layer_requirements_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _smoothability :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage := by
  exact
    ⟨ smoothabilityPackage_requirement_of_dependencies dependencies
    , analyticFoundationPackage_requirement_of_dependencies dependencies
    , surgeryPackage_requirement_of_dependencies dependencies
    , finiteExtinctionPackage_requirement_of_dependencies dependencies
    , topologyPackage_requirement_of_dependencies dependencies
    ⟩

/--
The aggregate dependency package-layer payload is the tuple of the named
package-layer requirements projected from the stored fields.
-/
theorem dependency_package_layer_requirements_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_package_layer_requirements_payload_of_dependencies dependencies =
      ⟨ smoothabilityPackage_requirement_of_dependencies dependencies
      , analyticFoundationPackage_requirement_of_dependencies dependencies
      , surgeryPackage_requirement_of_dependencies dependencies
      , finiteExtinctionPackage_requirement_of_dependencies dependencies
      , topologyPackage_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The package-layer payload is also the tuple of the generic package-layer
projections in package-layer order.
-/
theorem dependency_package_layer_requirements_payload_of_dependencies_to_generic_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_package_layer_requirements_payload_of_dependencies dependencies =
      ⟨ dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.smoothabilityPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.analyticFoundationPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.surgeryPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.finiteExtinctionPackage
      , dependencyPackageLayerRequirement_of_dependencies dependencies
          DependencyPackageLayer.topologyPackage
      ⟩ := by
  apply Subsingleton.elim

/--
The package-layer payload is also the tuple of named package-layer projections
in package-layer order.
-/
theorem dependency_package_layer_requirements_payload_of_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_package_layer_requirements_payload_of_dependencies dependencies =
      ⟨ smoothabilityPackage_requirement_of_dependencies dependencies
      , analyticFoundationPackage_requirement_of_dependencies dependencies
      , surgeryPackage_requirement_of_dependencies dependencies
      , finiteExtinctionPackage_requirement_of_dependencies dependencies
      , topologyPackage_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies supply every existing package-layer
requirement after forgetting the explicit equation-boundary data.
-/
theorem dependencyPackageLayerRequirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (layer : DependencyPackageLayer) :
    dependencyPackageLayerRequirement.{u} layer :=
  dependencyPackageLayerRequirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies) layer

/--
The strengthened dependency package-layer projection is the ordinary
package-layer projection applied to the forgetful dependency package.
-/
theorem dependencyPackageLayerRequirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyPackageLayerRequirement_of_equation_boundary_dependencies
        dependencies =
      dependencyPackageLayerRequirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  funext layer
  apply Subsingleton.elim

/--
Strengthened dependencies supply the smoothability package-layer requirement.
-/
theorem smoothabilityPackage_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.smoothabilityPackage :=
  smoothabilityPackage_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the analytic package-layer requirement after
forgetting equation-boundary data.
-/
theorem analyticFoundationPackage_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.analyticFoundationPackage :=
  analyticFoundationPackage_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the surgery package-layer requirement after
forgetting equation-boundary data.
-/
theorem surgeryPackage_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage :=
  surgeryPackage_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the finite-extinction package-layer
requirement after forgetting equation-boundary data.
-/
theorem finiteExtinctionPackage_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage :=
  finiteExtinctionPackage_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the topology package-layer requirement after
forgetting equation-boundary data.
-/
theorem topologyPackage_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyPackageLayerRequirement.{u} DependencyPackageLayer.topologyPackage :=
  topologyPackage_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened smoothability package-layer projection is the ordinary
projection of the forgetful dependency package.
-/
theorem smoothabilityPackage_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    smoothabilityPackage_requirement_of_equation_boundary_dependencies
        dependencies =
      smoothabilityPackage_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened analytic package-layer projection is the ordinary projection
of the forgetful dependency package.
-/
theorem analyticFoundationPackage_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analyticFoundationPackage_requirement_of_equation_boundary_dependencies
        dependencies =
      analyticFoundationPackage_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened surgery package-layer projection is the ordinary projection
of the forgetful dependency package.
-/
theorem surgeryPackage_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgeryPackage_requirement_of_equation_boundary_dependencies
        dependencies =
      surgeryPackage_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened finite-extinction package-layer projection is the ordinary
projection of the forgetful dependency package.
-/
theorem finiteExtinctionPackage_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    finiteExtinctionPackage_requirement_of_equation_boundary_dependencies
        dependencies =
      finiteExtinctionPackage_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened topology package-layer projection is the ordinary projection
of the forgetful dependency package.
-/
theorem topologyPackage_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topologyPackage_requirement_of_equation_boundary_dependencies
        dependencies =
      topologyPackage_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies supply the five existing
package-layer requirements after forgetting equation-boundary data.
-/
theorem dependency_package_layer_requirements_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage :=
  dependency_package_layer_requirements_payload_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened dependency package-layer payload is the ordinary package-layer
payload of the forgetful dependency package.
-/
theorem dependency_package_layer_requirements_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependency_package_layer_requirements_payload_of_equation_boundary_dependencies
        dependencies =
      dependency_package_layer_requirements_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency package-layer payload is also the tuple of the
named strengthened package-layer projections.
-/
theorem dependency_package_layer_requirements_payload_of_equation_boundary_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependency_package_layer_requirements_payload_of_equation_boundary_dependencies
        dependencies =
      ⟨ smoothabilityPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , analyticFoundationPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , surgeryPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , finiteExtinctionPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , topologyPackage_requirement_of_equation_boundary_dependencies
          dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The aggregate dependency package is equivalent to its five concrete
package-layer requirements.
-/
theorem poincareProofDependencies_iff_package_layer_requirements :
    PoincareProofDependencies.{u} ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · exact dependency_package_layer_requirements_payload_of_dependencies
  · rintro ⟨smoothability, _analytic, _surgery, finiteExtinction, topology⟩
    exact ⟨smoothability, finiteExtinction, topology⟩

/--
The package-layer requirement payload reconstructs the aggregate dependency
package by retaining the smoothability, finite-extinction, and topology fields.
-/
theorem poincareProofDependencies_of_package_layer_requirements_payload :
    (∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) →
      PoincareProofDependencies.{u} := by
  rintro ⟨smoothability, _analytic, _surgery, finiteExtinction, topology⟩
  exact ⟨smoothability, finiteExtinction, topology⟩

/--
The package-layer payload constructor is exactly the payload destructor that
keeps the smoothability, finite-extinction, and topology package-layer fields.
-/
theorem poincareProofDependencies_of_package_layer_requirements_payload_eq :
    poincareProofDependencies_of_package_layer_requirements_payload.{u} =
      (by
        rintro ⟨smoothability, _analytic, _surgery, finiteExtinction,
          topology⟩
        exact ⟨smoothability, finiteExtinction, topology⟩) := by
  apply Subsingleton.elim

/--
Projecting package-layer requirements from the aggregate dependencies
reconstructed from that payload returns the original payload.
-/
theorem dependency_package_layer_requirements_payload_of_package_layer_requirements_payload_eq
    (payload :
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage) :
    dependency_package_layer_requirements_payload_of_dependencies
      (poincareProofDependencies_of_package_layer_requirements_payload
        payload) =
      payload := by
  apply Subsingleton.elim

/--
The package-layer requirements constructor recovers any aggregate dependency
package from its projected package-layer payload.
-/
theorem poincareProofDependencies_of_package_layer_requirements_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincareProofDependencies_of_package_layer_requirements_payload
      (dependency_package_layer_requirements_payload_of_dependencies
        dependencies) =
      dependencies := by
  apply Subsingleton.elim

/--
The ordinary aggregate dependency reconstructed from the strengthened
package-layer payload is exactly the forgetful aggregate dependency package.
-/
theorem poincareProofDependencies_of_package_layer_requirements_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincareProofDependencies_of_package_layer_requirements_payload
      (dependency_package_layer_requirements_payload_of_equation_boundary_dependencies
        dependencies) =
      dependencies_of_equation_boundary_dependencies dependencies := by
  apply Subsingleton.elim

/--
The package-layer equivalence is exactly the named forward payload projection
paired with the named reverse constructor.
-/
theorem poincareProofDependencies_iff_package_layer_requirements_eq :
    poincareProofDependencies_iff_package_layer_requirements.{u} =
      ⟨dependency_package_layer_requirements_payload_of_dependencies,
        poincareProofDependencies_of_package_layer_requirements_payload⟩ := by
  apply Subsingleton.elim

/--
The component-slot and package-layer requirement payloads are equivalent routes
to the same aggregate dependency package.
-/
theorem component_requirements_iff_package_layer_requirements :
    (∃ _smoothability :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) ↔
      ∃ _smoothability :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.smoothabilityPackage,
      ∃ _analytic :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.analyticFoundationPackage,
      ∃ _surgery :
        dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
      ∃ _finiteExtinction :
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage,
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.topologyPackage := by
  constructor
  · intro payload
    exact
      dependency_package_layer_requirements_payload_of_dependencies
        (poincareProofDependencies_of_component_requirements_payload payload)
  · intro payload
    exact
      dependency_component_requirements_payload_of_dependencies
        (poincareProofDependencies_of_package_layer_requirements_payload payload)

/--
The component/package-layer payload bridge is exactly the pair of constructors
through the aggregate dependency package.
-/
theorem component_requirements_iff_package_layer_requirements_eq :
    component_requirements_iff_package_layer_requirements.{u} =
      ⟨ (fun payload =>
          dependency_package_layer_requirements_payload_of_dependencies
            (poincareProofDependencies_of_component_requirements_payload
              payload))
      , (fun payload =>
          dependency_component_requirements_payload_of_dependencies
            (poincareProofDependencies_of_package_layer_requirements_payload
              payload)) ⟩ := by
  apply Subsingleton.elim

/--
The proposition represented by the concrete package layer assigned to a
milestone.
-/
def dependencyMilestoneRequirement : DependencyMilestone → Prop :=
  fun milestone =>
    dependencyPackageLayerRequirement.{u} (dependencyLayerForMilestone milestone)

/--
The milestone requirement map is exactly the package-layer requirement map at
the package layer assigned to each milestone.
-/
theorem dependencyMilestoneRequirement_eq :
    dependencyMilestoneRequirement.{u} =
      fun milestone =>
        dependencyPackageLayerRequirement.{u}
          (dependencyLayerForMilestone milestone) :=
  rfl

/-- The smoothability milestone requires the smoothability package. -/
theorem dependencyMilestoneRequirement_smoothabilityBridge :
    dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge =
      SmoothabilityPackage.{u} :=
  rfl

/-- The analytic-foundation milestone is supplied by the target-family surgery package. -/
theorem dependencyMilestoneRequirement_ricciFlowAnalyticFoundation :
    dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowAnalyticFoundation =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω,
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M)) :=
  rfl

/-- The Ricci-flow-with-surgery milestone is supplied by the target-family surgery package. -/
theorem dependencyMilestoneRequirement_ricciFlowWithSurgery :
    dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
              PerelmanSingularityControlPackage (n := n) (M := M) flow) :=
  rfl

/-- The Perelman-control milestone is supplied by the target-family surgery package. -/
theorem dependencyMilestoneRequirement_perelmanSingularityControl :
    dependencyMilestoneRequirement.{u} DependencyMilestone.perelmanSingularityControl =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
              PerelmanSingularityControlPackage (n := n) (M := M) flow) :=
  rfl

/-- The finite-extinction milestone is supplied by the target-family surgery package. -/
theorem dependencyMilestoneRequirement_finiteExtinction :
    dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :=
  rfl

/-- The topology-extraction milestone requires the topology extraction package. -/
theorem dependencyMilestoneRequirement_extinctionToSphereHomeomorphism :
    dependencyMilestoneRequirement.{u} DependencyMilestone.extinctionToSphereHomeomorphism =
      ExtinctionTopologyExtractionPackage.{u} :=
  rfl

/-- The smoothability milestone requirement theorem is the direct `rfl` proof. -/
theorem dependencyMilestoneRequirement_smoothabilityBridge_eq :
    dependencyMilestoneRequirement_smoothabilityBridge.{u} =
      (rfl :
        dependencyMilestoneRequirement.{u}
            DependencyMilestone.smoothabilityBridge =
          SmoothabilityPackage.{u}) := by
  apply Subsingleton.elim

/-- The analytic-foundation milestone requirement theorem is the direct `rfl` proof. -/
theorem dependencyMilestoneRequirement_ricciFlowAnalyticFoundation_eq :
    dependencyMilestoneRequirement_ricciFlowAnalyticFoundation.{u} =
      (rfl :
        dependencyMilestoneRequirement.{u}
            DependencyMilestone.ricciFlowAnalyticFoundation =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              Nonempty (Σ n : ℕ∞ω,
                RicciFlowAnalyticFoundationPackage
                  ThreeManifoldModelWithCorners n M))) := by
  apply Subsingleton.elim

/-- The Ricci-flow-with-surgery milestone requirement theorem is the direct `rfl` proof. -/
theorem dependencyMilestoneRequirement_ricciFlowWithSurgery_eq :
    dependencyMilestoneRequirement_ricciFlowWithSurgery.{u} =
      (rfl :
        dependencyMilestoneRequirement.{u}
            DependencyMilestone.ricciFlowWithSurgery =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              ∃ n : ℕ∞ω,
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
                  RicciFlowWithSurgeryConstructionPackage
                    (n := n) (M := M) flow ∧
                  PerelmanSingularityControlPackage
                    (n := n) (M := M) flow)) := by
  apply Subsingleton.elim

/-- The Perelman-control milestone requirement theorem is the direct `rfl` proof. -/
theorem dependencyMilestoneRequirement_perelmanSingularityControl_eq :
    dependencyMilestoneRequirement_perelmanSingularityControl.{u} =
      (rfl :
        dependencyMilestoneRequirement.{u}
            DependencyMilestone.perelmanSingularityControl =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              ∃ n : ℕ∞ω,
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
                  RicciFlowWithSurgeryConstructionPackage
                    (n := n) (M := M) flow ∧
                  PerelmanSingularityControlPackage
                    (n := n) (M := M) flow)) := by
  apply Subsingleton.elim

/-- The finite-extinction milestone requirement theorem is the direct `rfl` proof. -/
theorem dependencyMilestoneRequirement_finiteExtinction_eq :
    dependencyMilestoneRequirement_finiteExtinction.{u} =
      (rfl :
        dependencyMilestoneRequirement.{u}
            DependencyMilestone.finiteExtinction =
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace ThreeManifoldModel M]
            [SimplyConnectedSpace M] [CompactSpace M]
            [IsManifold ThreeManifoldModelWithCorners 1 M],
              Nonempty (Σ n : ℕ∞ω,
                FiniteExtinctionSurgeryPackage n M))) := by
  apply Subsingleton.elim

/-- The topology-extraction milestone requirement theorem is the direct `rfl` proof. -/
theorem dependencyMilestoneRequirement_extinctionToSphereHomeomorphism_eq :
    dependencyMilestoneRequirement_extinctionToSphereHomeomorphism.{u} =
      (rfl :
        dependencyMilestoneRequirement.{u}
            DependencyMilestone.extinctionToSphereHomeomorphism =
          ExtinctionTopologyExtractionPackage.{u}) := by
  apply Subsingleton.elim

/-- A completed dependency package supplies the requirement for every milestone. -/
theorem dependencyMilestoneRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (milestone : DependencyMilestone) :
    dependencyMilestoneRequirement.{u} milestone := by
  cases milestone <;>
    exact dependencyPackageLayerRequirement_of_dependencies dependencies _

/--
The aggregate component requirement carrying a milestone is enough to discharge
that milestone's concrete package-layer requirement.
-/
theorem dependencyMilestoneRequirement_of_componentRequirement
    (milestone : DependencyMilestone) :
    dependencyComponentRequirement.{u}
        (dependencyComponentForMilestone milestone) →
      dependencyMilestoneRequirement.{u} milestone := by
  cases milestone <;>
    exact dependencyPackageLayerRequirement_of_componentRequirement _

/--
The component-to-milestone requirement bridge is exactly the package-layer
bridge at the package layer assigned to the milestone.
-/
theorem dependencyMilestoneRequirement_of_componentRequirement_eq :
    dependencyMilestoneRequirement_of_componentRequirement.{u} =
      (by
        intro milestone
        cases milestone <;>
          exact dependencyPackageLayerRequirement_of_componentRequirement _) := by
  funext milestone
  cases milestone <;> apply Subsingleton.elim

/-- Aggregate dependencies supply the smoothability milestone requirement. -/
theorem smoothabilityBridge_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge := by
  exact dependencyMilestoneRequirement_of_dependencies dependencies
    DependencyMilestone.smoothabilityBridge

/-- Aggregate dependencies supply the analytic-foundation milestone requirement. -/
theorem ricciFlowAnalyticFoundation_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.ricciFlowAnalyticFoundation := by
  exact dependencyMilestoneRequirement_of_dependencies dependencies
    DependencyMilestone.ricciFlowAnalyticFoundation

/-- Aggregate dependencies supply the Ricci-flow-with-surgery milestone requirement. -/
theorem ricciFlowWithSurgery_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery := by
  exact dependencyMilestoneRequirement_of_dependencies dependencies
    DependencyMilestone.ricciFlowWithSurgery

/-- Aggregate dependencies supply the Perelman-control milestone requirement. -/
theorem perelmanSingularityControl_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.perelmanSingularityControl := by
  exact dependencyMilestoneRequirement_of_dependencies dependencies
    DependencyMilestone.perelmanSingularityControl

/-- Aggregate dependencies supply the finite-extinction milestone requirement. -/
theorem finiteExtinction_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction := by
  exact dependencyMilestoneRequirement_of_dependencies dependencies
    DependencyMilestone.finiteExtinction

/-- Aggregate dependencies supply the topology-extraction milestone requirement. -/
theorem extinctionToSphereHomeomorphism_requirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.extinctionToSphereHomeomorphism := by
  exact dependencyMilestoneRequirement_of_dependencies dependencies
    DependencyMilestone.extinctionToSphereHomeomorphism

/--
The generic milestone projection is the generic package-layer projection at the
package layer assigned to that milestone.
-/
theorem dependencyMilestoneRequirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (milestone : DependencyMilestone) :
    dependencyMilestoneRequirement_of_dependencies dependencies milestone =
      dependencyPackageLayerRequirement_of_dependencies dependencies
        (dependencyLayerForMilestone milestone) := by
  cases milestone <;> rfl

/--
The smoothability milestone projection is the smoothability package-layer
projection.
-/
theorem smoothabilityBridge_requirement_of_dependencies_to_package_layer_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothabilityBridge_requirement_of_dependencies dependencies =
      smoothabilityPackage_requirement_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The analytic-foundation milestone projection is the analytic package-layer
projection.
-/
theorem ricciFlowAnalyticFoundation_requirement_of_dependencies_to_package_layer_eq
    (dependencies : PoincareProofDependencies.{u}) :
    ricciFlowAnalyticFoundation_requirement_of_dependencies dependencies =
      analyticFoundationPackage_requirement_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The Ricci-flow-with-surgery milestone projection is the surgery package-layer
projection.
-/
theorem ricciFlowWithSurgery_requirement_of_dependencies_to_package_layer_eq
    (dependencies : PoincareProofDependencies.{u}) :
    ricciFlowWithSurgery_requirement_of_dependencies dependencies =
      surgeryPackage_requirement_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The Perelman-control milestone projection is the surgery package-layer
projection.
-/
theorem perelmanSingularityControl_requirement_of_dependencies_to_package_layer_eq
    (dependencies : PoincareProofDependencies.{u}) :
    perelmanSingularityControl_requirement_of_dependencies dependencies =
      surgeryPackage_requirement_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The finite-extinction milestone projection is the finite-extinction
package-layer projection.
-/
theorem finiteExtinction_requirement_of_dependencies_to_package_layer_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finiteExtinction_requirement_of_dependencies dependencies =
      finiteExtinctionPackage_requirement_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The topology-extraction milestone projection is the topology package-layer
projection.
-/
theorem extinctionToSphereHomeomorphism_requirement_of_dependencies_to_package_layer_eq
    (dependencies : PoincareProofDependencies.{u}) :
    extinctionToSphereHomeomorphism_requirement_of_dependencies dependencies =
      topologyPackage_requirement_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The smoothability milestone projection is the generic milestone projection at
the smoothability milestone.
-/
theorem smoothabilityBridge_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothabilityBridge_requirement_of_dependencies dependencies =
      dependencyMilestoneRequirement_of_dependencies dependencies
        DependencyMilestone.smoothabilityBridge :=
  rfl

/--
The analytic-foundation milestone projection is the generic milestone projection
at the analytic-foundation milestone.
-/
theorem ricciFlowAnalyticFoundation_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    ricciFlowAnalyticFoundation_requirement_of_dependencies dependencies =
      dependencyMilestoneRequirement_of_dependencies dependencies
        DependencyMilestone.ricciFlowAnalyticFoundation :=
  rfl

/--
The Ricci-flow-with-surgery milestone projection is the generic milestone
projection at the Ricci-flow-with-surgery milestone.
-/
theorem ricciFlowWithSurgery_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    ricciFlowWithSurgery_requirement_of_dependencies dependencies =
      dependencyMilestoneRequirement_of_dependencies dependencies
        DependencyMilestone.ricciFlowWithSurgery :=
  rfl

/--
The Perelman-control milestone projection is the generic milestone projection at
the Perelman-control milestone.
-/
theorem perelmanSingularityControl_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    perelmanSingularityControl_requirement_of_dependencies dependencies =
      dependencyMilestoneRequirement_of_dependencies dependencies
        DependencyMilestone.perelmanSingularityControl :=
  rfl

/--
The finite-extinction milestone projection is the generic milestone projection
at the finite-extinction milestone.
-/
theorem finiteExtinction_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finiteExtinction_requirement_of_dependencies dependencies =
      dependencyMilestoneRequirement_of_dependencies dependencies
        DependencyMilestone.finiteExtinction :=
  rfl

/--
The topology-extraction milestone projection is the generic milestone projection
at the topology-extraction milestone.
-/
theorem extinctionToSphereHomeomorphism_requirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    extinctionToSphereHomeomorphism_requirement_of_dependencies dependencies =
      dependencyMilestoneRequirement_of_dependencies dependencies
        DependencyMilestone.extinctionToSphereHomeomorphism :=
  rfl

/--
A completed aggregate dependency package supplies the requirements for all six
named milestones in ledger order.
-/
theorem dependency_milestone_requirements_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _smoothabilityBridge :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
    ∃ _ricciFlowAnalyticFoundation :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation,
    ∃ _ricciFlowWithSurgery :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
    ∃ _perelmanSingularityControl :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl,
    ∃ _finiteExtinction :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism := by
  exact
    ⟨ smoothabilityBridge_requirement_of_dependencies dependencies
    , ricciFlowAnalyticFoundation_requirement_of_dependencies dependencies
    , ricciFlowWithSurgery_requirement_of_dependencies dependencies
    , perelmanSingularityControl_requirement_of_dependencies dependencies
    , finiteExtinction_requirement_of_dependencies dependencies
    , extinctionToSphereHomeomorphism_requirement_of_dependencies dependencies
    ⟩

/--
The aggregate dependency milestone payload is the tuple of the named milestone
requirements projected from the stored fields.
-/
theorem dependency_milestone_requirements_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_milestone_requirements_payload_of_dependencies dependencies =
      ⟨ smoothabilityBridge_requirement_of_dependencies dependencies
      , ricciFlowAnalyticFoundation_requirement_of_dependencies dependencies
      , ricciFlowWithSurgery_requirement_of_dependencies dependencies
      , perelmanSingularityControl_requirement_of_dependencies dependencies
      , finiteExtinction_requirement_of_dependencies dependencies
      , extinctionToSphereHomeomorphism_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The milestone payload is also the tuple of package-layer projections assigned
to the six ledger milestones.
-/
theorem dependency_milestone_requirements_payload_of_dependencies_to_package_layer_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_milestone_requirements_payload_of_dependencies dependencies =
      ⟨ smoothabilityPackage_requirement_of_dependencies dependencies
      , analyticFoundationPackage_requirement_of_dependencies dependencies
      , surgeryPackage_requirement_of_dependencies dependencies
      , surgeryPackage_requirement_of_dependencies dependencies
      , finiteExtinctionPackage_requirement_of_dependencies dependencies
      , topologyPackage_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The milestone payload is also the tuple of named milestone projections in
milestone order.
-/
theorem dependency_milestone_requirements_payload_of_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    dependency_milestone_requirements_payload_of_dependencies dependencies =
      ⟨ smoothabilityBridge_requirement_of_dependencies dependencies
      , ricciFlowAnalyticFoundation_requirement_of_dependencies dependencies
      , ricciFlowWithSurgery_requirement_of_dependencies dependencies
      , perelmanSingularityControl_requirement_of_dependencies dependencies
      , finiteExtinction_requirement_of_dependencies dependencies
      , extinctionToSphereHomeomorphism_requirement_of_dependencies dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies supply every milestone requirement
after forgetting the explicit equation-boundary data.
-/
theorem dependencyMilestoneRequirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (milestone : DependencyMilestone) :
    dependencyMilestoneRequirement.{u} milestone :=
  dependencyMilestoneRequirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies) milestone

/--
The strengthened dependency milestone projection is the ordinary milestone
projection applied to the forgetful dependency package.
-/
theorem dependencyMilestoneRequirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (milestone : DependencyMilestone) :
    dependencyMilestoneRequirement_of_equation_boundary_dependencies
        dependencies milestone =
      dependencyMilestoneRequirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        milestone := by
  apply Subsingleton.elim

/--
The strengthened dependency milestone projection factors through the
strengthened package-layer projection assigned to that milestone.
-/
theorem dependencyMilestoneRequirement_of_equation_boundary_dependencies_to_package_layer_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (milestone : DependencyMilestone) :
    dependencyMilestoneRequirement_of_equation_boundary_dependencies
        dependencies milestone =
      dependencyPackageLayerRequirement_of_equation_boundary_dependencies
        dependencies (dependencyLayerForMilestone milestone) := by
  cases milestone <;> apply Subsingleton.elim

/-- Strengthened dependencies supply the smoothability milestone requirement. -/
theorem smoothabilityBridge_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge :=
  smoothabilityBridge_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the analytic-foundation milestone requirement
after forgetting equation-boundary data.
-/
theorem ricciFlowAnalyticFoundation_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.ricciFlowAnalyticFoundation :=
  ricciFlowAnalyticFoundation_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the Ricci-flow-with-surgery milestone
requirement after forgetting equation-boundary data.
-/
theorem ricciFlowWithSurgery_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery :=
  ricciFlowWithSurgery_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the Perelman-control milestone requirement
after forgetting equation-boundary data.
-/
theorem perelmanSingularityControl_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.perelmanSingularityControl :=
  perelmanSingularityControl_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the finite-extinction milestone requirement
after forgetting equation-boundary data.
-/
theorem finiteExtinction_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction :=
  finiteExtinction_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
Strengthened dependencies supply the topology-extraction milestone requirement
after forgetting equation-boundary data.
-/
theorem extinctionToSphereHomeomorphism_requirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.extinctionToSphereHomeomorphism :=
  extinctionToSphereHomeomorphism_requirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened smoothability milestone projection is the ordinary projection
of the forgetful dependency package.
-/
theorem smoothabilityBridge_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    smoothabilityBridge_requirement_of_equation_boundary_dependencies
        dependencies =
      smoothabilityBridge_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened analytic-foundation milestone projection is the ordinary
projection of the forgetful dependency package.
-/
theorem ricciFlowAnalyticFoundation_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ricciFlowAnalyticFoundation_requirement_of_equation_boundary_dependencies
        dependencies =
      ricciFlowAnalyticFoundation_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened Ricci-flow-with-surgery milestone projection is the ordinary
projection of the forgetful dependency package.
-/
theorem ricciFlowWithSurgery_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ricciFlowWithSurgery_requirement_of_equation_boundary_dependencies
        dependencies =
      ricciFlowWithSurgery_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened Perelman-control milestone projection is the ordinary
projection of the forgetful dependency package.
-/
theorem perelmanSingularityControl_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    perelmanSingularityControl_requirement_of_equation_boundary_dependencies
        dependencies =
      perelmanSingularityControl_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened finite-extinction milestone projection is the ordinary
projection of the forgetful dependency package.
-/
theorem finiteExtinction_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    finiteExtinction_requirement_of_equation_boundary_dependencies
        dependencies =
      finiteExtinction_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened topology-extraction milestone projection is the ordinary
projection of the forgetful dependency package.
-/
theorem extinctionToSphereHomeomorphism_requirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    extinctionToSphereHomeomorphism_requirement_of_equation_boundary_dependencies
        dependencies =
      extinctionToSphereHomeomorphism_requirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies supply all six milestone
requirements after forgetting equation-boundary data.
-/
theorem dependency_milestone_requirements_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _smoothabilityBridge :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
    ∃ _ricciFlowAnalyticFoundation :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation,
    ∃ _ricciFlowWithSurgery :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
    ∃ _perelmanSingularityControl :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl,
    ∃ _finiteExtinction :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism :=
  dependency_milestone_requirements_payload_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened dependency milestone payload is the ordinary milestone payload
of the forgetful dependency package.
-/
theorem dependency_milestone_requirements_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependency_milestone_requirements_payload_of_equation_boundary_dependencies
        dependencies =
      dependency_milestone_requirements_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency milestone payload is also the tuple of the named
strengthened milestone projections in ledger order.
-/
theorem dependency_milestone_requirements_payload_of_equation_boundary_dependencies_to_named_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependency_milestone_requirements_payload_of_equation_boundary_dependencies
        dependencies =
      ⟨ smoothabilityBridge_requirement_of_equation_boundary_dependencies
          dependencies
      , ricciFlowAnalyticFoundation_requirement_of_equation_boundary_dependencies
          dependencies
      , ricciFlowWithSurgery_requirement_of_equation_boundary_dependencies
          dependencies
      , perelmanSingularityControl_requirement_of_equation_boundary_dependencies
          dependencies
      , finiteExtinction_requirement_of_equation_boundary_dependencies
          dependencies
      , extinctionToSphereHomeomorphism_requirement_of_equation_boundary_dependencies
          dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The strengthened dependency milestone payload is also the tuple of strengthened
package-layer projections assigned to the six ledger milestones.
-/
theorem dependency_milestone_requirements_payload_of_equation_boundary_dependencies_to_package_layer_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    dependency_milestone_requirements_payload_of_equation_boundary_dependencies
        dependencies =
      ⟨ smoothabilityPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , analyticFoundationPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , surgeryPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , surgeryPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , finiteExtinctionPackage_requirement_of_equation_boundary_dependencies
          dependencies
      , topologyPackage_requirement_of_equation_boundary_dependencies
          dependencies
      ⟩ := by
  apply Subsingleton.elim

/--
The aggregate dependency package is equivalent to supplying every milestone
requirement in the ledger.
-/
theorem poincareProofDependencies_iff_milestone_requirements :
    PoincareProofDependencies.{u} ↔
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism := by
  constructor
  · exact dependency_milestone_requirements_payload_of_dependencies
  · rintro ⟨smoothability, _analytic, _ricciFlowWithSurgery,
      _perelmanSingularityControl, finiteExtinction, topology⟩
    exact ⟨smoothability, finiteExtinction, topology⟩

/--
The milestone requirement payload reconstructs the aggregate dependency package
by retaining the smoothability, finite-extinction, and topology fields.
-/
theorem poincareProofDependencies_of_milestone_requirements_payload :
    (∃ _smoothabilityBridge :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
    ∃ _ricciFlowAnalyticFoundation :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation,
    ∃ _ricciFlowWithSurgery :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
    ∃ _perelmanSingularityControl :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl,
    ∃ _finiteExtinction :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism) →
      PoincareProofDependencies.{u} := by
  rintro ⟨smoothability, _analytic, _ricciFlowWithSurgery,
    _perelmanSingularityControl, finiteExtinction, topology⟩
  exact ⟨smoothability, finiteExtinction, topology⟩

/--
The milestone payload constructor is exactly the payload destructor that keeps
the smoothability, finite-extinction, and topology-extraction milestone fields.
-/
theorem poincareProofDependencies_of_milestone_requirements_payload_eq :
    poincareProofDependencies_of_milestone_requirements_payload.{u} =
      (by
        rintro ⟨smoothability, _analytic, _ricciFlowWithSurgery,
          _perelmanSingularityControl, finiteExtinction, topology⟩
        exact ⟨smoothability, finiteExtinction, topology⟩) := by
  apply Subsingleton.elim

/--
Projecting milestone requirements from the aggregate dependencies
reconstructed from that payload returns the original payload.
-/
theorem dependency_milestone_requirements_payload_of_milestone_requirements_payload_eq
    (payload :
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism) :
    dependency_milestone_requirements_payload_of_dependencies
      (poincareProofDependencies_of_milestone_requirements_payload payload) =
      payload := by
  apply Subsingleton.elim

/--
The milestone requirements constructor recovers any aggregate dependency
package from its projected milestone payload.
-/
theorem poincareProofDependencies_of_milestone_requirements_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincareProofDependencies_of_milestone_requirements_payload
      (dependency_milestone_requirements_payload_of_dependencies
        dependencies) =
      dependencies := by
  apply Subsingleton.elim

/--
The ordinary aggregate dependency reconstructed from the strengthened milestone
payload is exactly the forgetful aggregate dependency package.
-/
theorem poincareProofDependencies_of_milestone_requirements_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincareProofDependencies_of_milestone_requirements_payload
      (dependency_milestone_requirements_payload_of_equation_boundary_dependencies
        dependencies) =
      dependencies_of_equation_boundary_dependencies dependencies := by
  apply Subsingleton.elim

section VerificationFamilyDependencyRequirementPayloads

variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
component-slot payload through the strengthened dependency lift.
-/
theorem dependency_component_requirements_payload_of_dependencies_and_verification_family :
    ∃ _smoothability :
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u}
        DependencyComponentSlot.topologyComponent :=
  dependency_component_requirements_payload_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family component-slot payload delegates to the strengthened
component-slot payload after applying the verification-family lift.
-/
theorem dependency_component_requirements_payload_of_dependencies_and_verification_family_eq :
    dependency_component_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      dependency_component_requirements_payload_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary component-slot
payload of the aggregate dependencies.
-/
theorem dependency_component_requirements_payload_of_dependencies_and_verification_family_to_dependencies_eq :
    dependency_component_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      dependency_component_requirements_payload_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The component-slot constructor reconstructs the ordinary aggregate dependencies
from the verification-family component-slot payload.
-/
theorem poincareProofDependencies_of_component_requirements_payload_of_dependencies_and_verification_family_eq :
    poincareProofDependencies_of_component_requirements_payload
      (dependency_component_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily) =
      dependencies := by
  apply Subsingleton.elim

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
package-layer payload through the strengthened dependency lift.
-/
theorem dependency_package_layer_requirements_payload_of_dependencies_and_verification_family :
    ∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage :=
  dependency_package_layer_requirements_payload_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family package-layer payload delegates to the strengthened
package-layer payload after applying the verification-family lift.
-/
theorem dependency_package_layer_requirements_payload_of_dependencies_and_verification_family_eq :
    dependency_package_layer_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      dependency_package_layer_requirements_payload_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary package-layer
payload of the aggregate dependencies.
-/
theorem dependency_package_layer_requirements_payload_of_dependencies_and_verification_family_to_dependencies_eq :
    dependency_package_layer_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      dependency_package_layer_requirements_payload_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The package-layer constructor reconstructs the ordinary aggregate dependencies
from the verification-family package-layer payload.
-/
theorem poincareProofDependencies_of_package_layer_requirements_payload_of_dependencies_and_verification_family_eq :
    poincareProofDependencies_of_package_layer_requirements_payload
      (dependency_package_layer_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily) =
      dependencies := by
  apply Subsingleton.elim

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
milestone payload through the strengthened dependency lift.
-/
theorem dependency_milestone_requirements_payload_of_dependencies_and_verification_family :
    ∃ _smoothabilityBridge :
      dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
    ∃ _ricciFlowAnalyticFoundation :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowAnalyticFoundation,
    ∃ _ricciFlowWithSurgery :
      dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
    ∃ _perelmanSingularityControl :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl,
    ∃ _finiteExtinction :
      dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.extinctionToSphereHomeomorphism :=
  dependency_milestone_requirements_payload_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family milestone payload delegates to the strengthened
milestone payload after applying the verification-family lift.
-/
theorem dependency_milestone_requirements_payload_of_dependencies_and_verification_family_eq :
    dependency_milestone_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      dependency_milestone_requirements_payload_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary milestone payload
of the aggregate dependencies.
-/
theorem dependency_milestone_requirements_payload_of_dependencies_and_verification_family_to_dependencies_eq :
    dependency_milestone_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      dependency_milestone_requirements_payload_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The milestone constructor reconstructs the ordinary aggregate dependencies from
the verification-family milestone payload.
-/
theorem poincareProofDependencies_of_milestone_requirements_payload_of_dependencies_and_verification_family_eq :
    poincareProofDependencies_of_milestone_requirements_payload
      (dependency_milestone_requirements_payload_of_dependencies_and_verification_family
        dependencies verificationFamily) =
      dependencies := by
  apply Subsingleton.elim

end VerificationFamilyDependencyRequirementPayloads

/--
The milestone equivalence is exactly the named forward payload projection
paired with the named reverse constructor.
-/
theorem poincareProofDependencies_iff_milestone_requirements_eq :
    poincareProofDependencies_iff_milestone_requirements.{u} =
      ⟨dependency_milestone_requirements_payload_of_dependencies,
        poincareProofDependencies_of_milestone_requirements_payload⟩ := by
  apply Subsingleton.elim

/--
The package-layer and milestone requirement payloads are equivalent routes to
the same aggregate dependency package.
-/
theorem package_layer_requirements_iff_milestone_requirements :
    (∃ _smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage,
    ∃ _analytic :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.analyticFoundationPackage,
    ∃ _surgery :
      dependencyPackageLayerRequirement.{u} DependencyPackageLayer.surgeryPackage,
    ∃ _finiteExtinction :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage,
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) ↔
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism := by
  constructor
  · intro payload
    exact
      dependency_milestone_requirements_payload_of_dependencies
        (poincareProofDependencies_of_package_layer_requirements_payload
          payload)
  · intro payload
    exact
      dependency_package_layer_requirements_payload_of_dependencies
        (poincareProofDependencies_of_milestone_requirements_payload
          payload)

/--
The package-layer/milestone payload bridge is exactly the pair of constructors
through the aggregate dependency package.
-/
theorem package_layer_requirements_iff_milestone_requirements_eq :
    package_layer_requirements_iff_milestone_requirements.{u} =
      ⟨ (fun payload =>
          dependency_milestone_requirements_payload_of_dependencies
            (poincareProofDependencies_of_package_layer_requirements_payload
              payload))
      , (fun payload =>
          dependency_package_layer_requirements_payload_of_dependencies
            (poincareProofDependencies_of_milestone_requirements_payload
              payload)) ⟩ := by
  apply Subsingleton.elim

/--
The component-slot and milestone requirement payloads are equivalent routes to
the same aggregate dependency package.
-/
theorem component_requirements_iff_milestone_requirements :
    (∃ _smoothability :
      dependencyComponentRequirement.{u} DependencyComponentSlot.smoothabilityComponent,
    ∃ _surgery :
      dependencyComponentRequirement.{u} DependencyComponentSlot.surgeryComponent,
      dependencyComponentRequirement.{u} DependencyComponentSlot.topologyComponent) ↔
      ∃ _smoothabilityBridge :
        dependencyMilestoneRequirement.{u} DependencyMilestone.smoothabilityBridge,
      ∃ _ricciFlowAnalyticFoundation :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowAnalyticFoundation,
      ∃ _ricciFlowWithSurgery :
        dependencyMilestoneRequirement.{u} DependencyMilestone.ricciFlowWithSurgery,
      ∃ _perelmanSingularityControl :
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl,
      ∃ _finiteExtinction :
        dependencyMilestoneRequirement.{u} DependencyMilestone.finiteExtinction,
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.extinctionToSphereHomeomorphism := by
  constructor
  · intro payload
    exact
      dependency_milestone_requirements_payload_of_dependencies
        (poincareProofDependencies_of_component_requirements_payload payload)
  · intro payload
    exact
      dependency_component_requirements_payload_of_dependencies
        (poincareProofDependencies_of_milestone_requirements_payload payload)

/--
The component/milestone payload bridge is exactly the pair of constructors
through the aggregate dependency package.
-/
theorem component_requirements_iff_milestone_requirements_eq :
    component_requirements_iff_milestone_requirements.{u} =
      ⟨ (fun payload =>
          dependency_milestone_requirements_payload_of_dependencies
            (poincareProofDependencies_of_component_requirements_payload
              payload))
      , (fun payload =>
          dependency_component_requirements_payload_of_dependencies
            (poincareProofDependencies_of_milestone_requirements_payload
              payload)) ⟩ := by
  apply Subsingleton.elim

/-- The smoothability milestone is discharged by the smoothability package layer. -/
theorem dependencyLayerForMilestone_smoothabilityBridge :
    dependencyLayerForMilestone DependencyMilestone.smoothabilityBridge =
      DependencyPackageLayer.smoothabilityPackage :=
  rfl

/-- The analytic-foundation milestone is discharged by the analytic package layer. -/
theorem dependencyLayerForMilestone_ricciFlowAnalyticFoundation :
    dependencyLayerForMilestone DependencyMilestone.ricciFlowAnalyticFoundation =
      DependencyPackageLayer.analyticFoundationPackage :=
  rfl

/-- The Ricci-flow-with-surgery milestone is discharged by the surgery package layer. -/
theorem dependencyLayerForMilestone_ricciFlowWithSurgery :
    dependencyLayerForMilestone DependencyMilestone.ricciFlowWithSurgery =
      DependencyPackageLayer.surgeryPackage :=
  rfl

/-- The Perelman-control milestone is discharged by the surgery package layer. -/
theorem dependencyLayerForMilestone_perelmanSingularityControl :
    dependencyLayerForMilestone DependencyMilestone.perelmanSingularityControl =
      DependencyPackageLayer.surgeryPackage :=
  rfl

/-- The finite-extinction milestone is discharged by the finite-extinction package layer. -/
theorem dependencyLayerForMilestone_finiteExtinction :
    dependencyLayerForMilestone DependencyMilestone.finiteExtinction =
      DependencyPackageLayer.finiteExtinctionPackage :=
  rfl

/-- The post-extinction topology milestone is discharged by the topology package layer. -/
theorem dependencyLayerForMilestone_extinctionToSphereHomeomorphism :
    dependencyLayerForMilestone DependencyMilestone.extinctionToSphereHomeomorphism =
      DependencyPackageLayer.topologyPackage :=
  rfl

/-- The smoothability milestone-layer theorem is the direct `rfl` proof. -/
theorem dependencyLayerForMilestone_smoothabilityBridge_eq :
    dependencyLayerForMilestone_smoothabilityBridge =
      (rfl :
        dependencyLayerForMilestone DependencyMilestone.smoothabilityBridge =
          DependencyPackageLayer.smoothabilityPackage) :=
  rfl

/-- The analytic-foundation milestone-layer theorem is the direct `rfl` proof. -/
theorem dependencyLayerForMilestone_ricciFlowAnalyticFoundation_eq :
    dependencyLayerForMilestone_ricciFlowAnalyticFoundation =
      (rfl :
        dependencyLayerForMilestone
            DependencyMilestone.ricciFlowAnalyticFoundation =
          DependencyPackageLayer.analyticFoundationPackage) :=
  rfl

/-- The Ricci-flow-with-surgery milestone-layer theorem is the direct `rfl` proof. -/
theorem dependencyLayerForMilestone_ricciFlowWithSurgery_eq :
    dependencyLayerForMilestone_ricciFlowWithSurgery =
      (rfl :
        dependencyLayerForMilestone DependencyMilestone.ricciFlowWithSurgery =
          DependencyPackageLayer.surgeryPackage) :=
  rfl

/-- The Perelman-control milestone-layer theorem is the direct `rfl` proof. -/
theorem dependencyLayerForMilestone_perelmanSingularityControl_eq :
    dependencyLayerForMilestone_perelmanSingularityControl =
      (rfl :
        dependencyLayerForMilestone
            DependencyMilestone.perelmanSingularityControl =
          DependencyPackageLayer.surgeryPackage) :=
  rfl

/-- The finite-extinction milestone-layer theorem is the direct `rfl` proof. -/
theorem dependencyLayerForMilestone_finiteExtinction_eq :
    dependencyLayerForMilestone_finiteExtinction =
      (rfl :
        dependencyLayerForMilestone DependencyMilestone.finiteExtinction =
          DependencyPackageLayer.finiteExtinctionPackage) :=
  rfl

/-- The topology-extraction milestone-layer theorem is the direct `rfl` proof. -/
theorem dependencyLayerForMilestone_extinctionToSphereHomeomorphism_eq :
    dependencyLayerForMilestone_extinctionToSphereHomeomorphism =
      (rfl :
        dependencyLayerForMilestone
            DependencyMilestone.extinctionToSphereHomeomorphism =
          DependencyPackageLayer.topologyPackage) :=
  rfl

/--
The recorded dependency ledger has a package-layer target for every listed
milestone.
-/
theorem dependency_ledger_has_package_layers :
    dependencyMilestoneLedger.map dependencyLayerForMilestone =
      [ DependencyPackageLayer.smoothabilityPackage
      , DependencyPackageLayer.analyticFoundationPackage
      , DependencyPackageLayer.surgeryPackage
      , DependencyPackageLayer.surgeryPackage
      , DependencyPackageLayer.finiteExtinctionPackage
      , DependencyPackageLayer.topologyPackage
      ] := by
  rfl

/-- The package-layer ledger image theorem is the direct `rfl` proof. -/
theorem dependency_ledger_has_package_layers_eq :
    dependency_ledger_has_package_layers =
      (rfl :
        dependencyMilestoneLedger.map dependencyLayerForMilestone =
          [ DependencyPackageLayer.smoothabilityPackage
          , DependencyPackageLayer.analyticFoundationPackage
          , DependencyPackageLayer.surgeryPackage
          , DependencyPackageLayer.surgeryPackage
          , DependencyPackageLayer.finiteExtinctionPackage
          , DependencyPackageLayer.topologyPackage
          ]) := by
  apply Subsingleton.elim

/-- The mapped dependency ledger contains exactly the concrete package layers. -/
theorem dependency_ledger_package_layer_mem (layer : DependencyPackageLayer) :
    layer ∈ dependencyMilestoneLedger.map dependencyLayerForMilestone ↔
      layer = DependencyPackageLayer.smoothabilityPackage ∨
      layer = DependencyPackageLayer.analyticFoundationPackage ∨
      layer = DependencyPackageLayer.surgeryPackage ∨
      layer = DependencyPackageLayer.finiteExtinctionPackage ∨
      layer = DependencyPackageLayer.topologyPackage := by
  cases layer <;> simp [dependencyMilestoneLedger, dependencyLayerForMilestone]

/--
The package-layer ledger membership theorem is exactly the case split over the
five concrete package layers in the mapped ledger.
-/
theorem dependency_ledger_package_layer_mem_eq :
    dependency_ledger_package_layer_mem =
      (by
        intro layer
        cases layer <;> simp [dependencyMilestoneLedger,
          dependencyLayerForMilestone]) := by
  funext layer
  apply Subsingleton.elim

/--
The recorded dependency ledger folds to the three aggregate component slots.
The analytic, surgery, Perelman, and finite-extinction milestones are all carried
by the surgery component of `PoincareProofDependencies`.
-/
theorem dependency_ledger_has_component_slots :
    dependencyMilestoneLedger.map dependencyComponentForMilestone =
      [ DependencyComponentSlot.smoothabilityComponent
      , DependencyComponentSlot.surgeryComponent
      , DependencyComponentSlot.surgeryComponent
      , DependencyComponentSlot.surgeryComponent
      , DependencyComponentSlot.surgeryComponent
      , DependencyComponentSlot.topologyComponent
      ] := by
  rfl

/-- The component-slot ledger image theorem is the direct `rfl` proof. -/
theorem dependency_ledger_has_component_slots_eq :
    dependency_ledger_has_component_slots =
      (rfl :
        dependencyMilestoneLedger.map dependencyComponentForMilestone =
          [ DependencyComponentSlot.smoothabilityComponent
          , DependencyComponentSlot.surgeryComponent
          , DependencyComponentSlot.surgeryComponent
          , DependencyComponentSlot.surgeryComponent
          , DependencyComponentSlot.surgeryComponent
          , DependencyComponentSlot.topologyComponent
          ]) := by
  apply Subsingleton.elim

/-- The mapped dependency ledger contains exactly the aggregate component slots. -/
theorem dependency_ledger_component_slot_mem (slot : DependencyComponentSlot) :
    slot ∈ dependencyMilestoneLedger.map dependencyComponentForMilestone ↔
      slot = DependencyComponentSlot.smoothabilityComponent ∨
      slot = DependencyComponentSlot.surgeryComponent ∨
      slot = DependencyComponentSlot.topologyComponent := by
  cases slot <;> simp [dependencyMilestoneLedger, dependencyLayerForMilestone,
    dependencyComponentForPackageLayer, dependencyComponentForMilestone]

/--
The component-slot ledger membership theorem is exactly the case split over the
three aggregate component slots in the folded ledger.
-/
theorem dependency_ledger_component_slot_mem_eq :
    dependency_ledger_component_slot_mem =
      (by
        intro slot
        cases slot <;> simp [dependencyMilestoneLedger,
          dependencyLayerForMilestone, dependencyComponentForPackageLayer,
          dependencyComponentForMilestone]) := by
  funext slot
  apply Subsingleton.elim

/--
Map each external blocker through the checked milestone ledger into the concrete
package layers it prevents from becoming unconditional.
-/
def dependencyPackageLayersBlockedByExternalBlocker :
    ExternalFormalizationBlocker → List DependencyPackageLayer :=
  fun blocker =>
    (dependencyMilestonesBlockedByExternalBlocker blocker).map
      dependencyLayerForMilestone

/--
The external-blocker-to-package-layer map is exactly the blocker-to-milestone
map followed by the milestone-to-layer map.
-/
theorem dependencyPackageLayersBlockedByExternalBlocker_eq :
    dependencyPackageLayersBlockedByExternalBlocker =
      fun blocker =>
        (dependencyMilestonesBlockedByExternalBlocker blocker).map
          dependencyLayerForMilestone :=
  rfl

/-- The mathlib shortcut blocker covers the whole package-layer ledger image. -/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyPackageLayers :
    dependencyPackageLayersBlockedByExternalBlocker
        ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
      dependencyMilestoneLedger.map dependencyLayerForMilestone :=
  rfl

/-- The mathlib package-layer blocker theorem is the direct `rfl` proof. -/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyPackageLayers_eq :
    mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyPackageLayers =
      (rfl :
        dependencyPackageLayersBlockedByExternalBlocker
            ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
          dependencyMilestoneLedger.map dependencyLayerForMilestone) :=
  rfl

/-- The Ricci-specific geometry blocker lands on the analytic package layer. -/
theorem ricciSpecificGeometrySurface_blocks_analyticFoundationPackage :
    dependencyPackageLayersBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciSpecificGeometrySurface =
      [DependencyPackageLayer.analyticFoundationPackage] :=
  rfl

/-- The Ricci-specific package-layer blocker theorem is the direct `rfl` proof. -/
theorem ricciSpecificGeometrySurface_blocks_analyticFoundationPackage_eq :
    ricciSpecificGeometrySurface_blocks_analyticFoundationPackage =
      (rfl :
        dependencyPackageLayersBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciSpecificGeometrySurface =
          [DependencyPackageLayer.analyticFoundationPackage]) :=
  rfl

/--
The surgery-side blocker lands on the surgery and finite-extinction package
layers, with both surgery-side milestones retaining their ledger entries.
-/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryPackageLayers :
    dependencyPackageLayersBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
      [ DependencyPackageLayer.surgeryPackage
      , DependencyPackageLayer.surgeryPackage
      , DependencyPackageLayer.finiteExtinctionPackage
      ] :=
  rfl

/-- The surgery-side package-layer blocker theorem is the direct `rfl` proof. -/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryPackageLayers_eq :
    ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryPackageLayers =
      (rfl :
        dependencyPackageLayersBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
          [ DependencyPackageLayer.surgeryPackage
          , DependencyPackageLayer.surgeryPackage
          , DependencyPackageLayer.finiteExtinctionPackage
          ]) :=
  rfl

/--
An external blocker reaches the whole package-layer ledger image exactly when
it is the mathlib 3D Poincare proof-wanted shortcut.
-/
theorem externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted
    (blocker : ExternalFormalizationBlocker) :
    dependencyPackageLayersBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyLayerForMilestone ↔
      blocker =
        ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted := by
  cases blocker <;> simp [dependencyPackageLayersBlockedByExternalBlocker,
    dependencyMilestonesBlockedByExternalBlocker, dependencyMilestoneLedger,
    dependencyLayerForMilestone]

/-- The whole package-layer blocker characterization is the blocker case split. -/
theorem externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted_eq :
    externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted =
      (by
        intro blocker
        cases blocker <;> simp [dependencyPackageLayersBlockedByExternalBlocker,
          dependencyMilestonesBlockedByExternalBlocker, dependencyMilestoneLedger,
          dependencyLayerForMilestone]) := by
  funext blocker
  apply Subsingleton.elim

/--
Having statement-adapter endpoints is equivalent to reaching the whole
package-layer ledger image.
-/
theorem externalBlocker_statementAdapters_nonempty_iff_blocks_dependencyPackageLayers
    (blocker : ExternalFormalizationBlocker) :
    (∃ adapter : MathlibPoincareStatementAdapter,
        adapter ∈ statementAdaptersBlockedByExternalBlocker blocker) ↔
      dependencyPackageLayersBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyLayerForMilestone := by
  rw [externalBlocker_statementAdapters_nonempty_iff_mathlibProofWanted,
    externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted]

/-- The adapter/package-layer bridge is the shared mathlib-blocker characterization. -/
theorem externalBlocker_statementAdapters_nonempty_iff_blocks_dependencyPackageLayers_eq :
    externalBlocker_statementAdapters_nonempty_iff_blocks_dependencyPackageLayers =
      (by
        intro blocker
        rw [externalBlocker_statementAdapters_nonempty_iff_mathlibProofWanted,
          externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted]) := by
  funext blocker
  apply Subsingleton.elim

/--
Having exactly the full statement-adapter ledger is equivalent to reaching the
whole package-layer ledger image.
-/
theorem externalBlocker_statementAdapters_eq_adapterLedger_iff_blocks_dependencyPackageLayers
    (blocker : ExternalFormalizationBlocker) :
    statementAdaptersBlockedByExternalBlocker blocker =
        mathlibPoincareStatementAdapterLedger ↔
      dependencyPackageLayersBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyLayerForMilestone := by
  rw [externalBlocker_statementAdapters_eq_adapterLedger_iff_mathlibProofWanted,
    externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted]

/-- The full-adapter/package-layer bridge is the shared mathlib characterization. -/
theorem externalBlocker_statementAdapters_eq_adapterLedger_iff_blocks_dependencyPackageLayers_eq :
    externalBlocker_statementAdapters_eq_adapterLedger_iff_blocks_dependencyPackageLayers =
      (by
        intro blocker
        rw [externalBlocker_statementAdapters_eq_adapterLedger_iff_mathlibProofWanted,
          externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted]) := by
  funext blocker
  apply Subsingleton.elim

/--
Blocking the whole dependency milestone ledger is equivalent to reaching the
whole package-layer ledger image.
-/
theorem externalBlocker_blocks_dependencyMilestoneLedger_iff_blocks_dependencyPackageLayers
    (blocker : ExternalFormalizationBlocker) :
    dependencyMilestonesBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger ↔
      dependencyPackageLayersBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyLayerForMilestone := by
  rw [externalBlocker_blocks_dependencyMilestoneLedger_iff_mathlibProofWanted,
    externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted]

/-- The milestone/package-layer blocker bridge is the shared mathlib characterization. -/
theorem externalBlocker_blocks_dependencyMilestoneLedger_iff_blocks_dependencyPackageLayers_eq :
    externalBlocker_blocks_dependencyMilestoneLedger_iff_blocks_dependencyPackageLayers =
      (by
        intro blocker
        rw [externalBlocker_blocks_dependencyMilestoneLedger_iff_mathlibProofWanted,
          externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted]) := by
  funext blocker
  apply Subsingleton.elim

/--
Every milestone named by an external blocker maps to a package layer named by
the same blocker.
-/
theorem externalBlocker_milestone_layer_mem_dependencyPackageLayers
    (blocker : ExternalFormalizationBlocker) {milestone : DependencyMilestone} :
    milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker →
      dependencyLayerForMilestone milestone ∈
        dependencyPackageLayersBlockedByExternalBlocker blocker := by
  intro h
  rw [dependencyPackageLayersBlockedByExternalBlocker_eq]
  exact List.mem_map.mpr ⟨milestone, h, rfl⟩

/--
The theorem mapping externally blocked milestones into blocked package layers is
exactly the forward `List.mem_map` route.
-/
theorem externalBlocker_milestone_layer_mem_dependencyPackageLayers_eq :
    externalBlocker_milestone_layer_mem_dependencyPackageLayers =
      (by
        intro blocker milestone h
        rw [dependencyPackageLayersBlockedByExternalBlocker_eq]
        exact List.mem_map.mpr ⟨milestone, h, rfl⟩) := by
  funext blocker milestone
  apply Subsingleton.elim

/--
Every package layer named by an external blocker has a blocked milestone witness
mapping to that layer.
-/
theorem externalBlocker_packageLayer_mem_milestone_layer_image
    (blocker : ExternalFormalizationBlocker) {layer : DependencyPackageLayer} :
    layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker →
      ∃ milestone : DependencyMilestone,
        milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker ∧
          dependencyLayerForMilestone milestone = layer := by
  intro h
  rw [dependencyPackageLayersBlockedByExternalBlocker_eq] at h
  exact List.mem_map.mp h

/--
The theorem witnessing blocked package layers by blocked milestones is exactly
the reverse `List.mem_map` route after the blocker-to-package-layer definition.
-/
theorem externalBlocker_packageLayer_mem_milestone_layer_image_eq :
    externalBlocker_packageLayer_mem_milestone_layer_image =
      (by
        intro blocker layer h
        rw [dependencyPackageLayersBlockedByExternalBlocker_eq] at h
        exact List.mem_map.mp h) := by
  funext blocker layer
  apply Subsingleton.elim

/--
A package layer is named by an external blocker exactly when it is the layer
image of a milestone named by that same blocker.
-/
theorem externalBlocker_packageLayer_mem_iff_milestone_layer_image
    (blocker : ExternalFormalizationBlocker) (layer : DependencyPackageLayer) :
    layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker ↔
      ∃ milestone : DependencyMilestone,
        milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker ∧
          dependencyLayerForMilestone milestone = layer := by
  constructor
  · exact externalBlocker_packageLayer_mem_milestone_layer_image blocker
  · rintro ⟨milestone, hMilestone, hLayer⟩
    simpa [hLayer] using
      externalBlocker_milestone_layer_mem_dependencyPackageLayers
        blocker hMilestone

/--
The package-layer/milestone image iff is the pair of the two `List.mem_map`
routes.
-/
theorem externalBlocker_packageLayer_mem_iff_milestone_layer_image_eq :
    externalBlocker_packageLayer_mem_iff_milestone_layer_image =
      (by
        intro blocker layer
        constructor
        · exact externalBlocker_packageLayer_mem_milestone_layer_image blocker
        · rintro ⟨milestone, hMilestone, hLayer⟩
          simpa [hLayer] using
            externalBlocker_milestone_layer_mem_dependencyPackageLayers
              blocker hMilestone) := by
  funext blocker layer
  apply Subsingleton.elim

/--
Every package layer named by an external blocker is present in the checked
milestone package-layer image.
-/
theorem externalBlocker_packageLayers_mem_dependencyLedgerPackageLayers
    (blocker : ExternalFormalizationBlocker) {layer : DependencyPackageLayer} :
    layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker →
      layer ∈ dependencyMilestoneLedger.map dependencyLayerForMilestone := by
  cases blocker <;> cases layer <;> simp
    [dependencyPackageLayersBlockedByExternalBlocker,
      dependencyMilestonesBlockedByExternalBlocker,
      dependencyMilestoneLedger, dependencyLayerForMilestone]

/--
The theorem asserting that externally blocked package layers are ledger package
layers is exactly the blocker/layer case split.
-/
theorem externalBlocker_packageLayers_mem_dependencyLedgerPackageLayers_eq :
    externalBlocker_packageLayers_mem_dependencyLedgerPackageLayers =
      (by
        intro blocker layer
        cases blocker <;> cases layer <;> simp
          [dependencyPackageLayersBlockedByExternalBlocker,
            dependencyMilestonesBlockedByExternalBlocker,
            dependencyMilestoneLedger, dependencyLayerForMilestone]) := by
  funext blocker layer
  apply Subsingleton.elim

/--
Map each external blocker through the checked milestone ledger into the
aggregate component slots it prevents from becoming unconditional.
-/
def dependencyComponentSlotsBlockedByExternalBlocker :
    ExternalFormalizationBlocker → List DependencyComponentSlot :=
  fun blocker =>
    (dependencyMilestonesBlockedByExternalBlocker blocker).map
      dependencyComponentForMilestone

/--
The external-blocker-to-component-slot map is exactly the blocker-to-milestone
map followed by the milestone-to-component map.
-/
theorem dependencyComponentSlotsBlockedByExternalBlocker_eq :
    dependencyComponentSlotsBlockedByExternalBlocker =
      fun blocker =>
        (dependencyMilestonesBlockedByExternalBlocker blocker).map
          dependencyComponentForMilestone :=
  rfl

/--
Every milestone named by an external blocker maps to a component slot named by
the same blocker.
-/
theorem externalBlocker_milestone_component_mem_dependencyComponentSlots
    (blocker : ExternalFormalizationBlocker) {milestone : DependencyMilestone} :
    milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker →
      dependencyComponentForMilestone milestone ∈
        dependencyComponentSlotsBlockedByExternalBlocker blocker := by
  intro h
  rw [dependencyComponentSlotsBlockedByExternalBlocker_eq]
  exact List.mem_map.mpr ⟨milestone, h, rfl⟩

/--
The theorem mapping externally blocked milestones into blocked component slots
is exactly the forward `List.mem_map` route.
-/
theorem externalBlocker_milestone_component_mem_dependencyComponentSlots_eq :
    externalBlocker_milestone_component_mem_dependencyComponentSlots =
      (by
        intro blocker milestone h
        rw [dependencyComponentSlotsBlockedByExternalBlocker_eq]
        exact List.mem_map.mpr ⟨milestone, h, rfl⟩) := by
  funext blocker milestone
  apply Subsingleton.elim

/--
Every component slot named by an external blocker has a blocked milestone
witness mapping to that slot.
-/
theorem externalBlocker_componentSlot_mem_milestone_component_image
    (blocker : ExternalFormalizationBlocker) {slot : DependencyComponentSlot} :
    slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker →
      ∃ milestone : DependencyMilestone,
        milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker ∧
          dependencyComponentForMilestone milestone = slot := by
  intro h
  rw [dependencyComponentSlotsBlockedByExternalBlocker_eq] at h
  exact List.mem_map.mp h

/--
The theorem witnessing blocked component slots by blocked milestones is exactly
the reverse `List.mem_map` route after the blocker-to-component-slot definition.
-/
theorem externalBlocker_componentSlot_mem_milestone_component_image_eq :
    externalBlocker_componentSlot_mem_milestone_component_image =
      (by
        intro blocker slot h
        rw [dependencyComponentSlotsBlockedByExternalBlocker_eq] at h
        exact List.mem_map.mp h) := by
  funext blocker slot
  apply Subsingleton.elim

/--
A component slot is named by an external blocker exactly when it is the
component image of a milestone named by that same blocker.
-/
theorem externalBlocker_componentSlot_mem_iff_milestone_component_image
    (blocker : ExternalFormalizationBlocker) (slot : DependencyComponentSlot) :
    slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker ↔
      ∃ milestone : DependencyMilestone,
        milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker ∧
          dependencyComponentForMilestone milestone = slot := by
  constructor
  · exact externalBlocker_componentSlot_mem_milestone_component_image blocker
  · rintro ⟨milestone, hMilestone, hSlot⟩
    simpa [hSlot] using
      externalBlocker_milestone_component_mem_dependencyComponentSlots
        blocker hMilestone

/--
The component-slot/milestone image iff is the pair of the two `List.mem_map`
routes.
-/
theorem externalBlocker_componentSlot_mem_iff_milestone_component_image_eq :
    externalBlocker_componentSlot_mem_iff_milestone_component_image =
      (by
        intro blocker slot
        constructor
        · exact externalBlocker_componentSlot_mem_milestone_component_image blocker
        · rintro ⟨milestone, hMilestone, hSlot⟩
          simpa [hSlot] using
            externalBlocker_milestone_component_mem_dependencyComponentSlots
              blocker hMilestone) := by
  funext blocker slot
  apply Subsingleton.elim

/--
The external-blocker-to-component-slot map is also the blocker-to-package-layer
map followed by the package-layer-to-component fold.
-/
theorem dependencyComponentSlotsBlockedByExternalBlocker_eq_package_layer_map :
    dependencyComponentSlotsBlockedByExternalBlocker =
      fun blocker =>
        (dependencyPackageLayersBlockedByExternalBlocker blocker).map
          dependencyComponentForPackageLayer := by
  funext blocker
  cases blocker <;> rfl

/-- The blocker component-slot/package-layer bridge is the blocker case split. -/
theorem dependencyComponentSlotsBlockedByExternalBlocker_eq_package_layer_map_eq :
    dependencyComponentSlotsBlockedByExternalBlocker_eq_package_layer_map =
      (by
        funext blocker
        cases blocker <;> rfl) := by
  apply Subsingleton.elim

/-- The mathlib shortcut blocker covers the whole component-slot ledger image. -/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyComponentSlots :
    dependencyComponentSlotsBlockedByExternalBlocker
        ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
      dependencyMilestoneLedger.map dependencyComponentForMilestone :=
  rfl

/-- The mathlib component-slot blocker theorem is the direct `rfl` proof. -/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyComponentSlots_eq :
    mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyComponentSlots =
      (rfl :
        dependencyComponentSlotsBlockedByExternalBlocker
            ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
          dependencyMilestoneLedger.map dependencyComponentForMilestone) :=
  rfl

/-- The Ricci-specific geometry blocker lands on the surgery component slot. -/
theorem ricciSpecificGeometrySurface_blocks_surgeryComponentSlot :
    dependencyComponentSlotsBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciSpecificGeometrySurface =
      [DependencyComponentSlot.surgeryComponent] :=
  rfl

/-- The Ricci-specific component-slot blocker theorem is the direct `rfl` proof. -/
theorem ricciSpecificGeometrySurface_blocks_surgeryComponentSlot_eq :
    ricciSpecificGeometrySurface_blocks_surgeryComponentSlot =
      (rfl :
        dependencyComponentSlotsBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciSpecificGeometrySurface =
          [DependencyComponentSlot.surgeryComponent]) :=
  rfl

/-- The surgery-side blocker lands on the surgery component slot entries. -/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryComponentSlots :
    dependencyComponentSlotsBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
      [ DependencyComponentSlot.surgeryComponent
      , DependencyComponentSlot.surgeryComponent
      , DependencyComponentSlot.surgeryComponent
      ] :=
  rfl

/-- The surgery-side component-slot blocker theorem is the direct `rfl` proof. -/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryComponentSlots_eq :
    ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryComponentSlots =
      (rfl :
        dependencyComponentSlotsBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
          [ DependencyComponentSlot.surgeryComponent
          , DependencyComponentSlot.surgeryComponent
          , DependencyComponentSlot.surgeryComponent
          ]) :=
  rfl

/--
An external blocker reaches the whole component-slot ledger image exactly when
it is the mathlib 3D Poincare proof-wanted shortcut.
-/
theorem externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted
    (blocker : ExternalFormalizationBlocker) :
    dependencyComponentSlotsBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyComponentForMilestone ↔
      blocker =
        ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted := by
  cases blocker <;> simp [dependencyComponentSlotsBlockedByExternalBlocker,
    dependencyMilestonesBlockedByExternalBlocker, dependencyMilestoneLedger,
    dependencyLayerForMilestone, dependencyComponentForPackageLayer,
    dependencyComponentForMilestone]

/-- The whole component-slot blocker characterization is the blocker case split. -/
theorem externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted_eq :
    externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted =
      (by
        intro blocker
        cases blocker <;> simp [dependencyComponentSlotsBlockedByExternalBlocker,
          dependencyMilestonesBlockedByExternalBlocker, dependencyMilestoneLedger,
          dependencyLayerForMilestone, dependencyComponentForPackageLayer,
          dependencyComponentForMilestone]) := by
  funext blocker
  apply Subsingleton.elim

/--
Having statement-adapter endpoints is equivalent to reaching the whole
component-slot ledger image.
-/
theorem externalBlocker_statementAdapters_nonempty_iff_blocks_dependencyComponentSlots
    (blocker : ExternalFormalizationBlocker) :
    (∃ adapter : MathlibPoincareStatementAdapter,
        adapter ∈ statementAdaptersBlockedByExternalBlocker blocker) ↔
      dependencyComponentSlotsBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyComponentForMilestone := by
  rw [externalBlocker_statementAdapters_nonempty_iff_mathlibProofWanted,
    externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]

/-- The adapter/component-slot bridge is the shared mathlib-blocker characterization. -/
theorem externalBlocker_statementAdapters_nonempty_iff_blocks_dependencyComponentSlots_eq :
    externalBlocker_statementAdapters_nonempty_iff_blocks_dependencyComponentSlots =
      (by
        intro blocker
        rw [externalBlocker_statementAdapters_nonempty_iff_mathlibProofWanted,
          externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]) := by
  funext blocker
  apply Subsingleton.elim

/--
Having exactly the full statement-adapter ledger is equivalent to reaching the
whole component-slot ledger image.
-/
theorem externalBlocker_statementAdapters_eq_adapterLedger_iff_blocks_dependencyComponentSlots
    (blocker : ExternalFormalizationBlocker) :
    statementAdaptersBlockedByExternalBlocker blocker =
        mathlibPoincareStatementAdapterLedger ↔
      dependencyComponentSlotsBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyComponentForMilestone := by
  rw [externalBlocker_statementAdapters_eq_adapterLedger_iff_mathlibProofWanted,
    externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]

/-- The full-adapter/component-slot bridge is the shared mathlib characterization. -/
theorem externalBlocker_statementAdapters_eq_adapterLedger_iff_blocks_dependencyComponentSlots_eq :
    externalBlocker_statementAdapters_eq_adapterLedger_iff_blocks_dependencyComponentSlots =
      (by
        intro blocker
        rw [externalBlocker_statementAdapters_eq_adapterLedger_iff_mathlibProofWanted,
          externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]) := by
  funext blocker
  apply Subsingleton.elim

/--
Blocking the whole dependency milestone ledger is equivalent to reaching the
whole component-slot ledger image.
-/
theorem externalBlocker_blocks_dependencyMilestoneLedger_iff_blocks_dependencyComponentSlots
    (blocker : ExternalFormalizationBlocker) :
    dependencyMilestonesBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger ↔
      dependencyComponentSlotsBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyComponentForMilestone := by
  rw [externalBlocker_blocks_dependencyMilestoneLedger_iff_mathlibProofWanted,
    externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]

/-- The milestone/component-slot blocker bridge is the shared mathlib characterization. -/
theorem externalBlocker_blocks_dependencyMilestoneLedger_iff_blocks_dependencyComponentSlots_eq :
    externalBlocker_blocks_dependencyMilestoneLedger_iff_blocks_dependencyComponentSlots =
      (by
        intro blocker
        rw [externalBlocker_blocks_dependencyMilestoneLedger_iff_mathlibProofWanted,
          externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]) := by
  funext blocker
  apply Subsingleton.elim

/--
Reaching the whole package-layer ledger image is equivalent to reaching the
whole component-slot ledger image.
-/
theorem externalBlocker_blocks_dependencyPackageLayers_iff_blocks_dependencyComponentSlots
    (blocker : ExternalFormalizationBlocker) :
    dependencyPackageLayersBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyLayerForMilestone ↔
      dependencyComponentSlotsBlockedByExternalBlocker blocker =
        dependencyMilestoneLedger.map dependencyComponentForMilestone := by
  rw [externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted,
    externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]

/-- The package-layer/component-slot blocker bridge is the shared mathlib characterization. -/
theorem externalBlocker_blocks_dependencyPackageLayers_iff_blocks_dependencyComponentSlots_eq :
    externalBlocker_blocks_dependencyPackageLayers_iff_blocks_dependencyComponentSlots =
      (by
        intro blocker
        rw [externalBlocker_blocks_dependencyPackageLayers_iff_mathlibProofWanted,
          externalBlocker_blocks_dependencyComponentSlots_iff_mathlibProofWanted]) := by
  funext blocker
  apply Subsingleton.elim

/--
Every package layer named by an external blocker maps to a component slot named
by the same blocker.
-/
theorem externalBlocker_packageLayer_component_mem_dependencyComponentSlots
    (blocker : ExternalFormalizationBlocker) {layer : DependencyPackageLayer} :
    layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker →
      dependencyComponentForPackageLayer layer ∈
        dependencyComponentSlotsBlockedByExternalBlocker blocker := by
  intro h
  rw [dependencyComponentSlotsBlockedByExternalBlocker_eq_package_layer_map]
  exact List.mem_map.mpr ⟨layer, h, rfl⟩

/--
The theorem mapping externally blocked package layers into blocked component
slots is exactly the blocker/layer case split.
-/
theorem externalBlocker_packageLayer_component_mem_dependencyComponentSlots_eq :
    externalBlocker_packageLayer_component_mem_dependencyComponentSlots =
      (by
        intro blocker layer h
        rw [dependencyComponentSlotsBlockedByExternalBlocker_eq_package_layer_map]
        exact List.mem_map.mpr ⟨layer, h, rfl⟩) := by
  funext blocker layer
  apply Subsingleton.elim

/--
Every component slot named by an external blocker has a blocked package-layer
witness mapping to that slot.
-/
theorem externalBlocker_componentSlot_mem_packageLayer_component_image
    (blocker : ExternalFormalizationBlocker) {slot : DependencyComponentSlot} :
    slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker →
      ∃ layer : DependencyPackageLayer,
        layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker ∧
          dependencyComponentForPackageLayer layer = slot := by
  intro h
  rw [dependencyComponentSlotsBlockedByExternalBlocker_eq_package_layer_map] at h
  exact List.mem_map.mp h

/--
The theorem witnessing blocked component slots by blocked package layers is
exactly the reverse `List.mem_map` route after the map factorization.
-/
theorem externalBlocker_componentSlot_mem_packageLayer_component_image_eq :
    externalBlocker_componentSlot_mem_packageLayer_component_image =
      (by
        intro blocker slot h
        rw [dependencyComponentSlotsBlockedByExternalBlocker_eq_package_layer_map] at h
        exact List.mem_map.mp h) := by
  funext blocker slot
  apply Subsingleton.elim

/--
A component slot is named by an external blocker exactly when it is the
component image of a package layer named by that same blocker.
-/
theorem externalBlocker_componentSlot_mem_iff_packageLayer_component_image
    (blocker : ExternalFormalizationBlocker) (slot : DependencyComponentSlot) :
    slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker ↔
      ∃ layer : DependencyPackageLayer,
        layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker ∧
          dependencyComponentForPackageLayer layer = slot := by
  constructor
  · exact externalBlocker_componentSlot_mem_packageLayer_component_image blocker
  · rintro ⟨layer, hLayer, hSlot⟩
    simpa [hSlot] using
      externalBlocker_packageLayer_component_mem_dependencyComponentSlots
        blocker hLayer

/--
The component-slot/package-layer image iff is the pair of the two membership
bridges.
-/
theorem externalBlocker_componentSlot_mem_iff_packageLayer_component_image_eq :
    externalBlocker_componentSlot_mem_iff_packageLayer_component_image =
      (by
        intro blocker slot
        constructor
        · exact externalBlocker_componentSlot_mem_packageLayer_component_image
            blocker
        · rintro ⟨layer, hLayer, hSlot⟩
          simpa [hSlot] using
            externalBlocker_packageLayer_component_mem_dependencyComponentSlots
              blocker hLayer) := by
  funext blocker slot
  apply Subsingleton.elim

/--
The milestone-component and package-layer-component witness descriptions of a
blocked component slot are equivalent for each external blocker.
-/
theorem externalBlocker_componentSlot_milestone_image_iff_packageLayer_image
    (blocker : ExternalFormalizationBlocker) (slot : DependencyComponentSlot) :
    (∃ milestone : DependencyMilestone,
        milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker ∧
          dependencyComponentForMilestone milestone = slot) ↔
      ∃ layer : DependencyPackageLayer,
        layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker ∧
          dependencyComponentForPackageLayer layer = slot := by
  rw [← externalBlocker_componentSlot_mem_iff_milestone_component_image,
    externalBlocker_componentSlot_mem_iff_packageLayer_component_image]

/--
The component-slot witness-form equivalence is exactly the route through the
shared component-slot membership proposition.
-/
theorem externalBlocker_componentSlot_milestone_image_iff_packageLayer_image_eq :
    externalBlocker_componentSlot_milestone_image_iff_packageLayer_image =
      (by
        intro blocker slot
        rw [← externalBlocker_componentSlot_mem_iff_milestone_component_image,
          externalBlocker_componentSlot_mem_iff_packageLayer_component_image]) := by
  funext blocker slot
  apply Subsingleton.elim

/--
A blocked component slot whose component requirement has been discharged yields
a blocked package layer whose concrete package-layer requirement is discharged.
-/
theorem externalBlocker_blockedComponentRequirement_to_packageLayerRequirement
    (blocker : ExternalFormalizationBlocker) (slot : DependencyComponentSlot)
    (hslot : slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker)
    (hrequirement : dependencyComponentRequirement.{u} slot) :
    ∃ layer : DependencyPackageLayer,
      layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker ∧
        dependencyPackageLayerRequirement.{u} layer := by
  rcases externalBlocker_componentSlot_mem_packageLayer_component_image
      blocker (slot := slot) hslot with
    ⟨layer, hmem, hcomponent⟩
  exact
    ⟨layer, hmem,
      dependencyPackageLayerRequirement_of_componentRequirement layer
        (by simpa [hcomponent] using hrequirement)⟩

/--
The blocker component-slot to package-layer requirement bridge is exactly the
package-layer witness route followed by the component-carried requirement
bridge.
-/
theorem externalBlocker_blockedComponentRequirement_to_packageLayerRequirement_eq :
    externalBlocker_blockedComponentRequirement_to_packageLayerRequirement.{u} =
      (by
        intro blocker slot hslot hrequirement
        rcases externalBlocker_componentSlot_mem_packageLayer_component_image
            blocker (slot := slot) hslot with
          ⟨layer, hmem, hcomponent⟩
        exact
          ⟨layer, hmem,
            dependencyPackageLayerRequirement_of_componentRequirement layer
              (by simpa [hcomponent] using hrequirement)⟩) := by
  funext blocker slot hslot hrequirement
  apply Subsingleton.elim

/--
A blocked component slot whose component requirement has been discharged yields
a blocked milestone whose concrete milestone requirement is discharged.
-/
theorem externalBlocker_blockedComponentRequirement_to_milestoneRequirement
    (blocker : ExternalFormalizationBlocker) (slot : DependencyComponentSlot)
    (hslot : slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker)
    (hrequirement : dependencyComponentRequirement.{u} slot) :
    ∃ milestone : DependencyMilestone,
      milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker ∧
        dependencyMilestoneRequirement.{u} milestone := by
  rcases externalBlocker_componentSlot_mem_milestone_component_image
      blocker (slot := slot) hslot with
    ⟨milestone, hmem, hcomponent⟩
  exact
    ⟨milestone, hmem,
      dependencyMilestoneRequirement_of_componentRequirement milestone
        (by simpa [hcomponent] using hrequirement)⟩

/--
The blocker component-slot to milestone requirement bridge is exactly the
milestone witness route followed by the component-carried requirement bridge.
-/
theorem externalBlocker_blockedComponentRequirement_to_milestoneRequirement_eq :
    externalBlocker_blockedComponentRequirement_to_milestoneRequirement.{u} =
      (by
        intro blocker slot hslot hrequirement
        rcases externalBlocker_componentSlot_mem_milestone_component_image
            blocker (slot := slot) hslot with
          ⟨milestone, hmem, hcomponent⟩
        exact
          ⟨milestone, hmem,
            dependencyMilestoneRequirement_of_componentRequirement milestone
              (by simpa [hcomponent] using hrequirement)⟩) := by
  funext blocker slot hslot hrequirement
  apply Subsingleton.elim

/--
Aggregate dependencies discharge a blocked component slot by producing a
blocked package-layer witness whose concrete package-layer requirement holds.
-/
theorem externalBlocker_blockedComponentSlot_packageLayerRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (blocker : ExternalFormalizationBlocker) (slot : DependencyComponentSlot)
    (hslot : slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker) :
    ∃ layer : DependencyPackageLayer,
      layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker ∧
        dependencyPackageLayerRequirement.{u} layer :=
  externalBlocker_blockedComponentRequirement_to_packageLayerRequirement
    blocker slot hslot
    (dependencyComponentRequirement_of_dependencies dependencies slot)

/--
The aggregate-dependency package-layer blocker witness is exactly the
component-slot requirement projection followed by the blocker witness bridge.
-/
theorem externalBlocker_blockedComponentSlot_packageLayerRequirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    externalBlocker_blockedComponentSlot_packageLayerRequirement_of_dependencies
        dependencies =
      (fun blocker slot hslot =>
        externalBlocker_blockedComponentRequirement_to_packageLayerRequirement
          blocker slot hslot
          (dependencyComponentRequirement_of_dependencies dependencies slot)) := by
  funext blocker slot hslot
  apply Subsingleton.elim

/--
Aggregate dependencies discharge a blocked component slot by producing a
blocked milestone witness whose concrete milestone requirement holds.
-/
theorem externalBlocker_blockedComponentSlot_milestoneRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (blocker : ExternalFormalizationBlocker) (slot : DependencyComponentSlot)
    (hslot : slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker) :
    ∃ milestone : DependencyMilestone,
      milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker ∧
        dependencyMilestoneRequirement.{u} milestone :=
  externalBlocker_blockedComponentRequirement_to_milestoneRequirement
    blocker slot hslot
    (dependencyComponentRequirement_of_dependencies dependencies slot)

/--
The aggregate-dependency milestone blocker witness is exactly the component-slot
requirement projection followed by the blocker witness bridge.
-/
theorem externalBlocker_blockedComponentSlot_milestoneRequirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    externalBlocker_blockedComponentSlot_milestoneRequirement_of_dependencies
        dependencies =
      (fun blocker slot hslot =>
        externalBlocker_blockedComponentRequirement_to_milestoneRequirement
          blocker slot hslot
          (dependencyComponentRequirement_of_dependencies dependencies slot)) := by
  funext blocker slot hslot
  apply Subsingleton.elim

/--
Aggregate dependencies discharge every package layer named by an external
formalization blocker.
-/
theorem externalBlocker_blockedPackageLayerRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (blocker : ExternalFormalizationBlocker) {layer : DependencyPackageLayer}
    (_hlayer : layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker) :
    dependencyPackageLayerRequirement.{u} layer :=
  dependencyPackageLayerRequirement_of_dependencies dependencies layer

/--
The blocker package-layer discharge route is exactly the aggregate dependency
package-layer projection, with blocker membership recorded only as provenance.
-/
theorem externalBlocker_blockedPackageLayerRequirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    externalBlocker_blockedPackageLayerRequirement_of_dependencies dependencies =
      (fun _blocker layer _hlayer =>
        dependencyPackageLayerRequirement_of_dependencies dependencies layer) := by
  funext blocker layer hlayer
  apply Subsingleton.elim

/--
Aggregate dependencies discharge every milestone named by an external
formalization blocker.
-/
theorem externalBlocker_blockedMilestoneRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (blocker : ExternalFormalizationBlocker) {milestone : DependencyMilestone}
    (_hmilestone :
      milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker) :
    dependencyMilestoneRequirement.{u} milestone :=
  dependencyMilestoneRequirement_of_dependencies dependencies milestone

/--
The blocker milestone discharge route is exactly the aggregate dependency
milestone projection, with blocker membership recorded only as provenance.
-/
theorem externalBlocker_blockedMilestoneRequirement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    externalBlocker_blockedMilestoneRequirement_of_dependencies dependencies =
      (fun _blocker milestone _hmilestone =>
        dependencyMilestoneRequirement_of_dependencies dependencies milestone) := by
  funext blocker milestone hmilestone
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies discharge every package layer named
by an external formalization blocker after forgetting the extra boundary data.
-/
theorem externalBlocker_blockedPackageLayerRequirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (blocker : ExternalFormalizationBlocker) {layer : DependencyPackageLayer}
    (hlayer : layer ∈ dependencyPackageLayersBlockedByExternalBlocker blocker) :
    dependencyPackageLayerRequirement.{u} layer :=
  externalBlocker_blockedPackageLayerRequirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)
    blocker hlayer

/--
The strengthened blocker package-layer discharge route is exactly the ordinary
blocker discharge route applied to the forgetful dependency package.
-/
theorem externalBlocker_blockedPackageLayerRequirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    externalBlocker_blockedPackageLayerRequirement_of_equation_boundary_dependencies
        dependencies =
      externalBlocker_blockedPackageLayerRequirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  funext blocker layer hlayer
  apply Subsingleton.elim

/--
Strengthened equation-boundary dependencies discharge every milestone named by
an external formalization blocker after forgetting the extra boundary data.
-/
theorem externalBlocker_blockedMilestoneRequirement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (blocker : ExternalFormalizationBlocker) {milestone : DependencyMilestone}
    (hmilestone :
      milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker) :
    dependencyMilestoneRequirement.{u} milestone :=
  externalBlocker_blockedMilestoneRequirement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)
    blocker hmilestone

/--
The strengthened blocker milestone discharge route is exactly the ordinary
blocker discharge route applied to the forgetful dependency package.
-/
theorem externalBlocker_blockedMilestoneRequirement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    externalBlocker_blockedMilestoneRequirement_of_equation_boundary_dependencies
        dependencies =
      externalBlocker_blockedMilestoneRequirement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  funext blocker milestone hmilestone
  apply Subsingleton.elim

/--
Every component slot named by an external blocker is present in the checked
milestone component-slot image.
-/
theorem externalBlocker_componentSlots_mem_dependencyLedgerComponentSlots
    (blocker : ExternalFormalizationBlocker) {slot : DependencyComponentSlot} :
    slot ∈ dependencyComponentSlotsBlockedByExternalBlocker blocker →
      slot ∈ dependencyMilestoneLedger.map dependencyComponentForMilestone := by
  cases blocker <;> cases slot <;> simp
    [dependencyComponentSlotsBlockedByExternalBlocker,
      dependencyMilestonesBlockedByExternalBlocker,
      dependencyMilestoneLedger, dependencyLayerForMilestone,
      dependencyComponentForPackageLayer, dependencyComponentForMilestone]

/--
The theorem asserting that externally blocked component slots are ledger
component slots is exactly the blocker/slot case split.
-/
theorem externalBlocker_componentSlots_mem_dependencyLedgerComponentSlots_eq :
    externalBlocker_componentSlots_mem_dependencyLedgerComponentSlots =
      (by
        intro blocker slot
        cases blocker <;> cases slot <;> simp
          [dependencyComponentSlotsBlockedByExternalBlocker,
            dependencyMilestonesBlockedByExternalBlocker,
            dependencyMilestoneLedger, dependencyLayerForMilestone,
            dependencyComponentForPackageLayer, dependencyComponentForMilestone]) := by
  funext blocker slot
  apply Subsingleton.elim

end Poincare
