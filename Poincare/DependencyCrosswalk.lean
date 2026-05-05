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
The package-layer equivalence is exactly the named forward payload projection
paired with the named reverse constructor.
-/
theorem poincareProofDependencies_iff_package_layer_requirements_eq :
    poincareProofDependencies_iff_package_layer_requirements.{u} =
      ⟨dependency_package_layer_requirements_payload_of_dependencies,
        poincareProofDependencies_of_package_layer_requirements_payload⟩ := by
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

/-- A completed dependency package supplies the requirement for every milestone. -/
theorem dependencyMilestoneRequirement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (milestone : DependencyMilestone) :
    dependencyMilestoneRequirement.{u} milestone := by
  cases milestone <;>
    exact dependencyPackageLayerRequirement_of_dependencies dependencies _

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
The milestone equivalence is exactly the named forward payload projection
paired with the named reverse constructor.
-/
theorem poincareProofDependencies_iff_milestone_requirements_eq :
    poincareProofDependencies_iff_milestone_requirements.{u} =
      ⟨dependency_milestone_requirements_payload_of_dependencies,
        poincareProofDependencies_of_milestone_requirements_payload⟩ := by
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

/-- The mapped dependency ledger contains exactly the aggregate component slots. -/
theorem dependency_ledger_component_slot_mem (slot : DependencyComponentSlot) :
    slot ∈ dependencyMilestoneLedger.map dependencyComponentForMilestone ↔
      slot = DependencyComponentSlot.smoothabilityComponent ∨
      slot = DependencyComponentSlot.surgeryComponent ∨
      slot = DependencyComponentSlot.topologyComponent := by
  cases slot <;> simp [dependencyMilestoneLedger, dependencyLayerForMilestone,
    dependencyComponentForPackageLayer, dependencyComponentForMilestone]

end Poincare
