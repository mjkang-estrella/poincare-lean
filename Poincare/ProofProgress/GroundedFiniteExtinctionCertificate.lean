/-
Grounded finite-extinction production certificate.

`FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate` stores arbitrary
`Prop` fields with proofs, so it is trivially instantiable and carries no
mathematical content (see INTEGRITY_ASSESSMENT.md).  This module defines the
grounded replacement: a certificate that existentially requires the actual
named analytic, surgery, control, width, and frontier packages.  The grounded
certificate cannot be discharged without supplying that data, and it refines
the legacy certificate through the existing production route.
-/

import Poincare.CanonicalBridges
import Poincare.CompletionTarget
import Poincare.DependencyCrosswalk
import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterVolumeDifferential

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
A content-bearing finite-extinction certificate: existence of the full named
production data — a `C¹` structure, an analytic foundation at some smoothness
level, a Ricci-flow-with-surgery construction, Perelman singularity control,
the width subobligations, and the curvature/volume/surgery-volume/scalar-
curvature/volume-differential frontier chain.  Unlike the legacy certificate,
none of these can be replaced by `True`.
-/
def GroundedFiniteExtinctionProductionCertificate
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop :=
  ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
  ∃ n : ℕ∞ω,
  ∃ analyticFoundation :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
  ∃ surgeryConstruction :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
  ∃ perelmanControl :
      PerelmanSingularityControlPackage (n := n) (M := M)
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation),
  ∃ _widthStatement :
      FiniteExtinctionWidthSubobligationsStatement
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control,
  ∃ curvatureFrontier :
      FiniteExtinctionProductionCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl,
  ∃ volumeFrontier :
      FiniteExtinctionProductionVolumeEvolutionFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier,
  ∃ surgeryVolumeFrontier :
      FiniteExtinctionProductionSurgeryVolumeFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier,
  ∃ scalarCurvatureFrontier :
      FiniteExtinctionProductionScalarCurvatureFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier,
    Nonempty
      (FiniteExtinctionProductionVolumeDifferentialFrontier
        analyticFoundation surgeryConstruction perelmanControl
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier)

/--
A grounded certificate yields the finite-extinction conclusion for its
manifold, by building the legacy production certificate through the existing
volume-differential production route.  The converse direction is unprovable
precisely because the legacy certificate is vacuous.  (The legacy certificate
is `Type`-valued, so the grounded existential can only be eliminated into the
`Prop`-valued conclusion, not into the certificate itself.)
-/
theorem finiteExtinctionByRicciFlowWithSurgery_of_grounded
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    FiniteExtinctionByRicciFlowWithSurgery M := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    .of_production_certificate
      (finite_extinction_production_certificate_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier)

/--
A grounded certificate exposes the actual finite-extinction surgery package,
not only the final extinction proposition.  The package is reconstructed from
the analytic, surgery, Perelman-control, width, and frontier data stored in the
grounded existential.
-/
theorem finite_extinction_surgery_package_nonempty_of_grounded
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  exact ⟨⟨n, package⟩⟩

/--
The grounded package projection is exactly the volume-differential frontier
package constructor after unpacking the grounded existential.
-/
theorem finite_extinction_surgery_package_nonempty_of_grounded_eq
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    finite_extinction_surgery_package_nonempty_of_grounded grounded =
      (by
        obtain ⟨smooth, n, analyticFoundation, surgeryConstruction,
          perelmanControl, widthStatement, curvatureFrontier, volumeFrontier,
          surgeryVolumeFrontier, scalarCurvatureFrontier,
          ⟨volumeDifferentialFrontier⟩⟩ := grounded
        letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
        rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement curvatureFrontier volumeFrontier
            surgeryVolumeFrontier scalarCurvatureFrontier
            volumeDifferentialFrontier with
          ⟨package⟩
        exact ⟨⟨n, package⟩⟩) := by
  apply Subsingleton.elim

/--
A grounded certificate exposes a theorem-shaped payload: a concrete surgery
package, the finite-extinction statement obtained from that package, the
derivation certificate produced by the width/frontier route, and the resulting
finite-extinction witness.
-/
theorem finite_extinction_statement_payload_of_grounded
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ _package : FiniteExtinctionSurgeryPackage n M,
    ∃ _packageStatement : FiniteExtinctionStatement n M,
    ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
      FiniteExtinctionByRicciFlowWithSurgery M := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
    widthStatement, curvatureFrontier, volumeFrontier, surgeryVolumeFrontier,
    scalarCurvatureFrontier, ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  exact
    ⟨ n
    , ricci_flow_data_of_analytic_foundation_package analyticFoundation
    , surgeryConstruction.withSurgery
    , perelmanControl.control
    , package
    , finite_extinction_statement_of_surgery_package package
    , finite_extinction_derivation_of_width_statement
        analyticFoundation surgeryConstruction perelmanControl widthStatement
    , finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
        analyticFoundation surgeryConstruction perelmanControl widthStatement
        curvatureFrontier volumeFrontier surgeryVolumeFrontier
        scalarCurvatureFrontier volumeDifferentialFrontier
    ⟩

/--
The theorem-shaped grounded payload is exactly the tuple obtained by unpacking
the grounded existential and applying the volume-differential frontier package
constructor.
-/
theorem finite_extinction_statement_payload_of_grounded_eq
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    finite_extinction_statement_payload_of_grounded grounded =
      (by
        obtain ⟨smooth, n, analyticFoundation, surgeryConstruction,
          perelmanControl, widthStatement, curvatureFrontier, volumeFrontier,
          surgeryVolumeFrontier, scalarCurvatureFrontier,
          ⟨volumeDifferentialFrontier⟩⟩ := grounded
        letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
        rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement curvatureFrontier volumeFrontier
            surgeryVolumeFrontier scalarCurvatureFrontier
            volumeDifferentialFrontier with
          ⟨package⟩
        exact
          ⟨ n
          , ricci_flow_data_of_analytic_foundation_package analyticFoundation
          , surgeryConstruction.withSurgery
          , perelmanControl.control
          , package
          , finite_extinction_statement_of_surgery_package package
          , finite_extinction_derivation_of_width_statement
              analyticFoundation surgeryConstruction perelmanControl
              widthStatement
          , finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
              analyticFoundation surgeryConstruction perelmanControl
              widthStatement curvatureFrontier volumeFrontier
              surgeryVolumeFrontier scalarCurvatureFrontier
              volumeDifferentialFrontier
          ⟩) := by
  apply Subsingleton.elim

/--
A compact grounded finite-extinction payload: the grounded certificate exposes
the chosen time parameter, the completed surgery package at that parameter, the
theorem-shaped finite-extinction statement, and the resulting extinction
witness without requiring downstream consumers to reopen the full analytic and
frontier chain.
-/
theorem finite_extinction_package_statement_and_witness_of_grounded
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
    ∃ _package : FiniteExtinctionSurgeryPackage n M,
      FiniteExtinctionStatement n M ∧
        FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases finite_extinction_statement_payload_of_grounded grounded with
    ⟨n, _flow, _surgery, _control, package, statement, _derivation,
      finiteExtinction⟩
  exact ⟨n, package, statement, finiteExtinction⟩

/--
The grounded universal finite-extinction statement: every compact simply
connected topological 3-manifold carries a grounded certificate.  This is the
honest restatement of the Ricci-flow pillar — unlike
`UniversalFiniteExtinctionStatement`, it is not a tautology.
-/
def GroundedUniversalFiniteExtinctionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      GroundedFiniteExtinctionProductionCertificate M

/--
The grounded universal statement exposes theorem-shaped finite-extinction
payloads for every smooth target: a flow, surgery construction, Perelman
control, concrete surgery package, finite-extinction statement, derivation, and
finite-extinction witness.
-/
theorem finite_extinction_statement_payload_family_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
        ∃ _packageStatement : FiniteExtinctionStatement n M,
        ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
          FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact finite_extinction_statement_payload_of_grounded (grounded M)

/--
The family-level grounded payload is exactly pointwise projection from each
grounded target certificate.
-/
theorem finite_extinction_statement_payload_family_of_grounded_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    finite_extinction_statement_payload_family_of_grounded grounded =
      (by
        intro M _top _t2 _charted _simple _compact _manifold
        exact finite_extinction_statement_payload_of_grounded
          (grounded M)) := by
  apply Subsingleton.elim

/--
Family-level compact grounded finite-extinction payload: every smooth target
receives a concrete time parameter, completed finite-extinction surgery
package, theorem-shaped statement, and extinction witness.
-/
theorem finite_extinction_package_statement_and_witness_family_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact finite_extinction_package_statement_and_witness_of_grounded
    (grounded M)

/--
The grounded universal statement supplies the finite-extinction package-layer
requirement consumed by the dependency crosswalk.
-/
theorem finiteExtinctionPackage_requirement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact finite_extinction_surgery_package_nonempty_of_grounded
    (grounded M)

/--
The grounded package-layer requirement is exactly the family obtained by
projecting each grounded target certificate to a finite-extinction surgery
package.
-/
theorem finiteExtinctionPackage_requirement_of_grounded_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    finiteExtinctionPackage_requirement_of_grounded grounded =
      (by
        intro M _top _t2 _charted _simple _compact _manifold
        exact finite_extinction_surgery_package_nonempty_of_grounded
          (grounded M)) := by
  apply Subsingleton.elim

/--
The grounded package-layer requirement and the compact statement/witness family
come from the same grounded universal finite-extinction input.
-/
theorem finiteExtinctionPackage_requirement_and_package_statement_witness_family_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) :=
  ⟨ finiteExtinctionPackage_requirement_of_grounded grounded
  , finite_extinction_package_statement_and_witness_family_of_grounded grounded
  ⟩

/--
The grounded finite-extinction pillar discharges the finite-extinction milestone
requirement, whose dependency crosswalk target is the finite-extinction package
layer.
-/
theorem finiteExtinction_milestone_requirement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.finiteExtinction :=
  finiteExtinctionPackage_requirement_of_grounded grounded

/--
The grounded finite-extinction pillar also supplies the Ricci-flow-with-surgery
milestone: each grounded target yields a finite-extinction surgery package, and
that package stores the selected flow together with surgery construction and
Perelman control.
-/
theorem ricciFlowWithSurgery_milestone_requirement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.ricciFlowWithSurgery := by
  intro M _top _t2 _charted _simple _compact _manifold
  rcases finiteExtinctionPackage_requirement_of_grounded grounded M with
    ⟨⟨n, package⟩⟩
  exact
    ⟨ n
    , ricci_flow_data_of_surgery_package package
    , surgery_construction_package_of_surgery_package package
    , perelman_control_package_of_surgery_package package
    ⟩

/--
The same grounded package projection discharges the Perelman singularity-control
milestone, whose dependency crosswalk currently shares the fixed-flow
surgery/Perelman package target.
-/
theorem perelmanSingularityControl_milestone_requirement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.perelmanSingularityControl := by
  intro M _top _t2 _charted _simple _compact _manifold
  rcases finiteExtinctionPackage_requirement_of_grounded grounded M with
    ⟨⟨n, package⟩⟩
  exact
    ⟨ n
    , ricci_flow_data_of_surgery_package package
    , surgery_construction_package_of_surgery_package package
    , perelman_control_package_of_surgery_package package
    ⟩

/--
Grounded finite extinction closes the surgery, Perelman-control, and
finite-extinction milestones while retaining the compact package/statement/
witness family used by final assembly.
-/
theorem milestone_requirements_and_package_statement_witness_family_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) :=
  ⟨ ricciFlowWithSurgery_milestone_requirement_of_grounded grounded
  , perelmanSingularityControl_milestone_requirement_of_grounded grounded
  , finiteExtinction_milestone_requirement_of_grounded grounded
  , finite_extinction_package_statement_and_witness_family_of_grounded grounded
  ⟩

/--
The grounded pillar implies the legacy pillar, so the existing assembly route
to the Poincare statement remains available from grounded data.
-/
theorem universalFiniteExtinctionStatement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} :=
  fun M _ _ _ _ _ =>
    finiteExtinctionByRicciFlowWithSurgery_of_grounded (grounded M)

/--
Grounded universal finite extinction exposes the legacy universal statement,
the finite-extinction package layer, the Ricci-flow/Perelman/finite-extinction
milestones, and the compact package/statement/witness family without requiring
the topology-extraction package.
-/
theorem universal_package_milestones_and_package_statement_witness_family_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) := by
  let milestonePayload :=
    milestone_requirements_and_package_statement_witness_family_of_grounded
      grounded
  exact
    ⟨ universalFiniteExtinctionStatement_of_grounded grounded
    , finiteExtinctionPackage_requirement_of_grounded grounded
    , milestonePayload.1
    , milestonePayload.2.1
    , milestonePayload.2.2.1
    , milestonePayload.2.2.2
    ⟩

/--
Single proof object for the grounded finite-extinction pillar as consumed by
later assembly: the legacy universal statement, the finite-extinction package
layer, the Ricci-flow/Perelman/finite-extinction milestones, and the concrete
package/statement/witness family all come from the same grounded input.
-/
structure GroundedUniversalFiniteExtinctionAssemblyPayload where
  universalStatement :
    UniversalFiniteExtinctionStatement.{u}
  finiteExtinctionPackageRequirement :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage
  ricciFlowWithSurgeryMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.ricciFlowWithSurgery
  perelmanSingularityControlMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.perelmanSingularityControl
  finiteExtinctionMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.finiteExtinction
  packageStatementWitnessFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M

/--
The grounded universal finite-extinction statement constructs the single
assembly payload for the finite-extinction pillar.
-/
def groundedUniversalFiniteExtinctionAssemblyPayload
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    GroundedUniversalFiniteExtinctionAssemblyPayload.{u} where
  universalStatement :=
    universalFiniteExtinctionStatement_of_grounded grounded
  finiteExtinctionPackageRequirement :=
    finiteExtinctionPackage_requirement_of_grounded grounded
  ricciFlowWithSurgeryMilestone :=
    ricciFlowWithSurgery_milestone_requirement_of_grounded grounded
  perelmanSingularityControlMilestone :=
    perelmanSingularityControl_milestone_requirement_of_grounded grounded
  finiteExtinctionMilestone :=
    finiteExtinction_milestone_requirement_of_grounded grounded
  packageStatementWitnessFamily :=
    finite_extinction_package_statement_and_witness_family_of_grounded grounded

/--
The single assembly payload unpacks to exactly the previously exposed tuple of
grounded finite-extinction outputs.
-/
theorem groundedUniversalFiniteExtinctionAssemblyPayload_fields
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) := by
  let payload := groundedUniversalFiniteExtinctionAssemblyPayload grounded
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , payload.packageStatementWitnessFamily
    ⟩

/--
Detailed proof object for the grounded finite-extinction pillar.  In addition
to the package-layer and milestone outputs, this retains the selected Ricci
flow, surgery construction, Perelman control, finite-extinction package,
statement, derivation, and final extinction witness for every smooth target.
-/
structure GroundedUniversalFiniteExtinctionDetailedAssemblyPayload where
  universalStatement :
    UniversalFiniteExtinctionStatement.{u}
  finiteExtinctionPackageRequirement :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage
  ricciFlowWithSurgeryMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.ricciFlowWithSurgery
  perelmanSingularityControlMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.perelmanSingularityControl
  finiteExtinctionMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.finiteExtinction
  packageStatementWitnessFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M
  statementPayloadFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
        ∃ _packageStatement : FiniteExtinctionStatement n M,
        ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
          FiniteExtinctionByRicciFlowWithSurgery M

/--
Grounded universal finite extinction constructs the detailed finite-extinction
assembly payload, retaining both the compact package/statement/witness family
and the full flow/surgery/control/derivation family.
-/
def groundedUniversalFiniteExtinctionDetailedAssemblyPayload
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u} where
  universalStatement :=
    universalFiniteExtinctionStatement_of_grounded grounded
  finiteExtinctionPackageRequirement :=
    finiteExtinctionPackage_requirement_of_grounded grounded
  ricciFlowWithSurgeryMilestone :=
    ricciFlowWithSurgery_milestone_requirement_of_grounded grounded
  perelmanSingularityControlMilestone :=
    perelmanSingularityControl_milestone_requirement_of_grounded grounded
  finiteExtinctionMilestone :=
    finiteExtinction_milestone_requirement_of_grounded grounded
  packageStatementWitnessFamily :=
    finite_extinction_package_statement_and_witness_family_of_grounded grounded
  statementPayloadFamily :=
    finite_extinction_statement_payload_family_of_grounded grounded

/--
The detailed assembly payload unpacks to the package-layer outputs together
with both grounded finite-extinction witness families.
-/
theorem groundedUniversalFiniteExtinctionDetailedAssemblyPayload_fields
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control :
            HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
          ∃ _packageStatement : FiniteExtinctionStatement n M,
          ∃ _derivation :
            HasFiniteExtinctionDerivation flow surgery control,
            FiniteExtinctionByRicciFlowWithSurgery M) := by
  let payload :=
    groundedUniversalFiniteExtinctionDetailedAssemblyPayload grounded
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , payload.packageStatementWitnessFamily
    , payload.statementPayloadFamily
    ⟩

/--
Any inhabited detailed grounded finite-extinction assembly payload exposes the
same package-layer, milestone, compact witness-family, and full
flow/surgery/control/derivation-family data without requiring consumers to
reconstruct it from the original grounded universal statement.
-/
theorem groundedUniversalFiniteExtinctionDetailedAssemblyPayload_fields_of_nonempty
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u}) :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control :
            HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
          ∃ _packageStatement : FiniteExtinctionStatement n M,
          ∃ _derivation :
            HasFiniteExtinctionDerivation flow surgery control,
            FiniteExtinctionByRicciFlowWithSurgery M) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , payload.packageStatementWitnessFamily
    , payload.statementPayloadFamily
    ⟩

/--
The detailed finite-extinction assembly payload exposes the compact
flow/surgery/control/package family retained inside its full statement payload.
This projection is the finite-extinction analogue of the analytic
package-plus-subobligations projection: it keeps the actual Ricci flow,
surgery construction, Perelman control, finite-extinction package, theorem
statement, derivation, and final extinction witness for every smooth target.
-/
theorem groundedUniversalFiniteExtinctionDetailedAssemblyPayload_flowPackageFamily
    (payload : GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            HasFiniteExtinctionDerivation flow surgery control ∧
            FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _top _t2 _charted _simple _compact _manifold
  rcases payload.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement, derivation,
      finiteExtinction⟩
  exact
    ⟨n, flow, surgery, control, package, packageStatement, derivation,
      finiteExtinction⟩

/--
Construct the compact flow/surgery/control/package family directly from the
grounded universal finite-extinction statement.
-/
theorem groundedUniversalFiniteExtinction_flowPackageFamily_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            HasFiniteExtinctionDerivation flow surgery control ∧
            FiniteExtinctionByRicciFlowWithSurgery M :=
  groundedUniversalFiniteExtinctionDetailedAssemblyPayload_flowPackageFamily
    (groundedUniversalFiniteExtinctionDetailedAssemblyPayload grounded)

/--
The detailed finite-extinction assembly payload also exposes a package-first
certificate family: every smooth target has a finite-extinction package and
statement, a final extinction witness, and an explicit derivation witness
retained under an inner flow/surgery/control existential.
-/
theorem groundedUniversalFiniteExtinctionDetailedAssemblyPayload_packageStatementDerivationFamily
    (payload : GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M ∧
            ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            ∃ surgery : HasRicciFlowWithSurgery n M,
            ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
              HasFiniteExtinctionDerivation flow surgery control := by
  intro M _top _t2 _charted _simple _compact _manifold
  rcases payload.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement, derivation,
      finiteExtinction⟩
  exact
    ⟨n, package, packageStatement, finiteExtinction, flow, surgery, control,
      derivation⟩

/--
Construct the package-first finite-extinction certificate family directly from
the grounded universal finite-extinction statement.
-/
theorem groundedUniversalFiniteExtinction_packageStatementDerivationFamily_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M ∧
            ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            ∃ surgery : HasRicciFlowWithSurgery n M,
            ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
              HasFiniteExtinctionDerivation flow surgery control :=
  groundedUniversalFiniteExtinctionDetailedAssemblyPayload_packageStatementDerivationFamily
    (groundedUniversalFiniteExtinctionDetailedAssemblyPayload grounded)

/--
Grounded universal finite extinction plus theorem-shaped topology extraction
proves the project-level Poincare statement through the universal
finite-extinction topology-extraction route.
-/
theorem poincare_statement_of_grounded_and_topology_extraction_statement
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
    (universalFiniteExtinctionStatement_of_grounded grounded)
    topologyStatement

/--
The grounded/topology-extraction project statement is exactly the universal
finite-extinction/topology-extraction project statement after projecting
grounded finite extinction to the legacy universal statement.
-/
theorem poincare_statement_of_grounded_and_topology_extraction_statement_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_statement_of_grounded_and_topology_extraction_statement
        grounded topologyStatement =
      poincare_statement_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
        (universalFiniteExtinctionStatement_of_grounded grounded)
        topologyStatement := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction plus theorem-shaped topology extraction
exposes the project-level Poincare payload: the statement itself and all
universe-indexed completion criteria.
-/
theorem poincare_payload_of_grounded_and_topology_extraction_statement
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
    (universalFiniteExtinctionStatement_of_grounded grounded)
    topologyStatement

/--
The grounded/topology-extraction project payload is exactly the universal
finite-extinction/topology-extraction project payload after projecting grounded
finite extinction to the legacy universal statement.
-/
theorem poincare_payload_of_grounded_and_topology_extraction_statement_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_payload_of_grounded_and_topology_extraction_statement
        grounded topologyStatement =
      poincare_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
        (universalFiniteExtinctionStatement_of_grounded grounded)
        topologyStatement := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction plus theorem-shaped topology extraction
proves the canonical completion target through the same universal
finite-extinction interface consumed by the completion boundary.
-/
theorem canonical_completion_target_of_grounded_and_topology_extraction_statement
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonicalCompletionTarget.{u} :=
  canonical_completion_target_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
    (universalFiniteExtinctionStatement_of_grounded grounded)
    topologyStatement

/--
The grounded/topology-extraction canonical target is exactly the universal
finite-extinction/topology-extraction target after projecting grounded finite
extinction to the legacy universal statement.
-/
theorem canonical_completion_target_of_grounded_and_topology_extraction_statement_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_target_of_grounded_and_topology_extraction_statement
        grounded topologyStatement =
      canonical_completion_target_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
        (universalFiniteExtinctionStatement_of_grounded grounded)
        topologyStatement := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction plus theorem-shaped topology extraction
exposes the canonical completion payload: the canonical target together with
all universe-indexed completion criteria.
-/
theorem canonical_completion_payload_of_grounded_and_topology_extraction_statement
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _target : canonicalCompletionTarget.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_completion_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
    (universalFiniteExtinctionStatement_of_grounded grounded)
    topologyStatement

/--
The grounded/topology-extraction canonical payload is exactly the universal
finite-extinction/topology-extraction payload after projecting grounded finite
extinction to the legacy universal statement.
-/
theorem canonical_completion_payload_of_grounded_and_topology_extraction_statement_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_payload_of_grounded_and_topology_extraction_statement
        grounded topologyStatement =
      canonical_completion_payload_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
        (universalFiniteExtinctionStatement_of_grounded grounded)
        topologyStatement := by
  apply Subsingleton.elim

/--
The grounded/topology-extraction route discharges any universe-indexed
completion criterion through the canonical completion payload.
-/
theorem canonical_completion_criterion_of_grounded_and_topology_extraction_statement
    (witness : Type u)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
    witness
    (universalFiniteExtinctionStatement_of_grounded grounded)
    topologyStatement

/--
The grounded/topology-extraction criterion route is exactly the universal
finite-extinction/topology-extraction criterion route after projecting grounded
finite extinction to the legacy universal statement.
-/
theorem canonical_completion_criterion_of_grounded_and_topology_extraction_statement_eq
    (witness : Type u)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_completion_criterion_of_grounded_and_topology_extraction_statement
        witness grounded topologyStatement =
      canonical_completion_criterion_of_universalFiniteExtinctionStatement_and_topology_extraction_statement
        witness
        (universalFiniteExtinctionStatement_of_grounded grounded)
        topologyStatement := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction and theorem-shaped topology extraction
close the finite-extinction side of the canonical certificate payload: the
canonical target and the canonical completion payload.
-/
theorem canonical_certificate_payload_of_grounded_and_topology_extraction_statement
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonicalCompletionTarget.{u} ∧
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨ canonical_completion_target_of_grounded_and_topology_extraction_statement
      grounded topologyStatement
  , canonical_completion_payload_of_grounded_and_topology_extraction_statement
      grounded topologyStatement
  ⟩

/--
The grounded/topology-extraction canonical certificate payload is exactly the
tuple of the grounded canonical target route and grounded canonical payload
route.
-/
theorem canonical_certificate_payload_of_grounded_and_topology_extraction_statement_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    canonical_certificate_payload_of_grounded_and_topology_extraction_statement
        grounded topologyStatement =
      ⟨ canonical_completion_target_of_grounded_and_topology_extraction_statement
          grounded topologyStatement
      , canonical_completion_payload_of_grounded_and_topology_extraction_statement
          grounded topologyStatement
      ⟩ := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction and theorem-shaped topology extraction
close both public payload layers at once: the project-level Poincare statement
and payload, plus the canonical completion target and payload.
-/
theorem project_and_canonical_certificate_payload_of_grounded_and_topology_extraction_statement
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :=
  ⟨ poincare_statement_of_grounded_and_topology_extraction_statement
      grounded topologyStatement
  , poincare_payload_of_grounded_and_topology_extraction_statement
      grounded topologyStatement
  , canonical_completion_target_of_grounded_and_topology_extraction_statement
      grounded topologyStatement
  , canonical_completion_payload_of_grounded_and_topology_extraction_statement
      grounded topologyStatement
  ⟩

/--
The combined grounded project/canonical payload is exactly the tuple of the
four already-proved grounded topology-extraction routes.
-/
theorem project_and_canonical_certificate_payload_of_grounded_and_topology_extraction_statement_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    project_and_canonical_certificate_payload_of_grounded_and_topology_extraction_statement
        grounded topologyStatement =
      ⟨ poincare_statement_of_grounded_and_topology_extraction_statement
          grounded topologyStatement
      , poincare_payload_of_grounded_and_topology_extraction_statement
          grounded topologyStatement
      , canonical_completion_target_of_grounded_and_topology_extraction_statement
          grounded topologyStatement
      , canonical_completion_payload_of_grounded_and_topology_extraction_statement
          grounded topologyStatement
      ⟩ := by
  apply Subsingleton.elim

/--
A concrete topology extraction package supplies the theorem-shaped topology
extraction statement needed by the grounded finite-extinction project route.
-/
theorem poincare_statement_of_grounded_and_topology_package
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_grounded_and_topology_extraction_statement
    grounded
    (extinction_topology_extraction_statement_of_topology_package
      topologyPackage)

/-- The topology-package project route is the extraction-statement route after projection. -/
theorem poincare_statement_of_grounded_and_topology_package_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    poincare_statement_of_grounded_and_topology_package grounded topologyPackage =
      poincare_statement_of_grounded_and_topology_extraction_statement
        grounded
        (extinction_topology_extraction_statement_of_topology_package
          topologyPackage) := by
  apply Subsingleton.elim

/--
A concrete topology extraction package supplies the project-level payload from
grounded universal finite extinction.
-/
theorem poincare_payload_of_grounded_and_topology_package
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_payload_of_grounded_and_topology_extraction_statement
    grounded
    (extinction_topology_extraction_statement_of_topology_package
      topologyPackage)

/-- The topology-package project payload is the extraction-statement payload after projection. -/
theorem poincare_payload_of_grounded_and_topology_package_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    poincare_payload_of_grounded_and_topology_package grounded topologyPackage =
      poincare_payload_of_grounded_and_topology_extraction_statement
        grounded
        (extinction_topology_extraction_statement_of_topology_package
          topologyPackage) := by
  apply Subsingleton.elim

/--
A concrete topology extraction package supplies the canonical payload from
grounded universal finite extinction.
-/
theorem canonical_certificate_payload_of_grounded_and_topology_package
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonicalCompletionTarget.{u} ∧
      ∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  canonical_certificate_payload_of_grounded_and_topology_extraction_statement
    grounded
    (extinction_topology_extraction_statement_of_topology_package
      topologyPackage)

/-- The topology-package canonical payload is the extraction-statement payload after projection. -/
theorem canonical_certificate_payload_of_grounded_and_topology_package_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_certificate_payload_of_grounded_and_topology_package
        grounded topologyPackage =
      canonical_certificate_payload_of_grounded_and_topology_extraction_statement
        grounded
        (extinction_topology_extraction_statement_of_topology_package
          topologyPackage) := by
  apply Subsingleton.elim

/--
Grounded universal finite extinction and a concrete topology extraction package
close both public payload layers: project-level Poincare payload and canonical
completion payload.
-/
theorem project_and_canonical_certificate_payload_of_grounded_and_topology_package
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :=
  project_and_canonical_certificate_payload_of_grounded_and_topology_extraction_statement
    grounded
    (extinction_topology_extraction_statement_of_topology_package
      topologyPackage)

/-- The concrete-package bundle is exactly the extraction-statement bundle after projection. -/
theorem project_and_canonical_certificate_payload_of_grounded_and_topology_package_eq
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    project_and_canonical_certificate_payload_of_grounded_and_topology_package
        grounded topologyPackage =
      project_and_canonical_certificate_payload_of_grounded_and_topology_extraction_statement
        grounded
        (extinction_topology_extraction_statement_of_topology_package
          topologyPackage) := by
  apply Subsingleton.elim

/--
The grounded/topology-package route discharges each universe-indexed completion
criterion through the package-projected topology extraction statement.
-/
theorem canonical_completion_criterion_of_grounded_and_topology_package
    (witness : Type u)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    CompletionCriterionAtUniverse witness :=
  canonical_completion_criterion_of_grounded_and_topology_extraction_statement
    witness grounded
    (extinction_topology_extraction_statement_of_topology_package
      topologyPackage)

/-- The topology-package criterion route is the extraction-statement criterion after projection. -/
theorem canonical_completion_criterion_of_grounded_and_topology_package_eq
    (witness : Type u)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    canonical_completion_criterion_of_grounded_and_topology_package
        witness grounded topologyPackage =
      canonical_completion_criterion_of_grounded_and_topology_extraction_statement
        witness grounded
        (extinction_topology_extraction_statement_of_topology_package
          topologyPackage) := by
  apply Subsingleton.elim

/--
Grounded finite extinction and a concrete topology package expose the two
package-layer requirements they supply, together with both public and canonical
certificate-facing payload layers.  This keeps the grounded Ricci-flow input
visible while packaging exactly the data consumed by the final assembly
boundary.
-/
theorem package_requirements_and_project_canonical_payload_of_grounded_and_topology_package
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage ∧
      PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :=
  ⟨ finiteExtinctionPackage_requirement_of_grounded grounded
  , topologyPackage
  , project_and_canonical_certificate_payload_of_grounded_and_topology_package
      grounded topologyPackage
  ⟩

/--
Grounded finite extinction and a concrete topology package expose the finite
Ricci-flow milestone requirements, the package-layer requirements, the compact
finite-extinction package/statement/witness family, and both public/canonical
certificate-facing payload layers in one theorem-shaped endpoint.
-/
theorem milestone_requirements_package_requirements_and_project_canonical_payload_of_grounded_and_topology_package
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let milestonePayload :=
    milestone_requirements_and_package_statement_witness_family_of_grounded
      grounded
  exact
    ⟨ milestonePayload.1
    , milestonePayload.2.1
    , milestonePayload.2.2.1
    , finiteExtinctionPackage_requirement_of_grounded grounded
    , topologyPackage
    , milestonePayload.2.2.2
    , project_and_canonical_certificate_payload_of_grounded_and_topology_package
        grounded topologyPackage
    ⟩

/--
Grounded finite extinction and a concrete topology package expose the finite
Ricci-flow milestone requirements, the package-layer requirements, the compact
finite-extinction package/statement/witness family, both public/canonical
certificate-facing payload layers, and the requested universe-indexed
completion criterion in one endpoint.
-/
theorem milestone_requirements_package_requirements_project_canonical_payload_and_completion_criterion_of_grounded_and_topology_package
    (witness : Type u)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      CompletionCriterionAtUniverse witness := by
  rcases
    milestone_requirements_package_requirements_and_project_canonical_payload_of_grounded_and_topology_package
      grounded topologyPackage with
    ⟨ hRicci, hPerelman, hFinite, hFinitePackage, hTopologyPackage,
      hWitnessFamily, hStatement, hProjectPayload, hCanonicalTarget,
      hCanonicalPayload ⟩
  exact
    ⟨ hRicci, hPerelman, hFinite, hFinitePackage, hTopologyPackage,
      hWitnessFamily, hStatement, hProjectPayload, hCanonicalTarget,
      hCanonicalPayload, hCanonicalPayload.choose_spec witness ⟩

/--
Grounded finite extinction and a concrete topology package expose the finite
Ricci-flow milestone requirements, the package-layer requirements, the compact
finite-extinction package/statement/witness family, both public/canonical
certificate-facing payload layers, and the full universe-indexed completion
criterion family carried by the canonical payload.
-/
theorem milestone_requirements_package_requirements_project_canonical_payload_and_completion_criteria_of_grounded_and_topology_package
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage : ExtinctionTopologyExtractionPackage.{u}) :
    dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      PoincareConjectureStatement.{u} ∧
      (∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      canonicalCompletionTarget.{u} ∧
      (∃ _target : canonicalCompletionTarget.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases
    milestone_requirements_package_requirements_and_project_canonical_payload_of_grounded_and_topology_package
      grounded topologyPackage with
    ⟨ hRicci, hPerelman, hFinite, hFinitePackage, hTopologyPackage,
      hWitnessFamily, hStatement, hProjectPayload, hCanonicalTarget,
      hCanonicalPayload ⟩
  exact
    ⟨ hRicci, hPerelman, hFinite, hFinitePackage, hTopologyPackage,
      hWitnessFamily, hStatement, hProjectPayload, hCanonicalTarget,
      hCanonicalPayload, hCanonicalPayload.choose_spec ⟩

/--
Smoothability together with grounded finite extinction and the concrete
topology package reconstructs the remaining aggregate dependency package used
by the checked completion-certificate constructor.
-/
theorem remainingDependencyPackage_of_smoothability_grounded_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    RemainingDependencyPackage.{u} where
  smoothability := smoothability
  surgery := finiteExtinctionPackage_requirement_of_grounded grounded
  topology := topologyPackage

/--
The smoothability package, grounded finite extinction, and topology package
close the current checked completion certificate through the existing
remaining-dependency/universal-finite-extinction route.
-/
theorem completion_certificate_of_smoothability_grounded_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareCompletionCertificate.{u} :=
  completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
    (remainingDependencyPackage_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage)
    (universalFiniteExtinctionStatement_of_grounded grounded)

/--
The same three inputs expose both the reconstructed remaining dependency
package and the checked certificate it feeds.
-/
theorem remaining_dependency_package_and_completion_certificate_of_smoothability_grounded_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    RemainingDependencyPackage.{u} ∧ PoincareCompletionCertificate.{u} :=
  ⟨ remainingDependencyPackage_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage
  , completion_certificate_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage ⟩

/--
The smoothability package, grounded finite extinction, and topology package
also project the checked certificate to the public Poincare statement.
-/
theorem poincare_statement_and_completion_certificate_of_smoothability_grounded_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareConjectureStatement.{u} ∧ PoincareCompletionCertificate.{u} := by
  let certificate :=
    completion_certificate_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage
  exact
    ⟨ poincare_conjecture_of_completion_certificate certificate
    , certificate ⟩

/--
The same three inputs close the checked certificate, its public statement
projection, and the full universe-indexed completion-criterion family through
the standard certificate projection.
-/
theorem poincare_statement_completion_certificate_and_completion_criteria_of_smoothability_grounded_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let certificate :=
    completion_certificate_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage
  exact
    ⟨ poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate ⟩

/--
The smoothability package, grounded finite-extinction pillar, and topology
package expose the full finite-extinction milestone route together with the
reconstructed remaining dependency package, inhabited checked certificate,
public statement, and completion-criterion family used by final assembly.
-/
theorem milestone_requirements_remaining_dependency_certificate_and_completion_criteria_of_smoothability_grounded_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let milestonePayload :=
    milestone_requirements_and_package_statement_witness_family_of_grounded
      grounded
  let remaining :=
    remainingDependencyPackage_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage
  let certificate :=
    completion_certificate_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage
  exact
    ⟨ milestonePayload.1
    , milestonePayload.2.1
    , milestonePayload.2.2.1
    , smoothability
    , finiteExtinctionPackage_requirement_of_grounded grounded
    , topologyPackage
    , milestonePayload.2.2.2
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , ⟨certificate⟩
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
The same smoothability/grounded/topology route constructs the detailed grounded
finite-extinction assembly payload and carries it through to the reconstructed
remaining dependency package, inhabited checked certificate, public statement,
and completion-criterion family.
-/
theorem detailed_grounded_payload_remaining_dependency_certificate_and_completion_criteria_of_smoothability_grounded_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    Nonempty GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u} ∧
      UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
          ∃ _packageStatement : FiniteExtinctionStatement n M,
          ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
            FiniteExtinctionByRicciFlowWithSurgery M) ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let detailedPayload :=
    groundedUniversalFiniteExtinctionDetailedAssemblyPayload grounded
  let remaining :=
    remainingDependencyPackage_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage
  let certificate :=
    completion_certificate_of_smoothability_grounded_and_topology_package
      smoothability grounded topologyPackage
  exact
    ⟨ ⟨detailedPayload⟩
    , detailedPayload.universalStatement
    , detailedPayload.finiteExtinctionPackageRequirement
    , detailedPayload.ricciFlowWithSurgeryMilestone
    , detailedPayload.perelmanSingularityControlMilestone
    , detailedPayload.finiteExtinctionMilestone
    , detailedPayload.statementPayloadFamily
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , ⟨certificate⟩
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
An inhabited detailed grounded finite-extinction payload is enough to feed the
final certificate route directly once smoothability and topology-package inputs
are supplied.  This endpoint no longer requires consumers to retain the
original grounded statement: it reconstructs the remaining dependency package
from the payload's finite-extinction package requirement and universal
finite-extinction statement, then exposes the checked certificate endpoint and
the retained flow/surgery/control witness families.
-/
theorem detailed_grounded_payload_remaining_dependency_certificate_and_completion_criteria_of_nonempty_payload_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
          ∃ _packageStatement : FiniteExtinctionStatement n M,
          ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
            FiniteExtinctionByRicciFlowWithSurgery M) ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      Nonempty PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨payload⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := payload.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining payload.universalStatement
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , payload.packageStatementWitnessFamily
    , payload.statementPayloadFamily
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , ⟨certificate⟩
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
Concrete checked-certificate form of the detailed grounded-payload route.  An
inhabited detailed finite-extinction payload, smoothability, and a topology
package reconstruct the remaining dependency package and expose the actual
checked completion certificate, not only its inhabited wrapper.
-/
theorem detailed_grounded_payload_remaining_dependency_checked_certificate_and_completion_criteria_of_nonempty_payload_and_topology_package
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
          ∃ _packageStatement : FiniteExtinctionStatement n M,
          ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
            FiniteExtinctionByRicciFlowWithSurgery M) ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨payload⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := payload.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining payload.universalStatement
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , payload.packageStatementWitnessFamily
    , payload.statementPayloadFamily
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
Consumer payload for the grounded finite-extinction pillar.  It retains the
detailed assembly payload, the legacy universal statement, package-layer and
milestone requirements, the compact package/statement/witness family, the full
flow/surgery/control statement payload family, and the two package-first
projection families derived from that detailed payload.
-/
structure GroundedUniversalFiniteExtinctionCompleteConsumerPayload where
  detailedPayload :
    GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u}
  universalStatement :
    UniversalFiniteExtinctionStatement.{u}
  finiteExtinctionPackageRequirement :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.finiteExtinctionPackage
  ricciFlowWithSurgeryMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.ricciFlowWithSurgery
  perelmanSingularityControlMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.perelmanSingularityControl
  finiteExtinctionMilestone :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.finiteExtinction
  packageStatementWitnessFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M
  statementPayloadFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
        ∃ _packageStatement : FiniteExtinctionStatement n M,
        ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
          FiniteExtinctionByRicciFlowWithSurgery M
  flowPackageFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            HasFiniteExtinctionDerivation flow surgery control ∧
            FiniteExtinctionByRicciFlowWithSurgery M
  packageStatementDerivationFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackage n M,
          FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M ∧
            ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            ∃ surgery : HasRicciFlowWithSurgery n M,
            ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
              HasFiniteExtinctionDerivation flow surgery control

/--
An inhabited detailed grounded finite-extinction assembly payload constructs
the complete finite-extinction consumer payload without reopening the original
grounded certificate family.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_of_nonemptyDetailedAssemblyPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u}) :
    Nonempty
      GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ { detailedPayload := payload
        universalStatement := payload.universalStatement
        finiteExtinctionPackageRequirement :=
          payload.finiteExtinctionPackageRequirement
        ricciFlowWithSurgeryMilestone :=
          payload.ricciFlowWithSurgeryMilestone
        perelmanSingularityControlMilestone :=
          payload.perelmanSingularityControlMilestone
        finiteExtinctionMilestone :=
          payload.finiteExtinctionMilestone
        packageStatementWitnessFamily :=
          payload.packageStatementWitnessFamily
        statementPayloadFamily := payload.statementPayloadFamily
        flowPackageFamily :=
          groundedUniversalFiniteExtinctionDetailedAssemblyPayload_flowPackageFamily
            payload
        packageStatementDerivationFamily :=
          groundedUniversalFiniteExtinctionDetailedAssemblyPayload_packageStatementDerivationFamily
            payload } ⟩

/--
Grounded universal finite extinction constructs the complete finite-extinction
consumer payload, retaining both the compact package-first data and the full
flow/surgery/control derivation family.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    Nonempty
      GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
  groundedUniversalFiniteExtinction_completeConsumerPayload_of_nonemptyDetailedAssemblyPayload
    ⟨groundedUniversalFiniteExtinctionDetailedAssemblyPayload grounded⟩

/--
An inhabited complete finite-extinction consumer payload exposes the
package-layer requirement, all three Ricci-flow/singularity-control/extinction
milestones, and both package-first derivation families retained by the detailed
assembly payload.
-/
theorem groundedUniversalFiniteExtinction_requirements_and_packageDerivationFamilies_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u}) :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              HasFiniteExtinctionDerivation flow surgery control ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M ∧
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              ∃ surgery : HasRicciFlowWithSurgery n M,
              ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
                HasFiniteExtinctionDerivation flow surgery control) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , payload.flowPackageFamily
    , payload.packageStatementDerivationFamily
    ⟩

/--
The complete finite-extinction consumer payload is equivalent to the inhabited
detailed grounded finite-extinction assembly payload: the forward direction
projects the stored detailed payload, while the reverse direction rebuilds the
complete consumer payload from it.
-/
theorem groundedUniversalFiniteExtinction_nonemptyCompleteConsumerPayload_iff_nonemptyDetailedAssemblyPayload :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ↔
      Nonempty GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u} := by
  constructor
  · rintro ⟨payload⟩
    exact ⟨payload.detailedPayload⟩
  · exact
      groundedUniversalFiniteExtinction_completeConsumerPayload_of_nonemptyDetailedAssemblyPayload

end Poincare
