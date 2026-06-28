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
The grounded pillar implies the legacy pillar, so the existing assembly route
to the Poincare statement remains available from grounded data.
-/
theorem universalFiniteExtinctionStatement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} :=
  fun M _ _ _ _ _ =>
    finiteExtinctionByRicciFlowWithSurgery_of_grounded (grounded M)

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

end Poincare
