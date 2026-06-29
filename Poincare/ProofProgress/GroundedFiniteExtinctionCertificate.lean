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
A package-first grounded finite-extinction payload: the same grounded
certificate that supplies the compact package/statement/witness endpoint also
retains an explicit flow, surgery, Perelman-control, and derivation witness for
that package statement.
-/
theorem finite_extinction_package_statement_derivation_and_witness_of_grounded
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ n : ℕ∞ω,
    ∃ _package : FiniteExtinctionSurgeryPackage n M,
      FiniteExtinctionStatement n M ∧
        FiniteExtinctionByRicciFlowWithSurgery M ∧
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          HasFiniteExtinctionDerivation flow surgery control := by
  rcases finite_extinction_statement_payload_of_grounded grounded with
    ⟨n, flow, surgery, control, package, statement, derivation,
      finiteExtinction⟩
  exact
    ⟨n, package, statement, finiteExtinction, flow, surgery, control,
      derivation⟩

/--
The grounded certificate can be unpacked all the way down to the actual
analytic foundation, surgery construction, Perelman control, width statement,
frontier chain, volume-differential frontier, and the concrete
finite-extinction package/statement/derivation/witness produced from those
inputs.  This is the local proof-bearing bridge from grounded Ricci-flow data
to the finite-extinction package route.
-/
theorem finite_extinction_frontier_package_statement_derivation_and_witness_of_grounded
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (grounded : GroundedFiniteExtinctionProductionCertificate M) :
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ n : ℕ∞ω,
    ∃ analyticFoundation :
        RicciFlowAnalyticFoundationPackage
          ThreeManifoldModelWithCorners n M,
    ∃ surgeryConstruction :
        RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package
            analyticFoundation),
    ∃ perelmanControl :
        PerelmanSingularityControlPackage (n := n) (M := M)
          (ricci_flow_data_of_analytic_foundation_package
            analyticFoundation),
    ∃ widthStatement :
        FiniteExtinctionWidthSubobligationsStatement
          (ricci_flow_data_of_analytic_foundation_package
            analyticFoundation)
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
    ∃ volumeDifferentialFrontier :
        FiniteExtinctionProductionVolumeDifferentialFrontier
          analyticFoundation surgeryConstruction perelmanControl
          curvatureFrontier volumeFrontier surgeryVolumeFrontier
          scalarCurvatureFrontier,
    ∃ package : FiniteExtinctionSurgeryPackage n M,
    ∃ packageStatement : FiniteExtinctionStatement n M,
    ∃ derivation :
        HasFiniteExtinctionDerivation
          (ricci_flow_data_of_analytic_foundation_package
            analyticFoundation)
          surgeryConstruction.withSurgery perelmanControl.control,
    ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
      packageStatement =
          finite_extinction_statement_of_surgery_package package ∧
        derivation =
          finite_extinction_derivation_of_width_statement
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement ∧
        extinctionWitness =
          finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
            analyticFoundation surgeryConstruction perelmanControl
            widthStatement curvatureFrontier volumeFrontier
            surgeryVolumeFrontier scalarCurvatureFrontier
            volumeDifferentialFrontier := by
  obtain ⟨smooth, n, analyticFoundation, surgeryConstruction,
    perelmanControl, widthStatement, curvatureFrontier, volumeFrontier,
    surgeryVolumeFrontier, scalarCurvatureFrontier,
    ⟨volumeDifferentialFrontier⟩⟩ := grounded
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases finite_extinction_surgery_package_nonempty_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier with
    ⟨package⟩
  let packageStatement : FiniteExtinctionStatement n M :=
    finite_extinction_statement_of_surgery_package package
  let derivation :
      HasFiniteExtinctionDerivation
        (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
        surgeryConstruction.withSurgery perelmanControl.control :=
    finite_extinction_derivation_of_width_statement
      analyticFoundation surgeryConstruction perelmanControl widthStatement
  let extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M :=
    finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
      analyticFoundation surgeryConstruction perelmanControl widthStatement
      curvatureFrontier volumeFrontier surgeryVolumeFrontier
      scalarCurvatureFrontier volumeDifferentialFrontier
  exact
    ⟨ smooth
    , n
    , analyticFoundation
    , surgeryConstruction
    , perelmanControl
    , widthStatement
    , curvatureFrontier
    , volumeFrontier
    , surgeryVolumeFrontier
    , scalarCurvatureFrontier
    , volumeDifferentialFrontier
    , package
    , packageStatement
    , derivation
    , extinctionWitness
    , rfl
    , rfl
    , rfl
    ⟩

/--
Family-level grounded frontier payload: every smooth target carries the actual
analytic foundation, surgery construction, Perelman control, width statement,
frontier chain, concrete finite-extinction package, theorem-shaped statement,
derivation, and finite-extinction witness.  This exposes the real Ricci-flow
production route pointwise from the grounded universal statement, before any
final-certificate assembly is selected.
-/
theorem finite_extinction_frontier_package_statement_derivation_and_witness_family_of_grounded
    (grounded :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          GroundedFiniteExtinctionProductionCertificate M) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
        ∃ n : ℕ∞ω,
        ∃ analyticFoundation :
            RicciFlowAnalyticFoundationPackage
              ThreeManifoldModelWithCorners n M,
        ∃ surgeryConstruction :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
        ∃ perelmanControl :
            PerelmanSingularityControlPackage (n := n) (M := M)
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation),
        ∃ widthStatement :
            FiniteExtinctionWidthSubobligationsStatement
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
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
        ∃ volumeDifferentialFrontier :
            FiniteExtinctionProductionVolumeDifferentialFrontier
              analyticFoundation surgeryConstruction perelmanControl
              curvatureFrontier volumeFrontier surgeryVolumeFrontier
              scalarCurvatureFrontier,
        ∃ package : FiniteExtinctionSurgeryPackage n M,
        ∃ packageStatement : FiniteExtinctionStatement n M,
        ∃ derivation :
            HasFiniteExtinctionDerivation
              (ricci_flow_data_of_analytic_foundation_package
                analyticFoundation)
              surgeryConstruction.withSurgery perelmanControl.control,
        ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
          packageStatement =
              finite_extinction_statement_of_surgery_package package ∧
            derivation =
              finite_extinction_derivation_of_width_statement
                analyticFoundation surgeryConstruction perelmanControl
                widthStatement ∧
            extinctionWitness =
              finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
                analyticFoundation surgeryConstruction perelmanControl
                widthStatement curvatureFrontier volumeFrontier
                surgeryVolumeFrontier scalarCurvatureFrontier
                volumeDifferentialFrontier := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact
    finite_extinction_frontier_package_statement_derivation_and_witness_of_grounded
      (grounded M)

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
Family-level package-first grounded finite-extinction payload retaining the
explicit flow, surgery construction, Perelman-control, and derivation witness
for the theorem-shaped finite-extinction statement at each smooth target.
-/
theorem finite_extinction_package_statement_derivation_and_witness_family_of_grounded
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
            ∃ control :
                HasPerelmanSingularityControl (n := n) (M := M) flow,
              HasFiniteExtinctionDerivation flow surgery control := by
  intro M _top _t2 _charted _simple _compact _manifold
  exact finite_extinction_package_statement_derivation_and_witness_of_grounded
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
The grounded package-layer requirement and the package-first derivation family
come from the same grounded universal finite-extinction input.  This retains
the explicit flow/surgery/control derivation route alongside the dependency
package consumed by final assembly.
-/
theorem finiteExtinctionPackage_requirement_and_package_statement_derivation_witness_family_of_grounded
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
              FiniteExtinctionByRicciFlowWithSurgery M ∧
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              ∃ surgery : HasRicciFlowWithSurgery n M,
              ∃ control :
                  HasPerelmanSingularityControl (n := n) (M := M) flow,
                HasFiniteExtinctionDerivation flow surgery control) :=
  ⟨ finiteExtinctionPackage_requirement_of_grounded grounded
  , finite_extinction_package_statement_derivation_and_witness_family_of_grounded
      grounded
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
For a fixed target, the detailed grounded finite-extinction payload can select
both concrete derivation views from the same stored statement-payload family:
the flow-first view with explicit surgery/control data and the package-first
view used by downstream package consumers.  The theorem also records that the
two selected finite-extinction statements, derivations, and extinction
witnesses are synchronized, so callers do not have to reopen the grounded
certificate to compare the two views.
-/
theorem groundedUniversalFiniteExtinctionDetailedAssemblyPayload_fixedTarget_flowPackage_and_packageDerivation_fields
    (payload : GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω,
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ package : FiniteExtinctionSurgeryPackage n M,
    ∃ packageStatement : FiniteExtinctionStatement n M,
    ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
    ∃ packageStatementAgain : FiniteExtinctionStatement n M,
    ∃ derivationAgain : HasFiniteExtinctionDerivation flow surgery control,
      packageStatementAgain = packageStatement ∧
        derivationAgain = derivation ∧
        FiniteExtinctionByRicciFlowWithSurgery M ∧
        (∃ packageFirst :
          FiniteExtinctionSurgeryPackage n M,
          packageFirst = package ∧
            FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M ∧
            ∃ flowFirst : RicciFlowData ThreeManifoldModelWithCorners n M,
            ∃ surgeryFirst : HasRicciFlowWithSurgery n M,
            ∃ controlFirst :
              HasPerelmanSingularityControl (n := n) (M := M) flowFirst,
            ∃ derivationFirst :
              HasFiniteExtinctionDerivation flowFirst surgeryFirst
                controlFirst,
              flowFirst = flow ∧
                HEq derivationFirst derivation) := by
  rcases payload.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement, derivation,
      finiteExtinction⟩
  exact
    ⟨ n
    , flow
    , surgery
    , control
    , package
    , packageStatement
    , derivation
    , packageStatement
    , derivation
    , rfl
    , rfl
    , finiteExtinction
    , package
    , rfl
    , packageStatement
    , finiteExtinction
    , flow
    , surgery
    , control
    , derivation
    , rfl
    , HEq.rfl
    ⟩

/--
The fixed-target flow/package and package-first derivation synchronization is
available directly from the grounded universal finite-extinction statement via
the detailed assembly payload it constructs.
-/
theorem groundedUniversalFiniteExtinction_fixedTarget_flowPackage_and_packageDerivation_fields_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω,
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ package : FiniteExtinctionSurgeryPackage n M,
    ∃ packageStatement : FiniteExtinctionStatement n M,
    ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
    ∃ packageStatementAgain : FiniteExtinctionStatement n M,
    ∃ derivationAgain : HasFiniteExtinctionDerivation flow surgery control,
      packageStatementAgain = packageStatement ∧
        derivationAgain = derivation ∧
        FiniteExtinctionByRicciFlowWithSurgery M ∧
        (∃ packageFirst :
          FiniteExtinctionSurgeryPackage n M,
          packageFirst = package ∧
            FiniteExtinctionStatement n M ∧
            FiniteExtinctionByRicciFlowWithSurgery M ∧
            ∃ flowFirst : RicciFlowData ThreeManifoldModelWithCorners n M,
            ∃ surgeryFirst : HasRicciFlowWithSurgery n M,
            ∃ controlFirst :
              HasPerelmanSingularityControl (n := n) (M := M) flowFirst,
            ∃ derivationFirst :
              HasFiniteExtinctionDerivation flowFirst surgeryFirst
                controlFirst,
              flowFirst = flow ∧
                HEq derivationFirst derivation) :=
  groundedUniversalFiniteExtinctionDetailedAssemblyPayload_fixedTarget_flowPackage_and_packageDerivation_fields
    (groundedUniversalFiniteExtinctionDetailedAssemblyPayload grounded) M

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
An inhabited detailed grounded finite-extinction assembly payload selects a
complete consumer with the expected stored fields.  This pins the complete
consumer's universal statement, finite-extinction package requirement,
milestones, compact witness family, full statement-payload family, and both
package-first derivation families to one selected detailed payload.
-/
theorem groundedUniversalFiniteExtinction_nonemptyDetailedAssemblyPayload_selected_completeConsumerPayload_fields
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u}) :
    ∃ selected :
      GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
    ∃ detailed :
      GroundedUniversalFiniteExtinctionDetailedAssemblyPayload.{u},
      selected.detailedPayload = detailed ∧
        selected.universalStatement = detailed.universalStatement ∧
        selected.finiteExtinctionPackageRequirement =
          detailed.finiteExtinctionPackageRequirement ∧
        selected.ricciFlowWithSurgeryMilestone =
          detailed.ricciFlowWithSurgeryMilestone ∧
        selected.perelmanSingularityControlMilestone =
          detailed.perelmanSingularityControlMilestone ∧
        selected.finiteExtinctionMilestone =
          detailed.finiteExtinctionMilestone ∧
        selected.packageStatementWitnessFamily =
          detailed.packageStatementWitnessFamily ∧
        selected.statementPayloadFamily = detailed.statementPayloadFamily ∧
        selected.flowPackageFamily =
          groundedUniversalFiniteExtinctionDetailedAssemblyPayload_flowPackageFamily
            detailed ∧
        selected.packageStatementDerivationFamily =
          groundedUniversalFiniteExtinctionDetailedAssemblyPayload_packageStatementDerivationFamily
            detailed ∧
        UniversalFiniteExtinctionStatement.{u} ∧
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.finiteExtinction := by
  rcases payload with ⟨detailed⟩
  let selected :
      GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    { detailedPayload := detailed
      universalStatement := detailed.universalStatement
      finiteExtinctionPackageRequirement :=
        detailed.finiteExtinctionPackageRequirement
      ricciFlowWithSurgeryMilestone :=
        detailed.ricciFlowWithSurgeryMilestone
      perelmanSingularityControlMilestone :=
        detailed.perelmanSingularityControlMilestone
      finiteExtinctionMilestone :=
        detailed.finiteExtinctionMilestone
      packageStatementWitnessFamily :=
        detailed.packageStatementWitnessFamily
      statementPayloadFamily := detailed.statementPayloadFamily
      flowPackageFamily :=
        groundedUniversalFiniteExtinctionDetailedAssemblyPayload_flowPackageFamily
          detailed
      packageStatementDerivationFamily :=
        groundedUniversalFiniteExtinctionDetailedAssemblyPayload_packageStatementDerivationFamily
          detailed }
  exact
    ⟨ selected
    , detailed
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , selected.universalStatement
    , selected.finiteExtinctionPackageRequirement
    , selected.ricciFlowWithSurgeryMilestone
    , selected.perelmanSingularityControlMilestone
    , selected.finiteExtinctionMilestone
    ⟩

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
An inhabited complete finite-extinction consumer payload also exposes the
legacy universal statement, the compact package/statement witness family, and
the full flow/surgery/control statement payload family carried by the same
detailed grounded assembly object.
-/
theorem groundedUniversalFiniteExtinction_statementFamilies_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u}) :
    UniversalFiniteExtinctionStatement.{u} ∧
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
            FiniteExtinctionByRicciFlowWithSurgery M) := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.universalStatement
    , payload.packageStatementWitnessFamily
    , payload.statementPayloadFamily
    ⟩

/--
For a fixed target manifold, a complete grounded finite-extinction consumer
payload exposes the concrete scale, Ricci-flow data, surgery structure,
Perelman control, finite-extinction surgery package, finite-extinction
statement, derivation, and final extinction witness.
-/
theorem groundedUniversalFiniteExtinction_fixedTarget_statementPayload_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω,
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ _package : FiniteExtinctionSurgeryPackage n M,
    ∃ _packageStatement : FiniteExtinctionStatement n M,
    ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
      FiniteExtinctionStatement n M ∧
        HasFiniteExtinctionDerivation flow surgery control ∧
        FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases payload with ⟨payload⟩
  rcases payload.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement,
      derivation, extinction⟩
  exact
    ⟨n, flow, surgery, control, package, packageStatement,
      derivation, packageStatement, derivation, extinction⟩

/--
For a fixed target manifold, a complete grounded finite-extinction consumer
payload simultaneously exposes the finite-extinction package requirement, all
three Ricci-flow/singularity/extinction milestones, and the concrete
finite-extinction statement payload.
-/
theorem groundedUniversalFiniteExtinction_requirements_and_fixedTarget_statementPayload_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
      ∃ _packageStatement : FiniteExtinctionStatement n M,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionStatement n M ∧
          HasFiniteExtinctionDerivation flow surgery control ∧
          FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , groundedUniversalFiniteExtinction_fixedTarget_statementPayload_of_completeConsumerPayload
        ⟨payload⟩ M
    ⟩

/--
For a fixed target manifold, a complete grounded finite-extinction consumer
payload exposes the legacy universal finite-extinction statement, all named
package/milestone requirements, and the concrete finite-extinction statement
payload at the same endpoint.
-/
theorem groundedUniversalFiniteExtinction_universal_requirements_and_fixedTarget_statementPayload_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
      ∃ _packageStatement : FiniteExtinctionStatement n M,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionStatement n M ∧
          HasFiniteExtinctionDerivation flow surgery control ∧
          FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , groundedUniversalFiniteExtinction_fixedTarget_statementPayload_of_completeConsumerPayload
        ⟨payload⟩ M
    ⟩

/--
For a fixed target manifold, a complete grounded finite-extinction consumer
payload exposes the finite-extinction package, package statement, extinction
witness, selected flow/surgery/control data, and finite-extinction derivation
in the package-first order retained by the complete payload.
-/
theorem groundedUniversalFiniteExtinction_fixedTarget_packageDerivationPayload_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω,
    ∃ _package : FiniteExtinctionSurgeryPackage n M,
      FiniteExtinctionStatement n M ∧
        FiniteExtinctionByRicciFlowWithSurgery M ∧
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          HasFiniteExtinctionDerivation flow surgery control := by
  rcases payload with ⟨payload⟩
  exact payload.packageStatementDerivationFamily M

/--
For a fixed target manifold, the complete grounded finite-extinction consumer
payload can synchronize the flow-first statement payload with the package-first
derivation shape using the same selected scale, package, statement,
derivation, and extinction witness.
-/
theorem groundedUniversalFiniteExtinction_fixedTarget_synchronized_statement_and_packageDerivationPayload_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω,
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ _package : FiniteExtinctionSurgeryPackage n M,
      FiniteExtinctionStatement n M ∧
        HasFiniteExtinctionDerivation flow surgery control ∧
        FiniteExtinctionByRicciFlowWithSurgery M ∧
        (FiniteExtinctionStatement n M ∧
          FiniteExtinctionByRicciFlowWithSurgery M ∧
          ∃ flow' : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery' : HasRicciFlowWithSurgery n M,
          ∃ control' :
            HasPerelmanSingularityControl (n := n) (M := M) flow',
            HasFiniteExtinctionDerivation flow' surgery' control') := by
  rcases payload with ⟨payload⟩
  rcases payload.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement,
      derivation, extinction⟩
  exact
    ⟨ n
    , flow
    , surgery
    , control
    , package
    , packageStatement
    , derivation
    , extinction
    , packageStatement
    , extinction
    , flow
    , surgery
    , control
    , derivation
    ⟩

/--
For a fixed target manifold, a complete grounded finite-extinction consumer
payload exposes the actual extinction witness together with selected
flow/surgery/control data and the finite-extinction derivation, without
requiring downstream consumers to unpack the package statement separately.
-/
theorem groundedUniversalFiniteExtinction_fixedTarget_extinctionDerivationPayload_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    FiniteExtinctionByRicciFlowWithSurgery M ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        HasFiniteExtinctionDerivation flow surgery control := by
  rcases payload with ⟨payload⟩
  rcases payload.packageStatementDerivationFamily M with
    ⟨n, _package, _packageStatement, extinction,
      flow, surgery, control, derivation⟩
  exact ⟨extinction, n, flow, surgery, control, derivation⟩

/--
For a fixed target manifold, a complete grounded finite-extinction consumer
payload simultaneously exposes the named finite-extinction package/milestone
requirements and the package-first finite-extinction derivation payload.
-/
theorem groundedUniversalFiniteExtinction_requirements_and_fixedTarget_packageDerivationPayload_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      ∃ n : ℕ∞ω,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
        FiniteExtinctionStatement n M ∧
          FiniteExtinctionByRicciFlowWithSurgery M ∧
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
            HasFiniteExtinctionDerivation flow surgery control := by
  rcases payload with ⟨payload⟩
  exact
    ⟨ payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , payload.packageStatementDerivationFamily M
    ⟩

/--
For a fixed target manifold, a complete grounded finite-extinction consumer
payload exposes a flattened endpoint: the legacy universal statement, the
finite-extinction package and milestone requirements, and concrete selected
flow/surgery/control/package/statement/derivation/extinction witnesses from
one payload.
-/
theorem groundedUniversalFiniteExtinction_universal_requirements_and_fixedTarget_concreteDerivationWitnesses_of_completeConsumerPayload
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
      ∃ _packageStatement : FiniteExtinctionStatement n M,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionStatement n M ∧
          HasFiniteExtinctionDerivation flow surgery control ∧
          FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases payload with ⟨payload⟩
  rcases payload.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement,
      derivation, extinction⟩
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , n
    , flow
    , surgery
    , control
    , package
    , packageStatement
    , derivation
    , packageStatement
    , derivation
    , extinction
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

/--
The complete finite-extinction consumer payload is exactly the package-layer
and milestone requirements together with the two concrete finite-extinction
witness families.  The reverse direction rebuilds the detailed assembly object,
so consumers that already have the mathematical statement families can close
the complete finite-extinction payload without reusing the original grounded
certificate.
-/
theorem groundedUniversalFiniteExtinction_nonemptyCompleteConsumerPayload_iff_requirements_and_statementFamilies :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ↔
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
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.universalStatement
      , payload.finiteExtinctionPackageRequirement
      , payload.ricciFlowWithSurgeryMilestone
      , payload.perelmanSingularityControlMilestone
      , payload.finiteExtinctionMilestone
      , payload.packageStatementWitnessFamily
      , payload.statementPayloadFamily
      ⟩
  · rintro
      ⟨ universalStatement
      , finiteExtinctionPackageRequirement
      , ricciFlowWithSurgeryMilestone
      , perelmanSingularityControlMilestone
      , finiteExtinctionMilestone
      , packageStatementWitnessFamily
      , statementPayloadFamily
      ⟩
    exact
      groundedUniversalFiniteExtinction_completeConsumerPayload_of_nonemptyDetailedAssemblyPayload
        ⟨ { universalStatement := universalStatement
            finiteExtinctionPackageRequirement :=
              finiteExtinctionPackageRequirement
            ricciFlowWithSurgeryMilestone := ricciFlowWithSurgeryMilestone
            perelmanSingularityControlMilestone :=
              perelmanSingularityControlMilestone
            finiteExtinctionMilestone := finiteExtinctionMilestone
            packageStatementWitnessFamily := packageStatementWitnessFamily
            statementPayloadFamily := statementPayloadFamily } ⟩

/--
The complete finite-extinction consumer payload is also exactly the universal
finite-extinction statement, the named package/milestone requirements, and the
two package-first derivation families retained by the complete payload.  The
reverse direction converts those package-first families back into the detailed
assembly's compact package/statement witness family and full statement-payload
family, then rebuilds the complete consumer payload.
-/
theorem groundedUniversalFiniteExtinction_nonemptyCompleteConsumerPayload_iff_universal_requirements_and_packageDerivationFamilies :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ↔
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
            ∃ control :
              HasPerelmanSingularityControl (n := n) (M := M) flow,
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
                ∃ control :
                  HasPerelmanSingularityControl (n := n) (M := M) flow,
                  HasFiniteExtinctionDerivation flow surgery control) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.universalStatement
      , payload.finiteExtinctionPackageRequirement
      , payload.ricciFlowWithSurgeryMilestone
      , payload.perelmanSingularityControlMilestone
      , payload.finiteExtinctionMilestone
      , payload.flowPackageFamily
      , payload.packageStatementDerivationFamily
      ⟩
  · rintro
      ⟨ universalStatement
      , finiteExtinctionPackageRequirement
      , ricciFlowWithSurgeryMilestone
      , perelmanSingularityControlMilestone
      , finiteExtinctionMilestone
      , flowPackageFamily
      , packageStatementDerivationFamily
      ⟩
    let packageStatementWitnessFamily :
        ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
          [ChartedSpace ThreeManifoldModel M]
          [SimplyConnectedSpace M] [CompactSpace M]
          [IsManifold ThreeManifoldModelWithCorners 1 M],
            ∃ n : ℕ∞ω,
            ∃ _package : FiniteExtinctionSurgeryPackage n M,
              FiniteExtinctionStatement n M ∧
                FiniteExtinctionByRicciFlowWithSurgery M := by
      intro M _ _ _ _ _ _
      rcases packageStatementDerivationFamily M with
        ⟨n, package, packageStatement, extinction, _flow, _surgery,
          _control, _derivation⟩
      exact ⟨n, package, packageStatement, extinction⟩
    let statementPayloadFamily :
        ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
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
              FiniteExtinctionByRicciFlowWithSurgery M := by
      intro M _ _ _ _ _ _
      rcases flowPackageFamily M with
        ⟨n, flow, surgery, control, package, packageStatement,
          derivation, extinction⟩
      exact
        ⟨n, flow, surgery, control, package, packageStatement,
          derivation, extinction⟩
    exact
      groundedUniversalFiniteExtinction_completeConsumerPayload_of_nonemptyDetailedAssemblyPayload
        ⟨ { universalStatement := universalStatement
            finiteExtinctionPackageRequirement :=
              finiteExtinctionPackageRequirement
            ricciFlowWithSurgeryMilestone := ricciFlowWithSurgeryMilestone
            perelmanSingularityControlMilestone :=
              perelmanSingularityControlMilestone
            finiteExtinctionMilestone := finiteExtinctionMilestone
            packageStatementWitnessFamily := packageStatementWitnessFamily
            statementPayloadFamily := statementPayloadFamily } ⟩

/--
Package-derivation family data constructs the complete grounded
finite-extinction consumer payload and immediately exposes the fixed-target
concrete derivation witnesses from that constructed payload.  This is the
consumer-facing route for downstream assembly code that already has the
universal statement, package/milestone requirements, and package-first
derivation families, but not the concrete complete payload object.
-/
theorem groundedUniversalFiniteExtinction_requirements_packageDerivationFamilies_completeConsumerPayload_and_fixedTarget_concreteDerivationWitnesses
    (universalStatement : UniversalFiniteExtinctionStatement.{u})
    (finiteExtinctionPackageRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (ricciFlowWithSurgeryMilestone :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery)
    (perelmanSingularityControlMilestone :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl)
    (finiteExtinctionMilestone :
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction)
    (flowPackageFamily :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control :
            HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              HasFiniteExtinctionDerivation flow surgery control ∧
              FiniteExtinctionByRicciFlowWithSurgery M)
    (packageStatementDerivationFamily :
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
              ∃ control :
                HasPerelmanSingularityControl (n := n) (M := M) flow,
                HasFiniteExtinctionDerivation flow surgery control)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
      ∃ _packageStatement : FiniteExtinctionStatement n M,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionStatement n M ∧
          HasFiniteExtinctionDerivation flow surgery control ∧
          FiniteExtinctionByRicciFlowWithSurgery M := by
  let payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_nonemptyCompleteConsumerPayload_iff_universal_requirements_and_packageDerivationFamilies.2
      ⟨ universalStatement
      , finiteExtinctionPackageRequirement
      , ricciFlowWithSurgeryMilestone
      , perelmanSingularityControlMilestone
      , finiteExtinctionMilestone
      , flowPackageFamily
      , packageStatementDerivationFamily
      ⟩
  exact
    ⟨ payload
    , groundedUniversalFiniteExtinction_universal_requirements_and_fixedTarget_concreteDerivationWitnesses_of_completeConsumerPayload
        payload M
    ⟩

/--
The complete grounded finite-extinction consumer payload feeds the checked final
certificate route directly once the smoothability and topology package inputs
are supplied, while preserving a fixed-target finite-extinction derivation
endpoint for downstream consumers that still need the selected scale, flow,
surgery, control, package, statement, derivation, and extinction witnesses.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_checked_certificate_and_fixedTarget_concreteDerivationWitnesses
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
      ∃ _packageStatement : FiniteExtinctionStatement n M,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionStatement n M ∧
          HasFiniteExtinctionDerivation flow surgery control ∧
          FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases payload with ⟨payload⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := payload.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining payload.universalStatement
  rcases payload.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement,
      derivation, extinction⟩
  exact
    ⟨ payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    , n
    , flow
    , surgery
    , control
    , package
    , packageStatement
    , derivation
    , packageStatement
    , derivation
    , extinction
    ⟩

/--
The complete grounded finite-extinction consumer payload selects the exact
remaining-dependency package and checked-certificate route used by final
assembly.  This target-free endpoint pins the remaining package fields to the
selected complete consumer and specializes the completion-criteria family to a
single requested witness.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_selected_remaining_certificate_route_and_completionCriterion
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (witness : Type u) :
    ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
    ∃ remaining : RemainingDependencyPackage.{u},
    ∃ certificate : PoincareCompletionCertificate.{u},
      remaining.smoothability = smoothability ∧
        remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
        remaining.topology = topologyPackage ∧
        certificate =
          completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
            remaining selected.universalStatement ∧
        UniversalFiniteExtinctionStatement.{u} ∧
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.finiteExtinction ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        CompletionCriterionAtUniverse witness := by
  rcases payload with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  exact
    ⟨ selected
    , remaining
    , certificate
    , rfl
    , rfl
    , rfl
    , rfl
    , selected.universalStatement
    , selected.finiteExtinctionPackageRequirement
    , selected.ricciFlowWithSurgeryMilestone
    , selected.perelmanSingularityControlMilestone
    , selected.finiteExtinctionMilestone
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , completion_criterion_of_completion_certificate witness certificate
    ⟩

/--
The same selected complete finite-extinction consumer payload exposes the full
completion-criteria family along the pinned remaining-dependency certificate
route.  This is the target-free arbitrary-consumer endpoint needed when final
assembly already has a complete grounded finite-extinction payload and should
not reconstruct it from the original grounded universal statement.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_selected_remaining_certificate_route_and_completionCriteria
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (payload :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
    ∃ remaining : RemainingDependencyPackage.{u},
    ∃ certificate : PoincareCompletionCertificate.{u},
      remaining.smoothability = smoothability ∧
        remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
        remaining.topology = topologyPackage ∧
        certificate =
          completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
            remaining selected.universalStatement ∧
        UniversalFiniteExtinctionStatement.{u} ∧
        dependencyPackageLayerRequirement.{u}
          DependencyPackageLayer.finiteExtinctionPackage ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.ricciFlowWithSurgery ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.perelmanSingularityControl ∧
        dependencyMilestoneRequirement.{u}
          DependencyMilestone.finiteExtinction ∧
        PoincareConjectureStatement.{u} ∧
        PoincareCompletionCertificate.{u} ∧
        (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  rcases payload with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  exact
    ⟨ selected
    , remaining
    , certificate
    , rfl
    , rfl
    , rfl
    , rfl
    , selected.universalStatement
    , selected.finiteExtinctionPackageRequirement
    , selected.ricciFlowWithSurgeryMilestone
    , selected.perelmanSingularityControlMilestone
    , selected.finiteExtinctionMilestone
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
Grounded universal finite extinction constructs the complete finite-extinction
consumer payload and feeds the checked final-certificate route without choosing
a fixed target manifold.  This target-free endpoint exposes the selected
complete payload, the legacy universal statement, the finite-extinction package
requirement, the remaining-dependency package, the certificate-projected public
statement, the checked certificate, and all completion criteria.  Fixed-target
flow/package/derivation witnesses remain available from
`groundedUniversalFiniteExtinction_completeConsumerPayload_checked_certificate_and_fixedTarget_concreteDerivationWitnesses`.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_checked_certificate_and_completion_criteria_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases payload with ⟨payload⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := payload.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining payload.universalStatement
  exact
    ⟨ ⟨payload⟩
    , payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
Grounded universal finite extinction constructs a complete finite-extinction
consumer payload and immediately exposes the selected remaining-dependency
certificate route with all completion criteria.  This strengthens the
target-free grounded endpoint by retaining the selected complete consumer,
the remaining-package field equalities, the checked certificate constructor,
the projected milestones, and the all-witness completion family together.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_remaining_certificate_route_and_completionCriteria_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
      ∃ remaining : RemainingDependencyPackage.{u},
      ∃ certificate : PoincareCompletionCertificate.{u},
        remaining.smoothability = smoothability ∧
          remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
          remaining.topology = topologyPackage ∧
          certificate =
            completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
              remaining selected.universalStatement ∧
          UniversalFiniteExtinctionStatement.{u} ∧
          dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.finiteExtinctionPackage ∧
          dependencyMilestoneRequirement.{u}
            DependencyMilestone.ricciFlowWithSurgery ∧
          dependencyMilestoneRequirement.{u}
            DependencyMilestone.perelmanSingularityControl ∧
          dependencyMilestoneRequirement.{u}
            DependencyMilestone.finiteExtinction ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  exact
    ⟨ payload
    , groundedUniversalFiniteExtinction_completeConsumerPayload_selected_remaining_certificate_route_and_completionCriteria
        smoothability payload topologyPackage
    ⟩

/--
Grounded universal finite extinction feeds the same target-free checked
certificate route while retaining the Ricci-flow, Perelman-control, and
finite-extinction milestone requirements carried by the complete consumer
payload.  This is the milestone-preserving target-free endpoint for final
certificate assembly.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_milestones_checked_certificate_and_completion_criteria_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let payload :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases payload with ⟨payload⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := payload.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining payload.universalStatement
  exact
    ⟨ ⟨payload⟩
    , payload.universalStatement
    , payload.finiteExtinctionPackageRequirement
    , payload.ricciFlowWithSurgeryMilestone
    , payload.perelmanSingularityControlMilestone
    , payload.finiteExtinctionMilestone
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
Grounded universal finite extinction itself constructs the complete
finite-extinction consumer payload and feeds the checked final-certificate
route once smoothability and topology-package inputs are supplied.  The fixed
target still receives the selected scale, flow, surgery, control, package,
statement, derivation, and extinction witnesses from the constructed complete
payload.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_checked_certificate_and_fixedTarget_concreteDerivationWitnesses_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
      ∃ _packageStatement : FiniteExtinctionStatement n M,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionStatement n M ∧
          HasFiniteExtinctionDerivation flow surgery control ∧
          FiniteExtinctionByRicciFlowWithSurgery M := by
  let payload :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  exact
    ⟨ payload
    , groundedUniversalFiniteExtinction_completeConsumerPayload_checked_certificate_and_fixedTarget_concreteDerivationWitnesses
        smoothability payload topologyPackage M
    ⟩

/--
Grounded universal finite extinction also preserves the actual grounded
production certificate for the selected target while feeding the checked final
certificate route.  This endpoint keeps the target certificate synchronized
with the complete consumer payload, milestone requirements, remaining
dependency package, checked certificate, completion criteria, and concrete
finite-extinction derivation witnesses.
-/
theorem groundedUniversalFiniteExtinction_completeConsumerPayload_checked_certificate_targetCertificate_and_fixedTarget_concreteDerivationWitnesses_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      GroundedFiniteExtinctionProductionCertificate M ∧
      UniversalFiniteExtinctionStatement.{u} ∧
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.ricciFlowWithSurgery ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.perelmanSingularityControl ∧
      dependencyMilestoneRequirement.{u}
        DependencyMilestone.finiteExtinction ∧
      RemainingDependencyPackage.{u} ∧
      PoincareConjectureStatement.{u} ∧
      PoincareCompletionCertificate.{u} ∧
      (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ _package : FiniteExtinctionSurgeryPackage n M,
      ∃ _packageStatement : FiniteExtinctionStatement n M,
      ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
        FiniteExtinctionStatement n M ∧
          HasFiniteExtinctionDerivation flow surgery control ∧
          FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases
    groundedUniversalFiniteExtinction_completeConsumerPayload_checked_certificate_and_fixedTarget_concreteDerivationWitnesses_of_grounded
      smoothability grounded topologyPackage M with
    ⟨ payload
    , universalStatement
    , finiteExtinctionPackageRequirement
    , ricciFlowWithSurgeryMilestone
    , perelmanSingularityControlMilestone
    , finiteExtinctionMilestone
    , remaining
    , poincareStatement
    , certificate
    , completionCriteria
    , n
    , flow
    , surgery
    , control
    , package
    , packageStatement
    , derivation
    , packageStatementAgain
    , derivationAgain
    , extinction
    ⟩
  exact
    ⟨ payload
    , grounded M
    , universalStatement
    , finiteExtinctionPackageRequirement
    , ricciFlowWithSurgeryMilestone
    , perelmanSingularityControlMilestone
    , finiteExtinctionMilestone
    , remaining
    , poincareStatement
    , certificate
    , completionCriteria
    , n
    , flow
    , surgery
    , control
    , package
    , packageStatement
    , derivation
    , packageStatementAgain
    , derivationAgain
    , extinction
    ⟩

/--
Grounded universal finite extinction constructs a selected complete
finite-extinction consumer payload and keeps both fixed-target derivation
views available while feeding the checked final-certificate route.  The target
certificate, the flow-first statement payload, and the package-first derivation
payload all come from the same selected complete consumer produced from the
grounded hypothesis.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_checked_certificate_targetCertificate_statement_and_packageDerivationPayloads_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
        GroundedFiniteExtinctionProductionCertificate M ∧
          selected.universalStatement =
            universalFiniteExtinctionStatement_of_grounded grounded ∧
          selected.finiteExtinctionPackageRequirement =
            finiteExtinctionPackage_requirement_of_grounded grounded ∧
          selected.ricciFlowWithSurgeryMilestone =
            ricciFlowWithSurgery_milestone_requirement_of_grounded
              grounded ∧
          selected.perelmanSingularityControlMilestone =
            perelmanSingularityControl_milestone_requirement_of_grounded
              grounded ∧
          selected.finiteExtinctionMilestone =
            finiteExtinction_milestone_requirement_of_grounded grounded ∧
          RemainingDependencyPackage.{u} ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control :
            HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
          ∃ _packageStatement : FiniteExtinctionStatement n M,
          ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
            FiniteExtinctionStatement n M ∧
              HasFiniteExtinctionDerivation flow surgery control ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
          (∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M ∧
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              ∃ surgery : HasRicciFlowWithSurgery n M,
              ∃ control :
                HasPerelmanSingularityControl (n := n) (M := M) flow,
                HasFiniteExtinctionDerivation flow surgery control) := by
  let constructed :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases constructed with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  rcases selected.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement,
      derivation, extinction⟩
  rcases selected.packageStatementDerivationFamily M with
    ⟨n', package', packageStatement', extinction',
      flow', surgery', control', derivation'⟩
  refine ⟨⟨selected⟩, selected, ?_⟩
  refine
    ⟨ grounded M
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , remaining
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , (fun witness => completion_criterion_of_completion_certificate
        witness certificate)
    , ?_
    , ?_
    ⟩
  · exact
      ⟨ n
      , flow
      , surgery
      , control
      , package
      , packageStatement
      , derivation
      , packageStatement
      , derivation
      , extinction
      ⟩
  · exact
      ⟨ n'
      , package'
      , packageStatement'
      , extinction'
      , flow'
      , surgery'
      , control'
      , derivation'
      ⟩

/--
Grounded universal finite extinction selects one complete finite-extinction
consumer payload, pins the exact remaining-dependency package and checked
certificate constructor used by final assembly, and keeps the selected target
certificate together with both fixed-target derivation views.  This is the
combined endpoint for consumers that need the route equalities and the concrete
finite-extinction witnesses from the same selected payload.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_remaining_certificate_route_targetCertificate_statement_and_packageDerivationPayloads_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
      ∃ remaining : RemainingDependencyPackage.{u},
      ∃ certificate : PoincareCompletionCertificate.{u},
        remaining.smoothability = smoothability ∧
          remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
          remaining.topology = topologyPackage ∧
          certificate =
            completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
              remaining selected.universalStatement ∧
          GroundedFiniteExtinctionProductionCertificate M ∧
          selected.universalStatement =
            universalFiniteExtinctionStatement_of_grounded grounded ∧
          selected.finiteExtinctionPackageRequirement =
            finiteExtinctionPackage_requirement_of_grounded grounded ∧
          selected.ricciFlowWithSurgeryMilestone =
            ricciFlowWithSurgery_milestone_requirement_of_grounded
              grounded ∧
          selected.perelmanSingularityControlMilestone =
            perelmanSingularityControl_milestone_requirement_of_grounded
              grounded ∧
          selected.finiteExtinctionMilestone =
            finiteExtinction_milestone_requirement_of_grounded grounded ∧
          UniversalFiniteExtinctionStatement.{u} ∧
          dependencyPackageLayerRequirement.{u}
            DependencyPackageLayer.finiteExtinctionPackage ∧
          dependencyMilestoneRequirement.{u}
            DependencyMilestone.ricciFlowWithSurgery ∧
          dependencyMilestoneRequirement.{u}
            DependencyMilestone.perelmanSingularityControl ∧
          dependencyMilestoneRequirement.{u}
            DependencyMilestone.finiteExtinction ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control :
            HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
          ∃ _packageStatement : FiniteExtinctionStatement n M,
          ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
            FiniteExtinctionStatement n M ∧
              HasFiniteExtinctionDerivation flow surgery control ∧
              FiniteExtinctionByRicciFlowWithSurgery M) ∧
          (∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M ∧
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              ∃ surgery : HasRicciFlowWithSurgery n M,
              ∃ control :
                HasPerelmanSingularityControl (n := n) (M := M) flow,
                HasFiniteExtinctionDerivation flow surgery control) := by
  let constructed :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases constructed with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  rcases selected.statementPayloadFamily M with
    ⟨n, flow, surgery, control, package, packageStatement,
      derivation, extinction⟩
  rcases selected.packageStatementDerivationFamily M with
    ⟨n', package', packageStatement', extinction',
      flow', surgery', control', derivation'⟩
  refine ⟨⟨selected⟩, selected, remaining, certificate, ?_⟩
  refine
    ⟨ rfl
    , rfl
    , rfl
    , rfl
    , grounded M
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , (by apply Subsingleton.elim)
    , selected.universalStatement
    , selected.finiteExtinctionPackageRequirement
    , selected.ricciFlowWithSurgeryMilestone
    , selected.perelmanSingularityControlMilestone
    , selected.finiteExtinctionMilestone
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , (fun witness => completion_criterion_of_completion_certificate
        witness certificate)
    , ?_
    , ?_
    ⟩
  · exact
      ⟨ n
      , flow
      , surgery
      , control
      , package
      , packageStatement
      , derivation
      , packageStatement
      , derivation
      , extinction
      ⟩
  · exact
      ⟨ n'
      , package'
      , packageStatement'
      , extinction'
      , flow'
      , surgery'
      , control'
      , derivation'
      ⟩

/--
Grounded universal finite extinction selects the complete finite-extinction
consumer payload and pins the final-certificate route fields without reopening
the fixed-target derivation witnesses.  This endpoint keeps the selected
universal statement, package-layer requirement, Ricci-flow/Perelman/
finite-extinction milestones, remaining-dependency package, checked
certificate constructor, public Poincare statement, and all completion
criteria synchronized for final-certificate assembly.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_remaining_certificate_endpoint_fields_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
      ∃ remaining : RemainingDependencyPackage.{u},
      ∃ certificate : PoincareCompletionCertificate.{u},
        selected.universalStatement =
            universalFiniteExtinctionStatement_of_grounded grounded ∧
          selected.finiteExtinctionPackageRequirement =
            finiteExtinctionPackage_requirement_of_grounded grounded ∧
          selected.ricciFlowWithSurgeryMilestone =
            ricciFlowWithSurgery_milestone_requirement_of_grounded
              grounded ∧
          selected.perelmanSingularityControlMilestone =
            perelmanSingularityControl_milestone_requirement_of_grounded
              grounded ∧
          selected.finiteExtinctionMilestone =
            finiteExtinction_milestone_requirement_of_grounded grounded ∧
          remaining.smoothability = smoothability ∧
          remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
          remaining.topology = topologyPackage ∧
          certificate =
            completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
              remaining selected.universalStatement ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let constructed :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases constructed with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  refine ⟨⟨selected⟩, selected, remaining, certificate, ?_⟩
  exact
    ⟨ by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , rfl
    , rfl
    , rfl
    , rfl
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
Grounded universal finite extinction selects the complete finite-extinction
consumer payload, pins the final-certificate route fields, and keeps both
target-free finite-extinction derivation families from that same selected
payload.  This lets final assembly retain package-first and flow-first
finite-extinction witnesses without choosing a particular target manifold.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_remaining_certificate_endpoint_fields_and_derivationFamilies_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage) :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
      ∃ remaining : RemainingDependencyPackage.{u},
      ∃ certificate : PoincareCompletionCertificate.{u},
        selected.universalStatement =
            universalFiniteExtinctionStatement_of_grounded grounded ∧
          selected.finiteExtinctionPackageRequirement =
            finiteExtinctionPackage_requirement_of_grounded grounded ∧
          selected.ricciFlowWithSurgeryMilestone =
            ricciFlowWithSurgery_milestone_requirement_of_grounded
              grounded ∧
          selected.perelmanSingularityControlMilestone =
            perelmanSingularityControl_milestone_requirement_of_grounded
              grounded ∧
          selected.finiteExtinctionMilestone =
            finiteExtinction_milestone_requirement_of_grounded grounded ∧
          remaining.smoothability = smoothability ∧
          remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
          remaining.topology = topologyPackage ∧
          certificate =
            completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
              remaining selected.universalStatement ∧
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
                  ∃ control :
                    HasPerelmanSingularityControl
                      (n := n) (M := M) flow,
                    HasFiniteExtinctionDerivation
                      flow surgery control) ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) := by
  let constructed :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases constructed with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  refine ⟨⟨selected⟩, selected, remaining, certificate, ?_⟩
  exact
    ⟨ by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , rfl
    , rfl
    , rfl
    , rfl
    , selected.flowPackageFamily
    , selected.packageStatementDerivationFamily
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , fun witness => completion_criterion_of_completion_certificate
        witness certificate
    ⟩

/--
Grounded universal finite extinction selects the complete finite-extinction
consumer payload, pins the remaining-dependency certificate route, and keeps
the actual fixed-target analytic/surgery/Perelman/frontier chain that produces
the finite-extinction package.  This endpoint connects the checked final
certificate route to the grounded Ricci-flow inputs instead of only to the
derived package and derivation families.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_remaining_certificate_frontier_chain_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
      ∃ remaining : RemainingDependencyPackage.{u},
      ∃ certificate : PoincareCompletionCertificate.{u},
        remaining.smoothability = smoothability ∧
          remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
          remaining.topology = topologyPackage ∧
          certificate =
            completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
              remaining selected.universalStatement ∧
          selected.universalStatement =
            universalFiniteExtinctionStatement_of_grounded grounded ∧
          selected.finiteExtinctionPackageRequirement =
            finiteExtinctionPackage_requirement_of_grounded grounded ∧
          selected.ricciFlowWithSurgeryMilestone =
            ricciFlowWithSurgery_milestone_requirement_of_grounded
              grounded ∧
          selected.perelmanSingularityControlMilestone =
            perelmanSingularityControl_milestone_requirement_of_grounded
              grounded ∧
          selected.finiteExtinctionMilestone =
            finiteExtinction_milestone_requirement_of_grounded grounded ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
              RicciFlowAnalyticFoundationPackage
                ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation),
          ∃ perelmanControl :
              PerelmanSingularityControlPackage (n := n) (M := M)
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation),
          ∃ widthStatement :
              FiniteExtinctionWidthSubobligationsStatement
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
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
          ∃ volumeDifferentialFrontier :
              FiniteExtinctionProductionVolumeDifferentialFrontier
                analyticFoundation surgeryConstruction perelmanControl
                curvatureFrontier volumeFrontier surgeryVolumeFrontier
                scalarCurvatureFrontier,
          ∃ package : FiniteExtinctionSurgeryPackage n M,
          ∃ packageStatement : FiniteExtinctionStatement n M,
          ∃ derivation :
              HasFiniteExtinctionDerivation
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
                surgeryConstruction.withSurgery perelmanControl.control,
          ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
            packageStatement =
                finite_extinction_statement_of_surgery_package package ∧
              derivation =
                finite_extinction_derivation_of_width_statement
                  analyticFoundation surgeryConstruction perelmanControl
                  widthStatement ∧
              extinctionWitness =
                finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
                  analyticFoundation surgeryConstruction perelmanControl
                  widthStatement curvatureFrontier volumeFrontier
                  surgeryVolumeFrontier scalarCurvatureFrontier
                  volumeDifferentialFrontier := by
  let constructed :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases constructed with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  rcases
    finite_extinction_frontier_package_statement_derivation_and_witness_of_grounded
      (grounded M) with
    ⟨ smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier,
      surgeryVolumeFrontier, scalarCurvatureFrontier,
      volumeDifferentialFrontier, package, packageStatement, derivation,
      extinctionWitness, hStatement, hDerivation, hExtinction⟩
  refine ⟨⟨selected⟩, selected, remaining, certificate, ?_⟩
  exact
    ⟨ rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , (fun witness => completion_criterion_of_completion_certificate
        witness certificate)
    , smooth
    , n
    , analyticFoundation
    , surgeryConstruction
    , perelmanControl
    , widthStatement
    , curvatureFrontier
    , volumeFrontier
    , surgeryVolumeFrontier
    , scalarCurvatureFrontier
    , volumeDifferentialFrontier
    , package
    , packageStatement
    , derivation
    , extinctionWitness
    , hStatement
    , hDerivation
    , hExtinction
    ⟩

/--
Grounded universal finite extinction selects the complete finite-extinction
consumer payload, pins the checked final-certificate route, keeps the actual
grounded frontier chain for a fixed target, and also retains the package-first
finite-extinction derivation payload from the same selected consumer.  This is
the fixed-target endpoint for final assembly code that needs both the grounded
Ricci-flow production chain and the package-indexed derivation view.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_remaining_certificate_frontier_chain_and_packageDerivationPayload_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
      ∃ remaining : RemainingDependencyPackage.{u},
      ∃ certificate : PoincareCompletionCertificate.{u},
        remaining.smoothability = smoothability ∧
          remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
          remaining.topology = topologyPackage ∧
          certificate =
            completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
              remaining selected.universalStatement ∧
          selected.universalStatement =
            universalFiniteExtinctionStatement_of_grounded grounded ∧
          selected.finiteExtinctionPackageRequirement =
            finiteExtinctionPackage_requirement_of_grounded grounded ∧
          selected.ricciFlowWithSurgeryMilestone =
            ricciFlowWithSurgery_milestone_requirement_of_grounded
              grounded ∧
          selected.perelmanSingularityControlMilestone =
            perelmanSingularityControl_milestone_requirement_of_grounded
              grounded ∧
          selected.finiteExtinctionMilestone =
            finiteExtinction_milestone_requirement_of_grounded grounded ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
              RicciFlowAnalyticFoundationPackage
                ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation),
          ∃ perelmanControl :
              PerelmanSingularityControlPackage (n := n) (M := M)
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation),
          ∃ widthStatement :
              FiniteExtinctionWidthSubobligationsStatement
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
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
          ∃ volumeDifferentialFrontier :
              FiniteExtinctionProductionVolumeDifferentialFrontier
                analyticFoundation surgeryConstruction perelmanControl
                curvatureFrontier volumeFrontier surgeryVolumeFrontier
                scalarCurvatureFrontier,
          ∃ package : FiniteExtinctionSurgeryPackage n M,
          ∃ packageStatement : FiniteExtinctionStatement n M,
          ∃ derivation :
              HasFiniteExtinctionDerivation
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
                surgeryConstruction.withSurgery perelmanControl.control,
          ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
            packageStatement =
                finite_extinction_statement_of_surgery_package package ∧
              derivation =
                finite_extinction_derivation_of_width_statement
                  analyticFoundation surgeryConstruction perelmanControl
                  widthStatement ∧
              extinctionWitness =
                finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
                  analyticFoundation surgeryConstruction perelmanControl
                  widthStatement curvatureFrontier volumeFrontier
                  surgeryVolumeFrontier scalarCurvatureFrontier
                  volumeDifferentialFrontier) ∧
          (∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M ∧
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              ∃ surgery : HasRicciFlowWithSurgery n M,
              ∃ control :
                HasPerelmanSingularityControl (n := n) (M := M) flow,
                HasFiniteExtinctionDerivation flow surgery control) := by
  let constructed :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases constructed with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  rcases
    finite_extinction_frontier_package_statement_derivation_and_witness_of_grounded
      (grounded M) with
    ⟨ smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier,
      surgeryVolumeFrontier, scalarCurvatureFrontier,
      volumeDifferentialFrontier, package, packageStatement, derivation,
      extinctionWitness, hStatement, hDerivation, hExtinction⟩
  rcases selected.packageStatementDerivationFamily M with
    ⟨n', package', packageStatement', extinction',
      flow', surgery', control', derivation'⟩
  refine ⟨⟨selected⟩, selected, remaining, certificate, ?_⟩
  refine
    ⟨ rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , by apply Subsingleton.elim
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , (fun witness => completion_criterion_of_completion_certificate
        witness certificate)
    , ?_
    , ?_
    ⟩
  · exact
      ⟨ smooth
      , n
      , analyticFoundation
      , surgeryConstruction
      , perelmanControl
      , widthStatement
      , curvatureFrontier
      , volumeFrontier
      , surgeryVolumeFrontier
      , scalarCurvatureFrontier
      , volumeDifferentialFrontier
      , package
      , packageStatement
      , derivation
      , extinctionWitness
      , hStatement
      , hDerivation
      , hExtinction
      ⟩
  · exact
      ⟨ n'
      , package'
      , packageStatement'
      , extinction'
      , flow'
      , surgery'
      , control'
      , derivation'
      ⟩

/--
The selected complete consumer's universal finite-extinction statement and the
grounded frontier chain produce the same fixed-target finite-extinction
witness.  This keeps the final-certificate-facing selected consumer, the
remaining-dependency certificate route, the concrete analytic/surgery/Perelman
frontier chain, and the package-first derivation payload synchronized with the
actual target-family witness consumed by downstream assembly.
-/
theorem groundedUniversalFiniteExtinction_selected_completeConsumerPayload_remaining_certificate_frontier_chain_packageDerivationPayload_and_universalWitness_of_grounded
    (smoothability :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.smoothabilityPackage)
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} ∧
      ∃ selected : GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u},
      ∃ remaining : RemainingDependencyPackage.{u},
      ∃ certificate : PoincareCompletionCertificate.{u},
        remaining.smoothability = smoothability ∧
          remaining.surgery = selected.finiteExtinctionPackageRequirement ∧
          remaining.topology = topologyPackage ∧
          certificate =
            completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
              remaining selected.universalStatement ∧
          selected.universalStatement =
            universalFiniteExtinctionStatement_of_grounded grounded ∧
          PoincareConjectureStatement.{u} ∧
          PoincareCompletionCertificate.{u} ∧
          (∀ witness : Type u, CompletionCriterionAtUniverse witness) ∧
          (∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
          ∃ n : ℕ∞ω,
          ∃ analyticFoundation :
              RicciFlowAnalyticFoundationPackage
                ThreeManifoldModelWithCorners n M,
          ∃ surgeryConstruction :
              RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation),
          ∃ perelmanControl :
              PerelmanSingularityControlPackage (n := n) (M := M)
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation),
          ∃ widthStatement :
              FiniteExtinctionWidthSubobligationsStatement
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
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
          ∃ volumeDifferentialFrontier :
              FiniteExtinctionProductionVolumeDifferentialFrontier
                analyticFoundation surgeryConstruction perelmanControl
                curvatureFrontier volumeFrontier surgeryVolumeFrontier
                scalarCurvatureFrontier,
          ∃ package : FiniteExtinctionSurgeryPackage n M,
          ∃ packageStatement : FiniteExtinctionStatement n M,
          ∃ derivation :
              HasFiniteExtinctionDerivation
                (ricci_flow_data_of_analytic_foundation_package
                  analyticFoundation)
                surgeryConstruction.withSurgery perelmanControl.control,
          ∃ extinctionWitness : FiniteExtinctionByRicciFlowWithSurgery M,
            packageStatement =
                finite_extinction_statement_of_surgery_package package ∧
              derivation =
                finite_extinction_derivation_of_width_statement
                  analyticFoundation surgeryConstruction perelmanControl
                  widthStatement ∧
              extinctionWitness =
                finite_extinction_by_ricci_flow_with_surgery_of_volume_differential_frontier
                  analyticFoundation surgeryConstruction perelmanControl
                  widthStatement curvatureFrontier volumeFrontier
                  surgeryVolumeFrontier scalarCurvatureFrontier
                  volumeDifferentialFrontier ∧
              selected.universalStatement M = extinctionWitness) ∧
          (∃ n : ℕ∞ω,
          ∃ _package : FiniteExtinctionSurgeryPackage n M,
            FiniteExtinctionStatement n M ∧
              FiniteExtinctionByRicciFlowWithSurgery M ∧
              ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
              ∃ surgery : HasRicciFlowWithSurgery n M,
              ∃ control :
                HasPerelmanSingularityControl (n := n) (M := M) flow,
                HasFiniteExtinctionDerivation flow surgery control) := by
  let constructed :
      Nonempty GroundedUniversalFiniteExtinctionCompleteConsumerPayload.{u} :=
    groundedUniversalFiniteExtinction_completeConsumerPayload_of_grounded
      grounded
  rcases constructed with ⟨selected⟩
  let remaining : RemainingDependencyPackage.{u} :=
    { smoothability := smoothability
      surgery := selected.finiteExtinctionPackageRequirement
      topology := topologyPackage }
  let certificate : PoincareCompletionCertificate.{u} :=
    completion_certificate_of_remaining_dependency_and_universalFiniteExtinctionStatement
      remaining selected.universalStatement
  rcases
    finite_extinction_frontier_package_statement_derivation_and_witness_of_grounded
      (grounded M) with
    ⟨ smooth, n, analyticFoundation, surgeryConstruction, perelmanControl,
      widthStatement, curvatureFrontier, volumeFrontier,
      surgeryVolumeFrontier, scalarCurvatureFrontier,
      volumeDifferentialFrontier, package, packageStatement, derivation,
      extinctionWitness, hStatement, hDerivation, hExtinction⟩
  rcases selected.packageStatementDerivationFamily M with
    ⟨n', package', packageStatement', extinction',
      flow', surgery', control', derivation'⟩
  refine ⟨⟨selected⟩, selected, remaining, certificate, ?_⟩
  refine
    ⟨ rfl
    , rfl
    , rfl
    , rfl
    , by apply Subsingleton.elim
    , poincare_conjecture_of_completion_certificate certificate
    , certificate
    , (fun witness => completion_criterion_of_completion_certificate
        witness certificate)
    , ?_
    , ?_
    ⟩
  · exact
      ⟨ smooth
      , n
      , analyticFoundation
      , surgeryConstruction
      , perelmanControl
      , widthStatement
      , curvatureFrontier
      , volumeFrontier
      , surgeryVolumeFrontier
      , scalarCurvatureFrontier
      , volumeDifferentialFrontier
      , package
      , packageStatement
      , derivation
      , extinctionWitness
      , hStatement
      , hDerivation
      , hExtinction
      , by apply Subsingleton.elim
      ⟩
  · exact
      ⟨ n'
      , package'
      , packageStatement'
      , extinction'
      , flow'
      , surgery'
      , control'
      , derivation'
      ⟩

end Poincare
