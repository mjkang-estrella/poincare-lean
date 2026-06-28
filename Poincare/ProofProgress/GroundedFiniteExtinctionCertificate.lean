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
The grounded pillar implies the legacy pillar, so the existing assembly route
to the Poincare statement remains available from grounded data.
-/
theorem universalFiniteExtinctionStatement_of_grounded
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} :=
  fun M _ _ _ _ _ =>
    finiteExtinctionByRicciFlowWithSurgery_of_grounded (grounded M)

end Poincare
