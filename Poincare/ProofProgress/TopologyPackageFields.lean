import Poincare.DependencyCrosswalk
import Poincare.ProofProgress.TopologyExtractionPunctureTransport

namespace Poincare

universe u

/--
A fixed finite-extinction witness and a completed topology extraction package
give the one-point compactification recognition used by the puncture transport
theorems.
-/
theorem homeomorph_to_onePoint_threeSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :=
  homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
    (homeomorphism_of_topology_package package M extinction)

/--
The package-level homeomorphism projection transports each single-puncture
complement to Euclidean space, hence makes it contractible.
-/
theorem compl_singleton_contractibleSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    ContractibleSpace ({x}ᶜ : Set M) :=
  compl_singleton_contractibleSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) x

/--
The same package-level singleton-complement chart transports Euclidean simple
connectedness back to the punctured target.
-/
theorem compl_singleton_simplyConnectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M) :
    SimplyConnectedSpace ({x}ᶜ : Set M) :=
  (homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) x).toHomotopyEquiv.simplyConnectedSpace

/--
Consequently, every based fundamental group of a singleton complement selected
by the topology package is trivial.
-/
theorem compl_singleton_fundamentalGroup_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) := by
  letI : SimplyConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_simplyConnectedSpace_of_topology_package
      package M extinction x
  change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
  infer_instance

/--
The topology package gives the full low-homotopy singleton-complement collapse
at any supplied basepoint: path components, `π₀`, the fundamental group, and
`π₁` are all subsingletons after transporting the package-selected one-point
compactification chart.
-/
theorem compl_singleton_lowHomotopy_subsingleton_package_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) (x : M)
    (basepoint : ({x}ᶜ : Set M)) :
    Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
      Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) ∧
      Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) ∧
      Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) := by
  letI : ContractibleSpace ({x}ᶜ : Set M) :=
    compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  letI : PathConnectedSpace ({x}ᶜ : Set M) := inferInstance
  letI : SimplyConnectedSpace ({x}ᶜ : Set M) :=
    compl_singleton_simplyConnectedSpace_of_topology_package
      package M extinction x
  letI : Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) := inferInstance
  letI : Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) :=
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := ({x}ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
        inferInstance
  letI : Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) :=
    compl_singleton_fundamentalGroup_subsingleton_of_topology_package
      package M extinction x basepoint
  letI : Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) :=
    ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ({x}ᶜ : Set M)) (x := basepoint)).subsingleton_congr).mpr
        inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/--
The package-level homeomorphism projection transports any two-puncture
complement to a punctured Euclidean chart, hence makes it simply connected.
-/
theorem twoPointComplement_simplyConnectedSpace_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x) :
    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) :=
  twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) hyx

/--
Consequently, every based fundamental group of a two-puncture complement
selected by the topology package is trivial.
-/
theorem twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  twoPointComplement_fundamentalGroup_subsingleton_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction) hyx basepoint

/--
Consumer-facing recognition and puncture payload from one completed topology
package: the same finite-extinction witness supplies sphere recognition,
one-point compactification recognition, singleton-complement contractibility,
two-puncture simple connectedness, and trivial based fundamental groups for
two-puncture complements.
-/
theorem topology_package_recognition_and_puncture_payload
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    Nonempty (M ≃ₜ ThreeSphere) ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      ContractibleSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  ⟨ homeomorphism_of_topology_package package M extinction
  , homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction
  , compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  , twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  , twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint
  ⟩

/--
Target-family form of the topology package recognition and puncture payload:
for every finite-extinction target, the package supplies sphere and one-point
recognition, all singleton-complement contractibility instances, and all
two-puncture simple-connectedness/fundamental-group-triviality instances.
-/
theorem topology_package_recognition_and_puncture_payload_family
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        Nonempty (M ≃ₜ ThreeSphere) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint)) := by
  intro M _top _t2 _charted _simple _compact extinction
  exact
    ⟨ homeomorphism_of_topology_package package M extinction
    , homeomorph_to_onePoint_threeSpace_of_topology_package
        package M extinction
    , fun x =>
        compl_singleton_contractibleSpace_of_topology_package
          package M extinction x
    , fun hyx basepoint =>
        ⟨ twoPointComplement_simplyConnectedSpace_of_topology_package
            package M extinction hyx
        , twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
            package M extinction hyx basepoint
        ⟩
    ⟩

/--
The same package-level route exposes the concrete topology-extraction
classification and homeomorphism-derivation stack together with the transported
one-point and puncture-complement consequences.
-/
theorem topology_package_extraction_derivation_and_puncture_payload
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    {x y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
      homeomorphism = homeomorphism_of_topology_package package M extinction ∧
      ExtinctionTopologyClassificationSubobligationsPayload M extinction ∧
      ExtinctionTopologySimplyConnectedRecognitionStatement M extinction ∧
      ExtinctionTopologySphericalTrivialQuotientStatement M extinction ∧
      ExtinctionTopologySphericalHomeomorphismLiftStatement M extinction ∧
      ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
        homeomorphism ∧
      ExtinctionTopologyHomeomorphismDerivationStatement M extinction
        homeomorphism ∧
      ExtinctionTopologyLiftedHomeomorphismDerivationStatement M extinction
        homeomorphism ∧
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      ContractibleSpace ({x}ᶜ : Set M) ∧
      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
      Subsingleton (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) :=
  ⟨ homeomorphism_of_topology_package package M extinction
  , rfl
  , topology_classification_subobligations_of_topology_package
      package M extinction
  , topology_simply_connected_recognition_statement_of_topology_package
      package M extinction
  , topology_spherical_trivial_quotient_statement_of_topology_package
      package M extinction
  , topology_spherical_homeomorphism_lift_statement_of_topology_package
      package M extinction
  , topology_homeomorphism_assembly_statement_of_topology_package
      package M extinction
  , topology_homeomorphism_derivation_statement_of_topology_package
      package M extinction
  , topology_lifted_homeomorphism_derivation_statement_of_topology_package
      package M extinction
  , homeomorph_to_onePoint_threeSpace_of_topology_package
      package M extinction
  , compl_singleton_contractibleSpace_of_topology_package
      package M extinction x
  , twoPointComplement_simplyConnectedSpace_of_topology_package
      package M extinction hyx
  , twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
      package M extinction hyx basepoint
  ⟩

/--
Target-family form of the concrete topology derivation and puncture payload:
one completed topology package exposes the classification/recognition/lifted
homeomorphism stack, one-point recognition, every singleton-complement
contractibility instance, and every two-puncture simple-connectedness/trivial
fundamental-group instance for all finite-extinction targets.
-/
theorem topology_package_extraction_derivation_and_puncture_payload_family
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
          homeomorphism =
              homeomorphism_of_topology_package package M _extinction ∧
          ExtinctionTopologyClassificationSubobligationsPayload
            M _extinction ∧
          ExtinctionTopologySimplyConnectedRecognitionStatement
            M _extinction ∧
          ExtinctionTopologySphericalTrivialQuotientStatement M _extinction ∧
          ExtinctionTopologySphericalHomeomorphismLiftStatement M _extinction ∧
          ExtinctionTopologyHomeomorphismAssemblyStatement
            M _extinction homeomorphism ∧
          ExtinctionTopologyHomeomorphismDerivationStatement
            M _extinction homeomorphism ∧
          ExtinctionTopologyLiftedHomeomorphismDerivationStatement
            M _extinction homeomorphism ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint)) := by
  intro M _top _t2 _charted _simple _compact extinction
  exact
    ⟨ homeomorphism_of_topology_package package M extinction
    , rfl
    , topology_classification_subobligations_of_topology_package
        package M extinction
    , topology_simply_connected_recognition_statement_of_topology_package
        package M extinction
    , topology_spherical_trivial_quotient_statement_of_topology_package
        package M extinction
    , topology_spherical_homeomorphism_lift_statement_of_topology_package
        package M extinction
    , topology_homeomorphism_assembly_statement_of_topology_package
        package M extinction
    , topology_homeomorphism_derivation_statement_of_topology_package
        package M extinction
    , topology_lifted_homeomorphism_derivation_statement_of_topology_package
        package M extinction
    , homeomorph_to_onePoint_threeSpace_of_topology_package
        package M extinction
    , fun x =>
        compl_singleton_contractibleSpace_of_topology_package
          package M extinction x
    , fun hyx basepoint =>
        ⟨ twoPointComplement_simplyConnectedSpace_of_topology_package
            package M extinction hyx
        , twoPointComplement_fundamentalGroup_subsingleton_of_topology_package
            package M extinction hyx basepoint
        ⟩
    ⟩

/--
A completed topology package supplies the theorem-shaped extraction statement,
the final extractor consumed by the assembly layer, the lifted-homeomorphism
derivation package, and the target-family recognition/puncture payload.
-/
theorem topology_package_final_extractor_lifted_derivation_and_puncture_payload_family
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
      topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
      ExtinctionImpliesSphereStatement.{u} ∧
      ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
            homeomorphism =
                homeomorphism_of_topology_package package M _extinction ∧
            ExtinctionTopologyClassificationSubobligationsPayload
              M _extinction ∧
            ExtinctionTopologySimplyConnectedRecognitionStatement
              M _extinction ∧
            ExtinctionTopologySphericalTrivialQuotientStatement
              M _extinction ∧
            ExtinctionTopologySphericalHomeomorphismLiftStatement
              M _extinction ∧
            ExtinctionTopologyHomeomorphismAssemblyStatement
              M _extinction homeomorphism ∧
            ExtinctionTopologyHomeomorphismDerivationStatement
              M _extinction homeomorphism ∧
            ExtinctionTopologyLiftedHomeomorphismDerivationStatement
              M _extinction homeomorphism ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
            (∀ {x y : M} (_hyx : y ≠ x)
              (basepoint : (({x} ∪ {y})ᶜ : Set M)),
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  Subsingleton
                    (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                      basepoint))) :=
  ⟨ extinction_topology_extraction_statement_of_topology_package package
  , rfl
  , extinction_implies_sphere_of_topology_package package
  , topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
      package
  , topology_package_extraction_derivation_and_puncture_payload_family
      package
  ⟩

/--
Consumer payload for the topology-extraction pillar.  It retains the concrete
topology extraction package, its package-layer requirement, the final extractor
statement, the lifted-homeomorphism derivation route, and the target-family
recognition/puncture payload produced from that same package.
-/
structure ExtinctionTopologyCompleteConsumerPayload where
  topologyPackage : ExtinctionTopologyExtractionPackage.{u}
  topologyPackageRequirement : ExtinctionTopologyExtractionPackage.{u}
  topologyStatement : ExtinctionTopologyExtractionStatement.{u}
  topologyStatement_eq :
    topologyStatement =
      extinction_topology_extraction_statement_of_topology_package
        topologyPackage
  extinctionImpliesSphere : ExtinctionImpliesSphereStatement.{u}
  liftedHomeomorphismDerivation :
    ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u}
  derivationPunctureFamily :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
          homeomorphism =
              homeomorphism_of_topology_package topologyPackage M
                _extinction ∧
          ExtinctionTopologyClassificationSubobligationsPayload
            M _extinction ∧
          ExtinctionTopologySimplyConnectedRecognitionStatement
            M _extinction ∧
          ExtinctionTopologySphericalTrivialQuotientStatement
            M _extinction ∧
          ExtinctionTopologySphericalHomeomorphismLiftStatement
            M _extinction ∧
          ExtinctionTopologyHomeomorphismAssemblyStatement
            M _extinction homeomorphism ∧
          ExtinctionTopologyHomeomorphismDerivationStatement
            M _extinction homeomorphism ∧
          ExtinctionTopologyLiftedHomeomorphismDerivationStatement
            M _extinction homeomorphism ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint))

/--
A completed topology extraction package constructs the complete topology
consumer payload, without forcing downstream final-certificate code to reopen
the final extractor and puncture-transport projections separately.
-/
theorem extinctionTopology_completeConsumerPayload_of_topologyPackage
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}) :=
  ⟨ { topologyPackage := package
      topologyPackageRequirement := package
      topologyStatement :=
        extinction_topology_extraction_statement_of_topology_package
          package
      topologyStatement_eq := rfl
      extinctionImpliesSphere :=
        extinction_implies_sphere_of_topology_package package
      liftedHomeomorphismDerivation :=
        topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
          package
      derivationPunctureFamily :=
        topology_package_extraction_derivation_and_puncture_payload_family
          package } ⟩

/--
The complete topology consumer payload is equivalent to the concrete topology
extraction package: the payload stores the package in one direction, while the
reverse direction constructs all final extractor and puncture-transport fields
from that package.
-/
theorem nonempty_extinctionTopologyCompleteConsumerPayload_iff_topologyPackage :
    Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}) ↔
      ExtinctionTopologyExtractionPackage.{u} := by
  constructor
  · rintro ⟨payload⟩
    exact payload.topologyPackage
  · intro package
    exact extinctionTopology_completeConsumerPayload_of_topologyPackage package

/--
The complete topology consumer payload is exactly a concrete topology package
together with the final extraction statement equality, the global
extinction-implies-sphere and lifted-derivation endpoints, and the full
target-family derivation/puncture payload tied to that same package.  The
reverse direction rebuilds the complete consumer payload from those fields.
-/
theorem nonempty_extinctionTopologyCompleteConsumerPayload_iff_package_statement_and_derivationPunctureFamily :
    Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}) ↔
      ∃ package : ExtinctionTopologyExtractionPackage.{u},
        ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
          topologyStatement =
              extinction_topology_extraction_statement_of_topology_package
                package ∧
            ExtinctionImpliesSphereStatement.{u} ∧
            ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
            (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
              [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
              [SimplyConnectedSpace M] [CompactSpace M]
              (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
                ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
                  homeomorphism =
                      homeomorphism_of_topology_package package M
                        _extinction ∧
                  ExtinctionTopologyClassificationSubobligationsPayload
                    M _extinction ∧
                  ExtinctionTopologySimplyConnectedRecognitionStatement
                    M _extinction ∧
                  ExtinctionTopologySphericalTrivialQuotientStatement
                    M _extinction ∧
                  ExtinctionTopologySphericalHomeomorphismLiftStatement
                    M _extinction ∧
                  ExtinctionTopologyHomeomorphismAssemblyStatement
                    M _extinction homeomorphism ∧
                  ExtinctionTopologyHomeomorphismDerivationStatement
                    M _extinction homeomorphism ∧
                  ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                    M _extinction homeomorphism ∧
                  Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
                  (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
                  (∀ {x y : M} (_hyx : y ≠ x)
                    (basepoint : (({x} ∪ {y})ᶜ : Set M)),
                      SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                        Subsingleton
                          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                            basepoint))) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.topologyPackage
      , payload.topologyStatement
      , payload.topologyStatement_eq
      , payload.extinctionImpliesSphere
      , payload.liftedHomeomorphismDerivation
      , payload.derivationPunctureFamily
      ⟩
  · rintro
      ⟨ package
      , topologyStatement
      , topologyStatement_eq
      , extinctionImpliesSphere
      , liftedHomeomorphismDerivation
      , derivationPunctureFamily
      ⟩
    exact
      ⟨ { topologyPackage := package
          topologyPackageRequirement := package
          topologyStatement := topologyStatement
          topologyStatement_eq := topologyStatement_eq
          extinctionImpliesSphere := extinctionImpliesSphere
          liftedHomeomorphismDerivation := liftedHomeomorphismDerivation
          derivationPunctureFamily := derivationPunctureFamily } ⟩

/--
The complete topology consumer payload is also equivalent to a concrete
topology package, the lifted-homeomorphism derivation endpoint, and the full
package-tied derivation/puncture family.  The reverse direction derives the
global extinction-implies-sphere statement from the target-family
homeomorphism witness before rebuilding the complete payload.
-/
theorem nonempty_extinctionTopologyCompleteConsumerPayload_iff_package_liftedDerivation_and_derivationPunctureFamily :
    Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}) ↔
      ∃ package : ExtinctionTopologyExtractionPackage.{u},
        ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
          (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [SimplyConnectedSpace M] [CompactSpace M]
            (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
              ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
                homeomorphism =
                    homeomorphism_of_topology_package package M
                      _extinction ∧
                ExtinctionTopologyClassificationSubobligationsPayload
                  M _extinction ∧
                ExtinctionTopologySimplyConnectedRecognitionStatement
                  M _extinction ∧
                ExtinctionTopologySphericalTrivialQuotientStatement
                  M _extinction ∧
                ExtinctionTopologySphericalHomeomorphismLiftStatement
                  M _extinction ∧
                ExtinctionTopologyHomeomorphismAssemblyStatement
                  M _extinction homeomorphism ∧
                ExtinctionTopologyHomeomorphismDerivationStatement
                  M _extinction homeomorphism ∧
                ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                  M _extinction homeomorphism ∧
                Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
                (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
                (∀ {x y : M} (_hyx : y ≠ x)
                  (basepoint : (({x} ∪ {y})ᶜ : Set M)),
                    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                      Subsingleton
                        (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                          basepoint))) := by
  constructor
  · rintro ⟨payload⟩
    exact
      ⟨ payload.topologyPackage
      , payload.liftedHomeomorphismDerivation
      , payload.derivationPunctureFamily
      ⟩
  · rintro ⟨package, liftedHomeomorphismDerivation, derivationPunctureFamily⟩
    let extinctionImpliesSphere : ExtinctionImpliesSphereStatement.{u} := by
      intro M _top _t2 _charted _simple _compact extinction
      rcases derivationPunctureFamily M extinction with
        ⟨homeomorphism, _homeomorphism_eq, _classification,
          _simplyConnectedRecognition, _trivialQuotient, _lift,
          _assembly, _derivation, _liftedDerivation, _onePoint,
          _singletonContractible, _twoPoint⟩
      exact homeomorphism
    exact
      ⟨ { topologyPackage := package
          topologyPackageRequirement := package
          topologyStatement :=
            extinction_topology_extraction_statement_of_topology_package
              package
          topologyStatement_eq := rfl
          extinctionImpliesSphere := extinctionImpliesSphere
          liftedHomeomorphismDerivation := liftedHomeomorphismDerivation
          derivationPunctureFamily := derivationPunctureFamily } ⟩

/--
An inhabited complete topology consumer payload exposes the concrete topology
package, the final extraction statement, the extinction-implies-sphere
endpoint, and the lifted-homeomorphism derivation route carried by the same
package object.
-/
theorem extinctionTopology_package_statement_and_liftedDerivation_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u})) :
    ∃ _package : ExtinctionTopologyExtractionPackage.{u},
      ExtinctionTopologyExtractionStatement.{u} ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} :=
  by
    rcases payload with ⟨payload⟩
    exact
      ⟨ payload.topologyPackage
      , payload.topologyStatement
      , payload.extinctionImpliesSphere
      , payload.liftedHomeomorphismDerivation
      ⟩

/--
An inhabited complete topology consumer payload also exposes the full
recognition/puncture target family retained by the same concrete topology
package.  This keeps the one-point compactification and two-puncture
recognition obligations available to final-certificate consumers without
reconstructing the topology package.
-/
theorem extinctionTopology_derivationPunctureFamily_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u})) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
            homeomorphism =
                homeomorphism_of_topology_package package M
                  _extinction ∧
            ExtinctionTopologyClassificationSubobligationsPayload
              M _extinction ∧
            ExtinctionTopologySimplyConnectedRecognitionStatement
              M _extinction ∧
            ExtinctionTopologySphericalTrivialQuotientStatement
              M _extinction ∧
            ExtinctionTopologySphericalHomeomorphismLiftStatement
              M _extinction ∧
            ExtinctionTopologyHomeomorphismAssemblyStatement
              M _extinction homeomorphism ∧
            ExtinctionTopologyHomeomorphismDerivationStatement
              M _extinction homeomorphism ∧
            ExtinctionTopologyLiftedHomeomorphismDerivationStatement
              M _extinction homeomorphism ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
            (∀ {x y : M} (_hyx : y ≠ x)
              (basepoint : (({x} ∪ {y})ᶜ : Set M)),
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  Subsingleton
                    (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                      basepoint)) := by
  rcases payload with ⟨payload⟩
  exact ⟨payload.topologyPackage, payload.derivationPunctureFamily⟩

/--
A complete topology consumer payload specializes to a fixed finite-extinction
target: it supplies the selected sphere homeomorphism, its derivation statement,
the one-point compactification recognition, all singleton-complement
contractibility instances, and the two-puncture simple-connectivity/trivial
fundamental-group package.
-/
theorem extinctionTopology_fixedTarget_puncture_payload_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        homeomorphism =
            homeomorphism_of_topology_package package M extinction ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction homeomorphism ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
        (∀ {x y : M} (_hyx : y ≠ x)
          (basepoint : (({x} ∪ {y})ᶜ : Set M)),
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
              Subsingleton
                (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                  basepoint)) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, hDerivation, _liftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  exact
    ⟨payload.topologyPackage, homeomorphism, hHomeomorphism_eq,
      hDerivation, hOnePoint, hSingletonContractible, hTwoPoint⟩

/--
For a fixed finite-extinction target and chosen two-puncture basepoint, a
complete topology consumer payload exposes the package-selected sphere
recognition together with the concrete puncture-transport consequences derived
from that recognition: one-point recognition, a singleton Euclidean chart,
singleton contractibility, two-puncture simple connectedness, and based
fundamental-group collapse.
-/
theorem extinctionTopology_fixedTarget_recognition_and_transport_fields_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        homeomorphism =
            homeomorphism_of_topology_package package M extinction ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, _derivation, _liftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  exact
    ⟨ payload.topologyPackage
    , homeomorphism
    , hHomeomorphism_eq
    , hOnePoint
    , ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
        homeomorphism x⟩
    , hSingletonContractible x
    , (hTwoPoint hyx basepoint).1
    , (hTwoPoint hyx basepoint).2
    ⟩

/--
For a fixed finite-extinction target and chosen singleton-complement basepoint,
a complete topology consumer payload exposes the package-selected recognition
together with the singleton Euclidean chart, contractibility, simple
connectedness, and based fundamental-group collapse.
-/
theorem extinctionTopology_fixedTarget_singleton_fundamentalGroup_payload_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) (basepoint : ({x}ᶜ : Set M)) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        homeomorphism =
            homeomorphism_of_topology_package package M extinction ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, _derivation, _liftedDerivation, hOnePoint,
      hSingletonContractible, _twoPoint⟩
  exact
    ⟨ payload.topologyPackage
    , homeomorphism
    , hHomeomorphism_eq
    , hOnePoint
    , ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
        hOnePoint x⟩
    , hSingletonContractible x
    , compl_singleton_simplyConnectedSpace_of_topology_package
        payload.topologyPackage M extinction x
    , compl_singleton_fundamentalGroup_subsingleton_of_topology_package
        payload.topologyPackage M extinction x basepoint
    ⟩

/--
For a fixed finite-extinction target and chosen singleton-complement basepoint,
a complete topology consumer payload exposes the full singleton low-homotopy
collapse package retained by the topology package, not only the fundamental
group collapse.  This gives downstream puncture-transport consumers direct
access to path-component, `π₀`, fundamental-group, and `π₁` subsingleton facts
from the same selected package and recognition data.
-/
theorem extinctionTopology_fixedTarget_singleton_lowHomotopy_payload_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) (basepoint : ({x}ᶜ : Set M)) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        homeomorphism =
            homeomorphism_of_topology_package package M extinction ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M) basepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M) basepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M) basepoint) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, _derivation, _liftedDerivation, hOnePoint,
      hSingletonContractible, _twoPoint⟩
  rcases
    compl_singleton_lowHomotopy_subsingleton_package_of_topology_package
      payload.topologyPackage M extinction x basepoint with
    ⟨zerothSubsingleton, piZeroSubsingleton, fundamentalGroupSubsingleton,
      piOneSubsingleton⟩
  exact
    ⟨ payload.topologyPackage
    , homeomorphism
    , hHomeomorphism_eq
    , hOnePoint
    , ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
        hOnePoint x⟩
    , hSingletonContractible x
    , compl_singleton_simplyConnectedSpace_of_topology_package
        payload.topologyPackage M extinction x
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalGroupSubsingleton
    , piOneSubsingleton
    ⟩

/--
For a fixed finite-extinction target and chosen two-puncture basepoint, a
complete topology consumer payload exposes not only the package-selected
sphere recognition and puncture-transport consequences, but also the concrete
punctured-Euclidean model of that two-point complement.
-/
theorem extinctionTopology_fixedTarget_euclidean_puncture_models_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        homeomorphism =
            homeomorphism_of_topology_package package M extinction ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, _derivation, _liftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  rcases
    exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
      hOnePoint hyx with
    ⟨puncture, hPuncturedEuclidean⟩
  exact
    ⟨ payload.topologyPackage
    , homeomorphism
    , hHomeomorphism_eq
    , ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
        homeomorphism x⟩
    , ⟨puncture, hPuncturedEuclidean⟩
    , hSingletonContractible x
    , (hTwoPoint hyx basepoint).1
    , (hTwoPoint hyx basepoint).2
    ⟩

/--
For a fixed finite-extinction target, a complete topology consumer payload
exposes the selected 3-sphere homeomorphism together with the one-point
compactification homeomorphism transported by the same topology package.
-/
theorem extinctionTopology_fixedTarget_sphere_and_onePoint_homeomorphisms_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        homeomorphism =
            homeomorphism_of_topology_package package M extinction ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, _derivation, _liftedDerivation, hOnePoint,
      _singletonContractible, _twoPoint⟩
  exact
    ⟨ payload.topologyPackage
    , homeomorphism
    , hHomeomorphism_eq
    , hOnePoint
    ⟩

/--
For a fixed finite-extinction target, a complete topology consumer payload
exposes the topology package, global extraction statement,
extinction-to-sphere statement, selected sphere homeomorphism, and one-point
compactification homeomorphism for that same target.
-/
theorem extinctionTopology_package_statement_and_fixedTarget_sphere_onePoint_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ExtinctionTopologyExtractionStatement.{u} ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
          homeomorphism =
              homeomorphism_of_topology_package package M extinction ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, _derivation, _liftedDerivation, hOnePoint,
      _singletonContractible, _twoPoint⟩
  exact
    ⟨ payload.topologyPackage
    , payload.topologyStatement
    , payload.extinctionImpliesSphere
    , homeomorphism
    , hHomeomorphism_eq
    , hOnePoint
    ⟩

/--
For a fixed finite-extinction target, a complete topology consumer payload
exposes the concrete package, global extraction statements, selected
homeomorphism derivation, and puncture-transport package without requiring the
larger classification/lift surface.
-/
theorem extinctionTopology_package_statement_and_fixedTarget_puncture_payload_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ExtinctionTopologyExtractionStatement.{u} ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
        ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
          homeomorphism =
              homeomorphism_of_topology_package package M extinction ∧
          ExtinctionTopologyHomeomorphismDerivationStatement
            M extinction homeomorphism ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint)) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, hDerivation, _liftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  exact
    ⟨ payload.topologyPackage
    , payload.topologyStatement
    , payload.extinctionImpliesSphere
    , payload.liftedHomeomorphismDerivation
    , homeomorphism
    , hHomeomorphism_eq
    , hDerivation
    , hOnePoint
    , hSingletonContractible
    , hTwoPoint
    ⟩

/--
For a fixed finite-extinction target, the complete topology consumer payload
also exposes the full extraction surface: classification subobligations,
simply-connected recognition, quotient/lift/assembly/derivation statements,
and the puncture transport package.
-/
theorem extinctionTopology_fixedTarget_fullExtraction_payload_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        homeomorphism =
            homeomorphism_of_topology_package package M extinction ∧
        ExtinctionTopologyClassificationSubobligationsPayload
          M extinction ∧
        ExtinctionTopologySimplyConnectedRecognitionStatement
          M extinction ∧
        ExtinctionTopologySphericalTrivialQuotientStatement
          M extinction ∧
        ExtinctionTopologySphericalHomeomorphismLiftStatement
          M extinction ∧
        ExtinctionTopologyHomeomorphismAssemblyStatement
          M extinction homeomorphism ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction homeomorphism ∧
        ExtinctionTopologyLiftedHomeomorphismDerivationStatement
          M extinction homeomorphism ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
        (∀ {x y : M} (_hyx : y ≠ x)
          (basepoint : (({x} ∪ {y})ᶜ : Set M)),
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
              Subsingleton
                (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                  basepoint)) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, hClassification,
      hSimplyConnectedRecognition, hTrivialQuotient, hLift, hAssembly,
      hDerivation, hLiftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  exact
    ⟨ payload.topologyPackage
    , homeomorphism
    , hHomeomorphism_eq
    , hClassification
    , hSimplyConnectedRecognition
    , hTrivialQuotient
    , hLift
    , hAssembly
    , hDerivation
    , hLiftedDerivation
    , hOnePoint
    , hSingletonContractible
    , hTwoPoint
    ⟩

/--
For a fixed finite-extinction target, a complete topology consumer payload
exposes the concrete package requirement, global extraction statements, and the
full target-specific extraction and puncture-transport payload together.
-/
theorem extinctionTopology_package_statement_and_fixedTarget_fullExtraction_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ExtinctionTopologyExtractionStatement.{u} ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
        ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
          homeomorphism =
              homeomorphism_of_topology_package package M extinction ∧
          ExtinctionTopologyClassificationSubobligationsPayload
            M extinction ∧
          ExtinctionTopologySimplyConnectedRecognitionStatement
            M extinction ∧
          ExtinctionTopologySphericalTrivialQuotientStatement
            M extinction ∧
          ExtinctionTopologySphericalHomeomorphismLiftStatement
            M extinction ∧
          ExtinctionTopologyHomeomorphismAssemblyStatement
            M extinction homeomorphism ∧
          ExtinctionTopologyHomeomorphismDerivationStatement
            M extinction homeomorphism ∧
          ExtinctionTopologyLiftedHomeomorphismDerivationStatement
            M extinction homeomorphism ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint)) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, hClassification,
      hSimplyConnectedRecognition, hTrivialQuotient, hLift, hAssembly,
      hDerivation, hLiftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  exact
    ⟨ payload.topologyPackage
    , payload.topologyStatement
    , payload.extinctionImpliesSphere
    , payload.liftedHomeomorphismDerivation
    , homeomorphism
    , hHomeomorphism_eq
    , hClassification
    , hSimplyConnectedRecognition
    , hTrivialQuotient
    , hLift
    , hAssembly
    , hDerivation
    , hLiftedDerivation
    , hOnePoint
    , hSingletonContractible
    , hTwoPoint
    ⟩

/--
For a fixed finite-extinction target, a complete topology consumer payload
exposes the selected final homeomorphism as a concrete `M ≃ₜ ThreeSphere`
witness, while retaining the one-point compactification recognition and
puncture transport fields downstream consumers need.
-/
theorem extinctionTopology_fixedTarget_concrete_homeomorphism_and_puncture_payload_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ExtinctionTopologyExtractionStatement.{u} ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ∃ homeomorphism : M ≃ₜ ThreeSphere,
          Nonempty (M ≃ₜ ThreeSphere) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          ExtinctionTopologyHomeomorphismDerivationStatement
            M extinction (Nonempty.intro homeomorphism) ∧
          Nonempty.intro homeomorphism =
              homeomorphism_of_topology_package package M extinction ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint)) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift,
      _assembly, hDerivation, _liftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  rcases homeomorphism with ⟨homeomorphism⟩
  exact
    ⟨ payload.topologyPackage
    , payload.topologyStatement
    , payload.extinctionImpliesSphere
    , homeomorphism
    , ⟨homeomorphism⟩
    , hOnePoint
    , hDerivation
    , hHomeomorphism_eq
    , hSingletonContractible
    , hTwoPoint
    ⟩

/--
For a fixed finite-extinction target, a complete topology consumer payload
exposes the selected final homeomorphism as a concrete `M ≃ₜ ThreeSphere`
witness together with the full target-specific extraction surface:
classification subobligations, recognition, quotient/lift/assembly/derivation
routes, one-point compactification recognition, and puncture transport data.
-/
theorem extinctionTopology_fixedTarget_concrete_homeomorphism_fullExtraction_payload_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ExtinctionTopologyExtractionStatement.{u} ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
        ∃ homeomorphism : M ≃ₜ ThreeSphere,
          Nonempty.intro homeomorphism =
              homeomorphism_of_topology_package package M extinction ∧
          ExtinctionTopologyClassificationSubobligationsPayload
            M extinction ∧
          ExtinctionTopologySimplyConnectedRecognitionStatement
            M extinction ∧
          ExtinctionTopologySphericalTrivialQuotientStatement
            M extinction ∧
          ExtinctionTopologySphericalHomeomorphismLiftStatement
            M extinction ∧
          ExtinctionTopologyHomeomorphismAssemblyStatement
            M extinction (Nonempty.intro homeomorphism) ∧
          ExtinctionTopologyHomeomorphismDerivationStatement
            M extinction (Nonempty.intro homeomorphism) ∧
          ExtinctionTopologyLiftedHomeomorphismDerivationStatement
            M extinction (Nonempty.intro homeomorphism) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint)) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, hClassification,
      hSimplyConnectedRecognition, hTrivialQuotient, hLift, hAssembly,
      hDerivation, hLiftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  rcases homeomorphism with ⟨homeomorphism⟩
  exact
    ⟨ payload.topologyPackage
    , payload.topologyStatement
    , payload.extinctionImpliesSphere
    , payload.liftedHomeomorphismDerivation
    , homeomorphism
    , hHomeomorphism_eq
    , hClassification
    , hSimplyConnectedRecognition
    , hTrivialQuotient
    , hLift
    , hAssembly
    , hDerivation
    , hLiftedDerivation
    , hOnePoint
    , hSingletonContractible
    , hTwoPoint
    ⟩

/--
For a fixed finite-extinction target, a complete topology consumer payload
exposes the stored final-extraction statement together with its exact package
equality, then carries that same package through the concrete sphere
homeomorphism, one-point compactification recognition, and puncture transport
payload.
-/
theorem extinctionTopology_statementEquality_and_fixedTarget_concrete_homeomorphism_fullExtraction_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
    ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
      topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
        ∃ homeomorphism : M ≃ₜ ThreeSphere,
          Nonempty (M ≃ₜ ThreeSphere) ∧
          Nonempty.intro homeomorphism =
              homeomorphism_of_topology_package package M extinction ∧
          ExtinctionTopologyClassificationSubobligationsPayload
            M extinction ∧
          ExtinctionTopologySimplyConnectedRecognitionStatement
            M extinction ∧
          ExtinctionTopologySphericalTrivialQuotientStatement
            M extinction ∧
          ExtinctionTopologySphericalHomeomorphismLiftStatement
            M extinction ∧
          ExtinctionTopologyHomeomorphismAssemblyStatement
            M extinction (Nonempty.intro homeomorphism) ∧
          ExtinctionTopologyHomeomorphismDerivationStatement
            M extinction (Nonempty.intro homeomorphism) ∧
          ExtinctionTopologyLiftedHomeomorphismDerivationStatement
            M extinction (Nonempty.intro homeomorphism) ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
          (∀ {x y : M} (_hyx : y ≠ x)
            (basepoint : (({x} ∪ {y})ᶜ : Set M)),
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint)) := by
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨homeomorphism, hHomeomorphism_eq, hClassification,
      hSimplyConnectedRecognition, hTrivialQuotient, hLift, hAssembly,
      hDerivation, hLiftedDerivation, hOnePoint,
      hSingletonContractible, hTwoPoint⟩
  rcases homeomorphism with ⟨homeomorphism⟩
  exact
    ⟨ payload.topologyPackage
    , payload.topologyStatement
    , payload.topologyStatement_eq
    , payload.extinctionImpliesSphere
    , payload.liftedHomeomorphismDerivation
    , homeomorphism
    , ⟨homeomorphism⟩
    , hHomeomorphism_eq
    , hClassification
    , hSimplyConnectedRecognition
    , hTrivialQuotient
    , hLift
    , hAssembly
    , hDerivation
    , hLiftedDerivation
    , hOnePoint
    , hSingletonContractible
    , hTwoPoint
    ⟩

/--
For a fixed finite-extinction target and chosen two-puncture basepoint, a
complete topology consumer payload keeps the topology-package statement
equality and global extraction statements synchronized with the concrete final
homeomorphism and the Euclidean models of the singleton and two-point
complements.
-/
theorem extinctionTopology_package_statement_and_fixedTarget_euclidean_puncture_models_of_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (basepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ package : ExtinctionTopologyExtractionPackage.{u},
    ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
      topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        ExtinctionImpliesSphereStatement.{u} ∧
        ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
        ∃ homeomorphism : M ≃ₜ ThreeSphere,
          Nonempty.intro homeomorphism =
              homeomorphism_of_topology_package package M extinction ∧
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
          Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ContractibleSpace ({x}ᶜ : Set M) ∧
          SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
          Subsingleton
            (FundamentalGroup (({x} ∪ {y})ᶜ : Set M) basepoint) := by
  rcases
    extinctionTopology_statementEquality_and_fixedTarget_concrete_homeomorphism_fullExtraction_of_completeConsumerPayload
      payload M extinction with
    ⟨ package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , _nonemptyHomeomorphism
    , hHomeomorphism
    , _classification
    , _simplyConnectedRecognition
    , _trivialQuotient
    , _lift
    , _assembly
    , _derivation
    , _liftedDerivation
    , hOnePoint
    , hSingletonContractible
    , hTwoPoint
    ⟩
  rcases
    exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
      hOnePoint hyx with
    ⟨puncture, hPuncturedEuclidean⟩
  exact
    ⟨ package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , hHomeomorphism
    , hOnePoint
    , ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_threeSphere
        (Nonempty.intro homeomorphism) x⟩
    , ⟨puncture, hPuncturedEuclidean⟩
    , hSingletonContractible x
    , (hTwoPoint hyx basepoint).1
    , (hTwoPoint hyx basepoint).2
    ⟩

/--
The complete topology consumer payload supplies the named one-point
compactification recognition statement after finite extinction.  This is the
topology side of the final target route stated against the compactification
model, not just the project `ThreeSphere` endpoint.
-/
theorem extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionTopology_completeConsumerPayload
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u})) :
    ExtinctionOnePointThreeSpaceRecognitionStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction
  rcases payload with ⟨payload⟩
  rcases payload.derivationPunctureFamily M extinction with
    ⟨_homeomorphism, _hHomeomorphism_eq, _classification,
      _simplyConnectedRecognition, _trivialQuotient, _lift, _assembly,
      _derivation, _liftedDerivation, hOnePoint, _singletonContractible,
      _twoPoint⟩
  exact hOnePoint

/--
Universal finite extinction together with the complete topology consumer
payload discharges the project target statement through the named one-point
compactification recognition route retained by the topology payload.
-/
theorem poincare_statement_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u})) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_universalFiniteExtinctionStatement_and_extinctionOnePointThreeSpaceRecognitionStatement
    finiteExtinction
    (extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionTopology_completeConsumerPayload
      payload)

/--
Universal finite extinction and the complete topology consumer payload expose a
target-free final topology endpoint: the public Poincare statement, the named
one-point recognition route, the selected topology package, the exact topology
statement produced by that package, the extinction-to-sphere statement, and
the lifted-homeomorphism derivation route.  Fixed-target extraction and
puncture transport can then be selected separately from the same payload.
-/
theorem poincare_statement_recognition_and_topologyPackage_endpoint_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u})) :
    PoincareConjectureStatement.{u} ∧
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
      ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
        topologyStatement =
            extinction_topology_extraction_statement_of_topology_package
              package ∧
          ExtinctionImpliesSphereStatement.{u} ∧
          ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} := by
  let recognition :
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} :=
    extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionTopology_completeConsumerPayload
      payload
  let statement : PoincareConjectureStatement.{u} :=
    poincare_statement_of_universalFiniteExtinctionStatement_and_extinctionOnePointThreeSpaceRecognitionStatement
      finiteExtinction recognition
  rcases payload with ⟨payload⟩
  exact
    ⟨ statement
    , recognition
    , payload.topologyPackage
    , payload.topologyStatement
    , payload.topologyStatement_eq
    , payload.extinctionImpliesSphere
    , payload.liftedHomeomorphismDerivation
    ⟩

/--
Universal finite extinction and the complete topology consumer payload expose
the public Poincare statement together with the named one-point recognition
route and the fixed-target concrete full-extraction payload.  This packages the
final statement endpoint and the topology-extraction evidence for the selected
finite-extinction target without reopening the topology package.
-/
theorem poincare_statement_recognition_and_fixedTarget_concrete_fullExtraction_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    PoincareConjectureStatement.{u} ∧
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
      ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
        topologyStatement =
            extinction_topology_extraction_statement_of_topology_package
              package ∧
          ExtinctionImpliesSphereStatement.{u} ∧
          ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
          ∃ homeomorphism : M ≃ₜ ThreeSphere,
            Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty.intro homeomorphism =
                homeomorphism_of_topology_package package M extinction ∧
            ExtinctionTopologyClassificationSubobligationsPayload
              M extinction ∧
            ExtinctionTopologySimplyConnectedRecognitionStatement
              M extinction ∧
            ExtinctionTopologySphericalTrivialQuotientStatement
              M extinction ∧
            ExtinctionTopologySphericalHomeomorphismLiftStatement
              M extinction ∧
            ExtinctionTopologyHomeomorphismAssemblyStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyLiftedHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            (∀ x : M, ContractibleSpace ({x}ᶜ : Set M)) ∧
            (∀ {x y : M} (_hyx : y ≠ x)
              (basepoint : (({x} ∪ {y})ᶜ : Set M)),
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  Subsingleton
                    (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                      basepoint)) := by
  let recognition :
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} :=
    extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionTopology_completeConsumerPayload
      payload
  let statement : PoincareConjectureStatement.{u} :=
    poincare_statement_of_universalFiniteExtinctionStatement_and_extinctionOnePointThreeSpaceRecognitionStatement
      finiteExtinction recognition
  rcases
    extinctionTopology_statementEquality_and_fixedTarget_concrete_homeomorphism_fullExtraction_of_completeConsumerPayload
      payload M extinction with
    ⟨ package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , nonemptyHomeomorphism
    , hHomeomorphism
    , classification
    , simplyConnectedRecognition
    , trivialQuotient
    , lift
    , assembly
    , derivation
    , liftedDerivation
    , onePoint
    , singletonContractible
    , twoPoint
    ⟩
  exact
    ⟨ statement
    , recognition
    , package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , nonemptyHomeomorphism
    , hHomeomorphism
    , classification
    , simplyConnectedRecognition
    , trivialQuotient
    , lift
    , assembly
    , derivation
    , liftedDerivation
    , onePoint
    , singletonContractible
    , twoPoint
    ⟩

/--
Universal finite extinction and the complete topology consumer payload expose
the public Poincare statement while retaining the fixed-target topology
recognition data needed by puncture-transport consumers.  The selected package
is kept synchronized with its extraction statement, concrete `ThreeSphere`
homeomorphism, one-point compactification recognition, Euclidean models for
the singleton and two-point complements, and the full singleton low-homotopy
collapse at a chosen basepoint.
-/
theorem poincare_statement_recognition_fixedTarget_lowHomotopy_and_euclideanPunctureModels_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    PoincareConjectureStatement.{u} ∧
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
      ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
        topologyStatement =
            extinction_topology_extraction_statement_of_topology_package
              package ∧
          ExtinctionImpliesSphereStatement.{u} ∧
          ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
          ∃ homeomorphism : M ≃ₜ ThreeSphere,
            Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty.intro homeomorphism =
                homeomorphism_of_topology_package package M extinction ∧
            ExtinctionTopologyClassificationSubobligationsPayload
              M extinction ∧
            ExtinctionTopologySimplyConnectedRecognitionStatement
              M extinction ∧
            ExtinctionTopologySphericalTrivialQuotientStatement
              M extinction ∧
            ExtinctionTopologySphericalHomeomorphismLiftStatement
              M extinction ∧
            ExtinctionTopologyHomeomorphismAssemblyStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyLiftedHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            Nonempty (({x}ᶜ : Set M) ≃ₜ
              EuclideanSpace ℝ (Fin 3)) ∧
            (∃ puncture : EuclideanSpace ℝ (Fin 3),
              Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
            ContractibleSpace ({x}ᶜ : Set M) ∧
            SimplyConnectedSpace ({x}ᶜ : Set M) ∧
            Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
              singletonBasepoint) ∧
            Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
              singletonBasepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
              singletonBasepoint) ∧
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                twoPointBasepoint) := by
  let recognition :
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} :=
    extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionTopology_completeConsumerPayload
      payload
  let statement : PoincareConjectureStatement.{u} :=
    poincare_statement_of_universalFiniteExtinctionStatement_and_extinctionOnePointThreeSpaceRecognitionStatement
      finiteExtinction recognition
  rcases
    extinctionTopology_statementEquality_and_fixedTarget_concrete_homeomorphism_fullExtraction_of_completeConsumerPayload
      payload M extinction with
    ⟨ package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , nonemptyHomeomorphism
    , hHomeomorphism
    , classification
    , simplyConnectedRecognition
    , trivialQuotient
    , lift
    , assembly
    , derivation
    , liftedDerivation
    , onePoint
    , singletonContractible
    , twoPoint
    ⟩
  rcases
    exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
      onePoint hyx with
    ⟨puncture, puncturedEuclidean⟩
  rcases
    compl_singleton_lowHomotopy_subsingleton_package_of_topology_package
      package M extinction x singletonBasepoint with
    ⟨zerothSubsingleton, piZeroSubsingleton,
      fundamentalGroupSubsingleton, piOneSubsingleton⟩
  exact
    ⟨ statement
    , recognition
    , package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , nonemptyHomeomorphism
    , hHomeomorphism
    , classification
    , simplyConnectedRecognition
    , trivialQuotient
    , lift
    , assembly
    , derivation
    , liftedDerivation
    , onePoint
    , ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
        onePoint x⟩
    , ⟨puncture, puncturedEuclidean⟩
    , singletonContractible x
    , compl_singleton_simplyConnectedSpace_of_topology_package
        package M extinction x
    , zerothSubsingleton
    , piZeroSubsingleton
    , fundamentalGroupSubsingleton
    , piOneSubsingleton
    , (twoPoint hyx twoPointBasepoint).1
    , (twoPoint hyx twoPointBasepoint).2
    ⟩

/--
Universal finite extinction and the complete topology consumer payload expose
the public Poincare statement together with a target-family topology package:
for the selected finite-extinction target, every singleton complement has its
Euclidean model, contractibility, simple connectedness, and full low-homotopy
collapse at every basepoint, and every two-point complement has a punctured
Euclidean model plus the simple-connected/fundamental-group collapse at every
basepoint.
-/
theorem poincare_statement_recognition_fixedTarget_punctureFamily_and_lowHomotopy_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}))
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    PoincareConjectureStatement.{u} ∧
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
      ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
        topologyStatement =
            extinction_topology_extraction_statement_of_topology_package
              package ∧
          ExtinctionImpliesSphereStatement.{u} ∧
          ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
          ∃ homeomorphism : M ≃ₜ ThreeSphere,
            Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty.intro homeomorphism =
                homeomorphism_of_topology_package package M extinction ∧
            ExtinctionTopologyClassificationSubobligationsPayload
              M extinction ∧
            ExtinctionTopologySimplyConnectedRecognitionStatement
              M extinction ∧
            ExtinctionTopologySphericalTrivialQuotientStatement
              M extinction ∧
            ExtinctionTopologySphericalHomeomorphismLiftStatement
              M extinction ∧
            ExtinctionTopologyHomeomorphismAssemblyStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyLiftedHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            (∀ x : M,
              Nonempty (({x}ᶜ : Set M) ≃ₜ
                EuclideanSpace ℝ (Fin 3)) ∧
              ContractibleSpace ({x}ᶜ : Set M) ∧
              SimplyConnectedSpace ({x}ᶜ : Set M) ∧
              ∀ basepoint : ({x}ᶜ : Set M),
                Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                  basepoint) ∧
                Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                  basepoint) ∧
                Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                  basepoint)) ∧
            (∀ {x y : M} (_hyx : y ≠ x),
              (∃ puncture : EuclideanSpace ℝ (Fin 3),
                Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                  ({puncture}ᶜ :
                    Set (EuclideanSpace ℝ (Fin 3))))) ∧
              ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint)) := by
  let recognition :
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} :=
    extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionTopology_completeConsumerPayload
      payload
  let statement : PoincareConjectureStatement.{u} :=
    poincare_statement_of_universalFiniteExtinctionStatement_and_extinctionOnePointThreeSpaceRecognitionStatement
      finiteExtinction recognition
  rcases
    extinctionTopology_statementEquality_and_fixedTarget_concrete_homeomorphism_fullExtraction_of_completeConsumerPayload
      payload M extinction with
    ⟨ package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , nonemptyHomeomorphism
    , hHomeomorphism
    , classification
    , simplyConnectedRecognition
    , trivialQuotient
    , lift
    , assembly
    , derivation
    , liftedDerivation
    , onePoint
    , singletonContractible
    , twoPoint
    ⟩
  exact
    ⟨ statement
    , recognition
    , package
    , topologyStatement
    , hTopologyStatement
    , extinctionImpliesSphere
    , liftedHomeomorphismDerivation
    , homeomorphism
    , nonemptyHomeomorphism
    , hHomeomorphism
    , classification
    , simplyConnectedRecognition
    , trivialQuotient
    , lift
    , assembly
    , derivation
    , liftedDerivation
    , onePoint
    , fun x =>
        ⟨ ⟨homeomorph_compl_singleton_euclidean_of_homeomorph_to_onePoint_threeSpace
            onePoint x⟩
        , singletonContractible x
        , compl_singleton_simplyConnectedSpace_of_topology_package
            package M extinction x
        , fun basepoint =>
            compl_singleton_lowHomotopy_subsingleton_package_of_topology_package
              package M extinction x basepoint
        ⟩
    , fun hyx =>
        ⟨ exists_homeomorph_twoPointComplement_puncturedEuclidean_of_homeomorph_to_onePoint_threeSpace
            onePoint hyx
        , fun basepoint =>
            ⟨ (twoPoint hyx basepoint).1
            , (twoPoint hyx basepoint).2
            ⟩
        ⟩
    ⟩

/--
Universal finite extinction and a concrete topology extraction package already
construct the complete topology consumer payload needed by the final route.
This endpoint keeps that constructed payload visible while exposing the same
fixed-target one-point, singleton-complement, and two-puncture low-homotopy
family, so downstream final-certificate code can start from the package layer
without separately assuming the complete consumer payload.
-/
theorem poincare_statement_recognition_fixedTarget_punctureFamily_and_lowHomotopy_of_universalFiniteExtinctionStatement_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}) ∧
      PoincareConjectureStatement.{u} ∧
      ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
      ∃ package : ExtinctionTopologyExtractionPackage.{u},
      ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
        topologyStatement =
            extinction_topology_extraction_statement_of_topology_package
              package ∧
          ExtinctionImpliesSphereStatement.{u} ∧
          ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
          ∃ homeomorphism : M ≃ₜ ThreeSphere,
            Nonempty (M ≃ₜ ThreeSphere) ∧
            Nonempty.intro homeomorphism =
                homeomorphism_of_topology_package package M extinction ∧
            ExtinctionTopologyClassificationSubobligationsPayload
              M extinction ∧
            ExtinctionTopologySimplyConnectedRecognitionStatement
              M extinction ∧
            ExtinctionTopologySphericalTrivialQuotientStatement
              M extinction ∧
            ExtinctionTopologySphericalHomeomorphismLiftStatement
              M extinction ∧
            ExtinctionTopologyHomeomorphismAssemblyStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            ExtinctionTopologyLiftedHomeomorphismDerivationStatement
              M extinction (Nonempty.intro homeomorphism) ∧
            Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
            (∀ x : M,
              Nonempty (({x}ᶜ : Set M) ≃ₜ
                EuclideanSpace ℝ (Fin 3)) ∧
              ContractibleSpace ({x}ᶜ : Set M) ∧
              SimplyConnectedSpace ({x}ᶜ : Set M) ∧
              ∀ basepoint : ({x}ᶜ : Set M),
                Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                  basepoint) ∧
                Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                  basepoint) ∧
                Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                  basepoint)) ∧
            (∀ {x y : M} (_hyx : y ≠ x),
              (∃ puncture : EuclideanSpace ℝ (Fin 3),
                Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                  ({puncture}ᶜ :
                    Set (EuclideanSpace ℝ (Fin 3))))) ∧
              ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    basepoint)) := by
  let payload : Nonempty (ExtinctionTopologyCompleteConsumerPayload.{u}) :=
    extinctionTopology_completeConsumerPayload_of_topologyPackage package
  exact
    ⟨ payload
    , poincare_statement_recognition_fixedTarget_punctureFamily_and_lowHomotopy_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
        finiteExtinction payload M extinction
    ⟩

/--
Starting from a concrete topology package, select the complete topology
consumer payload and keep its package, extractor, and lifted-derivation fields
synchronized with the fixed-target low-homotopy endpoint.  This is the
package-layer entry point for final-certificate code that needs a named
consumer object and the fixed singleton/two-puncture collapse route at the same
target.
-/
theorem poincare_statement_selectedTopologyConsumer_fixedTarget_lowHomotopy_of_universalFiniteExtinctionStatement_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x : M) {y : M} (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
      (consumer.topologyPackage = package) ∧
        (consumer.topologyPackageRequirement = package) ∧
        (consumer.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package) ∧
        (consumer.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package) ∧
        (consumer.liftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package) ∧
        PoincareConjectureStatement.{u} ∧
          ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
          ∃ package : ExtinctionTopologyExtractionPackage.{u},
          ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
            topologyStatement =
                extinction_topology_extraction_statement_of_topology_package
                  package ∧
              ExtinctionImpliesSphereStatement.{u} ∧
              ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
              ∃ homeomorphism : M ≃ₜ ThreeSphere,
                Nonempty (M ≃ₜ ThreeSphere) ∧
                Nonempty.intro homeomorphism =
                    homeomorphism_of_topology_package package M extinction ∧
                ExtinctionTopologyClassificationSubobligationsPayload
                  M extinction ∧
                ExtinctionTopologySimplyConnectedRecognitionStatement
                  M extinction ∧
                ExtinctionTopologySphericalTrivialQuotientStatement
                  M extinction ∧
                ExtinctionTopologySphericalHomeomorphismLiftStatement
                  M extinction ∧
                ExtinctionTopologyHomeomorphismAssemblyStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
                Nonempty (({x}ᶜ : Set M) ≃ₜ
                  EuclideanSpace ℝ (Fin 3)) ∧
                (∃ puncture : EuclideanSpace ℝ (Fin 3),
                  Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                    ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
                ContractibleSpace ({x}ᶜ : Set M) ∧
                SimplyConnectedSpace ({x}ᶜ : Set M) ∧
                Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                  singletonBasepoint) ∧
                Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                  singletonBasepoint) ∧
                Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                  singletonBasepoint) ∧
                SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                Subsingleton
                  (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                    twoPointBasepoint) := by
  let consumer : ExtinctionTopologyCompleteConsumerPayload.{u} :=
    { topologyPackage := package
      topologyPackageRequirement := package
      topologyStatement :=
        extinction_topology_extraction_statement_of_topology_package
          package
      topologyStatement_eq := rfl
      extinctionImpliesSphere :=
        extinction_implies_sphere_of_topology_package package
      liftedHomeomorphismDerivation :=
        topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
          package
      derivationPunctureFamily :=
        topology_package_extraction_derivation_and_puncture_payload_family
          package }
  have endpoint :
      PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        ∃ package : ExtinctionTopologyExtractionPackage.{u},
        ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
          topologyStatement =
              extinction_topology_extraction_statement_of_topology_package
                package ∧
            ExtinctionImpliesSphereStatement.{u} ∧
            ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
            ∃ homeomorphism : M ≃ₜ ThreeSphere,
              Nonempty (M ≃ₜ ThreeSphere) ∧
              Nonempty.intro homeomorphism =
                  homeomorphism_of_topology_package package M extinction ∧
              ExtinctionTopologyClassificationSubobligationsPayload
                M extinction ∧
              ExtinctionTopologySimplyConnectedRecognitionStatement
                M extinction ∧
              ExtinctionTopologySphericalTrivialQuotientStatement
                M extinction ∧
              ExtinctionTopologySphericalHomeomorphismLiftStatement
                M extinction ∧
              ExtinctionTopologyHomeomorphismAssemblyStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              ExtinctionTopologyHomeomorphismDerivationStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
              Nonempty (({x}ᶜ : Set M) ≃ₜ
                EuclideanSpace ℝ (Fin 3)) ∧
              (∃ puncture : EuclideanSpace ℝ (Fin 3),
                Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
              ContractibleSpace ({x}ᶜ : Set M) ∧
              SimplyConnectedSpace ({x}ᶜ : Set M) ∧
              Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
              Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                singletonBasepoint) ∧
              Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                singletonBasepoint) ∧
              Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                singletonBasepoint) ∧
              SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
              Subsingleton
                (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                  twoPointBasepoint) :=
    poincare_statement_recognition_fixedTarget_lowHomotopy_and_euclideanPunctureModels_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
      finiteExtinction ⟨consumer⟩ M extinction x hyx singletonBasepoint
      twoPointBasepoint
  exact
    ⟨ consumer
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , endpoint
    ⟩

/--
The concrete topology package also selects a named complete topology consumer for
the full puncture-family endpoint: every singleton complement receives its
Euclidean model, contractibility, simple connectedness, and low-homotopy
collapse at every basepoint, and every two-point complement receives its
punctured-Euclidean model and fundamental-group collapse.  The selected
consumer's package, extraction statement, and lifted-derivation fields remain
definitionally synchronized with the input package.
-/
theorem poincare_statement_selectedTopologyConsumer_punctureFamily_and_lowHomotopy_of_universalFiniteExtinctionStatement_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
      (consumer.topologyPackage = package) ∧
        (consumer.topologyPackageRequirement = package) ∧
        (consumer.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package) ∧
        (consumer.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package) ∧
        (consumer.liftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package) ∧
        PoincareConjectureStatement.{u} ∧
          ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
          ∃ package : ExtinctionTopologyExtractionPackage.{u},
          ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
            topologyStatement =
                extinction_topology_extraction_statement_of_topology_package
                  package ∧
              ExtinctionImpliesSphereStatement.{u} ∧
              ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
              ∃ homeomorphism : M ≃ₜ ThreeSphere,
                Nonempty (M ≃ₜ ThreeSphere) ∧
                Nonempty.intro homeomorphism =
                    homeomorphism_of_topology_package package M extinction ∧
                ExtinctionTopologyClassificationSubobligationsPayload
                  M extinction ∧
                ExtinctionTopologySimplyConnectedRecognitionStatement
                  M extinction ∧
                ExtinctionTopologySphericalTrivialQuotientStatement
                  M extinction ∧
                ExtinctionTopologySphericalHomeomorphismLiftStatement
                  M extinction ∧
                ExtinctionTopologyHomeomorphismAssemblyStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
                (∀ x : M,
                  Nonempty (({x}ᶜ : Set M) ≃ₜ
                    EuclideanSpace ℝ (Fin 3)) ∧
                  ContractibleSpace ({x}ᶜ : Set M) ∧
                  SimplyConnectedSpace ({x}ᶜ : Set M) ∧
                  ∀ basepoint : ({x}ᶜ : Set M),
                    Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                    Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                      basepoint) ∧
                    Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                      basepoint) ∧
                    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                      basepoint)) ∧
                (∀ {x y : M} (_hyx : y ≠ x),
                  (∃ puncture : EuclideanSpace ℝ (Fin 3),
                    Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                      ({puncture}ᶜ :
                        Set (EuclideanSpace ℝ (Fin 3))))) ∧
                  ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                    Subsingleton
                      (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                        basepoint)) := by
  let consumer : ExtinctionTopologyCompleteConsumerPayload.{u} :=
    { topologyPackage := package
      topologyPackageRequirement := package
      topologyStatement :=
        extinction_topology_extraction_statement_of_topology_package
          package
      topologyStatement_eq := rfl
      extinctionImpliesSphere :=
        extinction_implies_sphere_of_topology_package package
      liftedHomeomorphismDerivation :=
        topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
          package
      derivationPunctureFamily :=
        topology_package_extraction_derivation_and_puncture_payload_family
          package }
  have endpoint :
      PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        ∃ package : ExtinctionTopologyExtractionPackage.{u},
        ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
          topologyStatement =
              extinction_topology_extraction_statement_of_topology_package
                package ∧
            ExtinctionImpliesSphereStatement.{u} ∧
            ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
            ∃ homeomorphism : M ≃ₜ ThreeSphere,
              Nonempty (M ≃ₜ ThreeSphere) ∧
              Nonempty.intro homeomorphism =
                  homeomorphism_of_topology_package package M extinction ∧
              ExtinctionTopologyClassificationSubobligationsPayload
                M extinction ∧
              ExtinctionTopologySimplyConnectedRecognitionStatement
                M extinction ∧
              ExtinctionTopologySphericalTrivialQuotientStatement
                M extinction ∧
              ExtinctionTopologySphericalHomeomorphismLiftStatement
                M extinction ∧
              ExtinctionTopologyHomeomorphismAssemblyStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              ExtinctionTopologyHomeomorphismDerivationStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
              (∀ x : M,
                Nonempty (({x}ᶜ : Set M) ≃ₜ
                  EuclideanSpace ℝ (Fin 3)) ∧
                ContractibleSpace ({x}ᶜ : Set M) ∧
                SimplyConnectedSpace ({x}ᶜ : Set M) ∧
                ∀ basepoint : ({x}ᶜ : Set M),
                  Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                  Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                    basepoint) ∧
                  Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                    basepoint) ∧
                  Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                    basepoint)) ∧
              (∀ {x y : M} (_hyx : y ≠ x),
                (∃ puncture : EuclideanSpace ℝ (Fin 3),
                  Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                    ({puncture}ᶜ :
                      Set (EuclideanSpace ℝ (Fin 3))))) ∧
                ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                  SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  Subsingleton
                    (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                      basepoint)) :=
    poincare_statement_recognition_fixedTarget_punctureFamily_and_lowHomotopy_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
      finiteExtinction ⟨consumer⟩ M extinction
  exact
    ⟨ consumer
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , endpoint
    ⟩

/--
The same selected complete topology consumer can serve both the all-puncture
family endpoint and concrete fixed singleton/two-point low-homotopy consumers.
This keeps the package-selected consumer fields, the one-point recognition
route, the full puncture family, and the fixed basepoint consequences
synchronized for final-certificate code that needs both shapes at once.
-/
theorem poincare_statement_selectedTopologyConsumer_punctureFamily_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
      (consumer.topologyPackage = package) ∧
        (consumer.topologyPackageRequirement = package) ∧
        (consumer.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package) ∧
        (consumer.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package) ∧
        (consumer.liftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package) ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ x : M,
          Nonempty (({x}ᶜ : Set M) ≃ₜ
            EuclideanSpace ℝ (Fin 3)) ∧
          ContractibleSpace ({x}ᶜ : Set M) ∧
          SimplyConnectedSpace ({x}ᶜ : Set M) ∧
          ∀ basepoint : ({x}ᶜ : Set M),
            Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
              basepoint)) ∧
        (∀ {x y : M} (_hyx : y ≠ x),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ :
                Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                basepoint)) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let consumer : ExtinctionTopologyCompleteConsumerPayload.{u} :=
    { topologyPackage := package
      topologyPackageRequirement := package
      topologyStatement :=
        extinction_topology_extraction_statement_of_topology_package
          package
      topologyStatement_eq := rfl
      extinctionImpliesSphere :=
        extinction_implies_sphere_of_topology_package package
      liftedHomeomorphismDerivation :=
        topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
          package
      derivationPunctureFamily :=
        topology_package_extraction_derivation_and_puncture_payload_family
          package }
  have endpoint :
      PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        ∃ package : ExtinctionTopologyExtractionPackage.{u},
        ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
          topologyStatement =
              extinction_topology_extraction_statement_of_topology_package
                package ∧
            ExtinctionImpliesSphereStatement.{u} ∧
            ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
            ∃ homeomorphism : M ≃ₜ ThreeSphere,
              Nonempty (M ≃ₜ ThreeSphere) ∧
              Nonempty.intro homeomorphism =
                  homeomorphism_of_topology_package package M extinction ∧
              ExtinctionTopologyClassificationSubobligationsPayload
                M extinction ∧
              ExtinctionTopologySimplyConnectedRecognitionStatement
                M extinction ∧
              ExtinctionTopologySphericalTrivialQuotientStatement
                M extinction ∧
              ExtinctionTopologySphericalHomeomorphismLiftStatement
                M extinction ∧
              ExtinctionTopologyHomeomorphismAssemblyStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              ExtinctionTopologyHomeomorphismDerivationStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                M extinction (Nonempty.intro homeomorphism) ∧
              Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
              (∀ x : M,
                Nonempty (({x}ᶜ : Set M) ≃ₜ
                  EuclideanSpace ℝ (Fin 3)) ∧
                ContractibleSpace ({x}ᶜ : Set M) ∧
                SimplyConnectedSpace ({x}ᶜ : Set M) ∧
                ∀ basepoint : ({x}ᶜ : Set M),
                  Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                  Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                    basepoint) ∧
                  Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                    basepoint) ∧
                  Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                    basepoint)) ∧
              (∀ {x y : M} (_hyx : y ≠ x),
                (∃ puncture : EuclideanSpace ℝ (Fin 3),
                  Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                    ({puncture}ᶜ :
                      Set (EuclideanSpace ℝ (Fin 3))))) ∧
                ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                  SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                  Subsingleton
                    (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                      basepoint)) :=
    poincare_statement_recognition_fixedTarget_punctureFamily_and_lowHomotopy_of_universalFiniteExtinctionStatement_and_extinctionTopology_completeConsumerPayload
      finiteExtinction ⟨consumer⟩ M extinction
  rcases endpoint with
    ⟨poincareStatement, recognition, package', topologyStatement,
      hTopologyStatement, extinctionImpliesSphere, liftedDerivation,
      homeomorphism, hHomeomorphism, hHomeomorphismEq,
      classification, simplyConnectedRecognition, trivialQuotient,
      homeomorphismLift, homeomorphismAssembly, homeomorphismDerivation,
      liftedHomeomorphismDerivation, onePoint, singletonFamily,
      twoPointFamily⟩
  rcases singletonFamily x with
    ⟨singletonModel, singletonContractible, singletonSimplyConnected,
      singletonLowHomotopy⟩
  rcases singletonLowHomotopy singletonBasepoint with
    ⟨singletonZeroth, singletonPi0, singletonPi1, singletonHomotopyPi1⟩
  rcases twoPointFamily hyx with ⟨twoPointModel, twoPointLowHomotopy⟩
  rcases twoPointLowHomotopy twoPointBasepoint with
    ⟨twoPointSimplyConnected, twoPointFundamentalGroup⟩
  exact
    ⟨ consumer
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , poincareStatement
    , recognition
    , onePoint
    , singletonFamily
    , @twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
The selected topology consumer can be retained together with the full
classification/lift/assembly/derivation endpoint and the concrete fixed-target
singleton/two-puncture consequences.  This gives final-certificate code one
package-synchronized entry point for the complete extraction stack and the
basepointed puncture collapses.
-/
theorem poincare_statement_selectedTopologyConsumer_fullExtraction_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
      (consumer.topologyPackage = package) ∧
        (consumer.topologyPackageRequirement = package) ∧
        (consumer.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package) ∧
        (consumer.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package) ∧
        (consumer.liftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package) ∧
        (PoincareConjectureStatement.{u} ∧
          ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
          ∃ package : ExtinctionTopologyExtractionPackage.{u},
          ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
            topologyStatement =
                extinction_topology_extraction_statement_of_topology_package
                  package ∧
              ExtinctionImpliesSphereStatement.{u} ∧
              ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
              ∃ homeomorphism : M ≃ₜ ThreeSphere,
                Nonempty (M ≃ₜ ThreeSphere) ∧
                Nonempty.intro homeomorphism =
                    homeomorphism_of_topology_package package M extinction ∧
                ExtinctionTopologyClassificationSubobligationsPayload
                  M extinction ∧
                ExtinctionTopologySimplyConnectedRecognitionStatement
                  M extinction ∧
                ExtinctionTopologySphericalTrivialQuotientStatement
                  M extinction ∧
                ExtinctionTopologySphericalHomeomorphismLiftStatement
                  M extinction ∧
                ExtinctionTopologyHomeomorphismAssemblyStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
                (∀ x : M,
                  Nonempty (({x}ᶜ : Set M) ≃ₜ
                    EuclideanSpace ℝ (Fin 3)) ∧
                  ContractibleSpace ({x}ᶜ : Set M) ∧
                  SimplyConnectedSpace ({x}ᶜ : Set M) ∧
                  ∀ basepoint : ({x}ᶜ : Set M),
                    Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                    Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                      basepoint) ∧
                    Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                      basepoint) ∧
                    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                      basepoint)) ∧
                (∀ {x y : M} (_hyx : y ≠ x),
                  (∃ puncture : EuclideanSpace ℝ (Fin 3),
                    Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                      ({puncture}ᶜ :
                        Set (EuclideanSpace ℝ (Fin 3))))) ∧
                  ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                    Subsingleton
                      (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                        basepoint))) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ x : M,
          Nonempty (({x}ᶜ : Set M) ≃ₜ
            EuclideanSpace ℝ (Fin 3)) ∧
          ContractibleSpace ({x}ᶜ : Set M) ∧
          SimplyConnectedSpace ({x}ᶜ : Set M) ∧
          ∀ basepoint : ({x}ᶜ : Set M),
            Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
              basepoint)) ∧
        (∀ {x y : M} (_hyx : y ≠ x),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ :
                Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                basepoint)) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  rcases
    poincare_statement_selectedTopologyConsumer_punctureFamily_and_lowHomotopy_of_universalFiniteExtinctionStatement_and_topologyPackage
      finiteExtinction package M extinction with
    ⟨ consumer
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , endpoint
    ⟩
  rcases
    poincare_statement_selectedTopologyConsumer_punctureFamily_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage
      finiteExtinction package M extinction x y hyx singletonBasepoint
      twoPointBasepoint with
    ⟨ _fixedConsumer
    , _fixedTopologyPackage
    , _fixedTopologyPackageRequirement
    , _fixedTopologyStatement
    , _fixedExtinctionImpliesSphere
    , _fixedLiftedDerivation
    , _poincareStatement
    , _recognition
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  exact
    ⟨ consumer
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , endpoint
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
The package-layer topology requirement gives the same selected-consumer
full-extraction and fixed-target puncture-collapse endpoint as a concrete
topology extraction package.  This is the final-certificate-facing route from
`DependencyPackageLayer.topologyPackage`: it keeps the selected topology
consumer synchronized with the package extractor, the full recognition and
lifted-homeomorphism derivation stack, the all-singleton/all-two-point
puncture-family transport, and the supplied singleton/two-point basepoint
low-homotopy consequences.
-/
theorem poincare_statement_selectedTopologyConsumer_packageLayer_fullExtraction_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
      (consumer.topologyPackage = package) ∧
        (consumer.topologyPackageRequirement = package) ∧
        (consumer.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package) ∧
        (consumer.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package) ∧
        (consumer.liftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package) ∧
        (PoincareConjectureStatement.{u} ∧
          ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
          ∃ package : ExtinctionTopologyExtractionPackage.{u},
          ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
            topologyStatement =
                extinction_topology_extraction_statement_of_topology_package
                  package ∧
              ExtinctionImpliesSphereStatement.{u} ∧
              ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} ∧
              ∃ homeomorphism : M ≃ₜ ThreeSphere,
                Nonempty (M ≃ₜ ThreeSphere) ∧
                Nonempty.intro homeomorphism =
                    homeomorphism_of_topology_package package M extinction ∧
                ExtinctionTopologyClassificationSubobligationsPayload
                  M extinction ∧
                ExtinctionTopologySimplyConnectedRecognitionStatement
                  M extinction ∧
                ExtinctionTopologySphericalTrivialQuotientStatement
                  M extinction ∧
                ExtinctionTopologySphericalHomeomorphismLiftStatement
                  M extinction ∧
                ExtinctionTopologyHomeomorphismAssemblyStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                ExtinctionTopologyLiftedHomeomorphismDerivationStatement
                  M extinction (Nonempty.intro homeomorphism) ∧
                Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
                (∀ x : M,
                  Nonempty (({x}ᶜ : Set M) ≃ₜ
                    EuclideanSpace ℝ (Fin 3)) ∧
                  ContractibleSpace ({x}ᶜ : Set M) ∧
                  SimplyConnectedSpace ({x}ᶜ : Set M) ∧
                  ∀ basepoint : ({x}ᶜ : Set M),
                    Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
                    Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
                      basepoint) ∧
                    Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
                      basepoint) ∧
                    Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
                      basepoint)) ∧
                (∀ {x y : M} (_hyx : y ≠ x),
                  (∃ puncture : EuclideanSpace ℝ (Fin 3),
                    Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
                      ({puncture}ᶜ :
                        Set (EuclideanSpace ℝ (Fin 3))))) ∧
                  ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
                    SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
                    Subsingleton
                      (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                        basepoint))) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ x : M,
          Nonempty (({x}ᶜ : Set M) ≃ₜ
            EuclideanSpace ℝ (Fin 3)) ∧
          ContractibleSpace ({x}ᶜ : Set M) ∧
          SimplyConnectedSpace ({x}ᶜ : Set M) ∧
          ∀ basepoint : ({x}ᶜ : Set M),
            Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
              basepoint)) ∧
        (∀ {x y : M} (_hyx : y ≠ x),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ :
                Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ∀ basepoint : (({x} ∪ {y})ᶜ : Set M),
            SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
                basepoint)) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  exact
    poincare_statement_selectedTopologyConsumer_fullExtraction_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage
      finiteExtinction package M extinction x y hyx singletonBasepoint
      twoPointBasepoint

/--
Package-layer concrete-homeomorphism endpoint for final-certificate consumers.
It opens the package-layer full-extraction route far enough to expose the
selected complete topology consumer, the concrete `ThreeSphere` homeomorphism
and derivation statement, the public Poincare/one-point recognition statements,
and the fixed singleton/two-puncture low-homotopy consequences at the supplied
basepoints.
-/
theorem poincare_statement_packageLayer_concreteHomeomorphism_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ package' : ExtinctionTopologyExtractionPackage.{u},
    ∃ topologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package' ∧
        Nonempty.intro homeomorphism =
          homeomorphism_of_topology_package package' M extinction ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction (Nonempty.intro homeomorphism) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_selectedTopologyConsumer_packageLayer_fullExtraction_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , hTopologyPackage
    , hTopologyPackageRequirement
    , _hTopologyStatement
    , _hExtinctionImpliesSphere
    , _hLiftedDerivation
    , endpoint
    , onePoint
    , _singletonFamily
    , _twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rcases endpoint with
    ⟨ poincareStatement
    , recognitionStatement
    , package'
    , topologyStatement
    , hTopologyStatement
    , _extinctionImpliesSphere
    , _liftedHomeomorphismDerivation
    , homeomorphism
    , _nonemptyHomeomorphism
    , hHomeomorphism
    , _classification
    , _simplyConnectedRecognition
    , _trivialQuotient
    , _lift
    , _assembly
    , derivation
    , _liftedDerivation
    , _onePointFamily
    , _singletonFamilyEndpoint
    , _twoPointFamilyEndpoint
    ⟩
  exact
    ⟨ consumer
    , package'
    , topologyStatement
    , homeomorphism
    , hTopologyPackage
    , hTopologyPackageRequirement
    , poincareStatement
    , recognitionStatement
    , hTopologyStatement
    , hHomeomorphism
    , derivation
    , onePoint
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
Package-layer concrete-homeomorphism endpoint with the selected consumer fields
opened explicitly.  This keeps the concrete topology statement, extinction
extraction statement, lifted-homeomorphism derivation route, concrete
`ThreeSphere` homeomorphism, and fixed singleton/two-puncture collapse
instances synchronized with the same package-layer topology requirement.
-/
theorem poincare_statement_packageLayer_selectedConsumerFields_concreteHomeomorphism_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ selectedTopologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ selectedExtinctionImpliesSphere :
      ExtinctionImpliesSphereStatement.{u},
    ∃ selectedLiftedHomeomorphismDerivation :
      ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u},
    ∃ endpointPackage : ExtinctionTopologyExtractionPackage.{u},
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        consumer.topologyStatement = selectedTopologyStatement ∧
        selectedTopologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        consumer.extinctionImpliesSphere =
          selectedExtinctionImpliesSphere ∧
        selectedExtinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package ∧
        consumer.liftedHomeomorphismDerivation =
          selectedLiftedHomeomorphismDerivation ∧
        selectedLiftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        Nonempty.intro homeomorphism =
          homeomorphism_of_topology_package endpointPackage M extinction ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction (Nonempty.intro homeomorphism) ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_selectedTopologyConsumer_packageLayer_fullExtraction_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , endpoint
    , onePoint
    , _singletonFamily
    , _twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rcases endpoint with
    ⟨ poincareStatement
    , recognitionStatement
    , endpointPackage
    , _endpointTopologyStatement
    , _hEndpointTopologyStatement
    , _endpointExtinctionImpliesSphere
    , _endpointLiftedHomeomorphismDerivation
    , homeomorphism
    , _nonemptyHomeomorphism
    , hHomeomorphism
    , _classification
    , _simplyConnectedRecognition
    , _trivialQuotient
    , _lift
    , _assembly
    , derivation
    , _liftedDerivation
    , _onePointFamily
    , _singletonFamilyEndpoint
    , _twoPointFamilyEndpoint
    ⟩
  exact
    ⟨ consumer
    , consumer.topologyStatement
    , consumer.extinctionImpliesSphere
    , consumer.liftedHomeomorphismDerivation
    , endpointPackage
    , homeomorphism
    , hTopologyPackage
    , hTopologyPackageRequirement
    , rfl
    , hTopologyStatement
    , rfl
    , hExtinctionImpliesSphere
    , rfl
    , hLiftedDerivation
    , poincareStatement
    , recognitionStatement
    , hHomeomorphism
    , derivation
    , onePoint
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
Package-layer concrete-homeomorphism endpoint centered on the actual topology
package selected from `DependencyPackageLayer.topologyPackage`.  Unlike the
generic full-extraction endpoint, this route identifies the concrete
`ThreeSphere` homeomorphism with `homeomorphism_of_topology_package package`
itself, while retaining the selected consumer fields and the fixed
singleton/two-puncture collapse instances needed by final assembly.
-/
theorem poincare_statement_packageLayer_selectedConsumerFields_packageHomeomorphism_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ selectedTopologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ selectedExtinctionImpliesSphere :
      ExtinctionImpliesSphereStatement.{u},
    ∃ selectedLiftedHomeomorphismDerivation :
      ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u},
    ∃ packageHomeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        consumer.topologyStatement = selectedTopologyStatement ∧
        selectedTopologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        consumer.extinctionImpliesSphere =
          selectedExtinctionImpliesSphere ∧
        selectedExtinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package ∧
        consumer.liftedHomeomorphismDerivation =
          selectedLiftedHomeomorphismDerivation ∧
        selectedLiftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package ∧
        packageHomeomorphism =
          homeomorphism_of_topology_package package M extinction ∧
        packageHomeomorphism = Nonempty.intro homeomorphism ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction packageHomeomorphism ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_selectedTopologyConsumer_packageLayer_fullExtraction_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , endpoint
    , onePoint
    , _singletonFamily
    , _twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rcases endpoint with
    ⟨ poincareStatement
    , recognitionStatement
    , _endpointPackage
    , _endpointTopologyStatement
    , _hEndpointTopologyStatement
    , _endpointExtinctionImpliesSphere
    , _endpointLiftedHomeomorphismDerivation
    , _endpointHomeomorphism
    , _nonemptyHomeomorphism
    , _hHomeomorphism
    , _classification
    , _simplyConnectedRecognition
    , _trivialQuotient
    , _lift
    , _assembly
    , _derivation
    , _liftedDerivation
    , _onePointFamily
    , _singletonFamilyEndpoint
    , _twoPointFamilyEndpoint
    ⟩
  rcases hPackageHomeomorphism :
      homeomorphism_of_topology_package package M extinction with
    ⟨homeomorphism⟩
  refine
    ⟨ consumer
    , consumer.topologyStatement
    , consumer.extinctionImpliesSphere
    , consumer.liftedHomeomorphismDerivation
    , Nonempty.intro homeomorphism
    , homeomorphism
    , hTopologyPackage
    , hTopologyPackageRequirement
    , rfl
    , hTopologyStatement
    , rfl
    , hExtinctionImpliesSphere
    , rfl
    , hLiftedDerivation
    , hPackageHomeomorphism.symm
    , rfl
    , ?_
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rw [← hPackageHomeomorphism]
  exact topology_homeomorphism_derivation_statement_of_topology_package
    package M extinction

/--
Opened model-witness form of the package-layer topology-recognition endpoint.
Starting from the same selected topology package, this route names the package
homeomorphism, a concrete `ThreeSphere` homeomorphism, the induced one-point
model, the singleton-complement Euclidean model, and the two-puncture Euclidean
puncture model while retaining the fixed low-homotopy collapse instances.
-/
theorem poincare_statement_packageLayer_openedPackageHomeomorphism_onePoint_and_punctureModels_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ selectedTopologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ selectedExtinctionImpliesSphere :
      ExtinctionImpliesSphereStatement.{u},
    ∃ selectedLiftedHomeomorphismDerivation :
      ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u},
    ∃ packageHomeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
    ∃ _onePointModel :
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))),
    ∃ _singletonModel :
      Nonempty (({x}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 3)),
    ∃ twoPointPuncture : EuclideanSpace ℝ (Fin 3),
    ∃ _twoPointModel :
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({twoPointPuncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        consumer.topologyStatement = selectedTopologyStatement ∧
        selectedTopologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        consumer.extinctionImpliesSphere =
          selectedExtinctionImpliesSphere ∧
        selectedExtinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package ∧
        consumer.liftedHomeomorphismDerivation =
          selectedLiftedHomeomorphismDerivation ∧
        selectedLiftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package ∧
        packageHomeomorphism =
          homeomorphism_of_topology_package package M extinction ∧
        packageHomeomorphism = Nonempty.intro homeomorphism ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction packageHomeomorphism ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_packageLayer_selectedConsumerFields_packageHomeomorphism_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , selectedTopologyStatement
    , selectedExtinctionImpliesSphere
    , selectedLiftedHomeomorphismDerivation
    , packageHomeomorphism
    , homeomorphism
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hSelectedTopologyStatement
    , hExtinctionImpliesSphere
    , hSelectedExtinctionImpliesSphere
    , hLiftedHomeomorphismDerivation
    , hSelectedLiftedHomeomorphismDerivation
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , onePointModel
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rcases twoPointModel with ⟨twoPointPuncture, twoPointModel⟩
  exact
    ⟨ consumer
    , selectedTopologyStatement
    , selectedExtinctionImpliesSphere
    , selectedLiftedHomeomorphismDerivation
    , packageHomeomorphism
    , homeomorphism
    , onePointModel
    , singletonModel
    , twoPointPuncture
    , twoPointModel
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hSelectedTopologyStatement
    , hExtinctionImpliesSphere
    , hSelectedExtinctionImpliesSphere
    , hLiftedHomeomorphismDerivation
    , hSelectedLiftedHomeomorphismDerivation
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
Package-layer topology recognition can keep the package-selected
`ThreeSphere` homeomorphism and its derivation synchronized with both shapes
of puncture transport: the all-singleton/all-two-point families and the
supplied fixed basepoint instances.  This is the family-strengthened form of
the opened package-homeomorphism endpoint.
-/
theorem poincare_statement_packageLayer_packageHomeomorphism_punctureFamily_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ packageHomeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        consumer.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        consumer.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package ∧
        consumer.liftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package ∧
        packageHomeomorphism =
          homeomorphism_of_topology_package package M extinction ∧
        packageHomeomorphism = Nonempty.intro homeomorphism ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction packageHomeomorphism ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ z : M,
          Nonempty (({z}ᶜ : Set M) ≃ₜ
            EuclideanSpace ℝ (Fin 3)) ∧
          ContractibleSpace ({z}ᶜ : Set M) ∧
          SimplyConnectedSpace ({z}ᶜ : Set M) ∧
          ∀ basepoint : ({z}ᶜ : Set M),
            Subsingleton (ZerothHomotopy ({z}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (FundamentalGroup ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({z}ᶜ : Set M)
              basepoint)) ∧
        (∀ {a b : M} (_hba : b ≠ a),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({a} ∪ {b})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ :
                Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ∀ basepoint : (({a} ∪ {b})ᶜ : Set M),
            SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({a} ∪ {b})ᶜ : Set M)
                basepoint)) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        (∃ puncture : EuclideanSpace ℝ (Fin 3),
          Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_selectedTopologyConsumer_packageLayer_fullExtraction_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , endpoint
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rcases endpoint with
    ⟨poincareStatement, recognitionStatement, _package,
      _topologyStatement, _hTopologyStatement, _extinctionImpliesSphere,
      _liftedDerivation, _homeomorphism, _nonemptyHomeomorphism,
      _hHomeomorphism, _classification, _simplyConnectedRecognition,
      _trivialQuotient, _homeomorphismLift, _homeomorphismAssembly,
      _homeomorphismDerivation, _liftedHomeomorphismDerivation,
      _onePointFamily, _singletonFamilyEndpoint, _twoPointFamilyEndpoint⟩
  rcases hPackageHomeomorphism :
      homeomorphism_of_topology_package package M extinction with
    ⟨homeomorphism⟩
  refine
    ⟨ consumer
    , Nonempty.intro homeomorphism
    , homeomorphism
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , hPackageHomeomorphism.symm
    , rfl
    , ?_
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonFamily
    , @twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  · rw [← hPackageHomeomorphism]
    exact topology_homeomorphism_derivation_statement_of_topology_package
      package M extinction

/--
Opened family-strengthened package-homeomorphism endpoint.  This keeps the
selected topology consumer, package-level `ThreeSphere` homeomorphism,
all-singleton/all-two-point puncture families, and fixed low-homotopy
instances while also naming the fixed two-puncture Euclidean puncture/model.
Downstream topology-recognition consumers can use the fixed punctured
Euclidean chart directly without reopening the bundled existential from the
family endpoint.
-/
theorem poincare_statement_packageLayer_packageHomeomorphism_openedPunctureFamily_and_fixedTarget_models_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ packageHomeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
    ∃ twoPointPuncture : EuclideanSpace ℝ (Fin 3),
    ∃ _twoPointModel :
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({twoPointPuncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        packageHomeomorphism =
          homeomorphism_of_topology_package package M extinction ∧
        packageHomeomorphism = Nonempty.intro homeomorphism ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction packageHomeomorphism ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ z : M,
          Nonempty (({z}ᶜ : Set M) ≃ₜ
            EuclideanSpace ℝ (Fin 3)) ∧
          ContractibleSpace ({z}ᶜ : Set M) ∧
          SimplyConnectedSpace ({z}ᶜ : Set M) ∧
          ∀ basepoint : ({z}ᶜ : Set M),
            Subsingleton (ZerothHomotopy ({z}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (FundamentalGroup ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({z}ᶜ : Set M)
              basepoint)) ∧
        (∀ {a b : M} (_hba : b ≠ a),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({a} ∪ {b})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ :
                Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ∀ basepoint : (({a} ∪ {b})ᶜ : Set M),
            SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({a} ∪ {b})ᶜ : Set M)
                basepoint)) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_packageLayer_packageHomeomorphism_punctureFamily_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , packageHomeomorphism
    , homeomorphism
    , hTopologyPackage
    , hTopologyPackageRequirement
    , _hTopologyStatement
    , _hExtinctionImpliesSphere
    , _hLiftedDerivation
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rcases twoPointModel with ⟨twoPointPuncture, twoPointModel⟩
  exact
    ⟨ consumer
    , packageHomeomorphism
    , homeomorphism
    , twoPointPuncture
    , twoPointModel
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
Opened package-homeomorphism endpoint retaining the selected topology package
field equalities together with the fixed two-puncture Euclidean model.  This is
the final-certificate-facing form when downstream consumers need both the
package statement/derivation fields and the opened fixed puncture chart.
-/
theorem poincare_statement_packageLayer_packageHomeomorphism_openedPunctureFamily_packageFields_and_fixedTarget_models_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ packageHomeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
    ∃ twoPointPuncture : EuclideanSpace ℝ (Fin 3),
    ∃ _twoPointModel :
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({twoPointPuncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        consumer.topologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        consumer.extinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package ∧
        consumer.liftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package ∧
        packageHomeomorphism =
          homeomorphism_of_topology_package package M extinction ∧
        packageHomeomorphism = Nonempty.intro homeomorphism ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction packageHomeomorphism ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ z : M,
          Nonempty (({z}ᶜ : Set M) ≃ₜ
            EuclideanSpace ℝ (Fin 3)) ∧
          ContractibleSpace ({z}ᶜ : Set M) ∧
          SimplyConnectedSpace ({z}ᶜ : Set M) ∧
          ∀ basepoint : ({z}ᶜ : Set M),
            Subsingleton (ZerothHomotopy ({z}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (FundamentalGroup ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({z}ᶜ : Set M)
              basepoint)) ∧
        (∀ {a b : M} (_hba : b ≠ a),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({a} ∪ {b})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ :
                Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ∀ basepoint : (({a} ∪ {b})ᶜ : Set M),
            SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({a} ∪ {b})ᶜ : Set M)
                basepoint)) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_packageLayer_packageHomeomorphism_punctureFamily_and_fixedTarget_instances_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , packageHomeomorphism
    , homeomorphism
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointModel
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  rcases twoPointModel with ⟨twoPointPuncture, twoPointModel⟩
  exact
    ⟨ consumer
    , packageHomeomorphism
    , homeomorphism
    , twoPointPuncture
    , twoPointModel
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
Opened package-field endpoint with named selected statement objects.  This
keeps the selected topology statement, extinction-implies-sphere statement,
lifted-homeomorphism derivation statement, package homeomorphism, all-puncture
families, and the fixed opened two-puncture model synchronized for downstream
final-certificate consumers that need both named package fields and the
concrete punctured-Euclidean target.
-/
theorem poincare_statement_packageLayer_namedPackageFields_openedPunctureFamily_and_fixedTarget_models_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (topologyPackage :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.topologyPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (x y : M) (hyx : y ≠ x)
    (singletonBasepoint : ({x}ᶜ : Set M))
    (twoPointBasepoint : (({x} ∪ {y})ᶜ : Set M)) :
    let package : ExtinctionTopologyExtractionPackage.{u} :=
      topologyPackage
    ∃ consumer : ExtinctionTopologyCompleteConsumerPayload.{u},
    ∃ selectedTopologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ selectedExtinctionImpliesSphere :
      ExtinctionImpliesSphereStatement.{u},
    ∃ selectedLiftedHomeomorphismDerivation :
      ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u},
    ∃ packageHomeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ homeomorphism : M ≃ₜ ThreeSphere,
    ∃ twoPointPuncture : EuclideanSpace ℝ (Fin 3),
    ∃ _twoPointModel :
      Nonempty ((({x} ∪ {y})ᶜ : Set M) ≃ₜ
        ({twoPointPuncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))),
      consumer.topologyPackage = package ∧
        consumer.topologyPackageRequirement = package ∧
        consumer.topologyStatement = selectedTopologyStatement ∧
        selectedTopologyStatement =
          extinction_topology_extraction_statement_of_topology_package
            package ∧
        consumer.extinctionImpliesSphere =
          selectedExtinctionImpliesSphere ∧
        selectedExtinctionImpliesSphere =
          extinction_implies_sphere_of_topology_package package ∧
        consumer.liftedHomeomorphismDerivation =
          selectedLiftedHomeomorphismDerivation ∧
        selectedLiftedHomeomorphismDerivation =
          topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            package ∧
        packageHomeomorphism =
          homeomorphism_of_topology_package package M extinction ∧
        packageHomeomorphism = Nonempty.intro homeomorphism ∧
        ExtinctionTopologyHomeomorphismDerivationStatement
          M extinction packageHomeomorphism ∧
        PoincareConjectureStatement.{u} ∧
        ExtinctionOnePointThreeSpaceRecognitionStatement.{u} ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        (∀ z : M,
          Nonempty (({z}ᶜ : Set M) ≃ₜ
            EuclideanSpace ℝ (Fin 3)) ∧
          ContractibleSpace ({z}ᶜ : Set M) ∧
          SimplyConnectedSpace ({z}ᶜ : Set M) ∧
          ∀ basepoint : ({z}ᶜ : Set M),
            Subsingleton (ZerothHomotopy ({z}ᶜ : Set M)) ∧
            Subsingleton (HomotopyGroup.Pi 0 ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (FundamentalGroup ({z}ᶜ : Set M)
              basepoint) ∧
            Subsingleton (HomotopyGroup.Pi 1 ({z}ᶜ : Set M)
              basepoint)) ∧
        (∀ {a b : M} (_hba : b ≠ a),
          (∃ puncture : EuclideanSpace ℝ (Fin 3),
            Nonempty ((({a} ∪ {b})ᶜ : Set M) ≃ₜ
              ({puncture}ᶜ :
                Set (EuclideanSpace ℝ (Fin 3))))) ∧
          ∀ basepoint : (({a} ∪ {b})ᶜ : Set M),
            SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set M) ∧
            Subsingleton
              (FundamentalGroup (({a} ∪ {b})ᶜ : Set M)
                basepoint)) ∧
        Nonempty (({x}ᶜ : Set M) ≃ₜ
          EuclideanSpace ℝ (Fin 3)) ∧
        ContractibleSpace ({x}ᶜ : Set M) ∧
        SimplyConnectedSpace ({x}ᶜ : Set M) ∧
        Subsingleton (ZerothHomotopy ({x}ᶜ : Set M)) ∧
        Subsingleton (HomotopyGroup.Pi 0 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (FundamentalGroup ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        Subsingleton (HomotopyGroup.Pi 1 ({x}ᶜ : Set M)
          singletonBasepoint) ∧
        SimplyConnectedSpace (({x} ∪ {y})ᶜ : Set M) ∧
        Subsingleton
          (FundamentalGroup (({x} ∪ {y})ᶜ : Set M)
            twoPointBasepoint) := by
  let package : ExtinctionTopologyExtractionPackage.{u} :=
    topologyPackage
  rcases
    poincare_statement_packageLayer_packageHomeomorphism_openedPunctureFamily_packageFields_and_fixedTarget_models_of_universalFiniteExtinctionStatement_and_topologyPackage_requirement
      finiteExtinction topologyPackage M extinction x y hyx
      singletonBasepoint twoPointBasepoint with
    ⟨ consumer
    , packageHomeomorphism
    , homeomorphism
    , twoPointPuncture
    , twoPointModel
    , hTopologyPackage
    , hTopologyPackageRequirement
    , hTopologyStatement
    , hExtinctionImpliesSphere
    , hLiftedDerivation
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩
  exact
    ⟨ consumer
    , consumer.topologyStatement
    , consumer.extinctionImpliesSphere
    , consumer.liftedHomeomorphismDerivation
    , packageHomeomorphism
    , homeomorphism
    , twoPointPuncture
    , twoPointModel
    , hTopologyPackage
    , hTopologyPackageRequirement
    , rfl
    , hTopologyStatement
    , rfl
    , hExtinctionImpliesSphere
    , rfl
    , hLiftedDerivation
    , hPackageHomeomorphism
    , hConcreteHomeomorphism
    , derivation
    , poincareStatement
    , recognitionStatement
    , onePoint
    , singletonFamily
    , twoPointFamily
    , singletonModel
    , singletonContractible
    , singletonSimplyConnected
    , singletonZeroth
    , singletonPi0
    , singletonPi1
    , singletonHomotopyPi1
    , twoPointSimplyConnected
    , twoPointFundamentalGroup
    ⟩

/--
Named production input for the first topology-package field: each finite
extinction witness supplies explicit certified decomposition data.
-/
def ExtinctionTopologyDecompositionDataStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      Nonempty (ExtinctionTopologyDecompositionData M extinction)

/--
Certified finite-extinction decomposition data now constructs the first
topology-package field for that fixed extinction witness.
-/
theorem extinction_topology_decomposition_of_decomposition_data_current_interface
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decompositionData : ExtinctionTopologyDecompositionData M extinction) :
    HasExtinctionTopologyDecomposition M extinction :=
  HasExtinctionTopologyDecomposition.ofData decompositionData

/--
The data statement supplies exactly the package-level decomposition witness
family. The next topology-production field is reconstruction of the surgery
trace for the decomposition selected here.
-/
theorem extinction_topology_decomposition_statement_of_decomposition_data_current_interface
    (decompositionData : ExtinctionTopologyDecompositionDataStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionTopologyDecomposition M extinction := by
  intro M _top _t2 _charted _simple _compact extinction
  rcases decompositionData M extinction with ⟨data⟩
  exact extinction_topology_decomposition_of_decomposition_data_current_interface
    M extinction data

end Poincare
