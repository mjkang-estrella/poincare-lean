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
