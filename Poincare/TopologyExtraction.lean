/-
Typed interfaces for the topological extraction layer after finite extinction.

Finite extinction under Ricci flow with surgery is still not the final
homeomorphism statement. This module names the post-extinction topology inputs
needed to identify the manifold with the standard 3-sphere.
-/

import Poincare.RicciFlowInterface

universe u

open scoped Manifold ContDiff

namespace Poincare

/-- The standard target sphere is homeomorphic to itself. -/
theorem threeSphere_self_homeomorph :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨Homeomorph.refl ThreeSphere⟩

/--
The self-homeomorphism witness for the standard sphere is the reflexive
homeomorphism.
-/
theorem threeSphere_self_homeomorph_eq :
    threeSphere_self_homeomorph =
      ⟨Homeomorph.refl ThreeSphere⟩ := by
  apply Subsingleton.elim

/--
The topology-extraction self-homeomorphism witness agrees with the assembly
route obtained by forgetting the standard sphere's reflexive self-diffeomorphism.
-/
theorem threeSphere_self_homeomorph_self_diffeomorph_route_eq :
    threeSphere_self_homeomorph =
      threeSphere_self_homeomorph_of_self_diffeomorph := by
  apply Subsingleton.elim

/--
Homeomorphism recognition composes through an intermediate space.

This is a small proof-bearing topology lemma used by the extraction layer: once
an intermediate model has been identified with `ThreeSphere`, any manifold
homeomorphic to that model is also identified with `ThreeSphere`.
-/
theorem homeomorph_to_threeSphere_of_homeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases hMN with ⟨eMN⟩
  rcases hN with ⟨eN⟩
  exact ⟨eMN.trans eN⟩

/--
The intermediate-space transport lemma is exactly composition of the supplied
homeomorphisms.
-/
theorem homeomorph_to_threeSphere_of_homeomorph_eq
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    homeomorph_to_threeSphere_of_homeomorph hMN hN =
      (by
        rcases hMN with ⟨eMN⟩
        rcases hN with ⟨eN⟩
        exact ⟨eMN.trans eN⟩) := by
  apply Subsingleton.elim

/--
Homeomorphism recognition can also be transported along a homeomorphism whose
direction is opposite the final target direction.
-/
theorem homeomorph_to_threeSphere_of_homeomorph_source
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hNM : Nonempty (N ≃ₜ M)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases hNM with ⟨eNM⟩
  rcases hN with ⟨eN⟩
  exact ⟨eNM.symm.trans eN⟩

/--
The source-side transport lemma is exactly inverse-then-composition of the
supplied homeomorphisms.
-/
theorem homeomorph_to_threeSphere_of_homeomorph_source_eq
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hNM : Nonempty (N ≃ₜ M)) (hN : Nonempty (N ≃ₜ ThreeSphere)) :
    homeomorph_to_threeSphere_of_homeomorph_source hNM hN =
      (by
        rcases hNM with ⟨eNM⟩
        rcases hN with ⟨eN⟩
        exact ⟨eNM.symm.trans eN⟩) := by
  apply Subsingleton.elim

/--
Being homeomorphic to the standard 3-sphere is invariant under replacing the
source by a homeomorphic space.
-/
theorem homeomorph_to_threeSphere_iff_of_homeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) :
    Nonempty (M ≃ₜ ThreeSphere) ↔ Nonempty (N ≃ₜ ThreeSphere) := by
  constructor
  · intro hM
    exact homeomorph_to_threeSphere_of_homeomorph_source hMN hM
  · intro hN
    exact homeomorph_to_threeSphere_of_homeomorph hMN hN

/--
The homeomorphism-invariance equivalence is the pair of the named transport
maps in the two directions.
-/
theorem homeomorph_to_threeSphere_iff_of_homeomorph_eq
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (hMN : Nonempty (M ≃ₜ N)) :
    homeomorph_to_threeSphere_iff_of_homeomorph hMN =
      (by
        constructor
        · intro hM
          exact homeomorph_to_threeSphere_of_homeomorph_source hMN hM
        · intro hN
          exact homeomorph_to_threeSphere_of_homeomorph hMN hN) := by
  apply Subsingleton.elim

/--
Recognition can be used in the target direction after inverting a homeomorphism
from the standard sphere.
-/
theorem homeomorph_to_threeSphere_of_threeSphere_homeomorph
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (ThreeSphere ≃ₜ M)) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/--
The target-side recognition lemma is exactly inversion of the supplied
homeomorphism from the standard sphere.
-/
theorem homeomorph_to_threeSphere_of_threeSphere_homeomorph_eq
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (ThreeSphere ≃ₜ M)) :
    homeomorph_to_threeSphere_of_threeSphere_homeomorph h =
      (by
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩) := by
  apply Subsingleton.elim

/--
The same recognition data can be used in the reverse direction by inverting the
homeomorphism to the standard sphere.
-/
theorem threeSphere_homeomorph_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    Nonempty (ThreeSphere ≃ₜ M) := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/--
The reverse target-side recognition lemma is exactly inversion of the supplied
homeomorphism to the standard sphere.
-/
theorem threeSphere_homeomorph_of_homeomorph_to_threeSphere_eq
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    threeSphere_homeomorph_of_homeomorph_to_threeSphere h =
      (by
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩) := by
  apply Subsingleton.elim

/--
Being homeomorphic to the standard 3-sphere is independent of which side of the
homeomorphism the standard sphere is written on.
-/
theorem homeomorph_to_threeSphere_iff_threeSphere_homeomorph
    {M : Type u} [TopologicalSpace M] :
    Nonempty (M ≃ₜ ThreeSphere) ↔ Nonempty (ThreeSphere ≃ₜ M) := by
  constructor
  · exact threeSphere_homeomorph_of_homeomorph_to_threeSphere
  · exact homeomorph_to_threeSphere_of_threeSphere_homeomorph

/--
The target-side homeomorphism equivalence is the pair of the named inverse
homeomorphism conversions.
-/
theorem homeomorph_to_threeSphere_iff_threeSphere_homeomorph_eq
    {M : Type u} [TopologicalSpace M] :
    (homeomorph_to_threeSphere_iff_threeSphere_homeomorph :
      Nonempty (M ≃ₜ ThreeSphere) ↔ Nonempty (ThreeSphere ≃ₜ M)) =
      (by
        constructor
        · exact threeSphere_homeomorph_of_homeomorph_to_threeSphere
        · exact homeomorph_to_threeSphere_of_threeSphere_homeomorph) := by
  apply Subsingleton.elim

/--
Interface for the decomposition information obtained from finite extinction.

This stands for the topological output of the extinction argument before the
final recognition theorem is applied.
-/
inductive HasExtinctionTopologyDecomposition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_extinction : FiniteExtinctionByRicciFlowWithSurgery M) : Prop

/--
Interface reconstructing the topological surgery trace represented by the
post-extinction decomposition.
-/
inductive HasExtinctionSurgeryTraceReconstruction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (_decomposition : HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for canceling the topological handles recorded by the surgery trace.
-/
inductive HasExtinctionSurgeryTraceHandleCancellation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_surgeryTrace :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition) : Prop

/--
Interface for classifying the topological components produced at extinction.
-/
inductive HasExtinctionComponentClassification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (_decomposition : HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for identifying discarded extinction components up to homeomorphism.
-/
inductive HasExtinctionDiscardedComponentHomeomorphismClassification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_componentClassification :
      HasExtinctionComponentClassification M extinction decomposition) : Prop

/--
Interface inventorying extinction components before prime-factor recognition.
-/
inductive HasExtinctionComponentInventory
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_componentClassification :
      HasExtinctionComponentClassification M extinction decomposition) : Prop

/--
Interface for proving that boundary components in the extinction inventory are spheres.
-/
inductive HasExtinctionComponentBoundarySphereControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (_componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification) : Prop

/--
Interface for the 3-sphere recognition/classification theorem needed after the
extinction decomposition is known.
-/
inductive HasThreeSphereRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_decomposition :
      ∀ extinction : FiniteExtinctionByRicciFlowWithSurgery M,
        HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for extracting a prime/connected-sum decomposition from the
post-extinction topology data.
-/
inductive HasExtinctionPrimeDecomposition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (_decomposition : HasExtinctionTopologyDecomposition M extinction) : Prop

/--
Interface for existence of the prime decomposition used in the extinction argument.
-/
inductive HasExtinctionPrimeDecompositionExistence
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface for the sphere-theorem input used to extract prime factors.
-/
inductive HasExtinctionSphereTheoremApplication
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface for producing embedded spheres that realize prime-decomposition cuts.
-/
inductive HasExtinctionEmbeddedSphereProduction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_sphereTheorem :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for the loop-theorem input used to control compressions in the cuts.
-/
inductive HasExtinctionLoopTheoremApplication
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_sphereTheorem :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for compatibility and uniqueness of the prime decomposition used by
the extinction classification.
-/
inductive HasExtinctionPrimeDecompositionCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface for uniqueness of the prime factors selected by the decomposition.
-/
inductive HasExtinctionPrimeFactorUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification
        primeDecomposition) : Prop

/--
Interface for the irreducibility input applied to the prime pieces produced by
finite extinction.
-/
inductive HasExtinctionIrreducibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (_primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition) : Prop

/--
Interface recognizing the irreducible prime factors arising after extinction.
-/
inductive HasExtinctionIrreducibleFactorRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for collapsing the connected-sum decomposition to the surviving prime
factor relevant to the simply connected target.
-/
inductive HasExtinctionConnectedSumCollapse
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (_irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition) : Prop

/--
Interface for the fundamental-group control used when collapsing connected sums.
-/
inductive HasExtinctionConnectedSumFundamentalGroupControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (_connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility) : Prop

/--
Interface for the van Kampen computation of the connected-sum fundamental group.
-/
inductive HasExtinctionConnectedSumVanKampenCalculation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_fundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for forcing the surviving prime factor to be simply connected.
-/
inductive HasExtinctionSimplyConnectedPrimeFactorControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_fundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for reducing the finite-extinction decomposition to spherical space
form pieces.
-/
inductive HasExtinctionSphericalSpaceFormReduction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (_connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility) : Prop

/--
Interface for the spherical-space-form classification theorem applied after
prime and connected-sum reduction.
-/
inductive HasSphericalSpaceFormClassification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for identifying the surviving pieces with spherical quotient models.
-/
inductive HasSphericalSpaceFormQuotientModel
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface for realizing a spherical space form as a free action on the sphere.
-/
inductive HasSphericalSpaceFormFreeAction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (_quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface for proving that the spherical space form universal cover is the
standard 3-sphere.
-/
inductive HasSphericalSpaceFormUniversalCover
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (_quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface identifying the quotient and universal-cover data as a covering
model of the spherical space form.
-/
inductive HasSphericalSpaceFormCoveringModel
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel) : Prop

/--
Interface for the covering projection from the universal cover to the quotient.
-/
inductive HasSphericalSpaceFormCoveringProjection
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (_coveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        universalCover) : Prop

/--
Interface for computing the fundamental group of the spherical space form
pieces arising after the extinction reduction.
-/
inductive HasSphericalSpaceFormFundamentalGroupComputation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (_sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse) : Prop

/--
Interface identifying the spherical-space-form deck group with the computed
fundamental group.
-/
inductive HasSphericalSpaceFormDeckGroupIdentification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface for proper discontinuity and freeness of the deck action.
-/
inductive HasSphericalSpaceFormDeckActionProperness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation) : Prop

/--
Interface for ruling out nontrivial deck groups/quotients using simple
connectedness of the original manifold.
-/
inductive HasSphericalSpaceFormDeckGroupTriviality
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (_fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction) : Prop

/--
Interface converting deck-group identification and triviality into a trivial
covering action.
-/
inductive HasSphericalSpaceFormDeckActionTrivialization
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (_deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction
        fundamentalGroupComputation) : Prop

/--
Interface identifying the quotient by a trivial deck action with the cover itself.
-/
inductive HasSphericalSpaceFormTrivialDeckQuotientIdentification
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction
        fundamentalGroupComputation)
    (_deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality) : Prop

/--
Interface for the simply connected reduction that rules out nontrivial
spherical space form factors.
-/
inductive HasSimplyConnectedExtinctionRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (_deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation) : Prop

/--
Interface turning the trivial deck group result into a trivial spherical
quotient.
-/
inductive HasTrivialSphericalSpaceFormQuotient
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (_deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation) : Prop

/--
Interface turning the trivial quotient statement into the final quotient
homeomorphism used by the extraction assembly.
-/
inductive HasSphericalSpaceFormTrivialQuotientHomeomorphism
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (_trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality) : Prop

/--
Interface lifting the final homeomorphism through the trivial spherical quotient.
-/
inductive HasSphericalSpaceFormHomeomorphismLift
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality)
    (_trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient) : Prop

/--
Interface assembling the topological classification outputs into the final
homeomorphism to the standard sphere.
-/
inductive HasExtinctionHomeomorphismAssembly
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (_trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (_homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop

/--
Interface certifying that the preceding topology inputs derive the projected
homeomorphism to the standard 3-sphere.
-/
inductive HasExtinctionHomeomorphismDerivation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (_homeomorphismAssembly :
      HasExtinctionHomeomorphismAssembly M extinction decomposition
        primeDecomposition irreducibility connectedSumCollapse sphericalReduction
        quotientModel fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality simplyConnectedRecognition trivialQuotient
        homeomorphism) : Prop

/--
The fixed-manifold topology extraction statement: finite extinction gives a
homeomorphism only together with the full post-extinction classification,
quotient, deck-group, trivial-quotient, assembly, and derivation chain.
-/
def ExtinctionTopologyDerivationStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop :=
  ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
  ∃ surgeryTraceReconstruction :
    HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
  ∃ _surgeryTraceHandleCancellation :
    HasExtinctionSurgeryTraceHandleCancellation
      M extinction decomposition surgeryTraceReconstruction,
  ∃ componentClassification :
    HasExtinctionComponentClassification M extinction decomposition,
  ∃ _discardedComponentHomeomorphismClassification :
    HasExtinctionDiscardedComponentHomeomorphismClassification
      M extinction decomposition componentClassification,
  ∃ componentInventory :
    HasExtinctionComponentInventory
      M extinction decomposition componentClassification,
  ∃ _componentBoundarySphereControl :
    HasExtinctionComponentBoundarySphereControl
      M extinction decomposition componentClassification componentInventory,
  ∃ primeDecomposition :
    HasExtinctionPrimeDecomposition M extinction decomposition,
  ∃ _primeDecompositionExistence :
    HasExtinctionPrimeDecompositionExistence
      M extinction decomposition primeDecomposition,
  ∃ sphereTheoremApplication :
    HasExtinctionSphereTheoremApplication
      M extinction decomposition primeDecomposition,
  ∃ _embeddedSphereProduction :
    HasExtinctionEmbeddedSphereProduction
      M extinction decomposition primeDecomposition sphereTheoremApplication,
  ∃ _loopTheoremApplication :
    HasExtinctionLoopTheoremApplication
      M extinction decomposition primeDecomposition sphereTheoremApplication,
  ∃ primeDecompositionCompatibility :
    HasExtinctionPrimeDecompositionCompatibility
      M extinction decomposition componentClassification primeDecomposition,
  ∃ _primeFactorUniqueness :
    HasExtinctionPrimeFactorUniqueness
      M extinction decomposition componentClassification primeDecomposition
      primeDecompositionCompatibility,
  ∃ irreducibility :
    HasExtinctionIrreducibility
      M extinction decomposition primeDecomposition,
  ∃ _irreducibleFactorRecognition :
    HasExtinctionIrreducibleFactorRecognition
      M extinction decomposition primeDecomposition irreducibility,
  ∃ connectedSumCollapse :
    HasExtinctionConnectedSumCollapse
      M extinction decomposition primeDecomposition irreducibility,
  ∃ connectedSumFundamentalGroupControl :
    HasExtinctionConnectedSumFundamentalGroupControl
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ _connectedSumVanKampen :
    HasExtinctionConnectedSumVanKampenCalculation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse connectedSumFundamentalGroupControl,
  ∃ _simplyConnectedPrimeFactorControl :
    HasExtinctionSimplyConnectedPrimeFactorControl
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse connectedSumFundamentalGroupControl,
  ∃ sphericalReduction :
    HasExtinctionSphericalSpaceFormReduction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ _sphericalClassification :
    HasSphericalSpaceFormClassification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ quotientModel :
    HasSphericalSpaceFormQuotientModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ _sphericalFreeAction :
    HasSphericalSpaceFormFreeAction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel,
  ∃ universalCover :
    HasSphericalSpaceFormUniversalCover
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel,
  ∃ sphericalCoveringModel :
    HasSphericalSpaceFormCoveringModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover,
  ∃ _sphericalCoveringProjection :
    HasSphericalSpaceFormCoveringProjection
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover
      sphericalCoveringModel,
  ∃ fundamentalGroupComputation :
    HasSphericalSpaceFormFundamentalGroupComputation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupIdentification :
    HasSphericalSpaceFormDeckGroupIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation,
  ∃ _deckActionProperness :
    HasSphericalSpaceFormDeckActionProperness
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification,
  ∃ deckGroupTriviality :
    HasSphericalSpaceFormDeckGroupTriviality
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation,
  ∃ deckActionTrivialization :
    HasSphericalSpaceFormDeckActionTrivialization
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
  ∃ _trivialDeckQuotientIdentification :
    HasSphericalSpaceFormTrivialDeckQuotientIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
      deckActionTrivialization,
  ∃ trivialQuotient :
    HasTrivialSphericalSpaceFormQuotient
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
  ∃ trivialQuotientHomeomorphism :
    HasSphericalSpaceFormTrivialQuotientHomeomorphism
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
      trivialQuotient,
  ∃ _sphericalHomeomorphismLift :
    HasSphericalSpaceFormHomeomorphismLift
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel universalCover
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
      trivialQuotient trivialQuotientHomeomorphism,
  ∃ simplyConnectedRecognition :
    HasSimplyConnectedExtinctionRecognition
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation
      deckGroupTriviality,
  ∃ homeomorphismAssembly :
    HasExtinctionHomeomorphismAssembly M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      quotientModel fundamentalGroupComputation deckGroupIdentification
      deckGroupTriviality simplyConnectedRecognition trivialQuotient
      homeomorphism,
    HasExtinctionHomeomorphismDerivation M extinction
      decomposition primeDecomposition irreducibility connectedSumCollapse
      sphericalReduction fundamentalGroupComputation deckGroupTriviality
      simplyConnectedRecognition quotientModel deckGroupIdentification
      trivialQuotient homeomorphism homeomorphismAssembly

/--
The fixed-manifold topology derivation statement is definitionally the full
post-extinction decomposition, trace, classification, space-form, recognition,
assembly, and derivation witness stack.
-/
theorem extinctionTopologyDerivationStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) :
    ExtinctionTopologyDerivationStatement M extinction homeomorphism =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ surgeryTraceReconstruction :
        HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
      ∃ _surgeryTraceHandleCancellation :
        HasExtinctionSurgeryTraceHandleCancellation
          M extinction decomposition surgeryTraceReconstruction,
      ∃ componentClassification :
        HasExtinctionComponentClassification M extinction decomposition,
      ∃ _discardedComponentHomeomorphismClassification :
        HasExtinctionDiscardedComponentHomeomorphismClassification
          M extinction decomposition componentClassification,
      ∃ componentInventory :
        HasExtinctionComponentInventory
          M extinction decomposition componentClassification,
      ∃ _componentBoundarySphereControl :
        HasExtinctionComponentBoundarySphereControl
          M extinction decomposition componentClassification componentInventory,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ _primeDecompositionExistence :
        HasExtinctionPrimeDecompositionExistence
          M extinction decomposition primeDecomposition,
      ∃ sphereTheoremApplication :
        HasExtinctionSphereTheoremApplication
          M extinction decomposition primeDecomposition,
      ∃ _embeddedSphereProduction :
        HasExtinctionEmbeddedSphereProduction
          M extinction decomposition primeDecomposition sphereTheoremApplication,
      ∃ _loopTheoremApplication :
        HasExtinctionLoopTheoremApplication
          M extinction decomposition primeDecomposition sphereTheoremApplication,
      ∃ primeDecompositionCompatibility :
        HasExtinctionPrimeDecompositionCompatibility
          M extinction decomposition componentClassification primeDecomposition,
      ∃ _primeFactorUniqueness :
        HasExtinctionPrimeFactorUniqueness
          M extinction decomposition componentClassification primeDecomposition
          primeDecompositionCompatibility,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ _irreducibleFactorRecognition :
        HasExtinctionIrreducibleFactorRecognition
          M extinction decomposition primeDecomposition irreducibility,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ connectedSumFundamentalGroupControl :
        HasExtinctionConnectedSumFundamentalGroupControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _connectedSumVanKampen :
        HasExtinctionConnectedSumVanKampenCalculation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse connectedSumFundamentalGroupControl,
      ∃ _simplyConnectedPrimeFactorControl :
        HasExtinctionSimplyConnectedPrimeFactorControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse connectedSumFundamentalGroupControl,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _sphericalClassification :
        HasSphericalSpaceFormClassification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ _sphericalFreeAction :
        HasSphericalSpaceFormFreeAction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ universalCover :
        HasSphericalSpaceFormUniversalCover
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ sphericalCoveringModel :
        HasSphericalSpaceFormCoveringModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover,
      ∃ _sphericalCoveringProjection :
        HasSphericalSpaceFormCoveringProjection
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover
          sphericalCoveringModel,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ _deckActionProperness :
        HasSphericalSpaceFormDeckActionProperness
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ deckActionTrivialization :
        HasSphericalSpaceFormDeckActionTrivialization
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
      ∃ _trivialDeckQuotientIdentification :
        HasSphericalSpaceFormTrivialDeckQuotientIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          deckActionTrivialization,
      ∃ trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
      ∃ trivialQuotientHomeomorphism :
        HasSphericalSpaceFormTrivialQuotientHomeomorphism
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          trivialQuotient,
      ∃ _sphericalHomeomorphismLift :
        HasSphericalSpaceFormHomeomorphismLift
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          trivialQuotient trivialQuotientHomeomorphism,
      ∃ simplyConnectedRecognition :
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality,
      ∃ homeomorphismAssembly :
        HasExtinctionHomeomorphismAssembly M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction quotientModel fundamentalGroupComputation
          deckGroupIdentification deckGroupTriviality simplyConnectedRecognition
          trivialQuotient homeomorphism,
        HasExtinctionHomeomorphismDerivation M extinction
          decomposition primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction fundamentalGroupComputation deckGroupTriviality
          simplyConnectedRecognition quotientModel deckGroupIdentification
          trivialQuotient homeomorphism homeomorphismAssembly) :=
  rfl

/--
The theorem-shaped post-extinction topology extraction input consumed by the
Poincare assembly: every finite-extinction witness yields a homeomorphism plus
the full derivation statement for that homeomorphism.
-/
def ExtinctionTopologyExtractionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
        ExtinctionTopologyDerivationStatement M extinction homeomorphism

/--
The theorem-shaped topology-extraction interface is exactly the universal
post-extinction homeomorphism plus derivation statement.
-/
theorem extinctionTopologyExtractionStatement_eq :
    ExtinctionTopologyExtractionStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
            ExtinctionTopologyDerivationStatement M extinction homeomorphism) :=
  rfl

/--
The derivation evidence corresponding to a particular theorem-shaped
finite-extinction-to-sphere extractor.

This separates the purely final homeomorphism conclusion from the longer
post-extinction topology derivation chain that explains why that conclusion was
obtained.
-/
def ExtinctionTopologyDerivationForExtractionStatement
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionTopologyDerivationStatement M extinction
        (extractSphere M extinction)

/--
The derivation evidence for a theorem-shaped extractor is exactly the universal
fixed-homeomorphism derivation statement for the extractor's chosen output.
-/
theorem extinctionTopologyDerivationForExtractionStatement_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u}) :
    ExtinctionTopologyDerivationForExtractionStatement extractSphere =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          ExtinctionTopologyDerivationStatement M extinction
            (extractSphere M extinction)) :=
  rfl

/--
Assemble the fixed-manifold topology derivation statement from the named
post-extinction topology components.
-/
theorem extinction_topology_derivation_statement_of_components
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition)
    (surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition surgeryTraceReconstruction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification)
    (componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification)
    (componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification componentInventory)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition)
    (sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition)
    (embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition)
    (primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        primeDecompositionCompatibility)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover)
    (sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        sphericalCoveringModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        deckActionTrivialization)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient)
    (sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient trivialQuotientHomeomorphism)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (homeomorphismAssembly :
      HasExtinctionHomeomorphismAssembly M extinction decomposition
        primeDecomposition irreducibility connectedSumCollapse sphericalReduction
        quotientModel fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality simplyConnectedRecognition trivialQuotient
        homeomorphism)
    (homeomorphismDerivation :
      HasExtinctionHomeomorphismDerivation M extinction
        decomposition primeDecomposition irreducibility connectedSumCollapse
        sphericalReduction fundamentalGroupComputation deckGroupTriviality
        simplyConnectedRecognition quotientModel deckGroupIdentification
        trivialQuotient homeomorphism homeomorphismAssembly) :
    ExtinctionTopologyDerivationStatement M extinction homeomorphism :=
  ⟨decomposition, surgeryTraceReconstruction,
    surgeryTraceHandleCancellation, componentClassification,
    discardedComponentHomeomorphismClassification, componentInventory,
    componentBoundarySphereControl, primeDecomposition,
    primeDecompositionExistence, sphereTheoremApplication,
    embeddedSphereProduction, loopTheoremApplication,
    primeDecompositionCompatibility, primeFactorUniqueness, irreducibility,
    irreducibleFactorRecognition, connectedSumCollapse,
    connectedSumFundamentalGroupControl, connectedSumVanKampen,
    simplyConnectedPrimeFactorControl, sphericalReduction,
    sphericalClassification, quotientModel, sphericalFreeAction,
    universalCover, sphericalCoveringModel, sphericalCoveringProjection,
    fundamentalGroupComputation, deckGroupIdentification,
    deckActionProperness, deckGroupTriviality, deckActionTrivialization,
    trivialDeckQuotientIdentification, trivialQuotient,
    trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
    simplyConnectedRecognition, homeomorphismAssembly,
    homeomorphismDerivation⟩

/--
The component assembler for the fixed-manifold topology derivation statement is
exactly the full tuple of post-extinction topology components.
-/
theorem extinction_topology_derivation_statement_of_components_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (decomposition : HasExtinctionTopologyDecomposition M extinction)
    (surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition)
    (surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition surgeryTraceReconstruction)
    (componentClassification :
      HasExtinctionComponentClassification M extinction decomposition)
    (discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification)
    (componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification)
    (componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification componentInventory)
    (primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition)
    (primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition)
    (sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition)
    (embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition sphereTheoremApplication)
    (primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition)
    (primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        primeDecompositionCompatibility)
    (irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition)
    (irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility)
    (connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse connectedSumFundamentalGroupControl)
    (sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse)
    (sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel)
    (sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover)
    (sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        sphericalCoveringModel)
    (fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction)
    (deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation)
    (deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification)
    (deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation)
    (deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        deckActionTrivialization)
    (trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality)
    (trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient)
    (sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        trivialQuotient trivialQuotientHomeomorphism)
    (simplyConnectedRecognition :
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality)
    (homeomorphismAssembly :
      HasExtinctionHomeomorphismAssembly M extinction decomposition
        primeDecomposition irreducibility connectedSumCollapse sphericalReduction
        quotientModel fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality simplyConnectedRecognition trivialQuotient
        homeomorphism)
    (homeomorphismDerivation :
      HasExtinctionHomeomorphismDerivation M extinction
        decomposition primeDecomposition irreducibility connectedSumCollapse
        sphericalReduction fundamentalGroupComputation deckGroupTriviality
        simplyConnectedRecognition quotientModel deckGroupIdentification
        trivialQuotient homeomorphism homeomorphismAssembly) :
    extinction_topology_derivation_statement_of_components M extinction
        homeomorphism decomposition surgeryTraceReconstruction
        surgeryTraceHandleCancellation componentClassification
        discardedComponentHomeomorphismClassification componentInventory
        componentBoundarySphereControl primeDecomposition
        primeDecompositionExistence sphereTheoremApplication
        embeddedSphereProduction loopTheoremApplication
        primeDecompositionCompatibility primeFactorUniqueness irreducibility
        irreducibleFactorRecognition connectedSumCollapse
        connectedSumFundamentalGroupControl connectedSumVanKampen
        simplyConnectedPrimeFactorControl sphericalReduction
        sphericalClassification quotientModel sphericalFreeAction
        universalCover sphericalCoveringModel sphericalCoveringProjection
        fundamentalGroupComputation deckGroupIdentification
        deckActionProperness deckGroupTriviality deckActionTrivialization
        trivialDeckQuotientIdentification trivialQuotient
        trivialQuotientHomeomorphism sphericalHomeomorphismLift
        simplyConnectedRecognition homeomorphismAssembly
        homeomorphismDerivation =
      (by
        exact ⟨decomposition, surgeryTraceReconstruction,
          surgeryTraceHandleCancellation, componentClassification,
          discardedComponentHomeomorphismClassification, componentInventory,
          componentBoundarySphereControl, primeDecomposition,
          primeDecompositionExistence, sphereTheoremApplication,
          embeddedSphereProduction, loopTheoremApplication,
          primeDecompositionCompatibility, primeFactorUniqueness,
          irreducibility, irreducibleFactorRecognition, connectedSumCollapse,
          connectedSumFundamentalGroupControl, connectedSumVanKampen,
          simplyConnectedPrimeFactorControl, sphericalReduction,
          sphericalClassification, quotientModel, sphericalFreeAction,
          universalCover, sphericalCoveringModel, sphericalCoveringProjection,
          fundamentalGroupComputation, deckGroupIdentification,
          deckActionProperness, deckGroupTriviality, deckActionTrivialization,
          trivialDeckQuotientIdentification, trivialQuotient,
          trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
          simplyConnectedRecognition, homeomorphismAssembly,
          homeomorphismDerivation⟩) := by
  apply Subsingleton.elim

/--
A package of future topology inputs that turns finite extinction into the
standard sphere homeomorphism conclusion.
-/
structure ExtinctionTopologyExtractionPackage where
  /-- Topological decomposition obtained from each finite-extinction proof. -/
  decomposition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionTopologyDecomposition M extinction
  /-- Reconstruction of the topological surgery trace represented by decomposition. -/
  surgeryTraceReconstruction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSurgeryTraceReconstruction M extinction
          (decomposition M extinction)
  /-- Cancellation of the handles recorded by the reconstructed surgery trace. -/
  surgeryTraceHandleCancellation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSurgeryTraceHandleCancellation M extinction
          (decomposition M extinction)
          (surgeryTraceReconstruction M extinction)
  /-- Classification of the components present after extinction. -/
  componentClassification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionComponentClassification M extinction
          (decomposition M extinction)
  /-- Homeomorphism classification of components discarded at extinction. -/
  discardedComponentHomeomorphismClassification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionDiscardedComponentHomeomorphismClassification M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
  /-- Component inventory extracted from the post-extinction classification. -/
  componentInventory :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionComponentInventory M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
  /-- Boundary-sphere control for the extinction component inventory. -/
  componentBoundarySphereControl :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionComponentBoundarySphereControl M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
          (componentInventory M extinction)
  /-- Recognition theorem for the standard 3-sphere. -/
  recognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasThreeSphereRecognition M (decomposition M)
  /-- Prime/connected-sum decomposition extracted from the extinction data. -/
  primeDecomposition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeDecomposition M extinction
          (decomposition M extinction)
  /-- Existence theorem for the prime decomposition used after extinction. -/
  primeDecompositionExistence :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeDecompositionExistence M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
  /-- Sphere-theorem input behind the prime decomposition. -/
  sphereTheoremApplication :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSphereTheoremApplication M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
  /-- Embedded spheres realizing the prime-decomposition cuts. -/
  embeddedSphereProduction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionEmbeddedSphereProduction M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (sphereTheoremApplication M extinction)
  /-- Loop-theorem input controlling compressions in the prime-decomposition cuts. -/
  loopTheoremApplication :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionLoopTheoremApplication M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (sphereTheoremApplication M extinction)
  /-- Compatibility and uniqueness for the selected prime decomposition. -/
  primeDecompositionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeDecompositionCompatibility M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
          (primeDecomposition M extinction)
  /-- Uniqueness of prime factors in the selected decomposition. -/
  primeFactorUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionPrimeFactorUniqueness M extinction
          (decomposition M extinction)
          (componentClassification M extinction)
          (primeDecomposition M extinction)
          (primeDecompositionCompatibility M extinction)
  /-- Irreducibility input for the prime pieces. -/
  irreducibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionIrreducibility M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
  /-- Recognition of irreducible prime factors after extinction. -/
  irreducibleFactorRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionIrreducibleFactorRecognition M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
  /-- Collapse of the connected-sum decomposition in the simply connected case. -/
  connectedSumCollapse :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionConnectedSumCollapse M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
  /-- Fundamental-group control for connected-sum collapse. -/
  connectedSumFundamentalGroupControl :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionConnectedSumFundamentalGroupControl M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
  /-- Van Kampen computation for connected-sum fundamental groups. -/
  connectedSumVanKampen :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionConnectedSumVanKampenCalculation M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (connectedSumFundamentalGroupControl M extinction)
  /-- Control forcing the surviving prime factor to be simply connected. -/
  simplyConnectedPrimeFactorControl :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSimplyConnectedPrimeFactorControl M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (connectedSumFundamentalGroupControl M extinction)
  /-- Reduction of the topological pieces to spherical space forms. -/
  sphericalSpaceFormReduction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionSphericalSpaceFormReduction M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
  /-- Classification theorem for the spherical-space-form pieces. -/
  sphericalSpaceFormClassification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormClassification M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
  /-- Spherical quotient model for the surviving pieces. -/
  sphericalQuotientModel :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormQuotientModel M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
  /-- Free spherical action realizing the quotient model. -/
  sphericalFreeAction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormFreeAction M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
  /-- Universal cover of the spherical space form is the standard 3-sphere. -/
  sphericalUniversalCover :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormUniversalCover M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
  /-- Covering model tying the quotient model to the universal cover. -/
  sphericalCoveringModel :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormCoveringModel M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
  /-- Covering projection from the spherical universal cover to the quotient model. -/
  sphericalCoveringProjection :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormCoveringProjection M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
          (sphericalCoveringModel M extinction)
  /-- Fundamental-group computation for the spherical space form pieces. -/
  sphericalFundamentalGroup :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormFundamentalGroupComputation M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
  /-- Identification of the deck group with the computed fundamental group. -/
  deckGroupIdentification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckGroupIdentification M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
  /-- Properness and freeness of the deck action. -/
  deckActionProperness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckActionProperness M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
  /-- Triviality of the spherical space form deck group in the simply connected case. -/
  deckGroupTriviality :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckGroupTriviality M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalFundamentalGroup M extinction)
  /-- Trivialization of the deck action from deck-group evidence. -/
  deckActionTrivialization :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormDeckActionTrivialization M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
  /-- Identification of the quotient by a trivial deck action with the cover. -/
  trivialDeckQuotientIdentification :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormTrivialDeckQuotientIdentification M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (deckActionTrivialization M extinction)
  /-- The trivial deck group produces the trivial spherical quotient. -/
  trivialSphericalQuotient :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasTrivialSphericalSpaceFormQuotient M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
  /-- Homeomorphism supplied by the trivial spherical quotient. -/
  trivialQuotientHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormTrivialQuotientHomeomorphism M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (trivialSphericalQuotient M extinction)
  /-- Lift of the final homeomorphism through the trivial spherical quotient. -/
  sphericalHomeomorphismLift :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSphericalSpaceFormHomeomorphismLift M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalUniversalCover M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (trivialSphericalQuotient M extinction)
          (trivialQuotientHomeomorphism M extinction)
  /-- Simply connected recognition eliminating nontrivial spherical factors. -/
  simplyConnectedRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasSimplyConnectedExtinctionRecognition M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupTriviality M extinction)
  /-- Final extraction theorem derived from the preceding topology inputs. -/
  extractHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        Nonempty (M ≃ₜ ThreeSphere)
  /-- Assembly of the classification data into the final homeomorphism. -/
  homeomorphismAssembly :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionHomeomorphismAssembly M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalQuotientModel M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupIdentification M extinction)
          (deckGroupTriviality M extinction)
          (simplyConnectedRecognition M extinction)
          (trivialSphericalQuotient M extinction)
          (extractHomeomorphism M extinction)
  /-- Certificate that the named topology sub-obligations derive the homeomorphism. -/
  homeomorphismDerivation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M]
      (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
        HasExtinctionHomeomorphismDerivation M extinction
          (decomposition M extinction)
          (primeDecomposition M extinction)
          (irreducibility M extinction)
          (connectedSumCollapse M extinction)
          (sphericalSpaceFormReduction M extinction)
          (sphericalFundamentalGroup M extinction)
          (deckGroupTriviality M extinction)
          (simplyConnectedRecognition M extinction)
          (sphericalQuotientModel M extinction)
          (deckGroupIdentification M extinction)
          (trivialSphericalQuotient M extinction)
          (extractHomeomorphism M extinction)
          (homeomorphismAssembly M extinction)

/--
A completed topology package supplies the post-extinction decomposition input.
-/
def extinction_decomposition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionTopologyDecomposition M extinction :=
  package.decomposition M extinction

/-- The named extinction-decomposition projection is the stored package field. -/
theorem extinction_decomposition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_decomposition_of_topology_package package M extinction =
      package.decomposition M extinction :=
  rfl

/--
A completed topology package supplies reconstruction of the topological surgery
trace encoded by decomposition.
-/
theorem extinction_surgery_trace_reconstruction_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSurgeryTraceReconstruction M extinction
      (extinction_decomposition_of_topology_package package M extinction) :=
  package.surgeryTraceReconstruction M extinction

/-- The named surgery-trace reconstruction projection is the stored package field. -/
theorem extinction_surgery_trace_reconstruction_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_surgery_trace_reconstruction_of_topology_package
      package M extinction =
      package.surgeryTraceReconstruction M extinction :=
  rfl

/-- A completed topology package supplies handle cancellation for the surgery trace. -/
theorem extinction_surgery_trace_handle_cancellation_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSurgeryTraceHandleCancellation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_surgery_trace_reconstruction_of_topology_package
        package M extinction) :=
  package.surgeryTraceHandleCancellation M extinction

/-- The named surgery-trace handle-cancellation projection is the stored package field. -/
theorem extinction_surgery_trace_handle_cancellation_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_surgery_trace_handle_cancellation_of_topology_package
      package M extinction =
      package.surgeryTraceHandleCancellation M extinction :=
  rfl

/-- A completed topology package supplies post-extinction component classification. -/
theorem extinction_component_classification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentClassification M extinction
      (extinction_decomposition_of_topology_package package M extinction) :=
  package.componentClassification M extinction

/-- The named component-classification projection is the stored package field. -/
theorem extinction_component_classification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_component_classification_of_topology_package
      package M extinction =
      package.componentClassification M extinction :=
  rfl

/--
A completed topology package supplies homeomorphism classification for
discarded extinction components.
-/
theorem extinction_discarded_component_homeomorphism_classification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionDiscardedComponentHomeomorphismClassification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction) :=
  package.discardedComponentHomeomorphismClassification M extinction

/--
The named discarded-component homeomorphism classification projection is the
stored package field.
-/
theorem extinction_discarded_component_homeomorphism_classification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_discarded_component_homeomorphism_classification_of_topology_package
      package M extinction =
      package.discardedComponentHomeomorphismClassification M extinction :=
  rfl

/-- A completed topology package supplies an inventory of extinction components. -/
theorem extinction_component_inventory_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentInventory M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction) :=
  package.componentInventory M extinction

/-- The named component-inventory projection is the stored package field. -/
theorem extinction_component_inventory_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_component_inventory_of_topology_package package M extinction =
      package.componentInventory M extinction :=
  rfl

/-- A completed topology package supplies boundary-sphere component control. -/
theorem extinction_component_boundary_sphere_control_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentBoundarySphereControl M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction)
      (extinction_component_inventory_of_topology_package
        package M extinction) :=
  package.componentBoundarySphereControl M extinction

/-- The named component boundary-sphere control projection is the stored package field. -/
theorem extinction_component_boundary_sphere_control_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_component_boundary_sphere_control_of_topology_package
      package M extinction =
      package.componentBoundarySphereControl M extinction :=
  rfl

/-- A completed topology package supplies the 3-sphere recognition input. -/
theorem three_sphere_recognition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasThreeSphereRecognition M
      (fun extinction =>
        extinction_decomposition_of_topology_package package M extinction) :=
  package.recognition M

/-- The named 3-sphere recognition projection is the stored package field. -/
theorem three_sphere_recognition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    three_sphere_recognition_of_topology_package package M =
      package.recognition M :=
  rfl

/-- A completed topology package supplies prime-decomposition evidence. -/
theorem extinction_prime_decomposition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecomposition M extinction
      (extinction_decomposition_of_topology_package package M extinction) :=
  package.primeDecomposition M extinction

/-- The named prime-decomposition projection is the stored package field. -/
theorem extinction_prime_decomposition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_decomposition_of_topology_package package M extinction =
      package.primeDecomposition M extinction :=
  rfl

/-- A completed topology package supplies prime-decomposition existence. -/
theorem extinction_prime_decomposition_existence_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecompositionExistence M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.primeDecompositionExistence M extinction

/-- The named prime-decomposition existence projection is the stored package field. -/
theorem extinction_prime_decomposition_existence_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_decomposition_existence_of_topology_package
      package M extinction =
      package.primeDecompositionExistence M extinction :=
  rfl

/-- A completed topology package supplies the sphere-theorem input for primes. -/
theorem extinction_sphere_theorem_application_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSphereTheoremApplication M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.sphereTheoremApplication M extinction

/-- The named sphere-theorem application projection is the stored package field. -/
theorem extinction_sphere_theorem_application_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_sphere_theorem_application_of_topology_package
      package M extinction =
      package.sphereTheoremApplication M extinction :=
  rfl

/-- A completed topology package supplies embedded spheres for prime cuts. -/
theorem extinction_embedded_sphere_production_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionEmbeddedSphereProduction M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_sphere_theorem_application_of_topology_package
        package M extinction) :=
  package.embeddedSphereProduction M extinction

/-- The named embedded-sphere production projection is the stored package field. -/
theorem extinction_embedded_sphere_production_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_embedded_sphere_production_of_topology_package
      package M extinction =
      package.embeddedSphereProduction M extinction :=
  rfl

/-- A completed topology package supplies loop-theorem control for prime cuts. -/
theorem extinction_loop_theorem_application_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionLoopTheoremApplication M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_sphere_theorem_application_of_topology_package
        package M extinction) :=
  package.loopTheoremApplication M extinction

/-- The named loop-theorem application projection is the stored package field. -/
theorem extinction_loop_theorem_application_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_loop_theorem_application_of_topology_package
      package M extinction =
      package.loopTheoremApplication M extinction :=
  rfl

/-- A completed topology package supplies prime-decomposition compatibility. -/
theorem extinction_prime_decomposition_compatibility_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecompositionCompatibility M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.primeDecompositionCompatibility M extinction

/-- The named prime-decomposition compatibility projection is the stored package field. -/
theorem extinction_prime_decomposition_compatibility_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_decomposition_compatibility_of_topology_package
      package M extinction =
      package.primeDecompositionCompatibility M extinction :=
  rfl

/-- A completed topology package supplies uniqueness of prime factors. -/
theorem extinction_prime_factor_uniqueness_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeFactorUniqueness M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_component_classification_of_topology_package
        package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_prime_decomposition_compatibility_of_topology_package
        package M extinction) :=
  package.primeFactorUniqueness M extinction

/-- The named prime-factor uniqueness projection is the stored package field. -/
theorem extinction_prime_factor_uniqueness_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_prime_factor_uniqueness_of_topology_package
      package M extinction =
      package.primeFactorUniqueness M extinction :=
  rfl

/-- A completed topology package supplies irreducibility evidence. -/
theorem extinction_irreducibility_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionIrreducibility M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction) :=
  package.irreducibility M extinction

/-- The named irreducibility projection is the stored package field. -/
theorem extinction_irreducibility_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_irreducibility_of_topology_package package M extinction =
      package.irreducibility M extinction :=
  rfl

/-- A completed topology package supplies recognition of irreducible factors. -/
theorem extinction_irreducible_factor_recognition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionIrreducibleFactorRecognition M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction) :=
  package.irreducibleFactorRecognition M extinction

/-- The named irreducible-factor recognition projection is the stored package field. -/
theorem extinction_irreducible_factor_recognition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_irreducible_factor_recognition_of_topology_package
      package M extinction =
      package.irreducibleFactorRecognition M extinction :=
  rfl

/-- A completed topology package supplies connected-sum collapse evidence. -/
theorem extinction_connected_sum_collapse_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumCollapse M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction) :=
  package.connectedSumCollapse M extinction

/-- The named connected-sum collapse projection is the stored package field. -/
theorem extinction_connected_sum_collapse_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_connected_sum_collapse_of_topology_package
      package M extinction =
      package.connectedSumCollapse M extinction :=
  rfl

/-- A completed topology package supplies connected-sum fundamental-group control. -/
theorem extinction_connected_sum_fundamental_group_control_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumFundamentalGroupControl M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction) :=
  package.connectedSumFundamentalGroupControl M extinction

/-- The named connected-sum fundamental-group control projection is the stored package field. -/
theorem extinction_connected_sum_fundamental_group_control_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_connected_sum_fundamental_group_control_of_topology_package
      package M extinction =
      package.connectedSumFundamentalGroupControl M extinction :=
  rfl

/--
A completed topology package supplies the van Kampen calculation for connected
sum fundamental groups.
-/
theorem extinction_connected_sum_van_kampen_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumVanKampenCalculation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_connected_sum_fundamental_group_control_of_topology_package
        package M extinction) :=
  package.connectedSumVanKampen M extinction

/-- The named connected-sum van Kampen projection is the stored package field. -/
theorem extinction_connected_sum_van_kampen_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_connected_sum_van_kampen_of_topology_package
      package M extinction =
      package.connectedSumVanKampen M extinction :=
  rfl

/-- A completed topology package forces the surviving prime factor to be simply connected. -/
theorem extinction_simply_connected_prime_factor_control_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSimplyConnectedPrimeFactorControl M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_connected_sum_fundamental_group_control_of_topology_package
        package M extinction) :=
  package.simplyConnectedPrimeFactorControl M extinction

/-- The named simply connected prime-factor control projection is the stored package field. -/
theorem extinction_simply_connected_prime_factor_control_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_simply_connected_prime_factor_control_of_topology_package
      package M extinction =
      package.simplyConnectedPrimeFactorControl M extinction :=
  rfl

/-- A completed topology package supplies spherical-space-form reduction evidence. -/
theorem extinction_spherical_space_form_reduction_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSphericalSpaceFormReduction M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction) :=
  package.sphericalSpaceFormReduction M extinction

/-- The named spherical-space-form reduction projection is the stored package field. -/
theorem extinction_spherical_space_form_reduction_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_spherical_space_form_reduction_of_topology_package
      package M extinction =
      package.sphericalSpaceFormReduction M extinction :=
  rfl

/-- A completed topology package supplies spherical-space-form classification. -/
theorem spherical_space_form_classification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormClassification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction) :=
  package.sphericalSpaceFormClassification M extinction

/-- The named spherical-space-form classification projection is the stored package field. -/
theorem spherical_space_form_classification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_space_form_classification_of_topology_package
      package M extinction =
      package.sphericalSpaceFormClassification M extinction :=
  rfl

/-- A completed topology package supplies the spherical quotient model. -/
theorem spherical_quotient_model_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormQuotientModel M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction) :=
  package.sphericalQuotientModel M extinction

/-- The named spherical quotient-model projection is the stored package field. -/
theorem spherical_quotient_model_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_quotient_model_of_topology_package package M extinction =
      package.sphericalQuotientModel M extinction :=
  rfl

/-- A completed topology package supplies the free spherical action. -/
theorem spherical_free_action_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormFreeAction M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction) :=
  package.sphericalFreeAction M extinction

/-- The named spherical free-action projection is the stored package field. -/
theorem spherical_free_action_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_free_action_of_topology_package package M extinction =
      package.sphericalFreeAction M extinction :=
  rfl

/-- A completed topology package supplies the spherical universal-cover input. -/
theorem spherical_universal_cover_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormUniversalCover M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction) :=
  package.sphericalUniversalCover M extinction

/-- The named spherical universal-cover projection is the stored package field. -/
theorem spherical_universal_cover_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_universal_cover_of_topology_package package M extinction =
      package.sphericalUniversalCover M extinction :=
  rfl

/-- A completed topology package supplies the spherical covering model. -/
theorem spherical_covering_model_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormCoveringModel M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction) :=
  package.sphericalCoveringModel M extinction

/-- The named spherical covering-model projection is the stored package field. -/
theorem spherical_covering_model_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_covering_model_of_topology_package package M extinction =
      package.sphericalCoveringModel M extinction :=
  rfl

/-- A completed topology package supplies the spherical covering projection. -/
theorem spherical_covering_projection_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormCoveringProjection M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction)
      (spherical_covering_model_of_topology_package package M extinction) :=
  package.sphericalCoveringProjection M extinction

/-- The named spherical covering-projection projection is the stored package field. -/
theorem spherical_covering_projection_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_covering_projection_of_topology_package package M extinction =
      package.sphericalCoveringProjection M extinction :=
  rfl

/-- A completed topology package supplies spherical-space-form group computation. -/
theorem spherical_fundamental_group_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormFundamentalGroupComputation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction) :=
  package.sphericalFundamentalGroup M extinction

/-- The named spherical fundamental-group projection is the stored package field. -/
theorem spherical_fundamental_group_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_fundamental_group_of_topology_package package M extinction =
      package.sphericalFundamentalGroup M extinction :=
  rfl

/-- A completed topology package identifies the deck group with the computed group. -/
theorem spherical_deck_group_identification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckGroupIdentification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction) :=
  package.deckGroupIdentification M extinction

/-- The named deck-group identification projection is the stored package field. -/
theorem spherical_deck_group_identification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_group_identification_of_topology_package
      package M extinction =
      package.deckGroupIdentification M extinction :=
  rfl

/-- A completed topology package supplies deck-action properness. -/
theorem spherical_deck_action_properness_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckActionProperness M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction) :=
  package.deckActionProperness M extinction

/-- The named deck-action properness projection is the stored package field. -/
theorem spherical_deck_action_properness_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_action_properness_of_topology_package
      package M extinction =
      package.deckActionProperness M extinction :=
  rfl

/-- A completed topology package supplies deck-group triviality evidence. -/
theorem spherical_deck_group_triviality_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckGroupTriviality M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction) :=
  package.deckGroupTriviality M extinction

/-- The named deck-group triviality projection is the stored package field. -/
theorem spherical_deck_group_triviality_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_group_triviality_of_topology_package
      package M extinction =
      package.deckGroupTriviality M extinction :=
  rfl

/-- A completed topology package supplies deck-action trivialization. -/
theorem spherical_deck_action_trivialization_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckActionTrivialization M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction) :=
  package.deckActionTrivialization M extinction

/-- The named deck-action trivialization projection is the stored package field. -/
theorem spherical_deck_action_trivialization_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_deck_action_trivialization_of_topology_package
      package M extinction =
      package.deckActionTrivialization M extinction :=
  rfl

/--
A completed topology package identifies the quotient by a trivial deck action
with the cover.
-/
theorem spherical_trivial_deck_quotient_identification_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormTrivialDeckQuotientIdentification M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (spherical_deck_action_trivialization_of_topology_package
        package M extinction) :=
  package.trivialDeckQuotientIdentification M extinction

/-- The named trivial deck-quotient identification projection is the stored package field. -/
theorem spherical_trivial_deck_quotient_identification_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_trivial_deck_quotient_identification_of_topology_package
      package M extinction =
      package.trivialDeckQuotientIdentification M extinction :=
  rfl

/-- A completed topology package supplies the trivial spherical quotient input. -/
theorem trivial_spherical_quotient_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasTrivialSphericalSpaceFormQuotient M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction) :=
  package.trivialSphericalQuotient M extinction

/-- The named trivial spherical quotient projection is the stored package field. -/
theorem trivial_spherical_quotient_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    trivial_spherical_quotient_of_topology_package package M extinction =
      package.trivialSphericalQuotient M extinction :=
  rfl

/-- A completed topology package supplies the trivial-quotient homeomorphism input. -/
theorem trivial_quotient_homeomorphism_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormTrivialQuotientHomeomorphism M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package
        package M extinction) :=
  package.trivialQuotientHomeomorphism M extinction

/--
The named trivial-quotient homeomorphism projection is the stored package
field.
-/
theorem trivial_quotient_homeomorphism_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    trivial_quotient_homeomorphism_of_topology_package package M extinction =
      package.trivialQuotientHomeomorphism M extinction :=
  rfl

/--
A completed topology package supplies the final homeomorphism lift through the
trivial spherical quotient.
-/
theorem spherical_homeomorphism_lift_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormHomeomorphismLift M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_universal_cover_of_topology_package package M extinction)
      (spherical_fundamental_group_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package package M extinction)
      (trivial_quotient_homeomorphism_of_topology_package
        package M extinction) :=
  package.sphericalHomeomorphismLift M extinction

/-- The named spherical homeomorphism-lift projection is the stored package field. -/
theorem spherical_homeomorphism_lift_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    spherical_homeomorphism_lift_of_topology_package package M extinction =
      package.sphericalHomeomorphismLift M extinction :=
  rfl

/-- A completed topology package supplies simply connected recognition evidence. -/
theorem simply_connected_extinction_recognition_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSimplyConnectedExtinctionRecognition M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction) :=
  package.simplyConnectedRecognition M extinction

/-- The named simply connected recognition projection is the stored package field. -/
theorem simply_connected_extinction_recognition_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    simply_connected_extinction_recognition_of_topology_package
      package M extinction =
      package.simplyConnectedRecognition M extinction :=
  rfl

/-- A completed topology package extracts the final homeomorphism from extinction. -/
theorem homeomorphism_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (M ≃ₜ ThreeSphere) :=
  package.extractHomeomorphism M extinction

/-- The named topology-package homeomorphism projection is the stored package field. -/
theorem homeomorphism_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_topology_package package M extinction =
      package.extractHomeomorphism M extinction :=
  rfl

/-- A completed topology package assembles classification data into the homeomorphism. -/
theorem extinction_homeomorphism_assembly_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionHomeomorphismAssembly M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (simply_connected_extinction_recognition_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package package M extinction)
      (homeomorphism_of_topology_package package M extinction) :=
  package.homeomorphismAssembly M extinction

/-- The named topology homeomorphism-assembly projection is the stored package field. -/
theorem extinction_homeomorphism_assembly_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_homeomorphism_assembly_of_topology_package
      package M extinction =
      package.homeomorphismAssembly M extinction :=
  rfl

/--
A completed topology package supplies the derivation certificate for its
projected homeomorphism.
-/
theorem extinction_homeomorphism_derivation_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionHomeomorphismDerivation M extinction
      (extinction_decomposition_of_topology_package package M extinction)
      (extinction_prime_decomposition_of_topology_package
        package M extinction)
      (extinction_irreducibility_of_topology_package
        package M extinction)
      (extinction_connected_sum_collapse_of_topology_package
        package M extinction)
      (extinction_spherical_space_form_reduction_of_topology_package
        package M extinction)
      (spherical_fundamental_group_of_topology_package
        package M extinction)
      (spherical_deck_group_triviality_of_topology_package
        package M extinction)
      (simply_connected_extinction_recognition_of_topology_package
        package M extinction)
      (spherical_quotient_model_of_topology_package package M extinction)
      (spherical_deck_group_identification_of_topology_package
        package M extinction)
      (trivial_spherical_quotient_of_topology_package package M extinction)
      (homeomorphism_of_topology_package package M extinction)
      (extinction_homeomorphism_assembly_of_topology_package
        package M extinction) :=
  package.homeomorphismDerivation M extinction

/-- The named topology homeomorphism-derivation projection is the stored package field. -/
theorem extinction_homeomorphism_derivation_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_homeomorphism_derivation_of_topology_package
      package M extinction =
      package.homeomorphismDerivation M extinction :=
  rfl

/--
A completed topology package assembles the fixed-manifold derivation statement
for its projected homeomorphism.
-/
theorem extinction_topology_derivation_statement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyDerivationStatement M extinction
      (homeomorphism_of_topology_package package M extinction) :=
  extinction_topology_derivation_statement_of_components M extinction
    (homeomorphism_of_topology_package package M extinction)
    (extinction_decomposition_of_topology_package package M extinction)
    (extinction_surgery_trace_reconstruction_of_topology_package
      package M extinction)
    (extinction_surgery_trace_handle_cancellation_of_topology_package
      package M extinction)
    (extinction_component_classification_of_topology_package
      package M extinction)
    (extinction_discarded_component_homeomorphism_classification_of_topology_package
      package M extinction)
    (extinction_component_inventory_of_topology_package package M extinction)
    (extinction_component_boundary_sphere_control_of_topology_package
      package M extinction)
    (extinction_prime_decomposition_of_topology_package package M extinction)
    (extinction_prime_decomposition_existence_of_topology_package
      package M extinction)
    (extinction_sphere_theorem_application_of_topology_package
      package M extinction)
    (extinction_embedded_sphere_production_of_topology_package
      package M extinction)
    (extinction_loop_theorem_application_of_topology_package
      package M extinction)
    (extinction_prime_decomposition_compatibility_of_topology_package
      package M extinction)
    (extinction_prime_factor_uniqueness_of_topology_package
      package M extinction)
    (extinction_irreducibility_of_topology_package package M extinction)
    (extinction_irreducible_factor_recognition_of_topology_package
      package M extinction)
    (extinction_connected_sum_collapse_of_topology_package
      package M extinction)
    (extinction_connected_sum_fundamental_group_control_of_topology_package
      package M extinction)
    (extinction_connected_sum_van_kampen_of_topology_package
      package M extinction)
    (extinction_simply_connected_prime_factor_control_of_topology_package
      package M extinction)
    (extinction_spherical_space_form_reduction_of_topology_package
      package M extinction)
    (spherical_space_form_classification_of_topology_package
      package M extinction)
    (spherical_quotient_model_of_topology_package package M extinction)
    (spherical_free_action_of_topology_package package M extinction)
    (spherical_universal_cover_of_topology_package package M extinction)
    (spherical_covering_model_of_topology_package package M extinction)
    (spherical_covering_projection_of_topology_package package M extinction)
    (spherical_fundamental_group_of_topology_package package M extinction)
    (spherical_deck_group_identification_of_topology_package
      package M extinction)
    (spherical_deck_action_properness_of_topology_package
      package M extinction)
    (spherical_deck_group_triviality_of_topology_package package M extinction)
    (spherical_deck_action_trivialization_of_topology_package
      package M extinction)
    (spherical_trivial_deck_quotient_identification_of_topology_package
      package M extinction)
    (trivial_spherical_quotient_of_topology_package package M extinction)
    (trivial_quotient_homeomorphism_of_topology_package package M extinction)
    (spherical_homeomorphism_lift_of_topology_package package M extinction)
    (simply_connected_extinction_recognition_of_topology_package
      package M extinction)
    (extinction_homeomorphism_assembly_of_topology_package package M extinction)
    (extinction_homeomorphism_derivation_of_topology_package package M extinction)

/--
The completed topology package route to the fixed-manifold topology derivation
statement is exactly the component assembly route applied to the package
projections.
-/
theorem extinction_topology_derivation_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_topology_derivation_statement_of_topology_package
        package M extinction =
      extinction_topology_derivation_statement_of_components M extinction
        (homeomorphism_of_topology_package package M extinction)
        (extinction_decomposition_of_topology_package package M extinction)
        (extinction_surgery_trace_reconstruction_of_topology_package
          package M extinction)
        (extinction_surgery_trace_handle_cancellation_of_topology_package
          package M extinction)
        (extinction_component_classification_of_topology_package
          package M extinction)
        (extinction_discarded_component_homeomorphism_classification_of_topology_package
          package M extinction)
        (extinction_component_inventory_of_topology_package package M extinction)
        (extinction_component_boundary_sphere_control_of_topology_package
          package M extinction)
        (extinction_prime_decomposition_of_topology_package package M extinction)
        (extinction_prime_decomposition_existence_of_topology_package
          package M extinction)
        (extinction_sphere_theorem_application_of_topology_package
          package M extinction)
        (extinction_embedded_sphere_production_of_topology_package
          package M extinction)
        (extinction_loop_theorem_application_of_topology_package
          package M extinction)
        (extinction_prime_decomposition_compatibility_of_topology_package
          package M extinction)
        (extinction_prime_factor_uniqueness_of_topology_package
          package M extinction)
        (extinction_irreducibility_of_topology_package package M extinction)
        (extinction_irreducible_factor_recognition_of_topology_package
          package M extinction)
        (extinction_connected_sum_collapse_of_topology_package
          package M extinction)
        (extinction_connected_sum_fundamental_group_control_of_topology_package
          package M extinction)
        (extinction_connected_sum_van_kampen_of_topology_package
          package M extinction)
        (extinction_simply_connected_prime_factor_control_of_topology_package
          package M extinction)
        (extinction_spherical_space_form_reduction_of_topology_package
          package M extinction)
        (spherical_space_form_classification_of_topology_package
          package M extinction)
        (spherical_quotient_model_of_topology_package package M extinction)
        (spherical_free_action_of_topology_package package M extinction)
        (spherical_universal_cover_of_topology_package package M extinction)
        (spherical_covering_model_of_topology_package package M extinction)
        (spherical_covering_projection_of_topology_package package M extinction)
        (spherical_fundamental_group_of_topology_package package M extinction)
        (spherical_deck_group_identification_of_topology_package
          package M extinction)
        (spherical_deck_action_properness_of_topology_package
          package M extinction)
        (spherical_deck_group_triviality_of_topology_package
          package M extinction)
        (spherical_deck_action_trivialization_of_topology_package
          package M extinction)
        (spherical_trivial_deck_quotient_identification_of_topology_package
          package M extinction)
        (trivial_spherical_quotient_of_topology_package package M extinction)
        (trivial_quotient_homeomorphism_of_topology_package package M extinction)
        (spherical_homeomorphism_lift_of_topology_package package M extinction)
        (simply_connected_extinction_recognition_of_topology_package
          package M extinction)
        (extinction_homeomorphism_assembly_of_topology_package
          package M extinction)
        (extinction_homeomorphism_derivation_of_topology_package
          package M extinction) := by
  apply Subsingleton.elim

/--
Semantic alias for the full post-extinction classification sub-obligation
payload exposed by a fixed-manifold topology derivation statement.
-/
abbrev ExtinctionTopologyClassificationSubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) : Prop :=
    ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
    ∃ _surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
    ∃ _surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition _surgeryTraceReconstruction,
    ∃ componentClassification :
      HasExtinctionComponentClassification M extinction decomposition,
    ∃ _discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification,
    ∃ _componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification,
    ∃ _componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification _componentInventory,
    ∃ primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition,
    ∃ _primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition,
    ∃ _sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition,
    ∃ _embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition,
    ∃ _primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        _primeDecompositionCompatibility,
    ∃ irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition,
    ∃ _irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility,
    ∃ connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility,
    ∃ _connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ _simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ _sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover,
    ∃ _sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        _sphericalCoveringModel,
    ∃ fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation,
    ∃ _deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification,
    ∃ deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation,
    ∃ _deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality,
    ∃ _trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality _deckActionTrivialization,
    ∃ _trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
    ∃ _trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient,
    ∃ _sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient _trivialQuotientHomeomorphism,
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality

/--
The topology classification sub-obligation payload alias is definitionally the
full decomposition, trace, component, prime-decomposition, connected-sum,
space-form, deck-group, quotient, lift, and recognition witness stack.
-/
theorem extinctionTopologyClassificationSubobligationsPayload_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyClassificationSubobligationsPayload M extinction =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ _surgeryTraceReconstruction :
        HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
      ∃ _surgeryTraceHandleCancellation :
        HasExtinctionSurgeryTraceHandleCancellation
          M extinction decomposition _surgeryTraceReconstruction,
      ∃ componentClassification :
        HasExtinctionComponentClassification M extinction decomposition,
      ∃ _discardedComponentHomeomorphismClassification :
        HasExtinctionDiscardedComponentHomeomorphismClassification
          M extinction decomposition componentClassification,
      ∃ _componentInventory :
        HasExtinctionComponentInventory
          M extinction decomposition componentClassification,
      ∃ _componentBoundarySphereControl :
        HasExtinctionComponentBoundarySphereControl
          M extinction decomposition componentClassification _componentInventory,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ _primeDecompositionExistence :
        HasExtinctionPrimeDecompositionExistence
          M extinction decomposition primeDecomposition,
      ∃ _sphereTheoremApplication :
        HasExtinctionSphereTheoremApplication
          M extinction decomposition primeDecomposition,
      ∃ _embeddedSphereProduction :
        HasExtinctionEmbeddedSphereProduction
          M extinction decomposition primeDecomposition
          _sphereTheoremApplication,
      ∃ _loopTheoremApplication :
        HasExtinctionLoopTheoremApplication
          M extinction decomposition primeDecomposition
          _sphereTheoremApplication,
      ∃ _primeDecompositionCompatibility :
        HasExtinctionPrimeDecompositionCompatibility
          M extinction decomposition componentClassification primeDecomposition,
      ∃ _primeFactorUniqueness :
        HasExtinctionPrimeFactorUniqueness
          M extinction decomposition componentClassification primeDecomposition
          _primeDecompositionCompatibility,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ _irreducibleFactorRecognition :
        HasExtinctionIrreducibleFactorRecognition
          M extinction decomposition primeDecomposition irreducibility,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ _connectedSumFundamentalGroupControl :
        HasExtinctionConnectedSumFundamentalGroupControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _connectedSumVanKampen :
        HasExtinctionConnectedSumVanKampenCalculation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse _connectedSumFundamentalGroupControl,
      ∃ _simplyConnectedPrimeFactorControl :
        HasExtinctionSimplyConnectedPrimeFactorControl
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse _connectedSumFundamentalGroupControl,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ _sphericalClassification :
        HasSphericalSpaceFormClassification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ _sphericalFreeAction :
        HasSphericalSpaceFormFreeAction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ _universalCover :
        HasSphericalSpaceFormUniversalCover
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel,
      ∃ _sphericalCoveringModel :
        HasSphericalSpaceFormCoveringModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover,
      ∃ _sphericalCoveringProjection :
        HasSphericalSpaceFormCoveringProjection
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover
          _sphericalCoveringModel,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ _deckActionProperness :
        HasSphericalSpaceFormDeckActionProperness
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ _deckActionTrivialization :
        HasSphericalSpaceFormDeckActionTrivialization
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
      ∃ _trivialDeckQuotientIdentification :
        HasSphericalSpaceFormTrivialDeckQuotientIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality _deckActionTrivialization,
      ∃ _trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
      ∃ _trivialQuotientHomeomorphism :
        HasSphericalSpaceFormTrivialQuotientHomeomorphism
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          _trivialQuotient,
      ∃ _sphericalHomeomorphismLift :
        HasSphericalSpaceFormHomeomorphismLift
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel _universalCover
          fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
          _trivialQuotient _trivialQuotientHomeomorphism,
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality) :=
  rfl

/--
The fixed-manifold topology derivation statement exposes the full
post-extinction classification sub-obligation stack.
-/
theorem topology_classification_subobligations_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
    ∃ _surgeryTraceReconstruction :
      HasExtinctionSurgeryTraceReconstruction M extinction decomposition,
    ∃ _surgeryTraceHandleCancellation :
      HasExtinctionSurgeryTraceHandleCancellation
        M extinction decomposition _surgeryTraceReconstruction,
    ∃ componentClassification :
      HasExtinctionComponentClassification M extinction decomposition,
    ∃ _discardedComponentHomeomorphismClassification :
      HasExtinctionDiscardedComponentHomeomorphismClassification
        M extinction decomposition componentClassification,
    ∃ _componentInventory :
      HasExtinctionComponentInventory
        M extinction decomposition componentClassification,
    ∃ _componentBoundarySphereControl :
      HasExtinctionComponentBoundarySphereControl
        M extinction decomposition componentClassification _componentInventory,
    ∃ primeDecomposition :
      HasExtinctionPrimeDecomposition M extinction decomposition,
    ∃ _primeDecompositionExistence :
      HasExtinctionPrimeDecompositionExistence
        M extinction decomposition primeDecomposition,
    ∃ _sphereTheoremApplication :
      HasExtinctionSphereTheoremApplication
        M extinction decomposition primeDecomposition,
    ∃ _embeddedSphereProduction :
      HasExtinctionEmbeddedSphereProduction
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _loopTheoremApplication :
      HasExtinctionLoopTheoremApplication
        M extinction decomposition primeDecomposition
        _sphereTheoremApplication,
    ∃ _primeDecompositionCompatibility :
      HasExtinctionPrimeDecompositionCompatibility
        M extinction decomposition componentClassification primeDecomposition,
    ∃ _primeFactorUniqueness :
      HasExtinctionPrimeFactorUniqueness
        M extinction decomposition componentClassification primeDecomposition
        _primeDecompositionCompatibility,
    ∃ irreducibility :
      HasExtinctionIrreducibility
        M extinction decomposition primeDecomposition,
    ∃ _irreducibleFactorRecognition :
      HasExtinctionIrreducibleFactorRecognition
        M extinction decomposition primeDecomposition irreducibility,
    ∃ connectedSumCollapse :
      HasExtinctionConnectedSumCollapse
        M extinction decomposition primeDecomposition irreducibility,
    ∃ _connectedSumFundamentalGroupControl :
      HasExtinctionConnectedSumFundamentalGroupControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _connectedSumVanKampen :
      HasExtinctionConnectedSumVanKampenCalculation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ _simplyConnectedPrimeFactorControl :
      HasExtinctionSimplyConnectedPrimeFactorControl
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse _connectedSumFundamentalGroupControl,
    ∃ sphericalReduction :
      HasExtinctionSphericalSpaceFormReduction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse,
    ∃ _sphericalClassification :
      HasSphericalSpaceFormClassification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ quotientModel :
      HasSphericalSpaceFormQuotientModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ _sphericalFreeAction :
      HasSphericalSpaceFormFreeAction
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _universalCover :
      HasSphericalSpaceFormUniversalCover
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel,
    ∃ _sphericalCoveringModel :
      HasSphericalSpaceFormCoveringModel
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover,
    ∃ _sphericalCoveringProjection :
      HasSphericalSpaceFormCoveringProjection
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        _sphericalCoveringModel,
    ∃ fundamentalGroupComputation :
      HasSphericalSpaceFormFundamentalGroupComputation
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction,
    ∃ deckGroupIdentification :
      HasSphericalSpaceFormDeckGroupIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation,
    ∃ _deckActionProperness :
      HasSphericalSpaceFormDeckActionProperness
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification,
    ∃ deckGroupTriviality :
      HasSphericalSpaceFormDeckGroupTriviality
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation,
    ∃ _deckActionTrivialization :
      HasSphericalSpaceFormDeckActionTrivialization
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality,
    ∃ _trivialDeckQuotientIdentification :
      HasSphericalSpaceFormTrivialDeckQuotientIdentification
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification
        deckGroupTriviality _deckActionTrivialization,
    ∃ _trivialQuotient :
      HasTrivialSphericalSpaceFormQuotient
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
    ∃ _trivialQuotientHomeomorphism :
      HasSphericalSpaceFormTrivialQuotientHomeomorphism
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient,
    ∃ _sphericalHomeomorphismLift :
      HasSphericalSpaceFormHomeomorphismLift
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction quotientModel _universalCover
        fundamentalGroupComputation deckGroupIdentification deckGroupTriviality
        _trivialQuotient _trivialQuotientHomeomorphism,
      HasSimplyConnectedExtinctionRecognition
        M extinction decomposition primeDecomposition irreducibility
        connectedSumCollapse sphericalReduction fundamentalGroupComputation
        deckGroupTriviality := by
  rcases derivationStatement with
    ⟨decomposition, surgeryTraceReconstruction,
      surgeryTraceHandleCancellation, componentClassification,
      discardedComponentHomeomorphismClassification, componentInventory,
      componentBoundarySphereControl, primeDecomposition,
      primeDecompositionExistence, sphereTheoremApplication,
      embeddedSphereProduction, loopTheoremApplication,
      primeDecompositionCompatibility, primeFactorUniqueness, irreducibility,
      irreducibleFactorRecognition, connectedSumCollapse,
      connectedSumFundamentalGroupControl, connectedSumVanKampen,
      simplyConnectedPrimeFactorControl, sphericalReduction,
      sphericalClassification, quotientModel, sphericalFreeAction,
      universalCover, sphericalCoveringModel, sphericalCoveringProjection,
      fundamentalGroupComputation, deckGroupIdentification,
      deckActionProperness, deckGroupTriviality, deckActionTrivialization,
      trivialDeckQuotientIdentification, trivialQuotient,
      trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
      simplyConnectedRecognition, _homeomorphismAssembly,
      _homeomorphismDerivation⟩
  exact ⟨decomposition, surgeryTraceReconstruction,
    surgeryTraceHandleCancellation, componentClassification,
    discardedComponentHomeomorphismClassification, componentInventory,
    componentBoundarySphereControl, primeDecomposition,
    primeDecompositionExistence, sphereTheoremApplication,
    embeddedSphereProduction, loopTheoremApplication,
    primeDecompositionCompatibility, primeFactorUniqueness, irreducibility,
    irreducibleFactorRecognition, connectedSumCollapse,
    connectedSumFundamentalGroupControl, connectedSumVanKampen,
    simplyConnectedPrimeFactorControl, sphericalReduction,
    sphericalClassification, quotientModel, sphericalFreeAction,
    universalCover, sphericalCoveringModel, sphericalCoveringProjection,
    fundamentalGroupComputation, deckGroupIdentification, deckActionProperness,
    deckGroupTriviality, deckActionTrivialization,
    trivialDeckQuotientIdentification, trivialQuotient,
    trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
    simplyConnectedRecognition⟩

/--
The classification-subobligation bridge from a full topology derivation
statement exposes exactly the post-extinction classification components stored
in it.
-/
theorem topology_classification_subobligations_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    topology_classification_subobligations_of_derivation_statement
        M extinction homeomorphism derivationStatement =
      (by
        rcases derivationStatement with
          ⟨decomposition, surgeryTraceReconstruction,
            surgeryTraceHandleCancellation, componentClassification,
            discardedComponentHomeomorphismClassification, componentInventory,
            componentBoundarySphereControl, primeDecomposition,
            primeDecompositionExistence, sphereTheoremApplication,
            embeddedSphereProduction, loopTheoremApplication,
            primeDecompositionCompatibility, primeFactorUniqueness,
            irreducibility, irreducibleFactorRecognition, connectedSumCollapse,
            connectedSumFundamentalGroupControl, connectedSumVanKampen,
            simplyConnectedPrimeFactorControl, sphericalReduction,
            sphericalClassification, quotientModel, sphericalFreeAction,
            universalCover, sphericalCoveringModel, sphericalCoveringProjection,
            fundamentalGroupComputation, deckGroupIdentification,
            deckActionProperness, deckGroupTriviality, deckActionTrivialization,
            trivialDeckQuotientIdentification, trivialQuotient,
            trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
            simplyConnectedRecognition, _homeomorphismAssembly,
            _homeomorphismDerivation⟩
        exact ⟨decomposition, surgeryTraceReconstruction,
          surgeryTraceHandleCancellation, componentClassification,
          discardedComponentHomeomorphismClassification, componentInventory,
          componentBoundarySphereControl, primeDecomposition,
          primeDecompositionExistence, sphereTheoremApplication,
          embeddedSphereProduction, loopTheoremApplication,
          primeDecompositionCompatibility, primeFactorUniqueness,
          irreducibility, irreducibleFactorRecognition, connectedSumCollapse,
          connectedSumFundamentalGroupControl, connectedSumVanKampen,
          simplyConnectedPrimeFactorControl, sphericalReduction,
          sphericalClassification, quotientModel, sphericalFreeAction,
          universalCover, sphericalCoveringModel, sphericalCoveringProjection,
          fundamentalGroupComputation, deckGroupIdentification,
          deckActionProperness, deckGroupTriviality, deckActionTrivialization,
          trivialDeckQuotientIdentification, trivialQuotient,
          trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
          simplyConnectedRecognition⟩) := by
  apply Subsingleton.elim

/--
The fixed-manifold homeomorphism assembly statement: the post-extinction
classification, quotient, deck-group, and simply-connected recognition data
assemble the projected homeomorphism to the standard 3-sphere.
-/
def ExtinctionTopologyHomeomorphismAssemblyStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop :=
  ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
  ∃ primeDecomposition :
    HasExtinctionPrimeDecomposition M extinction decomposition,
  ∃ irreducibility :
    HasExtinctionIrreducibility
      M extinction decomposition primeDecomposition,
  ∃ connectedSumCollapse :
    HasExtinctionConnectedSumCollapse
      M extinction decomposition primeDecomposition irreducibility,
  ∃ sphericalReduction :
    HasExtinctionSphericalSpaceFormReduction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ quotientModel :
    HasSphericalSpaceFormQuotientModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ fundamentalGroupComputation :
    HasSphericalSpaceFormFundamentalGroupComputation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupIdentification :
    HasSphericalSpaceFormDeckGroupIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation,
  ∃ deckGroupTriviality :
    HasSphericalSpaceFormDeckGroupTriviality
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation,
  ∃ simplyConnectedRecognition :
    HasSimplyConnectedExtinctionRecognition
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation
      deckGroupTriviality,
  ∃ trivialQuotient :
    HasTrivialSphericalSpaceFormQuotient
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
    HasExtinctionHomeomorphismAssembly M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      quotientModel fundamentalGroupComputation deckGroupIdentification
      deckGroupTriviality simplyConnectedRecognition trivialQuotient
      homeomorphism

/--
The homeomorphism assembly statement is definitionally the narrow
classification, quotient, deck-group, recognition, trivial-quotient, and
assembly witness stack.
-/
theorem extinctionTopologyHomeomorphismAssemblyStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) :
    ExtinctionTopologyHomeomorphismAssemblyStatement
      M extinction homeomorphism =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ simplyConnectedRecognition :
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality,
      ∃ trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
        HasExtinctionHomeomorphismAssembly M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction quotientModel fundamentalGroupComputation
          deckGroupIdentification deckGroupTriviality simplyConnectedRecognition
          trivialQuotient homeomorphism) :=
  rfl

/--
The fixed-manifold homeomorphism derivation statement: the assembled
homeomorphism certificate is sufficient to derive the projected homeomorphism.
-/
def ExtinctionTopologyHomeomorphismDerivationStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) : Prop :=
  ∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
  ∃ primeDecomposition :
    HasExtinctionPrimeDecomposition M extinction decomposition,
  ∃ irreducibility :
    HasExtinctionIrreducibility
      M extinction decomposition primeDecomposition,
  ∃ connectedSumCollapse :
    HasExtinctionConnectedSumCollapse
      M extinction decomposition primeDecomposition irreducibility,
  ∃ sphericalReduction :
    HasExtinctionSphericalSpaceFormReduction
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse,
  ∃ fundamentalGroupComputation :
    HasSphericalSpaceFormFundamentalGroupComputation
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupTriviality :
    HasSphericalSpaceFormDeckGroupTriviality
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation,
  ∃ simplyConnectedRecognition :
    HasSimplyConnectedExtinctionRecognition
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction fundamentalGroupComputation
      deckGroupTriviality,
  ∃ quotientModel :
    HasSphericalSpaceFormQuotientModel
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction,
  ∃ deckGroupIdentification :
    HasSphericalSpaceFormDeckGroupIdentification
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation,
  ∃ trivialQuotient :
    HasTrivialSphericalSpaceFormQuotient
      M extinction decomposition primeDecomposition irreducibility
      connectedSumCollapse sphericalReduction quotientModel
      fundamentalGroupComputation deckGroupIdentification deckGroupTriviality,
  ∃ homeomorphismAssembly :
    HasExtinctionHomeomorphismAssembly M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      quotientModel fundamentalGroupComputation deckGroupIdentification
      deckGroupTriviality simplyConnectedRecognition trivialQuotient
      homeomorphism,
    HasExtinctionHomeomorphismDerivation M extinction decomposition
      primeDecomposition irreducibility connectedSumCollapse sphericalReduction
      fundamentalGroupComputation deckGroupTriviality simplyConnectedRecognition
      quotientModel deckGroupIdentification trivialQuotient homeomorphism
      homeomorphismAssembly

/--
The homeomorphism derivation statement is definitionally the narrow recognition,
assembly, and derivation witness stack.
-/
theorem extinctionTopologyHomeomorphismDerivationStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere)) :
    ExtinctionTopologyHomeomorphismDerivationStatement
      M extinction homeomorphism =
      (∃ decomposition : HasExtinctionTopologyDecomposition M extinction,
      ∃ primeDecomposition :
        HasExtinctionPrimeDecomposition M extinction decomposition,
      ∃ irreducibility :
        HasExtinctionIrreducibility
          M extinction decomposition primeDecomposition,
      ∃ connectedSumCollapse :
        HasExtinctionConnectedSumCollapse
          M extinction decomposition primeDecomposition irreducibility,
      ∃ sphericalReduction :
        HasExtinctionSphericalSpaceFormReduction
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse,
      ∃ fundamentalGroupComputation :
        HasSphericalSpaceFormFundamentalGroupComputation
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupTriviality :
        HasSphericalSpaceFormDeckGroupTriviality
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation,
      ∃ simplyConnectedRecognition :
        HasSimplyConnectedExtinctionRecognition
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction fundamentalGroupComputation
          deckGroupTriviality,
      ∃ quotientModel :
        HasSphericalSpaceFormQuotientModel
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction,
      ∃ deckGroupIdentification :
        HasSphericalSpaceFormDeckGroupIdentification
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation,
      ∃ trivialQuotient :
        HasTrivialSphericalSpaceFormQuotient
          M extinction decomposition primeDecomposition irreducibility
          connectedSumCollapse sphericalReduction quotientModel
          fundamentalGroupComputation deckGroupIdentification
          deckGroupTriviality,
      ∃ homeomorphismAssembly :
        HasExtinctionHomeomorphismAssembly M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction quotientModel fundamentalGroupComputation
          deckGroupIdentification deckGroupTriviality simplyConnectedRecognition
          trivialQuotient homeomorphism,
        HasExtinctionHomeomorphismDerivation M extinction decomposition
          primeDecomposition irreducibility connectedSumCollapse
          sphericalReduction fundamentalGroupComputation deckGroupTriviality
          simplyConnectedRecognition quotientModel deckGroupIdentification
          trivialQuotient homeomorphism homeomorphismAssembly) :=
  rfl

/--
The full topology derivation statement contains the narrower homeomorphism
assembly statement.
-/
theorem topology_homeomorphism_assembly_statement_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    ExtinctionTopologyHomeomorphismAssemblyStatement
      M extinction homeomorphism := by
  rcases derivationStatement with
    ⟨decomposition, _surgeryTraceReconstruction,
      _surgeryTraceHandleCancellation, _componentClassification,
      _discardedComponentHomeomorphismClassification, _componentInventory,
      _componentBoundarySphereControl, primeDecomposition,
      _primeDecompositionExistence, _sphereTheoremApplication,
      _embeddedSphereProduction, _loopTheoremApplication,
      _primeDecompositionCompatibility, _primeFactorUniqueness, irreducibility,
      _irreducibleFactorRecognition, connectedSumCollapse,
      _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
      _simplyConnectedPrimeFactorControl, sphericalReduction,
      _sphericalClassification, quotientModel, _sphericalFreeAction,
      _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
      fundamentalGroupComputation, deckGroupIdentification,
      _deckActionProperness, deckGroupTriviality, _deckActionTrivialization,
      _trivialDeckQuotientIdentification, trivialQuotient,
      _trivialQuotientHomeomorphism, _sphericalHomeomorphismLift,
      simplyConnectedRecognition, homeomorphismAssembly,
      _homeomorphismDerivation⟩
  exact ⟨decomposition, primeDecomposition, irreducibility,
    connectedSumCollapse, sphericalReduction, quotientModel,
    fundamentalGroupComputation, deckGroupIdentification, deckGroupTriviality,
    simplyConnectedRecognition, trivialQuotient, homeomorphismAssembly⟩

/--
The assembly-statement bridge from a full topology derivation statement exposes
exactly the narrower homeomorphism assembly components stored in it.
-/
theorem topology_homeomorphism_assembly_statement_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    topology_homeomorphism_assembly_statement_of_derivation_statement
        M extinction homeomorphism derivationStatement =
      (by
        rcases derivationStatement with
          ⟨decomposition, _surgeryTraceReconstruction,
            _surgeryTraceHandleCancellation, _componentClassification,
            _discardedComponentHomeomorphismClassification, _componentInventory,
            _componentBoundarySphereControl, primeDecomposition,
            _primeDecompositionExistence, _sphereTheoremApplication,
            _embeddedSphereProduction, _loopTheoremApplication,
            _primeDecompositionCompatibility, _primeFactorUniqueness,
            irreducibility, _irreducibleFactorRecognition,
            connectedSumCollapse, _connectedSumFundamentalGroupControl,
            _connectedSumVanKampen, _simplyConnectedPrimeFactorControl,
            sphericalReduction, _sphericalClassification, quotientModel,
            _sphericalFreeAction, _universalCover, _sphericalCoveringModel,
            _sphericalCoveringProjection, fundamentalGroupComputation,
            deckGroupIdentification, _deckActionProperness, deckGroupTriviality,
            _deckActionTrivialization, _trivialDeckQuotientIdentification,
            trivialQuotient, _trivialQuotientHomeomorphism,
            _sphericalHomeomorphismLift, simplyConnectedRecognition,
            homeomorphismAssembly, _homeomorphismDerivation⟩
        exact ⟨decomposition, primeDecomposition, irreducibility,
          connectedSumCollapse, sphericalReduction, quotientModel,
          fundamentalGroupComputation, deckGroupIdentification,
          deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
          homeomorphismAssembly⟩) := by
  apply Subsingleton.elim

/--
The full topology derivation statement contains the narrower homeomorphism
derivation statement.
-/
theorem topology_homeomorphism_derivation_statement_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    ExtinctionTopologyHomeomorphismDerivationStatement
      M extinction homeomorphism := by
  rcases derivationStatement with
    ⟨decomposition, _surgeryTraceReconstruction,
      _surgeryTraceHandleCancellation, _componentClassification,
      _discardedComponentHomeomorphismClassification, _componentInventory,
      _componentBoundarySphereControl, primeDecomposition,
      _primeDecompositionExistence, _sphereTheoremApplication,
      _embeddedSphereProduction, _loopTheoremApplication,
      _primeDecompositionCompatibility, _primeFactorUniqueness, irreducibility,
      _irreducibleFactorRecognition, connectedSumCollapse,
      _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
      _simplyConnectedPrimeFactorControl, sphericalReduction,
      _sphericalClassification, quotientModel, _sphericalFreeAction,
      _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
      fundamentalGroupComputation, deckGroupIdentification,
      _deckActionProperness, deckGroupTriviality, _deckActionTrivialization,
      _trivialDeckQuotientIdentification, trivialQuotient,
      _trivialQuotientHomeomorphism, _sphericalHomeomorphismLift,
      simplyConnectedRecognition, homeomorphismAssembly,
      homeomorphismDerivation⟩
  exact ⟨decomposition, primeDecomposition, irreducibility,
    connectedSumCollapse, sphericalReduction, fundamentalGroupComputation,
    deckGroupTriviality, simplyConnectedRecognition, quotientModel,
    deckGroupIdentification, trivialQuotient, homeomorphismAssembly,
    homeomorphismDerivation⟩

/--
The derivation-statement bridge from a full topology derivation statement
exposes exactly the narrower homeomorphism derivation components stored in it.
-/
theorem topology_homeomorphism_derivation_statement_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    topology_homeomorphism_derivation_statement_of_derivation_statement
        M extinction homeomorphism derivationStatement =
      (by
        rcases derivationStatement with
          ⟨decomposition, _surgeryTraceReconstruction,
            _surgeryTraceHandleCancellation, _componentClassification,
            _discardedComponentHomeomorphismClassification, _componentInventory,
            _componentBoundarySphereControl, primeDecomposition,
            _primeDecompositionExistence, _sphereTheoremApplication,
            _embeddedSphereProduction, _loopTheoremApplication,
            _primeDecompositionCompatibility, _primeFactorUniqueness,
            irreducibility, _irreducibleFactorRecognition,
            connectedSumCollapse, _connectedSumFundamentalGroupControl,
            _connectedSumVanKampen, _simplyConnectedPrimeFactorControl,
            sphericalReduction, _sphericalClassification, quotientModel,
            _sphericalFreeAction, _universalCover, _sphericalCoveringModel,
            _sphericalCoveringProjection, fundamentalGroupComputation,
            deckGroupIdentification, _deckActionProperness, deckGroupTriviality,
            _deckActionTrivialization, _trivialDeckQuotientIdentification,
            trivialQuotient, _trivialQuotientHomeomorphism,
            _sphericalHomeomorphismLift, simplyConnectedRecognition,
            homeomorphismAssembly, homeomorphismDerivation⟩
        exact ⟨decomposition, primeDecomposition, irreducibility,
          connectedSumCollapse, sphericalReduction, fundamentalGroupComputation,
          deckGroupTriviality, simplyConnectedRecognition, quotientModel,
          deckGroupIdentification, trivialQuotient, homeomorphismAssembly,
          homeomorphismDerivation⟩) := by
  apply Subsingleton.elim

/--
A completed topology package supplies the theorem-shaped extraction statement
consumed by the final Poincare assembly.
-/
theorem extinction_topology_extraction_statement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExtinctionTopologyExtractionStatement.{u} := by
  intro M _ _ _ _ _ extinction
  exact ⟨homeomorphism_of_topology_package package M extinction,
    extinction_topology_derivation_statement_of_topology_package
      package M extinction⟩

/--
The package-to-topology-extraction statement constructor is the explicit
fixed-extinction homeomorphism plus derivation statement projection.
-/
theorem extinction_topology_extraction_statement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    extinction_topology_extraction_statement_of_topology_package package =
      (by
        intro M _ _ _ _ _ extinction
        exact ⟨homeomorphism_of_topology_package package M extinction,
          extinction_topology_derivation_statement_of_topology_package
            package M extinction⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement exposes the fixed-extinction
homeomorphism together with its derivation statement payload.
-/
theorem topology_derivation_statement_payload_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
      ExtinctionTopologyDerivationStatement M extinction homeomorphism := by
  rcases topologyStatement M extinction with
    ⟨homeomorphism, derivationStatement⟩
  exact ⟨homeomorphism, derivationStatement⟩

/--
The fixed-extinction topology payload destructures the theorem-shaped
extraction statement at that finite-extinction witness.
-/
theorem topology_derivation_statement_payload_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_extraction_statement
      topologyStatement M extinction =
      (by
        rcases topologyStatement M extinction with
          ⟨homeomorphism, derivationStatement⟩
        exact ⟨homeomorphism, derivationStatement⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement supplies the fixed-extinction
homeomorphism conclusion.
-/
theorem homeomorphism_of_topology_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases topology_derivation_statement_payload_of_extraction_statement
      topologyStatement M extinction with
    ⟨homeomorphism, _derivationStatement⟩
  exact homeomorphism

/--
The fixed-extinction homeomorphism projection is the first field of the
theorem-shaped topology payload.
-/
theorem homeomorphism_of_topology_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_topology_extraction_statement
      topologyStatement M extinction =
      (by
        rcases topology_derivation_statement_payload_of_extraction_statement
            topologyStatement M extinction with
          ⟨homeomorphism, _derivationStatement⟩
        exact homeomorphism) := by
  apply Subsingleton.elim

/--
The theorem-shaped topology extraction statement supplies the existing
finite-extinction-to-sphere interface.
-/
theorem extinction_implies_sphere_of_topology_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  intro M _ _ _ _ _ extinction
  exact homeomorphism_of_topology_extraction_statement
    topologyStatement M extinction

/--
The final extraction interface from a theorem-shaped topology statement is the
fixed-extinction homeomorphism projection at every finite-extinction witness.
-/
theorem extinction_implies_sphere_of_topology_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    extinction_implies_sphere_of_topology_extraction_statement
      topologyStatement =
      (by
        intro M _ _ _ _ _ extinction
        exact homeomorphism_of_topology_extraction_statement
          topologyStatement M extinction) := by
  apply Subsingleton.elim

/--
If a finite-extinction-to-sphere extractor is accompanied by derivation evidence
for the homeomorphism it returns, then it upgrades to the stronger topology
extraction statement.
-/
theorem extinction_topology_extraction_statement_of_extraction_and_derivation
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    ExtinctionTopologyExtractionStatement.{u} := by
  intro M _ _ _ _ _ extinction
  exact ⟨extractSphere M extinction, derive M extinction⟩

/--
The extraction-plus-derivation constructor packages the supplied extractor
with the derivation evidence at each finite-extinction witness.
-/
theorem extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    extinction_topology_extraction_statement_of_extraction_and_derivation
      extractSphere derive =
      (by
        intro M _ _ _ _ _ extinction
        exact ⟨extractSphere M extinction, derive M extinction⟩) := by
  apply Subsingleton.elim

/--
Projecting the fixed-extinction topology payload from a statement reconstructed
from an extractor and derivation evidence returns those supplied fields.
-/
theorem topology_derivation_statement_payload_of_extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_extraction_statement
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derive)
      M extinction =
      ⟨extractSphere M extinction, derive M extinction⟩ := by
  apply Subsingleton.elim

/--
The fixed-extinction homeomorphism projected from an extractor-plus-derivation
statement is the supplied extractor at that finite-extinction witness.
-/
theorem homeomorphism_of_extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_topology_extraction_statement
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derive)
      M extinction =
      extractSphere M extinction := by
  apply Subsingleton.elim

/--
The final extraction interface recovered from an extractor-plus-derivation
statement is the supplied extractor.
-/
theorem extinction_implies_sphere_of_extinction_topology_extraction_statement_of_extraction_and_derivation_eq
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derive :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    extinction_implies_sphere_of_topology_extraction_statement
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derive) =
      extractSphere := by
  apply Subsingleton.elim

/--
The strong topology extraction statement is exactly a
finite-extinction-to-sphere extractor together with derivation evidence for the
homeomorphism chosen by that extractor.
-/
theorem extinction_topology_extraction_statement_iff_extraction_with_derivation :
    ExtinctionTopologyExtractionStatement.{u} ↔
      ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
        ExtinctionTopologyDerivationForExtractionStatement.{u}
          extractSphere := by
  constructor
  · intro topologyStatement
    let extractSphere : ExtinctionImpliesSphereStatement.{u} := by
      intro M _ _ _ _ _ extinction
      exact (topologyStatement M extinction).choose
    refine ⟨extractSphere, ?_⟩
    intro M _ _ _ _ _ extinction
    exact (topologyStatement M extinction).choose_spec
  · rintro ⟨extractSphere, derive⟩
    exact extinction_topology_extraction_statement_of_extraction_and_derivation
      extractSphere derive

/--
The strong topology extraction equivalence is the pair of the named extractor
projection and the named constructor from extraction plus derivation evidence.
-/
theorem extinction_topology_extraction_statement_iff_extraction_with_derivation_eq :
    extinction_topology_extraction_statement_iff_extraction_with_derivation =
      (by
        constructor
        · intro topologyStatement
          let extractSphere : ExtinctionImpliesSphereStatement.{u} := by
            intro M _ _ _ _ _ extinction
            exact (topologyStatement M extinction).choose
          refine ⟨extractSphere, ?_⟩
          intro M _ _ _ _ _ extinction
          exact (topologyStatement M extinction).choose_spec
        · rintro ⟨extractSphere, derive⟩
          exact
            extinction_topology_extraction_statement_of_extraction_and_derivation
              extractSphere derive) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus the stronger topology extraction statement is
enough to discharge the project target.
-/
theorem poincare_statement_of_finite_extinction_and_topology_extraction_statement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  exact poincare_statement_of_extinction_and_extraction finiteExtinction
    (extinction_implies_sphere_of_topology_extraction_statement
      topologyStatement)

/--
The topology-extraction route to the project target is the existing
finite-extinction/extraction assembly applied to the statement-mediated final
extractor.
-/
theorem poincare_statement_of_finite_extinction_and_topology_extraction_statement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_statement_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement =
      poincare_statement_of_extinction_and_extraction finiteExtinction
        (extinction_implies_sphere_of_topology_extraction_statement
          topologyStatement) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus the stronger topology extraction statement
exposes the target and universe-indexed completion criterion as one payload.
-/
theorem poincare_payload_of_finite_extinction_and_topology_extraction_statement
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_poincareConjectureStatement
    (poincare_statement_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement)

/--
The topology-extraction project payload is the statement-layer completion
payload of the named topology-extraction target route.
-/
theorem poincare_payload_of_finite_extinction_and_topology_extraction_statement_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    poincare_payload_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction topologyStatement =
      poincare_completion_payload_of_poincareConjectureStatement
        (poincare_statement_of_finite_extinction_and_topology_extraction_statement
          finiteExtinction topologyStatement) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus a final extractor and its topology derivation
certificate is enough to discharge the project target.
-/
theorem poincare_statement_of_finite_extinction_and_extraction_derivation
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    PoincareConjectureStatement.{u} := by
  exact
    poincare_statement_of_finite_extinction_and_topology_extraction_statement
      finiteExtinction
      (extinction_topology_extraction_statement_of_extraction_and_derivation
        extractSphere derivation)

/--
The extractor-plus-derivation route to the project target factors through the
named topology-extraction statement constructor.
-/
theorem poincare_statement_of_finite_extinction_and_extraction_derivation_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    poincare_statement_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation =
      poincare_statement_of_finite_extinction_and_topology_extraction_statement
        finiteExtinction
        (extinction_topology_extraction_statement_of_extraction_and_derivation
          extractSphere derivation) := by
  apply Subsingleton.elim

/--
Universal finite extinction plus a final extractor and its topology derivation
certificate exposes the target and universe-indexed completion criterion as one
payload.
-/
theorem poincare_payload_of_finite_extinction_and_extraction_derivation
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact poincare_completion_payload_of_poincareConjectureStatement
    (poincare_statement_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation)

/--
The extractor-plus-derivation project payload is the statement-layer completion
payload of the named extractor-plus-derivation target route.
-/
theorem poincare_payload_of_finite_extinction_and_extraction_derivation_eq
    (finiteExtinction :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M)
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere) :
    poincare_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation =
      poincare_completion_payload_of_poincareConjectureStatement
        (poincare_statement_of_finite_extinction_and_extraction_derivation
          finiteExtinction extractSphere derivation) := by
  apply Subsingleton.elim

/--
A completed topology package supplies the theorem-shaped extraction statement
together with the final extraction interface consumed by the assembly layer.
-/
theorem topology_extraction_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ _topologyStatement : ExtinctionTopologyExtractionStatement.{u},
      ExtinctionImpliesSphereStatement.{u} := by
  let topologyStatement :=
    extinction_topology_extraction_statement_of_topology_package package
  exact ⟨topologyStatement,
    extinction_implies_sphere_of_topology_extraction_statement
      topologyStatement⟩

/--
The package extraction payload is the theorem-shaped statement paired with its
statement-mediated final extractor.
-/
theorem topology_extraction_payload_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    topology_extraction_payload_of_topology_package package =
      ⟨extinction_topology_extraction_statement_of_topology_package package,
        extinction_implies_sphere_of_topology_extraction_statement
          (extinction_topology_extraction_statement_of_topology_package
            package)⟩ := by
  apply Subsingleton.elim

/--
A completed topology package supplies a final extractor paired with the
post-extinction topology derivation certificate for that extractor.
-/
theorem topology_extraction_derivation_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  exact extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
    (extinction_topology_extraction_statement_of_topology_package package)

/--
The package extraction-derivation payload is the forward direction of the
extraction/derivation equivalence for the theorem-shaped package statement.
-/
theorem topology_extraction_derivation_payload_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    topology_extraction_derivation_payload_of_topology_package package =
      extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
        (extinction_topology_extraction_statement_of_topology_package
          package) := by
  apply Subsingleton.elim

/--
A completed topology package extracts the theorem-shaped topology statement,
its fixed-extinction homeomorphism, the full classification sub-obligation
stack, and the homeomorphism assembly/derivation statements from any
finite-extinction input.
-/
theorem topology_extraction_statement_payload_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ _topologyStatement : ExtinctionTopologyExtractionStatement.{u},
    ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
    ∃ _derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism,
    ∃ _classificationSubobligations :
      ExtinctionTopologyClassificationSubobligationsPayload M extinction,
    ∃ _assemblyStatement :
      ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
        homeomorphism,
      ExtinctionTopologyHomeomorphismDerivationStatement M extinction
        homeomorphism := by
  rcases topology_extraction_payload_of_topology_package package with
    ⟨topologyStatement, _extraction⟩
  rcases topology_derivation_statement_payload_of_extraction_statement
      topologyStatement M extinction with
    ⟨homeomorphism, derivationStatement⟩
  let classificationSubobligations :=
    topology_classification_subobligations_of_derivation_statement M
      extinction homeomorphism derivationStatement
  exact ⟨topologyStatement, homeomorphism, derivationStatement,
    classificationSubobligations,
    topology_homeomorphism_assembly_statement_of_derivation_statement M
      extinction homeomorphism derivationStatement,
    topology_homeomorphism_derivation_statement_of_derivation_statement M
      extinction homeomorphism derivationStatement⟩

/--
The fixed-extinction package payload is selected by first exposing the package
topology statement, then destructuring its homeomorphism/derivation payload and
the named derivation subpayload projections.
-/
theorem topology_extraction_statement_payload_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_topology_package
      package M extinction =
      (by
        rcases topology_extraction_payload_of_topology_package package with
          ⟨topologyStatement, _extraction⟩
        rcases topology_derivation_statement_payload_of_extraction_statement
            topologyStatement M extinction with
          ⟨homeomorphism, derivationStatement⟩
        let classificationSubobligations :=
          topology_classification_subobligations_of_derivation_statement M
            extinction homeomorphism derivationStatement
        exact ⟨topologyStatement, homeomorphism, derivationStatement,
          classificationSubobligations,
          topology_homeomorphism_assembly_statement_of_derivation_statement M
            extinction homeomorphism derivationStatement,
          topology_homeomorphism_derivation_statement_of_derivation_statement M
            extinction homeomorphism derivationStatement⟩) := by
  apply Subsingleton.elim

/--
A completed topology package directly exposes the named post-extinction
classification sub-obligation payload for each finite-extinction input.
-/
theorem topology_classification_subobligations_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyClassificationSubobligationsPayload M extinction :=
  topology_classification_subobligations_of_derivation_statement M extinction
    (homeomorphism_of_topology_package package M extinction)
    (extinction_topology_derivation_statement_of_topology_package
      package M extinction)

/--
The package-level topology classification bridge is exactly the derivation
statement bridge applied to the package's projected homeomorphism and
fixed-extinction derivation statement.
-/
theorem topology_classification_subobligations_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_topology_package
        package M extinction =
      topology_classification_subobligations_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package package M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          package M extinction) := by
  apply Subsingleton.elim

/--
Any completed topology extraction package supplies the existing extraction
interface consumed by the final Poincare assembly theorem.
-/
theorem extinction_implies_sphere_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  rcases topology_extraction_payload_of_topology_package package with
    ⟨_topologyStatement, extraction⟩
  exact extraction

/--
The package final extractor agrees with the extractor mediated by the package's
theorem-shaped topology extraction statement.
-/
theorem extinction_implies_sphere_of_topology_package_to_statement_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    extinction_implies_sphere_of_topology_package package =
      extinction_implies_sphere_of_topology_extraction_statement
        (extinction_topology_extraction_statement_of_topology_package
          package) := by
  apply Subsingleton.elim

/--
The final extraction projection agrees with the extractor supplied by the
package-level extraction payload.
-/
theorem extinction_implies_sphere_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    extinction_implies_sphere_of_topology_package package =
      (topology_extraction_payload_of_topology_package package).choose_spec :=
  by
    apply Subsingleton.elim

end Poincare
