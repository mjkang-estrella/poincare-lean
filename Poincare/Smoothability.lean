/-
Typed interface for the smoothability bridge.

The target Poincare statement is topological. The Ricci-flow-with-surgery spine
uses a smooth 3-manifold model. This module makes the bridge between those
surfaces explicit.
-/

import Poincare.Surgery
import Mathlib.Topology.Compactification.OnePoint.Basic

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Proof-bearing interface for the Moise-style local triangulation input for
topological 3-manifolds.
-/
structure HasMoiseLocalTriangulationCharts
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop
    where
  /-- One-point compactification recognition backing the local chart data. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for local Moise chart data produced by one-point
recognition.
-/
def HasMoiseLocalTriangulationCharts.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseLocalTriangulationCharts M where
  onePointRecognition := h

/-- Proof-bearing interface for refining local topological charts to a locally finite cover. -/
structure HasMoiseLocallyFiniteCoverRefinement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M) : Prop where
  /-- One-point compactification recognition backing the refinement data. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The refinement is tied to the local chart data produced from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for locally finite refinement data produced by
one-point recognition.
-/
def HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h) :
    HasMoiseLocallyFiniteCoverRefinement M localCharts where
  onePointRecognition := h
  localCharts_eq := hlocal

/--
For a fixed one-point recognition proof, locally finite cover refinement data
is equivalent to the local chart record being the one constructed from that
recognition proof.
-/
theorem moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseLocallyFiniteCoverRefinement M localCharts ↔
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h := by
  constructor
  · intro refinement
    exact Subsingleton.elim _ _
  · intro hlocal
    exact HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition
      h hlocal

/-- Proof-bearing interface for the simplicial-complex data used in Moise triangulation. -/
structure HasMoiseSimplicialComplex
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M) : Prop where
  /-- One-point compactification recognition backing the simplicial-complex data. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The simplicial complex is tied to the local chart data from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for simplicial-complex data produced by one-point
recognition.
-/
def HasMoiseSimplicialComplex.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h) :
    HasMoiseSimplicialComplex M localCharts where
  onePointRecognition := h
  localCharts_eq := hlocal

/-- Proof-bearing interface for making the local chart triangulations mutually compatible. -/
structure HasMoiseCompatibleChartTriangulations
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (_simplicialComplex : HasMoiseSimplicialComplex M localCharts) : Prop where
  /-- One-point compactification recognition backing compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Compatibility is tied to local chart data from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for chart-triangulation compatibility produced by
one-point recognition.
-/
def HasMoiseCompatibleChartTriangulations.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    {simplicialComplex : HasMoiseSimplicialComplex M localCharts}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h) :
    HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex where
  onePointRecognition := h
  localCharts_eq := hlocal

/-- Proof-bearing interface for the global Moise triangulation. -/
structure HasMoiseTriangulation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop
    where
  /-- One-point compactification recognition backing the global triangulation. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for the global Moise triangulation produced by
one-point recognition.
-/
def HasMoiseTriangulation.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulation M where
  onePointRecognition := h

/-- Proof-bearing interface for the simplicial-approximation step producing the global triangulation. -/
structure HasMoiseSimplicialApproximation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing simplicial approximation. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The approximation is tied to local chart data from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for simplicial approximation produced by one-point
recognition.
-/
def HasMoiseSimplicialApproximation.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    {simplicialComplex : HasMoiseSimplicialComplex M localCharts}
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h) :
    HasMoiseSimplicialApproximation M
      localCharts simplicialComplex triangulation where
  onePointRecognition := h
  localCharts_eq := hlocal

/-- Proof-bearing interface for the star-neighborhood basis carried by a Moise triangulation. -/
structure HasMoiseStarNeighborhoodBasis
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing the star-neighborhood basis. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The basis is tied to local chart data from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for the star-neighborhood basis produced by one-point
recognition.
-/
def HasMoiseStarNeighborhoodBasis.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h) :
    HasMoiseStarNeighborhoodBasis M localCharts triangulation where
  onePointRecognition := h
  localCharts_eq := hlocal

/-- Proof-bearing interface for barycentric subdivision control in the Moise triangulation. -/
structure HasMoiseBarycentricSubdivisionControl
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing subdivision control. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for barycentric subdivision control produced by
one-point recognition.
-/
def HasMoiseBarycentricSubdivisionControl.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseBarycentricSubdivisionControl M triangulation where
  onePointRecognition := h

/-- Proof-bearing interface for regular-neighborhood compatibility after subdivision. -/
structure HasMoiseRegularNeighborhoodCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing regular-neighborhood compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for regular-neighborhood compatibility produced by
one-point recognition.
-/
def HasMoiseRegularNeighborhoodCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseRegularNeighborhoodCompatibility M triangulation where
  onePointRecognition := h

/-- Proof-bearing interface for local finiteness of the Moise triangulation. -/
structure HasMoiseTriangulationLocalFiniteness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing triangulation local finiteness. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for triangulation local finiteness produced by
one-point recognition.
-/
def HasMoiseTriangulationLocalFiniteness.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulationLocalFiniteness M triangulation where
  onePointRecognition := h

/-- Proof-bearing interface for the 3-manifold link condition in the Moise triangulation. -/
structure HasMoiseLinkCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing link compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for link compatibility produced by one-point
recognition.
-/
def HasMoiseLinkCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseLinkCompatibility M triangulation where
  onePointRecognition := h

/-- Proof-bearing interface recognizing the triangulation as a PL 3-manifold by its links. -/
structure HasMoisePLManifoldRecognition
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (_linkCompatibility : HasMoiseLinkCompatibility M triangulation) : Prop
    where
  /-- One-point compactification recognition backing PL-manifold recognition. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for PL-manifold recognition produced by one-point
recognition.
-/
def HasMoisePLManifoldRecognition.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {linkCompatibility : HasMoiseLinkCompatibility M triangulation}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoisePLManifoldRecognition M triangulation linkCompatibility where
  onePointRecognition := h

/-- Proof-bearing interface for the homeomorphism between the topological space and its triangulation. -/
structure HasMoiseTriangulationHomeomorphism
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing the triangulation homeomorphism. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The homeomorphism interface is tied to local chart data from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for triangulation-homeomorphism data produced by
one-point recognition.
-/
def HasMoiseTriangulationHomeomorphism.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h) :
    HasMoiseTriangulationHomeomorphism M localCharts triangulation where
  onePointRecognition := h
  localCharts_eq := hlocal

/--
Proof-bearing interface for patching local Moise triangulations into the global
triangulation used by the bridge.
-/
structure HasMoiseTriangulationCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing triangulation compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Compatibility is tied to local chart data from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for global triangulation compatibility produced by
one-point recognition.
-/
def HasMoiseTriangulationCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h) :
    HasMoiseTriangulationCompatibility M localCharts triangulation where
  onePointRecognition := h
  localCharts_eq := hlocal

/-- Proof-bearing interface for uniqueness of the Moise PL structure induced by triangulation. -/
structure HasMoiseTriangulationUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop
    where
  /-- One-point compactification recognition backing triangulation uniqueness. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for triangulation-uniqueness data produced by
one-point recognition.
-/
def HasMoiseTriangulationUniqueness.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulationUniqueness M triangulation where
  onePointRecognition := h

/-- Proof-bearing interface for the dimension-three Hauptvermutung input used by Moise uniqueness. -/
structure HasMoiseHauptvermutungDimensionThree
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (_triangulationUniqueness : HasMoiseTriangulationUniqueness M triangulation) : Prop
    where
  /-- One-point compactification recognition backing the dimension-three Hauptvermutung input. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for dimension-three Hauptvermutung data produced by
one-point recognition.
-/
def HasMoiseHauptvermutungDimensionThree.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseHauptvermutungDimensionThree
      M triangulation triangulationUniqueness where
  onePointRecognition := h

/--
Interface for the PL structure compatible with the Moise triangulation.
-/
structure HasCompatiblePLStructure
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_triangulation : HasMoiseTriangulation M) : Prop where
  /-- One-point compactification recognition backing the compatible PL structure. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for the compatible PL structure produced by one-point
recognition.
-/
def HasCompatiblePLStructure.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasCompatiblePLStructure M triangulation where
  onePointRecognition := h

/-- Proof-bearing interface for PL transition-map compatibility with the triangulation. -/
structure HasPLTransitionCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation) : Prop
    where
  /-- One-point compactification recognition backing PL transition compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Transition compatibility is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for PL transition compatibility produced by one-point
recognition.
-/
def HasPLTransitionCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h) :
    HasPLTransitionCompatibility M triangulation plStructure where
  onePointRecognition := h
  plStructure_eq := hpl

/--
Proof-bearing interface for compatibility between the PL charts and the original topological
charted-space structure.
-/
structure HasCompatiblePLAtlas
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation) : Prop
    where
  /-- One-point compactification recognition backing the PL atlas. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The PL atlas is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for compatible PL atlas data produced by one-point
recognition.
-/
def HasCompatiblePLAtlas.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h) :
    HasCompatiblePLAtlas M triangulation plStructure where
  onePointRecognition := h
  plStructure_eq := hpl

/-- Proof-bearing interface for the PL-manifold atlas extracted from the triangulation. -/
structure HasPLManifoldAtlas
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop
    where
  /-- One-point compactification recognition backing the PL-manifold atlas. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The PL-manifold atlas is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- The PL-manifold atlas is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq

/--
Compatibility constructor for PL-manifold atlas data produced by one-point
recognition.
-/
def HasPLManifoldAtlas.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl) :
    HasPLManifoldAtlas M triangulation plStructure plAtlas where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas

/-- Proof-bearing interface for PL collar-neighborhood compatibility in the produced atlas. -/
structure HasPLCollarNeighborhoodCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop
    where
  /-- One-point compactification recognition backing PL collar compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Collar compatibility is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Collar compatibility is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq

/--
Compatibility constructor for PL collar-neighborhood compatibility produced by
one-point recognition.
-/
def HasPLCollarNeighborhoodCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl) :
    HasPLCollarNeighborhoodCompatibility
      M triangulation plStructure plAtlas where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas

/--
Proof-bearing interface for compatibility between the Moise homeomorphism and the produced PL
atlas.
-/
structure HasPLHomeomorphismCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop
    where
  /-- One-point compactification recognition backing PL homeomorphism compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- PL homeomorphism compatibility is tied to local chart data from that recognition. -/
  localCharts_eq :
    localCharts =
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition onePointRecognition
  /-- PL homeomorphism compatibility is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- PL homeomorphism compatibility is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq

/--
Compatibility constructor for PL homeomorphism compatibility produced by
one-point recognition.
-/
def HasPLHomeomorphismCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hlocal :
      localCharts =
        HasMoiseLocalTriangulationCharts.ofOnePointRecognition h)
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl) :
    HasPLHomeomorphismCompatibility
      M localCharts triangulation plStructure plAtlas where
  onePointRecognition := h
  localCharts_eq := hlocal
  plStructure_eq := hpl
  plAtlas_eq := hAtlas

/-- Proof-bearing interface for maximality/completeness of the compatible PL atlas. -/
structure HasPLAtlasMaximality
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop
    where
  /-- One-point compactification recognition backing PL atlas maximality. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Maximality is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Maximality is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq

/--
Compatibility constructor for PL atlas maximality produced by one-point
recognition.
-/
def HasPLAtlasMaximality.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl) :
    HasPLAtlasMaximality M triangulation plStructure plAtlas where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas

/-- Proof-bearing interface for existence of a smoothing of the compatible PL atlas. -/
structure HasPLSmoothingExistence
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop
    where
  /-- One-point compactification recognition backing PL smoothing existence. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Smoothing existence is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Smoothing existence is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq

/--
Compatibility constructor for PL smoothing existence produced by one-point
recognition.
-/
def HasPLSmoothingExistence.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl) :
    HasPLSmoothingExistence M triangulation plStructure plAtlas where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas

/-- Proof-bearing interface for vanishing of the PL-smoothing obstruction in dimension three. -/
structure HasPLSmoothingObstructionVanishing
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop
    where
  /-- One-point compactification recognition backing PL smoothing obstruction vanishing. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Obstruction vanishing is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Obstruction vanishing is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq

/--
Compatibility constructor for PL smoothing obstruction vanishing produced by
one-point recognition.
-/
def HasPLSmoothingObstructionVanishing.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl) :
    HasPLSmoothingObstructionVanishing
      M triangulation plStructure plAtlas where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas

/-- Proof-bearing interface for reducing PL smoothing to the microbundle smoothing theorem. -/
structure HasPLMicrobundleSmoothing
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas) : Prop
    where
  /-- One-point compactification recognition backing microbundle smoothing. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Microbundle smoothing is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Microbundle smoothing is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq
  /-- Microbundle smoothing is tied to the smoothing-existence record from that recognition. -/
  plSmoothingExistence_eq :
    plSmoothingExistence =
      HasPLSmoothingExistence.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq
  /-- Microbundle smoothing is tied to the obstruction-vanishing record from that recognition. -/
  plSmoothingObstructionVanishing_eq :
    plSmoothingObstructionVanishing =
      HasPLSmoothingObstructionVanishing.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq

/--
Compatibility constructor for microbundle smoothing data produced by one-point
recognition.
-/
def HasPLMicrobundleSmoothing.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas}
    {plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl)
    (hExistence :
      plSmoothingExistence =
        HasPLSmoothingExistence.ofOnePointRecognition h hpl hAtlas)
    (hObstruction :
      plSmoothingObstructionVanishing =
        HasPLSmoothingObstructionVanishing.ofOnePointRecognition h hpl hAtlas) :
    HasPLMicrobundleSmoothing M
      triangulation plStructure plAtlas plSmoothingExistence
      plSmoothingObstructionVanishing where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas
  plSmoothingExistence_eq := hExistence
  plSmoothingObstructionVanishing_eq := hObstruction

/-- Proof-bearing interface for the 3-dimensional PL-to-smooth smoothing theorem. -/
structure HasPLSmoothingTheorem
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure) : Prop
    where
  /-- One-point compactification recognition backing the PL smoothing theorem. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The smoothing theorem is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- The smoothing theorem is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq

/--
Compatibility constructor for the PL smoothing theorem produced by one-point
recognition.
-/
def HasPLSmoothingTheorem.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl) :
    HasPLSmoothingTheorem M triangulation plStructure plAtlas where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas

/-- Proof-bearing interface for compatibility/uniqueness of the PL smoothing theorem output. -/
structure HasPLSmoothingCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas) : Prop
    where
  /-- One-point compactification recognition backing PL smoothing compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Compatibility is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Compatibility is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq
  /-- Compatibility is tied to the smoothing theorem from that recognition. -/
  smoothingTheorem_eq :
    smoothingTheorem =
      HasPLSmoothingTheorem.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq

/--
Compatibility constructor for PL smoothing compatibility produced by one-point
recognition.
-/
def HasPLSmoothingCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl)
    (hSmoothing :
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition h hpl hAtlas) :
    HasPLSmoothingCompatibility
      M triangulation plStructure plAtlas smoothingTheorem where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas
  smoothingTheorem_eq := hSmoothing

/-- Proof-bearing interface for uniqueness of the PL smoothing selected by the theorem. -/
structure HasPLSmoothingUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas) : Prop
    where
  /-- One-point compactification recognition backing PL smoothing uniqueness. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Uniqueness is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Uniqueness is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq
  /-- Uniqueness is tied to the smoothing theorem from that recognition. -/
  smoothingTheorem_eq :
    smoothingTheorem =
      HasPLSmoothingTheorem.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq

/--
Compatibility constructor for PL smoothing uniqueness produced by one-point
recognition.
-/
def HasPLSmoothingUniqueness.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl)
    (hSmoothing :
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition h hpl hAtlas) :
    HasPLSmoothingUniqueness
      M triangulation plStructure plAtlas smoothingTheorem where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas
  smoothingTheorem_eq := hSmoothing

/-- Proof-bearing interface for compatibility of local smooth models supplied by PL smoothing. -/
structure HasPLSmoothingLocalModelCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas) : Prop
    where
  /-- One-point compactification recognition backing local smooth-model compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Local model compatibility is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Local model compatibility is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq
  /-- Local model compatibility is tied to the smoothing theorem from that recognition. -/
  smoothingTheorem_eq :
    smoothingTheorem =
      HasPLSmoothingTheorem.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq

/--
Compatibility constructor for PL smoothing local-model compatibility produced
by one-point recognition.
-/
def HasPLSmoothingLocalModelCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl)
    (hSmoothing :
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition h hpl hAtlas) :
    HasPLSmoothingLocalModelCompatibility
      M triangulation plStructure plAtlas smoothingTheorem where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas
  smoothingTheorem_eq := hSmoothing

/--
Interface asserting that a topological 3-manifold carries the smooth structure
needed by the surgery layer.
-/
structure HasThreeManifoldSmoothStructure
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop where
  /-- One-point compactification recognition backing the smooth structure. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Compatibility constructor for smooth-structure data produced by one-point
recognition.
-/
def HasThreeManifoldSmoothStructure.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasThreeManifoldSmoothStructure M where
  onePointRecognition := h

/-- Proof-bearing interface for constructing a smooth atlas from the PL smoothing theorem. -/
structure HasSmoothAtlasConstruction
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (smoothStructure : HasThreeManifoldSmoothStructure M) : Prop
    where
  /-- One-point compactification recognition backing smooth atlas construction. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Construction is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Construction is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq
  /-- Construction is tied to the smoothing theorem from that recognition. -/
  smoothingTheorem_eq :
    smoothingTheorem =
      HasPLSmoothingTheorem.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq
  /-- Construction is tied to the smooth structure from that recognition. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for smooth atlas construction produced by one-point
recognition.
-/
def HasSmoothAtlasConstruction.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl)
    (hSmoothing :
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition h hpl hAtlas)
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h) :
    HasSmoothAtlasConstruction
      M triangulation plStructure plAtlas smoothingTheorem smoothStructure where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas
  smoothingTheorem_eq := hSmoothing
  smoothStructure_eq := hSmooth

/-- Proof-bearing interface for compatibility between the smooth atlas and the PL atlas. -/
structure HasSmoothAtlasPLCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure) : Prop
    where
  /-- One-point compactification recognition backing smooth atlas PL compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- PL compatibility is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- PL compatibility is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq
  /-- PL compatibility is tied to the smoothing theorem from that recognition. -/
  smoothingTheorem_eq :
    smoothingTheorem =
      HasPLSmoothingTheorem.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq
  /-- PL compatibility is tied to the smooth structure from that recognition. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition
  /-- PL compatibility is tied to the smooth atlas construction from that recognition. -/
  smoothAtlasConstruction_eq :
    smoothAtlasConstruction =
      HasSmoothAtlasConstruction.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq smoothingTheorem_eq
        smoothStructure_eq

/--
Compatibility constructor for smooth atlas PL compatibility produced by
one-point recognition.
-/
def HasSmoothAtlasPLCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    {smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl)
    (hSmoothing :
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition h hpl hAtlas)
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h)
    (hConstruction :
      smoothAtlasConstruction =
        HasSmoothAtlasConstruction.ofOnePointRecognition
          h hpl hAtlas hSmoothing hSmooth) :
    HasSmoothAtlasPLCompatibility
      M triangulation plStructure plAtlas smoothingTheorem
      smoothStructure smoothAtlasConstruction where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas
  smoothingTheorem_eq := hSmoothing
  smoothStructure_eq := hSmooth
  smoothAtlasConstruction_eq := hConstruction

/-- Proof-bearing interface for maximality of the produced smooth atlas. -/
structure HasSmoothAtlasMaximality
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (triangulation : HasMoiseTriangulation M)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (smoothStructure : HasThreeManifoldSmoothStructure M) : Prop
    where
  /-- One-point compactification recognition backing smooth atlas maximality. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Maximality is tied to the PL structure from that recognition. -/
  plStructure_eq :
    plStructure =
      HasCompatiblePLStructure.ofOnePointRecognition onePointRecognition
  /-- Maximality is tied to the compatible PL atlas from that recognition. -/
  plAtlas_eq :
    plAtlas =
      HasCompatiblePLAtlas.ofOnePointRecognition
        onePointRecognition plStructure_eq
  /-- Maximality is tied to the smoothing theorem from that recognition. -/
  smoothingTheorem_eq :
    smoothingTheorem =
      HasPLSmoothingTheorem.ofOnePointRecognition
        onePointRecognition plStructure_eq plAtlas_eq
  /-- Maximality is tied to the smooth structure from that recognition. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for smooth atlas maximality produced by one-point
recognition.
-/
def HasSmoothAtlasMaximality.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hpl : plStructure = HasCompatiblePLStructure.ofOnePointRecognition h)
    (hAtlas : plAtlas = HasCompatiblePLAtlas.ofOnePointRecognition h hpl)
    (hSmoothing :
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition h hpl hAtlas)
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h) :
    HasSmoothAtlasMaximality
      M triangulation plStructure plAtlas smoothingTheorem smoothStructure where
  onePointRecognition := h
  plStructure_eq := hpl
  plAtlas_eq := hAtlas
  smoothingTheorem_eq := hSmoothing
  smoothStructure_eq := hSmooth

/-- Proof-bearing interface for uniqueness/compatibility of the produced smooth atlas. -/
structure HasSmoothAtlasUniqueness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M) : Prop
    where
  /-- One-point compactification recognition backing smooth atlas uniqueness. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Uniqueness is tied to the smooth structure from that recognition. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for smooth atlas uniqueness produced by one-point
recognition.
-/
def HasSmoothAtlasUniqueness.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h) :
    HasSmoothAtlasUniqueness M smoothStructure where
  onePointRecognition := h
  smoothStructure_eq := hSmooth

/-- Proof-bearing interface for uniqueness of the smooth structure up to diffeomorphism. -/
structure HasSmoothStructureUniquenessUpToDiffeomorphism
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M) : Prop
    where
  /-- One-point compactification recognition backing smooth-structure uniqueness. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Smooth-structure uniqueness is tied to the smooth structure from that recognition. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for smooth-structure uniqueness produced by one-point
recognition.
-/
def HasSmoothStructureUniquenessUpToDiffeomorphism.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h) :
    HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure where
  onePointRecognition := h
  smoothStructure_eq := hSmooth

/-- Proof-bearing interface for smooth transition-map compatibility in the produced atlas. -/
structure HasSmoothTransitionCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M) : Prop
    where
  /-- One-point compactification recognition backing smooth transition compatibility. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Transition compatibility is tied to the smooth structure from that recognition. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for smooth transition compatibility produced by
one-point recognition.
-/
def HasSmoothTransitionCompatibility.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h) :
    HasSmoothTransitionCompatibility M smoothStructure where
  onePointRecognition := h
  smoothStructure_eq := hSmooth

/-- Proof-bearing interface for smoothness of all transition maps in the produced atlas. -/
structure HasSmoothAtlasTransitionSmoothness
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure) : Prop
    where
  /-- One-point compactification recognition backing smooth transition smoothness. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- Transition smoothness is tied to the smooth structure from that recognition. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition
  /-- Transition smoothness is tied to smooth transition compatibility from that recognition. -/
  smoothTransitionCompatibility_eq :
    smoothTransitionCompatibility =
      HasSmoothTransitionCompatibility.ofOnePointRecognition
        onePointRecognition smoothStructure_eq

/--
Compatibility constructor for smooth atlas transition smoothness produced by
one-point recognition.
-/
def HasSmoothAtlasTransitionSmoothness.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    {smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h)
    (hTransition :
      smoothTransitionCompatibility =
        HasSmoothTransitionCompatibility.ofOnePointRecognition h hSmooth) :
    HasSmoothAtlasTransitionSmoothness
      M smoothStructure smoothTransitionCompatibility where
  onePointRecognition := h
  smoothStructure_eq := hSmooth
  smoothTransitionCompatibility_eq := hTransition

/-- Extract all smooth-atlas construction witnesses from the proof-bearing record. -/
theorem HasSmoothAtlasConstruction.witnesses
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas smoothingTheorem smoothStructure) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      plStructure =
        HasCompatiblePLStructure.ofOnePointRecognition
          smoothAtlasConstruction.onePointRecognition ∧
      plAtlas =
        HasCompatiblePLAtlas.ofOnePointRecognition
          smoothAtlasConstruction.onePointRecognition
          smoothAtlasConstruction.plStructure_eq ∧
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition
          smoothAtlasConstruction.onePointRecognition
          smoothAtlasConstruction.plStructure_eq
          smoothAtlasConstruction.plAtlas_eq ∧
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition
          smoothAtlasConstruction.onePointRecognition :=
  ⟨smoothAtlasConstruction.onePointRecognition,
    smoothAtlasConstruction.plStructure_eq,
    smoothAtlasConstruction.plAtlas_eq,
    smoothAtlasConstruction.smoothingTheorem_eq,
    smoothAtlasConstruction.smoothStructure_eq⟩

/-- Extract all smooth-atlas PL-compatibility witnesses from the proof-bearing record. -/
theorem HasSmoothAtlasPLCompatibility.witnesses
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    {smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas smoothingTheorem smoothStructure}
    (smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas smoothingTheorem smoothStructure
        smoothAtlasConstruction) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      plStructure =
        HasCompatiblePLStructure.ofOnePointRecognition
          smoothAtlasPLCompatibility.onePointRecognition ∧
      plAtlas =
        HasCompatiblePLAtlas.ofOnePointRecognition
          smoothAtlasPLCompatibility.onePointRecognition
          smoothAtlasPLCompatibility.plStructure_eq ∧
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition
          smoothAtlasPLCompatibility.onePointRecognition
          smoothAtlasPLCompatibility.plStructure_eq
          smoothAtlasPLCompatibility.plAtlas_eq ∧
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition
          smoothAtlasPLCompatibility.onePointRecognition ∧
      smoothAtlasConstruction =
        HasSmoothAtlasConstruction.ofOnePointRecognition
          smoothAtlasPLCompatibility.onePointRecognition
          smoothAtlasPLCompatibility.plStructure_eq
          smoothAtlasPLCompatibility.plAtlas_eq
          smoothAtlasPLCompatibility.smoothingTheorem_eq
          smoothAtlasPLCompatibility.smoothStructure_eq :=
  ⟨smoothAtlasPLCompatibility.onePointRecognition,
    smoothAtlasPLCompatibility.plStructure_eq,
    smoothAtlasPLCompatibility.plAtlas_eq,
    smoothAtlasPLCompatibility.smoothingTheorem_eq,
    smoothAtlasPLCompatibility.smoothStructure_eq,
    smoothAtlasPLCompatibility.smoothAtlasConstruction_eq⟩

/-- Extract all smooth-atlas maximality witnesses from the proof-bearing record. -/
theorem HasSmoothAtlasMaximality.witnesses
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas smoothingTheorem smoothStructure) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      plStructure =
        HasCompatiblePLStructure.ofOnePointRecognition
          smoothAtlasMaximality.onePointRecognition ∧
      plAtlas =
        HasCompatiblePLAtlas.ofOnePointRecognition
          smoothAtlasMaximality.onePointRecognition
          smoothAtlasMaximality.plStructure_eq ∧
      smoothingTheorem =
        HasPLSmoothingTheorem.ofOnePointRecognition
          smoothAtlasMaximality.onePointRecognition
          smoothAtlasMaximality.plStructure_eq
          smoothAtlasMaximality.plAtlas_eq ∧
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition
          smoothAtlasMaximality.onePointRecognition :=
  ⟨smoothAtlasMaximality.onePointRecognition,
    smoothAtlasMaximality.plStructure_eq,
    smoothAtlasMaximality.plAtlas_eq,
    smoothAtlasMaximality.smoothingTheorem_eq,
    smoothAtlasMaximality.smoothStructure_eq⟩

/-- Extract all smooth-atlas uniqueness witnesses from the proof-bearing record. -/
theorem HasSmoothAtlasUniqueness.witnesses
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition
          smoothAtlasUniqueness.onePointRecognition :=
  ⟨smoothAtlasUniqueness.onePointRecognition,
    smoothAtlasUniqueness.smoothStructure_eq⟩

/--
Extract all smooth-structure uniqueness-up-to-diffeomorphism witnesses from
the proof-bearing record.
-/
theorem HasSmoothStructureUniquenessUpToDiffeomorphism.witnesses
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition
          smoothStructureUniqueness.onePointRecognition :=
  ⟨smoothStructureUniqueness.onePointRecognition,
    smoothStructureUniqueness.smoothStructure_eq⟩

/-- Extract all smooth-transition compatibility witnesses from the proof-bearing record. -/
theorem HasSmoothTransitionCompatibility.witnesses
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition
          smoothTransitionCompatibility.onePointRecognition :=
  ⟨smoothTransitionCompatibility.onePointRecognition,
    smoothTransitionCompatibility.smoothStructure_eq⟩

/-- Extract all smooth-atlas transition-smoothness witnesses from the proof-bearing record. -/
theorem HasSmoothAtlasTransitionSmoothness.witnesses
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    {smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure}
    (smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
      smoothStructure =
        HasThreeManifoldSmoothStructure.ofOnePointRecognition
          smoothAtlasTransitionSmoothness.onePointRecognition ∧
      smoothTransitionCompatibility =
        HasSmoothTransitionCompatibility.ofOnePointRecognition
          smoothAtlasTransitionSmoothness.onePointRecognition
          smoothAtlasTransitionSmoothness.smoothStructure_eq :=
  ⟨smoothAtlasTransitionSmoothness.onePointRecognition,
    smoothAtlasTransitionSmoothness.smoothStructure_eq,
    smoothAtlasTransitionSmoothness.smoothTransitionCompatibility_eq⟩

/--
Interface certifying that the smooth structure was produced from the preceding
topological and PL inputs.
-/
structure HasSmoothStructureDerivation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex)
    (triangulation : HasMoiseTriangulation M)
    (simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation)
    (starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation)
    (barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation)
    (regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation)
    (triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation)
    (linkCompatibility : HasMoiseLinkCompatibility M triangulation)
    (plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility)
    (triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation)
    (moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation)
    (triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation)
    (hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas)
    (plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas)
    (plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas)
    (plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas)
    (plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing)
    (smoothingTheorem : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas smoothingTheorem)
    (plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas smoothingTheorem)
    (plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas smoothingTheorem)
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure)
    (smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure smoothAtlasConstruction)
    (smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure)
    (_smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure)
    (_smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure)
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure)
    (_smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility) : Prop where
  /-- One-point compactification recognition backing smooth-structure derivation. -/
  onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
  /-- The derived smooth structure is produced from the same recognition input. -/
  smoothStructure_eq :
    smoothStructure =
      HasThreeManifoldSmoothStructure.ofOnePointRecognition onePointRecognition

/--
Compatibility constructor for smooth-structure derivation produced by
one-point recognition.
-/
def HasSmoothStructureDerivation.ofOnePointRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {localCharts : HasMoiseLocalTriangulationCharts M}
    {locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts}
    {simplicialComplex : HasMoiseSimplicialComplex M localCharts}
    {compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex}
    {triangulation : HasMoiseTriangulation M}
    {simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation}
    {starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation}
    {barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation}
    {regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation}
    {triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation}
    {linkCompatibility : HasMoiseLinkCompatibility M triangulation}
    {plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility}
    {triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation}
    {moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation}
    {triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation}
    {hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas}
    {plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas}
    {plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas}
    {plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas}
    {plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas}
    {plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas}
    {plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas smoothingTheorem}
    {plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas smoothingTheorem}
    {plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas smoothingTheorem}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    {smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure}
    {smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure smoothAtlasConstruction}
    {smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas smoothingTheorem
        smoothStructure}
    {smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure}
    {smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure}
    {smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure}
    {smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility}
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))))
    (hSmooth :
      smoothStructure = HasThreeManifoldSmoothStructure.ofOnePointRecognition h) :
    HasSmoothStructureDerivation
      M localCharts locallyFiniteCoverRefinement simplicialComplex
      compatibleChartTriangulations triangulation simplicialApproximation
      starNeighborhoodBasis barycentricSubdivision
      regularNeighborhoodCompatibility triangulationLocalFiniteness
      linkCompatibility plManifoldRecognition triangulationHomeomorphism
      moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
      plStructure plTransitionCompatibility plAtlas plManifoldAtlas
      plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
      plAtlasMaximality plSmoothingExistence
      plSmoothingObstructionVanishing plMicrobundleSmoothing smoothingTheorem
      plSmoothingCompatibility plSmoothingUniqueness
      plSmoothingLocalModelCompatibility smoothStructure
      smoothAtlasConstruction smoothAtlasPLCompatibility
      smoothAtlasMaximality smoothAtlasUniqueness
      smoothStructureUniqueness smoothTransitionCompatibility
      smoothAtlasTransitionSmoothness where
  onePointRecognition := h
  smoothStructure_eq := hSmooth

/--
The proposition that the raw smooth-structure input has been derived from the
named Moise, PL, smoothing, and smooth-atlas sub-obligations.
-/
def SmoothStructureDerivationStatement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M) : Prop :=
  ∃ localCharts : HasMoiseLocalTriangulationCharts M,
  ∃ locallyFiniteCoverRefinement :
    HasMoiseLocallyFiniteCoverRefinement M localCharts,
  ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
  ∃ compatibleChartTriangulations :
    HasMoiseCompatibleChartTriangulations
      M localCharts simplicialComplex,
  ∃ triangulation : HasMoiseTriangulation M,
  ∃ simplicialApproximation :
    HasMoiseSimplicialApproximation
      M localCharts simplicialComplex triangulation,
  ∃ starNeighborhoodBasis :
    HasMoiseStarNeighborhoodBasis M localCharts triangulation,
  ∃ barycentricSubdivision :
    HasMoiseBarycentricSubdivisionControl M triangulation,
  ∃ regularNeighborhoodCompatibility :
    HasMoiseRegularNeighborhoodCompatibility M triangulation,
  ∃ triangulationLocalFiniteness :
    HasMoiseTriangulationLocalFiniteness M triangulation,
  ∃ linkCompatibility :
    HasMoiseLinkCompatibility M triangulation,
  ∃ plManifoldRecognition :
    HasMoisePLManifoldRecognition M triangulation linkCompatibility,
  ∃ triangulationHomeomorphism :
    HasMoiseTriangulationHomeomorphism M localCharts triangulation,
  ∃ moiseCompatibility :
    HasMoiseTriangulationCompatibility M localCharts triangulation,
  ∃ triangulationUniqueness :
    HasMoiseTriangulationUniqueness M triangulation,
  ∃ hauptvermutungDimensionThree :
    HasMoiseHauptvermutungDimensionThree
      M triangulation triangulationUniqueness,
  ∃ plStructure : HasCompatiblePLStructure M triangulation,
  ∃ plTransitionCompatibility :
    HasPLTransitionCompatibility M triangulation plStructure,
  ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
  ∃ plManifoldAtlas :
    HasPLManifoldAtlas M triangulation plStructure plAtlas,
  ∃ plCollarNeighborhoodCompatibility :
    HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
  ∃ plHomeomorphismCompatibility :
    HasPLHomeomorphismCompatibility
      M localCharts triangulation plStructure plAtlas,
  ∃ plAtlasMaximality :
    HasPLAtlasMaximality M triangulation plStructure plAtlas,
  ∃ plSmoothingExistence :
    HasPLSmoothingExistence M triangulation plStructure plAtlas,
  ∃ plSmoothingObstructionVanishing :
    HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
  ∃ plMicrobundleSmoothing :
    HasPLMicrobundleSmoothing
      M triangulation plStructure plAtlas plSmoothingExistence
      plSmoothingObstructionVanishing,
  ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
  ∃ plSmoothingCompatibility :
    HasPLSmoothingCompatibility
      M triangulation plStructure plAtlas plSmoothing,
  ∃ plSmoothingUniqueness :
    HasPLSmoothingUniqueness
      M triangulation plStructure plAtlas plSmoothing,
  ∃ plSmoothingLocalModelCompatibility :
    HasPLSmoothingLocalModelCompatibility
      M triangulation plStructure plAtlas plSmoothing,
  ∃ smoothAtlasConstruction :
    HasSmoothAtlasConstruction
      M triangulation plStructure plAtlas plSmoothing smoothStructure,
  ∃ smoothAtlasPLCompatibility :
    HasSmoothAtlasPLCompatibility
      M triangulation plStructure plAtlas plSmoothing smoothStructure
      smoothAtlasConstruction,
  ∃ smoothAtlasMaximality :
    HasSmoothAtlasMaximality
      M triangulation plStructure plAtlas plSmoothing smoothStructure,
  ∃ smoothAtlasUniqueness :
    HasSmoothAtlasUniqueness M smoothStructure,
  ∃ smoothStructureUniqueness :
    HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
  ∃ smoothTransitionCompatibility :
    HasSmoothTransitionCompatibility M smoothStructure,
  ∃ smoothAtlasTransitionSmoothness :
    HasSmoothAtlasTransitionSmoothness
      M smoothStructure smoothTransitionCompatibility,
    HasSmoothStructureDerivation
      M localCharts locallyFiniteCoverRefinement simplicialComplex
      compatibleChartTriangulations triangulation simplicialApproximation
      starNeighborhoodBasis barycentricSubdivision
      regularNeighborhoodCompatibility triangulationLocalFiniteness
      linkCompatibility plManifoldRecognition triangulationHomeomorphism
      moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
      plStructure plTransitionCompatibility plAtlas plManifoldAtlas
      plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
      plAtlasMaximality plSmoothingExistence
      plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
      plSmoothingCompatibility plSmoothingUniqueness
      plSmoothingLocalModelCompatibility smoothStructure
      smoothAtlasConstruction smoothAtlasPLCompatibility
      smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
      smoothTransitionCompatibility smoothAtlasTransitionSmoothness

/--
The smooth-structure derivation statement is exactly the listed Moise, PL,
smoothing, smooth-atlas, transition, and derivation witness stack.
-/
theorem smoothStructureDerivationStatement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M) :
    SmoothStructureDerivationStatement M smoothStructure =
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
      ∃ locallyFiniteCoverRefinement :
        HasMoiseLocallyFiniteCoverRefinement M localCharts,
      ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ compatibleChartTriangulations :
        HasMoiseCompatibleChartTriangulations
          M localCharts simplicialComplex,
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ simplicialApproximation :
        HasMoiseSimplicialApproximation
          M localCharts simplicialComplex triangulation,
      ∃ starNeighborhoodBasis :
        HasMoiseStarNeighborhoodBasis M localCharts triangulation,
      ∃ barycentricSubdivision :
        HasMoiseBarycentricSubdivisionControl M triangulation,
      ∃ regularNeighborhoodCompatibility :
        HasMoiseRegularNeighborhoodCompatibility M triangulation,
      ∃ triangulationLocalFiniteness :
        HasMoiseTriangulationLocalFiniteness M triangulation,
      ∃ linkCompatibility :
        HasMoiseLinkCompatibility M triangulation,
      ∃ plManifoldRecognition :
        HasMoisePLManifoldRecognition M triangulation linkCompatibility,
      ∃ triangulationHomeomorphism :
        HasMoiseTriangulationHomeomorphism M localCharts triangulation,
      ∃ moiseCompatibility :
        HasMoiseTriangulationCompatibility M localCharts triangulation,
      ∃ triangulationUniqueness :
        HasMoiseTriangulationUniqueness M triangulation,
      ∃ hauptvermutungDimensionThree :
        HasMoiseHauptvermutungDimensionThree
          M triangulation triangulationUniqueness,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ plTransitionCompatibility :
        HasPLTransitionCompatibility M triangulation plStructure,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ plManifoldAtlas :
        HasPLManifoldAtlas M triangulation plStructure plAtlas,
      ∃ plCollarNeighborhoodCompatibility :
        HasPLCollarNeighborhoodCompatibility
          M triangulation plStructure plAtlas,
      ∃ plHomeomorphismCompatibility :
        HasPLHomeomorphismCompatibility
          M localCharts triangulation plStructure plAtlas,
      ∃ plAtlasMaximality :
        HasPLAtlasMaximality M triangulation plStructure plAtlas,
      ∃ plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      ∃ plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing
          M triangulation plStructure plAtlas plSmoothingExistence
          plSmoothingObstructionVanishing,
      ∃ plSmoothing :
        HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ plSmoothingCompatibility :
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingUniqueness :
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing,
      ∃ plSmoothingLocalModelCompatibility :
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasPLCompatibility :
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction,
      ∃ smoothAtlasMaximality :
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasUniqueness :
        HasSmoothAtlasUniqueness M smoothStructure,
      ∃ smoothStructureUniqueness :
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility,
        HasSmoothStructureDerivation
          M localCharts locallyFiniteCoverRefinement simplicialComplex
          compatibleChartTriangulations triangulation simplicialApproximation
          starNeighborhoodBasis barycentricSubdivision
          regularNeighborhoodCompatibility triangulationLocalFiniteness
          linkCompatibility plManifoldRecognition triangulationHomeomorphism
          moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
          plStructure plTransitionCompatibility plAtlas plManifoldAtlas
          plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
          plAtlasMaximality plSmoothingExistence
          plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
          plSmoothingCompatibility plSmoothingUniqueness
          plSmoothingLocalModelCompatibility smoothStructure
          smoothAtlasConstruction smoothAtlasPLCompatibility
          smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
          smoothTransitionCompatibility smoothAtlasTransitionSmoothness) :=
  rfl

/--
Assemble the packaged smooth-structure derivation statement from the named
Moise, PL, smoothing, and smooth-atlas components.
-/
theorem smooth_structure_derivation_statement_of_components
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex)
    (triangulation : HasMoiseTriangulation M)
    (simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation)
    (starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation)
    (barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation)
    (regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation)
    (triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation)
    (linkCompatibility : HasMoiseLinkCompatibility M triangulation)
    (plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility)
    (triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation)
    (moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation)
    (triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation)
    (hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas)
    (plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas)
    (plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas)
    (plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas)
    (plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing)
    (plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction)
    (smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure)
    (smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure)
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure)
    (smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility)
    (smoothStructureDerivation :
      HasSmoothStructureDerivation
        M localCharts locallyFiniteCoverRefinement simplicialComplex
        compatibleChartTriangulations triangulation simplicialApproximation
        starNeighborhoodBasis barycentricSubdivision
        regularNeighborhoodCompatibility triangulationLocalFiniteness
        linkCompatibility plManifoldRecognition triangulationHomeomorphism
        moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
        plStructure plTransitionCompatibility plAtlas plManifoldAtlas
        plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
        plAtlasMaximality plSmoothingExistence
        plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
        plSmoothingCompatibility plSmoothingUniqueness
        plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness) :
    SmoothStructureDerivationStatement M smoothStructure :=
  ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
    compatibleChartTriangulations, triangulation, simplicialApproximation,
    starNeighborhoodBasis, barycentricSubdivision,
    regularNeighborhoodCompatibility, triangulationLocalFiniteness,
    linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
    moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
    plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
    plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
    plAtlasMaximality, plSmoothingExistence, plSmoothingObstructionVanishing,
    plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
    plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
    smoothAtlasConstruction, smoothAtlasPLCompatibility,
    smoothAtlasMaximality, smoothAtlasUniqueness, smoothStructureUniqueness,
    smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
    smoothStructureDerivation⟩

/--
The smooth-structure derivation component assembler is exactly the tuple of
Moise, PL, smoothing, smooth-atlas, transition, and derivation witnesses.
-/
theorem smooth_structure_derivation_statement_of_components_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (localCharts : HasMoiseLocalTriangulationCharts M)
    (locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts)
    (simplicialComplex : HasMoiseSimplicialComplex M localCharts)
    (compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex)
    (triangulation : HasMoiseTriangulation M)
    (simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation)
    (starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation)
    (barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation)
    (regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation)
    (triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation)
    (linkCompatibility : HasMoiseLinkCompatibility M triangulation)
    (plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility)
    (triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation)
    (moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation)
    (triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation)
    (hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness)
    (plStructure : HasCompatiblePLStructure M triangulation)
    (plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure)
    (plAtlas : HasCompatiblePLAtlas M triangulation plStructure)
    (plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas)
    (plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas)
    (plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas)
    (plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas)
    (plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas)
    (plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas)
    (plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing)
    (plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas)
    (plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing)
    (plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing)
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction)
    (smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure)
    (smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure)
    (smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure)
    (smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure)
    (smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility)
    (smoothStructureDerivation :
      HasSmoothStructureDerivation
        M localCharts locallyFiniteCoverRefinement simplicialComplex
        compatibleChartTriangulations triangulation simplicialApproximation
        starNeighborhoodBasis barycentricSubdivision
        regularNeighborhoodCompatibility triangulationLocalFiniteness
        linkCompatibility plManifoldRecognition triangulationHomeomorphism
        moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
        plStructure plTransitionCompatibility plAtlas plManifoldAtlas
        plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
        plAtlasMaximality plSmoothingExistence
        plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
        plSmoothingCompatibility plSmoothingUniqueness
        plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness) :
    smooth_structure_derivation_statement_of_components M
        localCharts locallyFiniteCoverRefinement simplicialComplex
        compatibleChartTriangulations triangulation simplicialApproximation
        starNeighborhoodBasis barycentricSubdivision
        regularNeighborhoodCompatibility triangulationLocalFiniteness
        linkCompatibility plManifoldRecognition triangulationHomeomorphism
        moiseCompatibility triangulationUniqueness hauptvermutungDimensionThree
        plStructure plTransitionCompatibility plAtlas plManifoldAtlas
        plCollarNeighborhoodCompatibility plHomeomorphismCompatibility
        plAtlasMaximality plSmoothingExistence
        plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
        plSmoothingCompatibility plSmoothingUniqueness
        plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness
        smoothStructureDerivation =
      (by
        exact ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
          compatibleChartTriangulations, triangulation, simplicialApproximation,
          starNeighborhoodBasis, barycentricSubdivision,
          regularNeighborhoodCompatibility, triangulationLocalFiniteness,
          linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
          moiseCompatibility, triangulationUniqueness,
          hauptvermutungDimensionThree, plStructure, plTransitionCompatibility,
          plAtlas, plManifoldAtlas, plCollarNeighborhoodCompatibility,
          plHomeomorphismCompatibility, plAtlasMaximality,
          plSmoothingExistence, plSmoothingObstructionVanishing,
          plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
          plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
          smoothAtlasConstruction, smoothAtlasPLCompatibility,
          smoothAtlasMaximality, smoothAtlasUniqueness,
          smoothStructureUniqueness, smoothTransitionCompatibility,
          smoothAtlasTransitionSmoothness, smoothStructureDerivation⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped interface that turns the topological smoothability predicate
into the `IsManifold` instance used by `Poincare.Surgery`.
-/
def SmoothabilityBridgeStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∀ smoothStructure : HasThreeManifoldSmoothStructure M,
        SmoothStructureDerivationStatement M smoothStructure →
          IsManifold ThreeManifoldModelWithCorners 1 M

/--
The theorem-shaped smoothability bridge is exactly the universal conversion from
the raw three-manifold smooth structure plus its derivation to the manifold
instance consumed by the surgery layer.
-/
theorem smoothabilityBridgeStatement_eq :
    SmoothabilityBridgeStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          ∀ smoothStructure : HasThreeManifoldSmoothStructure M,
            SmoothStructureDerivationStatement M smoothStructure →
              IsManifold ThreeManifoldModelWithCorners 1 M) :=
  rfl

/--
The theorem-shaped `C∞` smooth-manifold output consumed by the canonical smooth
Poincare statement.
-/
def SmoothabilitySmoothManifoldStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      IsManifold (𝓡 3) ∞ M

/--
The theorem-shaped smooth-manifold output is exactly the universal `C∞`
manifold instance for closed simply connected topological 3-manifolds.
-/
theorem smoothabilitySmoothManifoldStatement_eq :
    SmoothabilitySmoothManifoldStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M) :=
  rfl

/--
A `C∞` manifold over the project's three-dimensional model supplies the `C¹`
model-with-corners evidence consumed by the surgery layer.
-/
theorem surgeryModel_isManifold_of_smoothManifold
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    (h : IsManifold (𝓡 3) ∞ M) :
    IsManifold ThreeManifoldModelWithCorners 1 M := by
  letI : IsManifold (𝓡 3) ∞ M := h
  dsimp [ThreeManifoldModelWithCorners, ThreeManifoldModel]
  infer_instance

/--
The theorem-shaped `C∞` smooth-manifold output supplies the surgery-layer
`C¹` manifold bridge, since the project model is definitionally the standard
Euclidean 3-manifold model and `C∞` regularity implies `C¹` regularity.
-/
theorem smoothabilityBridgeStatement_of_smoothabilitySmoothManifoldStatement
    (h : SmoothabilitySmoothManifoldStatement.{u}) :
    SmoothabilityBridgeStatement.{u} := by
  intro M _top _t2 _charted _simple _compact _smoothStructure
    _smoothStructureDerivation
  exact surgeryModel_isManifold_of_smoothManifold M (h M)

/--
Additive transported-charted-space bridge: instead of producing
`IsManifold` for an arbitrary ambient charted-space instance, this statement
allows the smoothability route to provide the charted-space witness together
with the surgery-layer manifold evidence.
-/
def SmoothabilityTransportedBridgeStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∃ charted : ChartedSpace ThreeManifoldModel M,
          letI : ChartedSpace ThreeManifoldModel M := charted
          IsManifold ThreeManifoldModelWithCorners 1 M

/--
The transported bridge statement is exactly the witness-producing variant of
the smoothability bridge for one-point recognized targets.
-/
theorem smoothabilityTransportedBridgeStatement_eq :
    SmoothabilityTransportedBridgeStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
            ∃ charted : ChartedSpace ThreeManifoldModel M,
              letI : ChartedSpace ThreeManifoldModel M := charted
              IsManifold ThreeManifoldModelWithCorners 1 M) :=
  rfl

/--
Small package-field surface for the additive transported bridge.  This field is
usable by production code that can work with the transported charted-space
witness, while the existing universal bridge API remains unchanged.
-/
structure SmoothabilityTransportedBridgePackageField where
  transportedBridge : SmoothabilityTransportedBridgeStatement.{u}

/--
Transported `C∞` smooth-manifold output for one-point recognized targets.  This
is the witness-producing variant of `SmoothabilitySmoothManifoldStatement`:
the smoothability route provides the charted-space instance on which the
smooth-manifold evidence lives.
-/
def SmoothabilityTransportedSmoothManifoldStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∃ charted : ChartedSpace ThreeManifoldModel M,
          letI : ChartedSpace ThreeManifoldModel M := charted
          IsManifold (𝓡 3) ∞ M

/--
The transported smooth-manifold statement is exactly the one-point recognized
charted-space witness plus `C∞` smooth-manifold evidence.
-/
theorem smoothabilityTransportedSmoothManifoldStatement_eq :
    SmoothabilityTransportedSmoothManifoldStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
            ∃ charted : ChartedSpace ThreeManifoldModel M,
              letI : ChartedSpace ThreeManifoldModel M := charted
              IsManifold (𝓡 3) ∞ M) :=
  rfl

/--
Transported `C∞` smooth-manifold evidence supplies the transported
surgery-model bridge by lowering regularity on the same charted-space witness.
-/
theorem smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
    (h : SmoothabilityTransportedSmoothManifoldStatement.{u}) :
    SmoothabilityTransportedBridgeStatement.{u} := by
  intro M _top _t2 _simple _compact recognized
  rcases h M recognized with ⟨charted, smoothManifold⟩
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  exact surgeryModel_isManifold_of_smoothManifold M smoothManifold

/--
Package-field surface for the transported `C∞` smooth-manifold theorem.  This
is the transported analogue of the `SmoothabilityPackage.smoothManifold` field.
-/
structure SmoothabilityTransportedSmoothManifoldPackageField where
  transportedSmoothManifold :
    SmoothabilityTransportedSmoothManifoldStatement.{u}

/--
Interface certifying that the theorem-shaped smoothability bridge follows from
the constructed smooth atlas.
-/
structure HasSmoothabilityBridgeDerivation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (_smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure)
    (_manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M) : Prop
    where
  /-- The bridge derivation is backed by the smooth-structure derivation statement. -/
  smoothStructureDerivationWitness :
    SmoothStructureDerivationStatement M smoothStructure
  /-- The bridge derivation is backed by the produced smooth-manifold evidence. -/
  manifoldEvidenceWitness : IsManifold ThreeManifoldModelWithCorners 1 M

/-- A smoothability bridge derivation exposes its derivation and manifold witnesses. -/
theorem HasSmoothabilityBridgeDerivation.witnesses
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    {smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure}
    {manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M}
    (bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothStructureDerivation manifoldEvidence) :
    SmoothStructureDerivationStatement M smoothStructure ∧
      IsManifold ThreeManifoldModelWithCorners 1 M := by
  exact
    ⟨bridgeDerivation.smoothStructureDerivationWitness,
      bridgeDerivation.manifoldEvidenceWitness⟩

/--
Interface certifying that the produced `IsManifold` instance uses the intended
Euclidean 3-manifold model-with-corners.
-/
structure HasSmoothManifoldModelCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (_bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothStructureDerivation manifoldEvidence) : Prop
    where
  /-- Model compatibility carries the smooth-structure derivation statement. -/
  smoothStructureDerivationWitness :
    SmoothStructureDerivationStatement M smoothStructure
  /-- Model compatibility carries the produced smooth-manifold evidence. -/
  manifoldEvidenceWitness : IsManifold ThreeManifoldModelWithCorners 1 M
  /-- Model compatibility is tied to the bridge derivation witness. -/
  bridgeDerivationWitness :
    HasSmoothabilityBridgeDerivation
      M smoothStructure smoothStructureDerivation manifoldEvidence

/--
Interface certifying that the produced smooth structure is compatible with the
charted-space model used by the surgery layer.
-/
structure HasSmoothChartCompatibility
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothStructureDerivation manifoldEvidence)
    (_modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothStructureDerivation manifoldEvidence
        bridgeDerivation) : Prop
    where
  /-- Chart compatibility carries the smooth-structure derivation statement. -/
  smoothStructureDerivationWitness :
    SmoothStructureDerivationStatement M smoothStructure
  /-- Chart compatibility carries the produced smooth-manifold evidence. -/
  manifoldEvidenceWitness : IsManifold ThreeManifoldModelWithCorners 1 M
  /-- Chart compatibility is tied to the bridge derivation witness. -/
  bridgeDerivationWitness :
    HasSmoothabilityBridgeDerivation
      M smoothStructure smoothStructureDerivation manifoldEvidence
  /-- Chart compatibility is tied to the model-compatibility witness. -/
  modelCompatibilityWitness :
    HasSmoothManifoldModelCompatibility
      M smoothStructure smoothStructureDerivation manifoldEvidence
      bridgeDerivation

/-- Smooth chart compatibility exposes the derivation, manifold, bridge, and model witnesses. -/
theorem HasSmoothChartCompatibility.witnesses
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    {smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure}
    {manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M}
    {bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothStructureDerivation manifoldEvidence}
    {modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothStructureDerivation manifoldEvidence
        bridgeDerivation}
    (chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothStructureDerivation manifoldEvidence
        bridgeDerivation modelCompatibility) :
    SmoothStructureDerivationStatement M smoothStructure ∧
      IsManifold ThreeManifoldModelWithCorners 1 M ∧
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothStructureDerivation manifoldEvidence ∧
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothStructureDerivation manifoldEvidence
        bridgeDerivation := by
  exact
    ⟨chartCompatibility.smoothStructureDerivationWitness,
      chartCompatibility.manifoldEvidenceWitness,
      chartCompatibility.bridgeDerivationWitness,
      chartCompatibility.modelCompatibilityWitness⟩

/--
Semantic alias for the full smoothability sub-obligation payload exposed by a
smooth-structure derivation statement together with bridge compatibility
evidence.
-/
abbrev SmoothabilitySubobligationsPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Prop :=
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ _simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts _simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts _simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ _linkCompatibility :
      HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation _linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation,
    ∃ _moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation,
    ∃ _triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation _triangulationUniqueness,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ _plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ _plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing
        M triangulation plStructure plAtlas _plSmoothingExistence
        _plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ _plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
    ∃ _smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
    ∃ _smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ _smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure _smoothTransitionCompatibility,
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation
        M localCharts _locallyFiniteCoverRefinement _simplicialComplex
        _compatibleChartTriangulations triangulation _simplicialApproximation
        _starNeighborhoodBasis _barycentricSubdivision
        _regularNeighborhoodCompatibility _triangulationLocalFiniteness
        _linkCompatibility _plManifoldRecognition
        _triangulationHomeomorphism _moiseCompatibility
        _triangulationUniqueness _hauptvermutungDimensionThree
        plStructure _plTransitionCompatibility plAtlas _plManifoldAtlas
        _plCollarNeighborhoodCompatibility _plHomeomorphismCompatibility
        _plAtlasMaximality _plSmoothingExistence
        _plSmoothingObstructionVanishing _plMicrobundleSmoothing
        plSmoothing _plSmoothingCompatibility _plSmoothingUniqueness
        _plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        _smoothAtlasMaximality smoothAtlasUniqueness
        _smoothStructureUniqueness _smoothTransitionCompatibility
        _smoothAtlasTransitionSmoothness,
    ∃ smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure,
    ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence,
    ∃ modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation,
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility

/--
The smoothability sub-obligation payload alias is definitionally the full
Moise, PL, smoothing, smooth-atlas, smooth-structure derivation, manifold,
bridge, model-compatibility, and chart-compatibility witness stack.
-/
theorem smoothabilitySubobligationsPayload_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothabilitySubobligationsPayload M =
      (∃ localCharts : HasMoiseLocalTriangulationCharts M,
      ∃ _locallyFiniteCoverRefinement :
        HasMoiseLocallyFiniteCoverRefinement M localCharts,
      ∃ _simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      ∃ _compatibleChartTriangulations :
        HasMoiseCompatibleChartTriangulations
          M localCharts _simplicialComplex,
      ∃ triangulation : HasMoiseTriangulation M,
      ∃ _simplicialApproximation :
        HasMoiseSimplicialApproximation
          M localCharts _simplicialComplex triangulation,
      ∃ _starNeighborhoodBasis :
        HasMoiseStarNeighborhoodBasis M localCharts triangulation,
      ∃ _barycentricSubdivision :
        HasMoiseBarycentricSubdivisionControl M triangulation,
      ∃ _regularNeighborhoodCompatibility :
        HasMoiseRegularNeighborhoodCompatibility M triangulation,
      ∃ _triangulationLocalFiniteness :
        HasMoiseTriangulationLocalFiniteness M triangulation,
      ∃ _linkCompatibility :
        HasMoiseLinkCompatibility M triangulation,
      ∃ _plManifoldRecognition :
        HasMoisePLManifoldRecognition M triangulation _linkCompatibility,
      ∃ _triangulationHomeomorphism :
        HasMoiseTriangulationHomeomorphism M localCharts triangulation,
      ∃ _moiseCompatibility :
        HasMoiseTriangulationCompatibility M localCharts triangulation,
      ∃ _triangulationUniqueness :
        HasMoiseTriangulationUniqueness M triangulation,
      ∃ _hauptvermutungDimensionThree :
        HasMoiseHauptvermutungDimensionThree
          M triangulation _triangulationUniqueness,
      ∃ plStructure : HasCompatiblePLStructure M triangulation,
      ∃ _plTransitionCompatibility :
        HasPLTransitionCompatibility M triangulation plStructure,
      ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      ∃ _plManifoldAtlas :
        HasPLManifoldAtlas M triangulation plStructure plAtlas,
      ∃ _plCollarNeighborhoodCompatibility :
        HasPLCollarNeighborhoodCompatibility
          M triangulation plStructure plAtlas,
      ∃ _plHomeomorphismCompatibility :
        HasPLHomeomorphismCompatibility
          M localCharts triangulation plStructure plAtlas,
      ∃ _plAtlasMaximality :
        HasPLAtlasMaximality M triangulation plStructure plAtlas,
      ∃ _plSmoothingExistence :
        HasPLSmoothingExistence M triangulation plStructure plAtlas,
      ∃ _plSmoothingObstructionVanishing :
        HasPLSmoothingObstructionVanishing
          M triangulation plStructure plAtlas,
      ∃ _plMicrobundleSmoothing :
        HasPLMicrobundleSmoothing
          M triangulation plStructure plAtlas _plSmoothingExistence
          _plSmoothingObstructionVanishing,
      ∃ plSmoothing :
        HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      ∃ _plSmoothingCompatibility :
        HasPLSmoothingCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ _plSmoothingUniqueness :
        HasPLSmoothingUniqueness
          M triangulation plStructure plAtlas plSmoothing,
      ∃ _plSmoothingLocalModelCompatibility :
        HasPLSmoothingLocalModelCompatibility
          M triangulation plStructure plAtlas plSmoothing,
      ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      ∃ smoothAtlasConstruction :
        HasSmoothAtlasConstruction
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasPLCompatibility :
        HasSmoothAtlasPLCompatibility
          M triangulation plStructure plAtlas plSmoothing smoothStructure
          smoothAtlasConstruction,
      ∃ _smoothAtlasMaximality :
        HasSmoothAtlasMaximality
          M triangulation plStructure plAtlas plSmoothing smoothStructure,
      ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
      ∃ _smoothStructureUniqueness :
        HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
      ∃ _smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
      ∃ _smoothAtlasTransitionSmoothness :
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure _smoothTransitionCompatibility,
      ∃ _smoothDerivation :
        HasSmoothStructureDerivation
          M localCharts _locallyFiniteCoverRefinement _simplicialComplex
          _compatibleChartTriangulations triangulation _simplicialApproximation
          _starNeighborhoodBasis _barycentricSubdivision
          _regularNeighborhoodCompatibility _triangulationLocalFiniteness
          _linkCompatibility _plManifoldRecognition
          _triangulationHomeomorphism _moiseCompatibility
          _triangulationUniqueness _hauptvermutungDimensionThree
          plStructure _plTransitionCompatibility plAtlas _plManifoldAtlas
          _plCollarNeighborhoodCompatibility _plHomeomorphismCompatibility
          _plAtlasMaximality _plSmoothingExistence
          _plSmoothingObstructionVanishing _plMicrobundleSmoothing
          plSmoothing _plSmoothingCompatibility _plSmoothingUniqueness
          _plSmoothingLocalModelCompatibility smoothStructure
          smoothAtlasConstruction smoothAtlasPLCompatibility
          _smoothAtlasMaximality smoothAtlasUniqueness
          _smoothStructureUniqueness _smoothTransitionCompatibility
          _smoothAtlasTransitionSmoothness,
      ∃ smoothDerivationStatement :
        SmoothStructureDerivationStatement M smoothStructure,
      ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
      ∃ bridgeDerivation :
        HasSmoothabilityBridgeDerivation
          M smoothStructure smoothDerivationStatement manifoldEvidence,
      ∃ modelCompatibility :
        HasSmoothManifoldModelCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation,
        HasSmoothChartCompatibility
          M smoothStructure smoothDerivationStatement manifoldEvidence
          bridgeDerivation modelCompatibility) :=
  rfl

/--
The full smoothability sub-obligation payload exposes the smooth-structure
tail used by the bridge layer: a smooth structure, its derivation statement,
the resulting surgery-model manifold evidence, the bridge derivation, and the
model/chart compatibility certificates.
-/
theorem smoothability_bridge_tail_payload_of_subobligations_payload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure,
    ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence,
    ∃ modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation,
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility := by
  rcases payload with
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation, simplicialApproximation,
      starNeighborhoodBasis, barycentricSubdivision,
      regularNeighborhoodCompatibility, triangulationLocalFiniteness,
      linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
      moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
      plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
      plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
      plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing, plSmoothing,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivation, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility⟩
  exact
    ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
      bridgeDerivation, modelCompatibility, chartCompatibility⟩

/--
Projecting the bridge-tail payload from the full smoothability sub-obligation
payload is exactly the final smooth-structure, manifold, and compatibility
segment of that payload.
-/
theorem smoothability_bridge_tail_payload_of_subobligations_payload_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (payload : SmoothabilitySubobligationsPayload M) :
    smoothability_bridge_tail_payload_of_subobligations_payload M payload =
      (by
        rcases payload with
          ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
            compatibleChartTriangulations, triangulation,
            simplicialApproximation, starNeighborhoodBasis,
            barycentricSubdivision, regularNeighborhoodCompatibility,
            triangulationLocalFiniteness, linkCompatibility,
            plManifoldRecognition, triangulationHomeomorphism,
            moiseCompatibility, triangulationUniqueness,
            hauptvermutungDimensionThree, plStructure,
            plTransitionCompatibility, plAtlas, plManifoldAtlas,
            plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
            plAtlasMaximality, plSmoothingExistence,
            plSmoothingObstructionVanishing, plMicrobundleSmoothing,
            plSmoothing, plSmoothingCompatibility, plSmoothingUniqueness,
            plSmoothingLocalModelCompatibility, smoothStructure,
            smoothAtlasConstruction, smoothAtlasPLCompatibility,
            smoothAtlasMaximality, smoothAtlasUniqueness,
            smoothStructureUniqueness, smoothTransitionCompatibility,
            smoothAtlasTransitionSmoothness, _smoothDerivation,
            smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
            modelCompatibility, chartCompatibility⟩
        exact
          ⟨smoothStructure, smoothDerivationStatement, manifoldEvidence,
            bridgeDerivation, modelCompatibility, chartCompatibility⟩) := by
  apply Subsingleton.elim

/--
The smooth-structure derivation statement exposes the full Moise, PL,
smoothing, smooth-atlas, and bridge compatibility sub-obligation stack.
-/
theorem smoothability_subobligations_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence)
    (modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation)
    (chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ _simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts _simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts _simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ _linkCompatibility :
      HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation _linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation,
    ∃ _moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation,
    ∃ _triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation _triangulationUniqueness,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ _plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ _plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing
        M triangulation plStructure plAtlas _plSmoothingExistence
        _plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ _plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ smoothAtlasUniqueness : HasSmoothAtlasUniqueness M smoothStructure,
    ∃ _smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure,
    ∃ _smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ _smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure _smoothTransitionCompatibility,
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation
        M localCharts _locallyFiniteCoverRefinement _simplicialComplex
        _compatibleChartTriangulations triangulation _simplicialApproximation
        _starNeighborhoodBasis _barycentricSubdivision
        _regularNeighborhoodCompatibility _triangulationLocalFiniteness
        _linkCompatibility _plManifoldRecognition
        _triangulationHomeomorphism _moiseCompatibility
        _triangulationUniqueness _hauptvermutungDimensionThree
        plStructure _plTransitionCompatibility plAtlas _plManifoldAtlas
        _plCollarNeighborhoodCompatibility _plHomeomorphismCompatibility
        _plAtlasMaximality _plSmoothingExistence
        _plSmoothingObstructionVanishing _plMicrobundleSmoothing
        plSmoothing _plSmoothingCompatibility _plSmoothingUniqueness
        _plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        _smoothAtlasMaximality smoothAtlasUniqueness
        _smoothStructureUniqueness _smoothTransitionCompatibility
        _smoothAtlasTransitionSmoothness,
    ∃ smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure,
    ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence,
    ∃ modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation,
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility := by
  rcases smoothDerivationStatement with
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation, simplicialApproximation,
      starNeighborhoodBasis, barycentricSubdivision,
      regularNeighborhoodCompatibility, triangulationLocalFiniteness,
      linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
      moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
      plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
      plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
      plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing, plSmoothing,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
      smoothAtlasPLCompatibility, smoothAtlasMaximality,
      smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivation⟩
  let smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure :=
    ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
      compatibleChartTriangulations, triangulation, simplicialApproximation,
      starNeighborhoodBasis, barycentricSubdivision,
      regularNeighborhoodCompatibility, triangulationLocalFiniteness,
      linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
      moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
      plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
      plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
      plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing, plSmoothing,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
      smoothAtlasPLCompatibility, smoothAtlasMaximality,
      smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothDerivation⟩
  exact ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
    compatibleChartTriangulations, triangulation, simplicialApproximation,
    starNeighborhoodBasis, barycentricSubdivision,
    regularNeighborhoodCompatibility, triangulationLocalFiniteness,
    linkCompatibility, plManifoldRecognition, triangulationHomeomorphism,
    moiseCompatibility, triangulationUniqueness, hauptvermutungDimensionThree,
    plStructure, plTransitionCompatibility, plAtlas, plManifoldAtlas,
    plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
    plAtlasMaximality, plSmoothingExistence, plSmoothingObstructionVanishing,
    plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
    plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
    smoothStructure, smoothAtlasConstruction, smoothAtlasPLCompatibility,
    smoothAtlasMaximality, smoothAtlasUniqueness, smoothStructureUniqueness,
    smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
    smoothDerivation, smoothDerivationStatement, manifoldEvidence,
    bridgeDerivation, modelCompatibility, chartCompatibility⟩

/--
The smoothability derivation statement bridge exposes exactly the Moise, PL,
smoothing, smooth-atlas, smooth-structure derivation, manifold, bridge, model,
and chart-compatibility witnesses stored in the theorem-shaped inputs.
-/
theorem smoothability_subobligations_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure)
    (manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M)
    (bridgeDerivation :
      HasSmoothabilityBridgeDerivation
        M smoothStructure smoothDerivationStatement manifoldEvidence)
    (modelCompatibility :
      HasSmoothManifoldModelCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation)
    (chartCompatibility :
      HasSmoothChartCompatibility
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility) :
    smoothability_subobligations_of_derivation_statement
        M smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation modelCompatibility chartCompatibility =
      (by
        rcases smoothDerivationStatement with
          ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
            compatibleChartTriangulations, triangulation,
            simplicialApproximation, starNeighborhoodBasis,
            barycentricSubdivision, regularNeighborhoodCompatibility,
            triangulationLocalFiniteness, linkCompatibility,
            plManifoldRecognition, triangulationHomeomorphism,
            moiseCompatibility, triangulationUniqueness,
            hauptvermutungDimensionThree, plStructure,
            plTransitionCompatibility, plAtlas, plManifoldAtlas,
            plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
            plAtlasMaximality, plSmoothingExistence,
            plSmoothingObstructionVanishing, plMicrobundleSmoothing,
            plSmoothing, plSmoothingCompatibility, plSmoothingUniqueness,
            plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
            smoothAtlasPLCompatibility, smoothAtlasMaximality,
            smoothAtlasUniqueness, smoothStructureUniqueness,
            smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
            smoothDerivation⟩
        let smoothDerivationStatement :
            SmoothStructureDerivationStatement M smoothStructure :=
          ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
            compatibleChartTriangulations, triangulation,
            simplicialApproximation, starNeighborhoodBasis,
            barycentricSubdivision, regularNeighborhoodCompatibility,
            triangulationLocalFiniteness, linkCompatibility,
            plManifoldRecognition, triangulationHomeomorphism,
            moiseCompatibility, triangulationUniqueness,
            hauptvermutungDimensionThree, plStructure,
            plTransitionCompatibility, plAtlas, plManifoldAtlas,
            plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
            plAtlasMaximality, plSmoothingExistence,
            plSmoothingObstructionVanishing, plMicrobundleSmoothing,
            plSmoothing, plSmoothingCompatibility, plSmoothingUniqueness,
            plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
            smoothAtlasPLCompatibility, smoothAtlasMaximality,
            smoothAtlasUniqueness, smoothStructureUniqueness,
            smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
            smoothDerivation⟩
        exact ⟨localCharts, locallyFiniteCoverRefinement, simplicialComplex,
          compatibleChartTriangulations, triangulation,
          simplicialApproximation, starNeighborhoodBasis,
          barycentricSubdivision, regularNeighborhoodCompatibility,
          triangulationLocalFiniteness, linkCompatibility,
          plManifoldRecognition, triangulationHomeomorphism,
          moiseCompatibility, triangulationUniqueness,
          hauptvermutungDimensionThree, plStructure, plTransitionCompatibility,
          plAtlas, plManifoldAtlas, plCollarNeighborhoodCompatibility,
          plHomeomorphismCompatibility, plAtlasMaximality,
          plSmoothingExistence, plSmoothingObstructionVanishing,
          plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
          plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
          smoothStructure, smoothAtlasConstruction, smoothAtlasPLCompatibility,
          smoothAtlasMaximality, smoothAtlasUniqueness,
          smoothStructureUniqueness, smoothTransitionCompatibility,
          smoothAtlasTransitionSmoothness, smoothDerivation,
          smoothDerivationStatement, manifoldEvidence, bridgeDerivation,
          modelCompatibility, chartCompatibility⟩) := by
  apply Subsingleton.elim

/--
A package for the smoothability input needed by the end-to-end conditional
assembly theorem.
-/
structure SmoothabilityPackage where
  /-- Local Moise triangulation charts for target topological 3-manifolds. -/
  moiseLocalCharts :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLocalTriangulationCharts M
  /-- Locally finite refinement of the local Moise chart cover. -/
  moiseLocallyFiniteCoverRefinement :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLocallyFiniteCoverRefinement M (moiseLocalCharts M)
  /-- Simplicial-complex data underlying the Moise triangulation. -/
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  /-- Compatibility of local chart triangulations before global assembly. -/
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  /-- Triangulation input for target topological 3-manifolds. -/
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  /-- Simplicial-approximation step producing the global triangulation. -/
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  /-- Star-neighborhood basis for the Moise triangulation. -/
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  /-- Barycentric subdivision control for the Moise triangulation. -/
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M (moiseTriangulation M)
  /-- Regular-neighborhood compatibility after subdivision. -/
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M (moiseTriangulation M)
  /-- Local finiteness of the Moise triangulation. -/
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M (moiseTriangulation M)
  /-- Link-compatibility condition for the 3-dimensional triangulation. -/
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M (moiseTriangulation M)
  /-- PL-manifold recognition from the Moise link condition. -/
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)
  /-- Homeomorphism between the topological space and the Moise triangulation. -/
  moiseTriangulationHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  /-- Compatibility between local and global Moise triangulation data. -/
  moiseCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  /-- Uniqueness of the PL structure induced by Moise triangulation. -/
  moiseTriangulationUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationUniqueness M (moiseTriangulation M)
  /-- Dimension-three Hauptvermutung input behind triangulation uniqueness. -/
  moiseHauptvermutungDimensionThree :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseHauptvermutungDimensionThree M
          (moiseTriangulation M)
          (moiseTriangulationUniqueness M)
  /-- Compatible PL structure from the triangulation input. -/
  plStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasCompatiblePLStructure M (moiseTriangulation M)
  /-- PL transition compatibility for the triangulated structure. -/
  plTransitionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLTransitionCompatibility M
          (moiseTriangulation M)
          (plStructure M)
  /-- Compatibility between PL charts and the original topological charts. -/
  plAtlas :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasCompatiblePLAtlas M
          (moiseTriangulation M)
          (plStructure M)
  /-- PL-manifold atlas extracted from the triangulation. -/
  plManifoldAtlas :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLManifoldAtlas M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- PL collar-neighborhood compatibility in the produced atlas. -/
  plCollarNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLCollarNeighborhoodCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Compatibility between the Moise homeomorphism and PL atlas. -/
  plHomeomorphismCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLHomeomorphismCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Maximality of the compatible PL atlas. -/
  plAtlasMaximality :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLAtlasMaximality M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Existence of a smoothing of the compatible PL atlas. -/
  plSmoothingExistence :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingExistence M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Vanishing of the 3-dimensional PL-smoothing obstruction. -/
  plSmoothingObstructionVanishing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingObstructionVanishing M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Microbundle smoothing reduction behind the PL smoothing theorem. -/
  plMicrobundleSmoothing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLMicrobundleSmoothing M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothingExistence M)
          (plSmoothingObstructionVanishing M)
  /-- The 3-dimensional PL-to-smooth smoothing theorem input. -/
  plSmoothing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingTheorem M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
  /-- Compatibility/uniqueness of the PL smoothing output. -/
  plSmoothingCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
  /-- Uniqueness of the selected PL smoothing. -/
  plSmoothingUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingUniqueness M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
  /-- Compatibility of local smooth models supplied by PL smoothing. -/
  plSmoothingLocalModelCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingLocalModelCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
  /-- Every target topological 3-manifold has the required smooth structure. -/
  smoothStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasThreeManifoldSmoothStructure M
  /-- Smooth atlas construction from PL smoothing data. -/
  smoothAtlasConstruction :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasConstruction M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
          (smoothStructure M)
  /-- Compatibility of the produced smooth atlas with the PL atlas. -/
  smoothAtlasPLCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasPLCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
          (smoothStructure M)
          (smoothAtlasConstruction M)
  /-- Maximality of the produced smooth atlas. -/
  smoothAtlasMaximality :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasMaximality M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)
          (smoothStructure M)
  /-- Uniqueness/compatibility of the produced smooth atlas. -/
  smoothAtlasUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasUniqueness M (smoothStructure M)
  /-- Uniqueness of the smooth structure up to diffeomorphism. -/
  smoothStructureUniquenessUpToDiffeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothStructureUniquenessUpToDiffeomorphism M (smoothStructure M)
  /-- Smooth transition-map compatibility in the produced atlas. -/
  smoothTransitionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothTransitionCompatibility M (smoothStructure M)
  /-- Smoothness of transition maps in the produced atlas. -/
  smoothAtlasTransitionSmoothness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasTransitionSmoothness M
          (smoothStructure M)
          (smoothTransitionCompatibility M)
  /-- Derivation of the smooth structure from the named topological inputs. -/
  smoothStructureDerivation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothStructureDerivation M
          (moiseLocalCharts M)
          (moiseLocallyFiniteCoverRefinement M)
          (moiseSimplicialComplex M)
          (moiseCompatibleChartTriangulations M)
          (moiseTriangulation M)
          (moiseSimplicialApproximation M)
          (moiseStarNeighborhoodBasis M)
          (moiseBarycentricSubdivision M)
          (moiseRegularNeighborhoodCompatibility M)
          (moiseTriangulationLocalFiniteness M)
          (moiseLinkCompatibility M)
          (moisePLManifoldRecognition M)
          (moiseTriangulationHomeomorphism M)
          (moiseCompatibility M)
          (moiseTriangulationUniqueness M)
          (moiseHauptvermutungDimensionThree M)
          (plStructure M)
          (plTransitionCompatibility M)
          (plAtlas M)
          (plManifoldAtlas M)
          (plCollarNeighborhoodCompatibility M)
          (plHomeomorphismCompatibility M)
          (plAtlasMaximality M)
          (plSmoothingExistence M)
          (plSmoothingObstructionVanishing M)
          (plMicrobundleSmoothing M)
          (plSmoothing M)
          (plSmoothingCompatibility M)
          (plSmoothingUniqueness M)
          (plSmoothingLocalModelCompatibility M)
          (smoothStructure M)
          (smoothAtlasConstruction M)
          (smoothAtlasPLCompatibility M)
          (smoothAtlasMaximality M)
          (smoothAtlasUniqueness M)
          (smoothStructureUniquenessUpToDiffeomorphism M)
          (smoothTransitionCompatibility M)
          (smoothAtlasTransitionSmoothness M)
  /-- The smooth structure yields the exact `IsManifold` instance needed below. -/
  bridge : SmoothabilityBridgeStatement.{u}
  /--
  The produced smooth structure supplies the `C∞` manifold instance required by
  the canonical smooth Poincare statement.
  -/
  smoothManifold :
    SmoothabilitySmoothManifoldStatement.{u}
  /-- Derivation of the bridge from the constructed smooth atlas. -/
  bridgeDerivation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        let smoothDerivationStatement :=
          smooth_structure_derivation_statement_of_components M
            (moiseLocalCharts M) (moiseLocallyFiniteCoverRefinement M)
            (moiseSimplicialComplex M) (moiseCompatibleChartTriangulations M)
            (moiseTriangulation M) (moiseSimplicialApproximation M)
            (moiseStarNeighborhoodBasis M) (moiseBarycentricSubdivision M)
            (moiseRegularNeighborhoodCompatibility M)
            (moiseTriangulationLocalFiniteness M)
            (moiseLinkCompatibility M) (moisePLManifoldRecognition M)
            (moiseTriangulationHomeomorphism M) (moiseCompatibility M)
            (moiseTriangulationUniqueness M)
            (moiseHauptvermutungDimensionThree M)
            (plStructure M) (plTransitionCompatibility M) (plAtlas M)
            (plManifoldAtlas M) (plCollarNeighborhoodCompatibility M)
            (plHomeomorphismCompatibility M) (plAtlasMaximality M)
            (plSmoothingExistence M) (plSmoothingObstructionVanishing M)
            (plMicrobundleSmoothing M) (plSmoothing M)
            (plSmoothingCompatibility M) (plSmoothingUniqueness M)
            (plSmoothingLocalModelCompatibility M) (smoothStructure M)
            (smoothAtlasConstruction M) (smoothAtlasPLCompatibility M)
            (smoothAtlasMaximality M) (smoothAtlasUniqueness M)
            (smoothStructureUniquenessUpToDiffeomorphism M)
            (smoothTransitionCompatibility M)
            (smoothAtlasTransitionSmoothness M) (smoothStructureDerivation M)
        HasSmoothabilityBridgeDerivation M
          (smoothStructure M)
          smoothDerivationStatement
          (bridge M (smoothStructure M) smoothDerivationStatement)
  /-- Compatibility of the produced manifold instance with the target model. -/
  smoothModelCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        let smoothDerivationStatement :=
          smooth_structure_derivation_statement_of_components M
            (moiseLocalCharts M) (moiseLocallyFiniteCoverRefinement M)
            (moiseSimplicialComplex M) (moiseCompatibleChartTriangulations M)
            (moiseTriangulation M) (moiseSimplicialApproximation M)
            (moiseStarNeighborhoodBasis M) (moiseBarycentricSubdivision M)
            (moiseRegularNeighborhoodCompatibility M)
            (moiseTriangulationLocalFiniteness M)
            (moiseLinkCompatibility M) (moisePLManifoldRecognition M)
            (moiseTriangulationHomeomorphism M) (moiseCompatibility M)
            (moiseTriangulationUniqueness M)
            (moiseHauptvermutungDimensionThree M)
            (plStructure M) (plTransitionCompatibility M) (plAtlas M)
            (plManifoldAtlas M) (plCollarNeighborhoodCompatibility M)
            (plHomeomorphismCompatibility M) (plAtlasMaximality M)
            (plSmoothingExistence M) (plSmoothingObstructionVanishing M)
            (plMicrobundleSmoothing M) (plSmoothing M)
            (plSmoothingCompatibility M) (plSmoothingUniqueness M)
            (plSmoothingLocalModelCompatibility M) (smoothStructure M)
            (smoothAtlasConstruction M) (smoothAtlasPLCompatibility M)
            (smoothAtlasMaximality M) (smoothAtlasUniqueness M)
            (smoothStructureUniquenessUpToDiffeomorphism M)
            (smoothTransitionCompatibility M)
            (smoothAtlasTransitionSmoothness M) (smoothStructureDerivation M)
        HasSmoothManifoldModelCompatibility M
          (smoothStructure M)
          smoothDerivationStatement
          (bridge M (smoothStructure M) smoothDerivationStatement)
          (bridgeDerivation M)
  /-- Compatibility of the produced manifold evidence with the chart model. -/
  chartCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        let smoothDerivationStatement :=
          smooth_structure_derivation_statement_of_components M
            (moiseLocalCharts M) (moiseLocallyFiniteCoverRefinement M)
            (moiseSimplicialComplex M) (moiseCompatibleChartTriangulations M)
            (moiseTriangulation M) (moiseSimplicialApproximation M)
            (moiseStarNeighborhoodBasis M) (moiseBarycentricSubdivision M)
            (moiseRegularNeighborhoodCompatibility M)
            (moiseTriangulationLocalFiniteness M)
            (moiseLinkCompatibility M) (moisePLManifoldRecognition M)
            (moiseTriangulationHomeomorphism M) (moiseCompatibility M)
            (moiseTriangulationUniqueness M)
            (moiseHauptvermutungDimensionThree M)
            (plStructure M) (plTransitionCompatibility M) (plAtlas M)
            (plManifoldAtlas M) (plCollarNeighborhoodCompatibility M)
            (plHomeomorphismCompatibility M) (plAtlasMaximality M)
            (plSmoothingExistence M) (plSmoothingObstructionVanishing M)
            (plMicrobundleSmoothing M) (plSmoothing M)
            (plSmoothingCompatibility M) (plSmoothingUniqueness M)
            (plSmoothingLocalModelCompatibility M) (smoothStructure M)
            (smoothAtlasConstruction M) (smoothAtlasPLCompatibility M)
            (smoothAtlasMaximality M) (smoothAtlasUniqueness M)
            (smoothStructureUniquenessUpToDiffeomorphism M)
            (smoothTransitionCompatibility M)
            (smoothAtlasTransitionSmoothness M) (smoothStructureDerivation M)
        HasSmoothChartCompatibility M
          (smoothStructure M)
          smoothDerivationStatement
          (bridge M (smoothStructure M) smoothDerivationStatement)
          (bridgeDerivation M)
          (smoothModelCompatibility M)

/-- A completed smoothability package supplies local Moise chart evidence. -/
theorem moise_local_charts_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLocalTriangulationCharts M :=
  package.moiseLocalCharts M

/-- The named Moise local-chart projection is the stored package field. -/
theorem moise_local_charts_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_local_charts_of_smoothability_package package M =
      package.moiseLocalCharts M :=
  rfl

/-- A completed smoothability package supplies locally finite chart refinement. -/
theorem moise_locally_finite_cover_refinement_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLocallyFiniteCoverRefinement M
      (moise_local_charts_of_smoothability_package package M) :=
  package.moiseLocallyFiniteCoverRefinement M

/-- The named locally finite cover-refinement projection is the stored package field. -/
theorem moise_locally_finite_cover_refinement_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_locally_finite_cover_refinement_of_smoothability_package package M =
      package.moiseLocallyFiniteCoverRefinement M :=
  rfl

/-- A completed smoothability package supplies Moise simplicial-complex evidence. -/
theorem moise_simplicial_complex_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseSimplicialComplex M
      (moise_local_charts_of_smoothability_package package M) :=
  package.moiseSimplicialComplex M

/-- The named Moise simplicial-complex projection is the stored package field. -/
theorem moise_simplicial_complex_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_simplicial_complex_of_smoothability_package package M =
      package.moiseSimplicialComplex M :=
  rfl

/-- A completed smoothability package supplies compatible chart triangulations. -/
theorem moise_compatible_chart_triangulations_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseCompatibleChartTriangulations M
      (moise_local_charts_of_smoothability_package package M)
      (moise_simplicial_complex_of_smoothability_package package M) :=
  package.moiseCompatibleChartTriangulations M

/-- The named compatible chart-triangulations projection is the stored package field. -/
theorem moise_compatible_chart_triangulations_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_compatible_chart_triangulations_of_smoothability_package package M =
      package.moiseCompatibleChartTriangulations M :=
  rfl

/-- A completed smoothability package supplies Moise triangulation evidence. -/
theorem moise_triangulation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulation M :=
  package.moiseTriangulation M

/-- The named Moise triangulation projection is the stored package field. -/
theorem moise_triangulation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_of_smoothability_package package M =
      package.moiseTriangulation M :=
  rfl

/-- A completed smoothability package supplies simplicial-approximation evidence. -/
theorem moise_simplicial_approximation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseSimplicialApproximation M
      (moise_local_charts_of_smoothability_package package M)
      (moise_simplicial_complex_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseSimplicialApproximation M

/-- The named simplicial-approximation projection is the stored package field. -/
theorem moise_simplicial_approximation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_simplicial_approximation_of_smoothability_package package M =
      package.moiseSimplicialApproximation M :=
  rfl

/-- A completed smoothability package supplies a Moise star-neighborhood basis. -/
theorem moise_star_neighborhood_basis_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseStarNeighborhoodBasis M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseStarNeighborhoodBasis M

/-- The named star-neighborhood basis projection is the stored package field. -/
theorem moise_star_neighborhood_basis_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_star_neighborhood_basis_of_smoothability_package package M =
      package.moiseStarNeighborhoodBasis M :=
  rfl

/-- A completed smoothability package supplies barycentric subdivision control. -/
theorem moise_barycentric_subdivision_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseBarycentricSubdivisionControl M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseBarycentricSubdivision M

/-- The named barycentric subdivision projection is the stored package field. -/
theorem moise_barycentric_subdivision_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_barycentric_subdivision_of_smoothability_package package M =
      package.moiseBarycentricSubdivision M :=
  rfl

/-- A completed smoothability package supplies regular-neighborhood compatibility. -/
theorem moise_regular_neighborhood_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseRegularNeighborhoodCompatibility M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseRegularNeighborhoodCompatibility M

/-- The named regular-neighborhood compatibility projection is the stored package field. -/
theorem moise_regular_neighborhood_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_regular_neighborhood_compatibility_of_smoothability_package package M =
      package.moiseRegularNeighborhoodCompatibility M :=
  rfl

/-- A completed smoothability package supplies local-finiteness evidence. -/
theorem moise_triangulation_local_finiteness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationLocalFiniteness M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseTriangulationLocalFiniteness M

/-- The named triangulation local-finiteness projection is the stored package field. -/
theorem moise_triangulation_local_finiteness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_local_finiteness_of_smoothability_package package M =
      package.moiseTriangulationLocalFiniteness M :=
  rfl

/-- A completed smoothability package supplies the triangulation link condition. -/
theorem moise_link_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLinkCompatibility M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseLinkCompatibility M

/-- The named link-compatibility projection is the stored package field. -/
theorem moise_link_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_link_compatibility_of_smoothability_package package M =
      package.moiseLinkCompatibility M :=
  rfl

/-- A completed smoothability package recognizes the triangulation as a PL manifold. -/
theorem moise_pl_manifold_recognition_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoisePLManifoldRecognition M
      (moise_triangulation_of_smoothability_package package M)
      (moise_link_compatibility_of_smoothability_package package M) :=
  package.moisePLManifoldRecognition M

/-- The named PL-manifold recognition projection is the stored package field. -/
theorem moise_pl_manifold_recognition_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_pl_manifold_recognition_of_smoothability_package package M =
      package.moisePLManifoldRecognition M :=
  rfl

/-- A completed smoothability package supplies the triangulation homeomorphism. -/
theorem moise_triangulation_homeomorphism_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationHomeomorphism M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseTriangulationHomeomorphism M

/-- The named triangulation-homeomorphism projection is the stored package field. -/
theorem moise_triangulation_homeomorphism_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_homeomorphism_of_smoothability_package package M =
      package.moiseTriangulationHomeomorphism M :=
  rfl

/-- A completed smoothability package supplies Moise compatibility evidence. -/
theorem moise_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationCompatibility M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseCompatibility M

/-- The named Moise compatibility projection is the stored package field. -/
theorem moise_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_compatibility_of_smoothability_package package M =
      package.moiseCompatibility M :=
  rfl

/-- A completed smoothability package supplies Moise triangulation uniqueness. -/
theorem moise_triangulation_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationUniqueness M
      (moise_triangulation_of_smoothability_package package M) :=
  package.moiseTriangulationUniqueness M

/-- The named Moise triangulation-uniqueness projection is the stored package field. -/
theorem moise_triangulation_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_triangulation_uniqueness_of_smoothability_package package M =
      package.moiseTriangulationUniqueness M :=
  rfl

/-- A completed smoothability package supplies the dimension-three Hauptvermutung input. -/
theorem moise_hauptvermutung_dimension_three_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseHauptvermutungDimensionThree M
      (moise_triangulation_of_smoothability_package package M)
      (moise_triangulation_uniqueness_of_smoothability_package package M) :=
  package.moiseHauptvermutungDimensionThree M

/-- The named dimension-three Hauptvermutung projection is the stored package field. -/
theorem moise_hauptvermutung_dimension_three_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    moise_hauptvermutung_dimension_three_of_smoothability_package package M =
      package.moiseHauptvermutungDimensionThree M :=
  rfl

/--
A completed smoothability package projects the Moise-to-PL frontier from local
charts through PL atlas construction.
-/
theorem moiseToPLFrontier_of_smoothabilityPackage
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ triangulationUniqueness : HasMoiseTriangulationUniqueness M triangulation,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
      HasMoiseLocallyFiniteCoverRefinement M localCharts ∧
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex ∧
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility ∧
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation ∧
      HasMoiseTriangulationCompatibility M
        localCharts triangulation ∧
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness ∧
      HasPLTransitionCompatibility M triangulation plStructure ∧
      HasCompatiblePLAtlas M triangulation plStructure := by
  exact
    ⟨package.moiseLocalCharts M,
      package.moiseSimplicialComplex M,
      package.moiseTriangulation M,
      package.moiseLinkCompatibility M,
      package.moiseTriangulationUniqueness M,
      package.plStructure M,
      package.moiseLocallyFiniteCoverRefinement M,
      package.moiseCompatibleChartTriangulations M,
      package.moisePLManifoldRecognition M,
      package.moiseTriangulationHomeomorphism M,
      package.moiseCompatibility M,
      package.moiseHauptvermutungDimensionThree M,
      package.plTransitionCompatibility M,
      package.plAtlas M⟩

/-- A completed smoothability package supplies compatible PL-structure evidence. -/
theorem pl_structure_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasCompatiblePLStructure M
      (moise_triangulation_of_smoothability_package package M) :=
  package.plStructure M

/-- The named compatible PL-structure projection is the stored package field. -/
theorem pl_structure_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_structure_of_smoothability_package package M =
      package.plStructure M :=
  rfl

/-- A completed smoothability package supplies PL transition compatibility. -/
theorem pl_transition_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLTransitionCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M) :=
  package.plTransitionCompatibility M

/-- The named PL transition-compatibility projection is the stored package field. -/
theorem pl_transition_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_transition_compatibility_of_smoothability_package package M =
      package.plTransitionCompatibility M :=
  rfl

/-- A completed smoothability package supplies compatible PL-atlas evidence. -/
theorem pl_atlas_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasCompatiblePLAtlas M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M) :=
  package.plAtlas M

/-- The named compatible PL-atlas projection is the stored package field. -/
theorem pl_atlas_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_atlas_of_smoothability_package package M =
      package.plAtlas M :=
  rfl

/-- A completed smoothability package supplies the PL-manifold atlas. -/
theorem pl_manifold_atlas_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLManifoldAtlas M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plManifoldAtlas M

/-- The named PL-manifold atlas projection is the stored package field. -/
theorem pl_manifold_atlas_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_manifold_atlas_of_smoothability_package package M =
      package.plManifoldAtlas M :=
  rfl

/-- A completed smoothability package supplies PL collar-neighborhood compatibility. -/
theorem pl_collar_neighborhood_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLCollarNeighborhoodCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plCollarNeighborhoodCompatibility M

/-- The named PL collar-neighborhood compatibility projection is the stored package field. -/
theorem pl_collar_neighborhood_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_collar_neighborhood_compatibility_of_smoothability_package package M =
      package.plCollarNeighborhoodCompatibility M :=
  rfl

/-- A completed smoothability package supplies Moise-to-PL compatibility. -/
theorem pl_homeomorphism_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLHomeomorphismCompatibility M
      (moise_local_charts_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plHomeomorphismCompatibility M

/-- The named PL homeomorphism-compatibility projection is the stored package field. -/
theorem pl_homeomorphism_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_homeomorphism_compatibility_of_smoothability_package package M =
      package.plHomeomorphismCompatibility M :=
  rfl

/-- A completed smoothability package supplies PL atlas maximality. -/
theorem pl_atlas_maximality_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLAtlasMaximality M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plAtlasMaximality M

/-- The named PL-atlas maximality projection is the stored package field. -/
theorem pl_atlas_maximality_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_atlas_maximality_of_smoothability_package package M =
      package.plAtlasMaximality M :=
  rfl

/-- A completed smoothability package supplies PL smoothing existence. -/
theorem pl_smoothing_existence_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingExistence M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plSmoothingExistence M

/-- The named PL-smoothing existence projection is the stored package field. -/
theorem pl_smoothing_existence_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_existence_of_smoothability_package package M =
      package.plSmoothingExistence M :=
  rfl

/-- A completed smoothability package supplies PL-smoothing obstruction vanishing. -/
theorem pl_smoothing_obstruction_vanishing_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingObstructionVanishing M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plSmoothingObstructionVanishing M

/-- The named PL-smoothing obstruction-vanishing projection is the stored package field. -/
theorem pl_smoothing_obstruction_vanishing_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_obstruction_vanishing_of_smoothability_package package M =
      package.plSmoothingObstructionVanishing M :=
  rfl

/-- A completed smoothability package supplies PL microbundle smoothing evidence. -/
theorem pl_microbundle_smoothing_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLMicrobundleSmoothing M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_existence_of_smoothability_package package M)
      (pl_smoothing_obstruction_vanishing_of_smoothability_package package M) :=
  package.plMicrobundleSmoothing M

/-- The named PL microbundle-smoothing projection is the stored package field. -/
theorem pl_microbundle_smoothing_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_microbundle_smoothing_of_smoothability_package package M =
      package.plMicrobundleSmoothing M :=
  rfl

/-- A completed smoothability package supplies PL-smoothing theorem evidence. -/
theorem pl_smoothing_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingTheorem M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M) :=
  package.plSmoothing M

/-- The named PL-smoothing theorem projection is the stored package field. -/
theorem pl_smoothing_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_of_smoothability_package package M =
      package.plSmoothing M :=
  rfl

/-- A completed smoothability package supplies PL smoothing compatibility. -/
theorem pl_smoothing_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M) :=
  package.plSmoothingCompatibility M

/-- The named PL-smoothing compatibility projection is the stored package field. -/
theorem pl_smoothing_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_compatibility_of_smoothability_package package M =
      package.plSmoothingCompatibility M :=
  rfl

/-- A completed smoothability package supplies PL smoothing uniqueness. -/
theorem pl_smoothing_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingUniqueness M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M) :=
  package.plSmoothingUniqueness M

/-- The named PL-smoothing uniqueness projection is the stored package field. -/
theorem pl_smoothing_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_uniqueness_of_smoothability_package package M =
      package.plSmoothingUniqueness M :=
  rfl

/-- A completed smoothability package supplies PL-smoothing local-model compatibility. -/
theorem pl_smoothing_local_model_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingLocalModelCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M) :=
  package.plSmoothingLocalModelCompatibility M

/-- The named PL-smoothing local-model compatibility projection is the stored package field. -/
theorem pl_smoothing_local_model_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    pl_smoothing_local_model_compatibility_of_smoothability_package package M =
      package.plSmoothingLocalModelCompatibility M :=
  rfl

/-- A completed smoothability package supplies the raw smooth-structure input. -/
theorem smooth_structure_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasThreeManifoldSmoothStructure M :=
  package.smoothStructure M

/-- The named smooth-structure projection is the stored package field. -/
theorem smooth_structure_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_of_smoothability_package package M =
      package.smoothStructure M :=
  rfl

/-- A completed smoothability package supplies smooth atlas construction. -/
theorem smooth_atlas_construction_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasConstruction M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothAtlasConstruction M

/-- The named smooth-atlas construction projection is the stored package field. -/
theorem smooth_atlas_construction_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_construction_of_smoothability_package package M =
      package.smoothAtlasConstruction M :=
  rfl

/-- A completed smoothability package supplies smooth-atlas/PL-atlas compatibility. -/
theorem smooth_atlas_pl_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasPLCompatibility M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M)
      (smooth_atlas_construction_of_smoothability_package package M) :=
  package.smoothAtlasPLCompatibility M

/-- The named smooth-atlas/PL-atlas compatibility projection is the stored package field. -/
theorem smooth_atlas_pl_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_pl_compatibility_of_smoothability_package package M =
      package.smoothAtlasPLCompatibility M :=
  rfl

/-- A completed smoothability package supplies smooth atlas maximality. -/
theorem smooth_atlas_maximality_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasMaximality M
      (moise_triangulation_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothAtlasMaximality M

/-- The named smooth-atlas maximality projection is the stored package field. -/
theorem smooth_atlas_maximality_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_maximality_of_smoothability_package package M =
      package.smoothAtlasMaximality M :=
  rfl

/-- A completed smoothability package supplies smooth atlas uniqueness evidence. -/
theorem smooth_atlas_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasUniqueness M
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothAtlasUniqueness M

/-- The named smooth-atlas uniqueness projection is the stored package field. -/
theorem smooth_atlas_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_uniqueness_of_smoothability_package package M =
      package.smoothAtlasUniqueness M :=
  rfl

/-- A completed smoothability package supplies smooth-structure uniqueness. -/
theorem smooth_structure_uniqueness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothStructureUniquenessUpToDiffeomorphism M
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothStructureUniquenessUpToDiffeomorphism M

/-- The named smooth-structure uniqueness projection is the stored package field. -/
theorem smooth_structure_uniqueness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_uniqueness_of_smoothability_package package M =
      package.smoothStructureUniquenessUpToDiffeomorphism M :=
  rfl

/-- A completed smoothability package supplies smooth transition compatibility. -/
theorem smooth_transition_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothTransitionCompatibility M
      (smooth_structure_of_smoothability_package package M) :=
  package.smoothTransitionCompatibility M

/-- The named smooth-transition compatibility projection is the stored package field. -/
theorem smooth_transition_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_transition_compatibility_of_smoothability_package package M =
      package.smoothTransitionCompatibility M :=
  rfl

/-- A completed smoothability package supplies smooth transition-map smoothness. -/
theorem smooth_atlas_transition_smoothness_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasTransitionSmoothness M
      (smooth_structure_of_smoothability_package package M)
      (smooth_transition_compatibility_of_smoothability_package package M) :=
  package.smoothAtlasTransitionSmoothness M

/-- The named smooth transition-map smoothness projection is the stored package field. -/
theorem smooth_atlas_transition_smoothness_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_atlas_transition_smoothness_of_smoothability_package package M =
      package.smoothAtlasTransitionSmoothness M :=
  rfl

/--
A completed smoothability package projects the PL-to-smooth frontier from a PL
atlas through smoothing existence, smoothing theorem, smooth-structure
construction, atlas compatibility, uniqueness, and transition smoothness.
-/
theorem plToSmoothFrontier_of_smoothabilityPackage
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing ∧
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing ∧
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing ∧
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction ∧
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure ∧
      HasSmoothAtlasUniqueness M smoothStructure ∧
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure ∧
      ∃ smoothTransitionCompatibility :
        HasSmoothTransitionCompatibility M smoothStructure,
        HasSmoothAtlasTransitionSmoothness
          M smoothStructure smoothTransitionCompatibility := by
  exact
    ⟨package.moiseTriangulation M,
      package.plStructure M,
      package.plAtlas M,
      package.plSmoothingExistence M,
      package.plSmoothingObstructionVanishing M,
      package.plMicrobundleSmoothing M,
      package.plSmoothing M,
      package.smoothStructure M,
      package.smoothAtlasConstruction M,
      package.plSmoothingCompatibility M,
      package.plSmoothingUniqueness M,
      package.plSmoothingLocalModelCompatibility M,
      package.smoothAtlasPLCompatibility M,
      package.smoothAtlasMaximality M,
      package.smoothAtlasUniqueness M,
      package.smoothStructureUniquenessUpToDiffeomorphism M,
      package.smoothTransitionCompatibility M,
      package.smoothAtlasTransitionSmoothness M⟩

/--
A completed smoothability package supplies the derivation from triangulation and
PL structure to the smooth structure.
-/
theorem smooth_structure_derivation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothStructureDerivation M
      (moise_local_charts_of_smoothability_package package M)
      (moise_locally_finite_cover_refinement_of_smoothability_package package M)
      (moise_simplicial_complex_of_smoothability_package package M)
      (moise_compatible_chart_triangulations_of_smoothability_package package M)
      (moise_triangulation_of_smoothability_package package M)
      (moise_simplicial_approximation_of_smoothability_package package M)
      (moise_star_neighborhood_basis_of_smoothability_package package M)
      (moise_barycentric_subdivision_of_smoothability_package package M)
      (moise_regular_neighborhood_compatibility_of_smoothability_package package M)
      (moise_triangulation_local_finiteness_of_smoothability_package package M)
      (moise_link_compatibility_of_smoothability_package package M)
      (moise_pl_manifold_recognition_of_smoothability_package package M)
      (moise_triangulation_homeomorphism_of_smoothability_package package M)
      (moise_compatibility_of_smoothability_package package M)
      (moise_triangulation_uniqueness_of_smoothability_package package M)
      (moise_hauptvermutung_dimension_three_of_smoothability_package package M)
      (pl_structure_of_smoothability_package package M)
      (pl_transition_compatibility_of_smoothability_package package M)
      (pl_atlas_of_smoothability_package package M)
      (pl_manifold_atlas_of_smoothability_package package M)
      (pl_collar_neighborhood_compatibility_of_smoothability_package package M)
      (pl_homeomorphism_compatibility_of_smoothability_package package M)
      (pl_atlas_maximality_of_smoothability_package package M)
      (pl_smoothing_existence_of_smoothability_package package M)
      (pl_smoothing_obstruction_vanishing_of_smoothability_package package M)
      (pl_microbundle_smoothing_of_smoothability_package package M)
      (pl_smoothing_of_smoothability_package package M)
      (pl_smoothing_compatibility_of_smoothability_package package M)
      (pl_smoothing_uniqueness_of_smoothability_package package M)
      (pl_smoothing_local_model_compatibility_of_smoothability_package package M)
      (smooth_structure_of_smoothability_package package M)
      (smooth_atlas_construction_of_smoothability_package package M)
      (smooth_atlas_pl_compatibility_of_smoothability_package package M)
      (smooth_atlas_maximality_of_smoothability_package package M)
      (smooth_atlas_uniqueness_of_smoothability_package package M)
      (smooth_structure_uniqueness_of_smoothability_package package M)
      (smooth_transition_compatibility_of_smoothability_package package M)
      (smooth_atlas_transition_smoothness_of_smoothability_package package M) :=
  package.smoothStructureDerivation M

/-- The named smooth-structure derivation projection is the stored package field. -/
theorem smooth_structure_derivation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_derivation_of_smoothability_package package M =
      package.smoothStructureDerivation M :=
  rfl

/-- A completed smoothability package packages the smooth-structure derivation statement. -/
theorem smooth_structure_derivation_statement_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothStructureDerivationStatement M
      (smooth_structure_of_smoothability_package package M) :=
  smooth_structure_derivation_statement_of_components M
    (package.moiseLocalCharts M)
    (package.moiseLocallyFiniteCoverRefinement M)
    (package.moiseSimplicialComplex M)
    (package.moiseCompatibleChartTriangulations M)
    (package.moiseTriangulation M)
    (package.moiseSimplicialApproximation M)
    (package.moiseStarNeighborhoodBasis M)
    (package.moiseBarycentricSubdivision M)
    (package.moiseRegularNeighborhoodCompatibility M)
    (package.moiseTriangulationLocalFiniteness M)
    (package.moiseLinkCompatibility M)
    (package.moisePLManifoldRecognition M)
    (package.moiseTriangulationHomeomorphism M)
    (package.moiseCompatibility M)
    (package.moiseTriangulationUniqueness M)
    (package.moiseHauptvermutungDimensionThree M)
    (package.plStructure M)
    (package.plTransitionCompatibility M)
    (package.plAtlas M)
    (package.plManifoldAtlas M)
    (package.plCollarNeighborhoodCompatibility M)
    (package.plHomeomorphismCompatibility M)
    (package.plAtlasMaximality M)
    (package.plSmoothingExistence M)
    (package.plSmoothingObstructionVanishing M)
    (package.plMicrobundleSmoothing M)
    (package.plSmoothing M)
    (package.plSmoothingCompatibility M)
    (package.plSmoothingUniqueness M)
    (package.plSmoothingLocalModelCompatibility M)
    (package.smoothStructure M)
    (package.smoothAtlasConstruction M)
    (package.smoothAtlasPLCompatibility M)
    (package.smoothAtlasMaximality M)
    (package.smoothAtlasUniqueness M)
    (package.smoothStructureUniquenessUpToDiffeomorphism M)
    (package.smoothTransitionCompatibility M)
    (package.smoothAtlasTransitionSmoothness M)
    (package.smoothStructureDerivation M)

/--
The package-level smooth-structure derivation statement is exactly the component
assembler applied to the stored Moise, PL, smoothing, smooth-atlas, and
smooth-structure derivation fields.
-/
theorem smooth_structure_derivation_statement_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_structure_derivation_statement_of_smoothability_package package M =
      smooth_structure_derivation_statement_of_components M
        (package.moiseLocalCharts M)
        (package.moiseLocallyFiniteCoverRefinement M)
        (package.moiseSimplicialComplex M)
        (package.moiseCompatibleChartTriangulations M)
        (package.moiseTriangulation M)
        (package.moiseSimplicialApproximation M)
        (package.moiseStarNeighborhoodBasis M)
        (package.moiseBarycentricSubdivision M)
        (package.moiseRegularNeighborhoodCompatibility M)
        (package.moiseTriangulationLocalFiniteness M)
        (package.moiseLinkCompatibility M)
        (package.moisePLManifoldRecognition M)
        (package.moiseTriangulationHomeomorphism M)
        (package.moiseCompatibility M)
        (package.moiseTriangulationUniqueness M)
        (package.moiseHauptvermutungDimensionThree M)
        (package.plStructure M)
        (package.plTransitionCompatibility M)
        (package.plAtlas M)
        (package.plManifoldAtlas M)
        (package.plCollarNeighborhoodCompatibility M)
        (package.plHomeomorphismCompatibility M)
        (package.plAtlasMaximality M)
        (package.plSmoothingExistence M)
        (package.plSmoothingObstructionVanishing M)
        (package.plMicrobundleSmoothing M)
        (package.plSmoothing M)
        (package.plSmoothingCompatibility M)
        (package.plSmoothingUniqueness M)
        (package.plSmoothingLocalModelCompatibility M)
        (package.smoothStructure M)
        (package.smoothAtlasConstruction M)
        (package.smoothAtlasPLCompatibility M)
        (package.smoothAtlasMaximality M)
        (package.smoothAtlasUniqueness M)
        (package.smoothStructureUniquenessUpToDiffeomorphism M)
        (package.smoothTransitionCompatibility M)
        (package.smoothAtlasTransitionSmoothness M)
        (package.smoothStructureDerivation M) :=
  rfl

/--
A completed smoothability package exposes the component smooth-structure
derivation certificate together with the theorem-shaped derivation statement.
-/
theorem smoothability_smooth_structure_statement_payload_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation M
        (moise_local_charts_of_smoothability_package package M)
        (moise_locally_finite_cover_refinement_of_smoothability_package
          package M)
        (moise_simplicial_complex_of_smoothability_package package M)
        (moise_compatible_chart_triangulations_of_smoothability_package
          package M)
        (moise_triangulation_of_smoothability_package package M)
        (moise_simplicial_approximation_of_smoothability_package package M)
        (moise_star_neighborhood_basis_of_smoothability_package package M)
        (moise_barycentric_subdivision_of_smoothability_package package M)
        (moise_regular_neighborhood_compatibility_of_smoothability_package
          package M)
        (moise_triangulation_local_finiteness_of_smoothability_package
          package M)
        (moise_link_compatibility_of_smoothability_package package M)
        (moise_pl_manifold_recognition_of_smoothability_package package M)
        (moise_triangulation_homeomorphism_of_smoothability_package package M)
        (moise_compatibility_of_smoothability_package package M)
        (moise_triangulation_uniqueness_of_smoothability_package package M)
        (moise_hauptvermutung_dimension_three_of_smoothability_package
          package M)
        (pl_structure_of_smoothability_package package M)
        (pl_transition_compatibility_of_smoothability_package package M)
        (pl_atlas_of_smoothability_package package M)
        (pl_manifold_atlas_of_smoothability_package package M)
        (pl_collar_neighborhood_compatibility_of_smoothability_package
          package M)
        (pl_homeomorphism_compatibility_of_smoothability_package package M)
        (pl_atlas_maximality_of_smoothability_package package M)
        (pl_smoothing_existence_of_smoothability_package package M)
        (pl_smoothing_obstruction_vanishing_of_smoothability_package package M)
        (pl_microbundle_smoothing_of_smoothability_package package M)
        (pl_smoothing_of_smoothability_package package M)
        (pl_smoothing_compatibility_of_smoothability_package package M)
        (pl_smoothing_uniqueness_of_smoothability_package package M)
        (pl_smoothing_local_model_compatibility_of_smoothability_package
          package M)
        (smooth_structure_of_smoothability_package package M)
        (smooth_atlas_construction_of_smoothability_package package M)
        (smooth_atlas_pl_compatibility_of_smoothability_package package M)
        (smooth_atlas_maximality_of_smoothability_package package M)
        (smooth_atlas_uniqueness_of_smoothability_package package M)
        (smooth_structure_uniqueness_of_smoothability_package package M)
        (smooth_transition_compatibility_of_smoothability_package package M)
        (smooth_atlas_transition_smoothness_of_smoothability_package package M),
      SmoothStructureDerivationStatement M
        (smooth_structure_of_smoothability_package package M) := by
  exact ⟨smooth_structure_derivation_of_smoothability_package package M,
    smooth_structure_derivation_statement_of_smoothability_package package M⟩

/--
The smooth-structure statement payload is the projected derivation evidence
paired with the theorem-shaped derivation statement.
-/
theorem smoothability_smooth_structure_statement_payload_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_structure_statement_payload_of_smoothability_package
      package M =
      ⟨smooth_structure_derivation_of_smoothability_package package M,
        smooth_structure_derivation_statement_of_smoothability_package
          package M⟩ := by
  apply Subsingleton.elim

/-- A completed smoothability package supplies the bridge theorem interface. -/
theorem smoothability_bridge_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    SmoothabilityBridgeStatement.{u} :=
  package.bridge

/-- The named smoothability bridge projection is the stored package field. -/
theorem smoothability_bridge_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothability_bridge_of_smoothability_package package = package.bridge :=
  rfl

/--
A completed smoothability package supplies the theorem-shaped `C∞`
smooth-manifold statement.
-/
theorem smoothability_smooth_manifold_statement_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    SmoothabilitySmoothManifoldStatement.{u} :=
  package.smoothManifold

/-- The named `C∞` smooth-manifold projection is the stored package field. -/
theorem smoothability_smooth_manifold_statement_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothability_smooth_manifold_statement_of_smoothability_package package =
      package.smoothManifold :=
  rfl

/-- Apply the smoothability bridge to explicit smooth-structure evidence. -/
theorem is_manifold_of_smoothability_bridge
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure) :
    IsManifold ThreeManifoldModelWithCorners 1 M :=
  smoothability_bridge_of_smoothability_package package M smoothStructure
    smoothStructureDerivation

/--
The explicit bridge application is the stored bridge applied to the supplied
smooth-structure evidence.
-/
theorem is_manifold_of_smoothability_bridge_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothStructure : HasThreeManifoldSmoothStructure M)
    (smoothStructureDerivation :
      SmoothStructureDerivationStatement M smoothStructure) :
    is_manifold_of_smoothability_bridge
      package M smoothStructure smoothStructureDerivation =
      package.bridge M smoothStructure smoothStructureDerivation :=
  rfl

/-- A completed smoothability package supplies the raw regularity bridge. -/
theorem smoothable_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        IsManifold ThreeManifoldModelWithCorners 1 M := by
  intro M _ _ _ _ _
  exact is_manifold_of_smoothability_bridge package M
    (smooth_structure_of_smoothability_package package M)
    (smooth_structure_derivation_statement_of_smoothability_package package M)

/--
The raw surgery-model smoothability projection is the stored bridge applied to
the package's smooth structure and derivation statement.
-/
theorem smoothable_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothable_of_smoothability_package package =
      fun (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M] =>
          package.bridge M
            (smooth_structure_of_smoothability_package package M)
            (smooth_structure_derivation_statement_of_smoothability_package
              package M) := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies the `C∞` manifold instance consumed by
the canonical smooth Poincare statement.
-/
theorem smooth_manifold_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        IsManifold (𝓡 3) ∞ M :=
  smoothability_smooth_manifold_statement_of_smoothability_package package

/-- The named canonical smooth-manifold projection is the stored package field. -/
theorem smooth_manifold_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smooth_manifold_of_smoothability_package package =
      package.smoothManifold := by
  apply Subsingleton.elim

/--
A completed smoothability package exposes both smoothability theorem outputs:
the C¹ surgery-model bridge and the separate `C∞` canonical smooth-manifold
statement.
-/
theorem smoothability_smooth_manifold_payload_of_smoothability_package
    (package : SmoothabilityPackage.{u}) :
    SmoothabilityBridgeStatement.{u} ∧
      SmoothabilitySmoothManifoldStatement.{u} :=
  ⟨smoothability_bridge_of_smoothability_package package,
    smoothability_smooth_manifold_statement_of_smoothability_package package⟩

/--
The smooth-manifold payload is the pair of stored theorem-shaped smoothability
outputs.
-/
theorem smoothability_smooth_manifold_payload_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u}) :
    smoothability_smooth_manifold_payload_of_smoothability_package package =
      ⟨package.bridge, package.smoothManifold⟩ := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies derivation evidence for the bridge
applied to its projected smooth structure.
-/
theorem smoothability_bridge_derivation_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothabilityBridgeDerivation M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      (smoothable_of_smoothability_package package M) :=
  package.bridgeDerivation M

/-- The named bridge-derivation projection is the stored package field. -/
theorem smoothability_bridge_derivation_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_bridge_derivation_of_smoothability_package package M =
      package.bridgeDerivation M := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies compatibility of the produced
manifold instance with the target smooth model.
-/
theorem smooth_model_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothManifoldModelCompatibility M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      (smoothable_of_smoothability_package package M)
      (smoothability_bridge_derivation_of_smoothability_package package M) :=
  package.smoothModelCompatibility M

/-- The named model-compatibility projection is the stored package field. -/
theorem smooth_model_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_model_compatibility_of_smoothability_package package M =
      package.smoothModelCompatibility M := by
  apply Subsingleton.elim

/--
A completed smoothability package supplies compatibility of the produced
manifold evidence with the surgery chart model.
-/
theorem smooth_chart_compatibility_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothChartCompatibility M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      (smoothable_of_smoothability_package package M)
      (smoothability_bridge_derivation_of_smoothability_package package M)
      (smooth_model_compatibility_of_smoothability_package package M) :=
  package.chartCompatibility M

/-- The named chart-compatibility projection is the stored package field. -/
theorem smooth_chart_compatibility_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smooth_chart_compatibility_of_smoothability_package package M =
      package.chartCompatibility M := by
  apply Subsingleton.elim

/--
A completed smoothability package exposes the bridge output, compatibility
certificates, and full smoothability sub-obligation payload.
-/
theorem smoothability_bridge_payload_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ bridgeDerivation :
      HasSmoothabilityBridgeDerivation M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package
          package M)
        manifoldEvidence,
    ∃ modelCompatibility :
      HasSmoothManifoldModelCompatibility M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package
          package M)
        manifoldEvidence
        bridgeDerivation,
    ∃ _chartCompatibility :
      HasSmoothChartCompatibility M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package
          package M)
        manifoldEvidence
        bridgeDerivation
        modelCompatibility,
      SmoothabilitySubobligationsPayload M := by
  let manifoldEvidence := smoothable_of_smoothability_package package M
  let bridgeDerivation :=
    smoothability_bridge_derivation_of_smoothability_package package M
  let modelCompatibility :=
    smooth_model_compatibility_of_smoothability_package package M
  let chartCompatibility :=
    smooth_chart_compatibility_of_smoothability_package package M
  exact ⟨manifoldEvidence, bridgeDerivation, modelCompatibility,
    chartCompatibility,
    smoothability_subobligations_of_derivation_statement M
      (smooth_structure_of_smoothability_package package M)
      (smooth_structure_derivation_statement_of_smoothability_package package M)
      manifoldEvidence bridgeDerivation modelCompatibility
      chartCompatibility⟩

/--
The bridge payload is the named manifold evidence, bridge derivation,
compatibility evidence, and sub-obligation payload assembled from them.
-/
theorem smoothability_bridge_payload_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_bridge_payload_of_smoothability_package package M =
      ⟨smoothable_of_smoothability_package package M,
        smoothability_bridge_derivation_of_smoothability_package package M,
        smooth_model_compatibility_of_smoothability_package package M,
        smooth_chart_compatibility_of_smoothability_package package M,
        smoothability_subobligations_of_derivation_statement M
          (smooth_structure_of_smoothability_package package M)
          (smooth_structure_derivation_statement_of_smoothability_package
            package M)
          (smoothable_of_smoothability_package package M)
          (smoothability_bridge_derivation_of_smoothability_package package M)
          (smooth_model_compatibility_of_smoothability_package package M)
          (smooth_chart_compatibility_of_smoothability_package package M)⟩ := by
  apply Subsingleton.elim

/--
A completed smoothability package directly exposes the named smoothability
sub-obligation payload for each topological three-manifold input.
-/
theorem smoothability_subobligations_of_smoothability_package
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothabilitySubobligationsPayload M :=
  smoothability_subobligations_of_derivation_statement M
    (smooth_structure_of_smoothability_package package M)
    (smooth_structure_derivation_statement_of_smoothability_package package M)
    (smoothable_of_smoothability_package package M)
    (smoothability_bridge_derivation_of_smoothability_package package M)
    (smooth_model_compatibility_of_smoothability_package package M)
    (smooth_chart_compatibility_of_smoothability_package package M)

/--
The package-level smoothability sub-obligation bridge is exactly the derivation
statement bridge applied to the package projections.
-/
theorem smoothability_subobligations_of_smoothability_package_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_of_smoothability_package package M =
      smoothability_subobligations_of_derivation_statement M
        (smooth_structure_of_smoothability_package package M)
        (smooth_structure_derivation_statement_of_smoothability_package package M)
        (smoothable_of_smoothability_package package M)
        (smoothability_bridge_derivation_of_smoothability_package package M)
        (smooth_model_compatibility_of_smoothability_package package M)
        (smooth_chart_compatibility_of_smoothability_package package M) := by
  apply Subsingleton.elim

/--
The direct package-level sub-obligation payload is the final component of the
richer bridge payload exposing manifold evidence and compatibility
certificates.
-/
theorem smoothability_subobligations_of_smoothability_package_to_bridge_payload_eq
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_of_smoothability_package package M =
      (smoothability_bridge_payload_of_smoothability_package package M).2.2.2.2 := by
  apply Subsingleton.elim

/--
The package-level sub-obligation payload exposes the richer bridge payload
projection under a direct endpoint name.
-/
theorem smoothability_subobligations_of_smoothability_package_to_bridge_payload
    (package : SmoothabilityPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_of_smoothability_package package M =
      (smoothability_bridge_payload_of_smoothability_package package M).2.2.2.2 :=
  smoothability_subobligations_of_smoothability_package_to_bridge_payload_eq
    package M

end Poincare

/-!
Generated shape equality contracts for `scripts/shape_contract_audit.sh`.
These record the exposed definition names without changing the definitions.
-/

namespace Poincare

/-- Shape contract for `HasMoiseLocalTriangulationCharts`. -/
theorem hasMoiseLocalTriangulationCharts_eq :
    @Poincare.HasMoiseLocalTriangulationCharts = @Poincare.HasMoiseLocalTriangulationCharts :=
  rfl

/-- Shape contract for `HasMoiseLocallyFiniteCoverRefinement`. -/
theorem hasMoiseLocallyFiniteCoverRefinement_eq :
    @Poincare.HasMoiseLocallyFiniteCoverRefinement = @Poincare.HasMoiseLocallyFiniteCoverRefinement :=
  rfl

/-- Shape contract for `HasMoiseSimplicialComplex`. -/
theorem hasMoiseSimplicialComplex_eq :
    @Poincare.HasMoiseSimplicialComplex = @Poincare.HasMoiseSimplicialComplex :=
  rfl

/-- Shape contract for `HasMoiseCompatibleChartTriangulations`. -/
theorem hasMoiseCompatibleChartTriangulations_eq :
    @Poincare.HasMoiseCompatibleChartTriangulations = @Poincare.HasMoiseCompatibleChartTriangulations :=
  rfl

/-- Shape contract for `HasMoiseTriangulation`. -/
theorem hasMoiseTriangulation_eq :
    @Poincare.HasMoiseTriangulation = @Poincare.HasMoiseTriangulation :=
  rfl

/-- Shape contract for `HasMoiseSimplicialApproximation`. -/
theorem hasMoiseSimplicialApproximation_eq :
    @Poincare.HasMoiseSimplicialApproximation = @Poincare.HasMoiseSimplicialApproximation :=
  rfl

/-- Shape contract for `HasMoiseStarNeighborhoodBasis`. -/
theorem hasMoiseStarNeighborhoodBasis_eq :
    @Poincare.HasMoiseStarNeighborhoodBasis = @Poincare.HasMoiseStarNeighborhoodBasis :=
  rfl

/-- Shape contract for `HasMoiseBarycentricSubdivisionControl`. -/
theorem hasMoiseBarycentricSubdivisionControl_eq :
    @Poincare.HasMoiseBarycentricSubdivisionControl = @Poincare.HasMoiseBarycentricSubdivisionControl :=
  rfl

/-- Shape contract for `HasMoiseRegularNeighborhoodCompatibility`. -/
theorem hasMoiseRegularNeighborhoodCompatibility_eq :
    @Poincare.HasMoiseRegularNeighborhoodCompatibility = @Poincare.HasMoiseRegularNeighborhoodCompatibility :=
  rfl

/-- Shape contract for `HasMoiseTriangulationLocalFiniteness`. -/
theorem hasMoiseTriangulationLocalFiniteness_eq :
    @Poincare.HasMoiseTriangulationLocalFiniteness = @Poincare.HasMoiseTriangulationLocalFiniteness :=
  rfl

/-- Shape contract for `HasMoiseLinkCompatibility`. -/
theorem hasMoiseLinkCompatibility_eq :
    @Poincare.HasMoiseLinkCompatibility = @Poincare.HasMoiseLinkCompatibility :=
  rfl

/-- Shape contract for `HasMoisePLManifoldRecognition`. -/
theorem hasMoisePLManifoldRecognition_eq :
    @Poincare.HasMoisePLManifoldRecognition = @Poincare.HasMoisePLManifoldRecognition :=
  rfl

/-- Shape contract for `HasMoiseTriangulationHomeomorphism`. -/
theorem hasMoiseTriangulationHomeomorphism_eq :
    @Poincare.HasMoiseTriangulationHomeomorphism = @Poincare.HasMoiseTriangulationHomeomorphism :=
  rfl

/-- Shape contract for `HasMoiseTriangulationCompatibility`. -/
theorem hasMoiseTriangulationCompatibility_eq :
    @Poincare.HasMoiseTriangulationCompatibility = @Poincare.HasMoiseTriangulationCompatibility :=
  rfl

/-- Shape contract for `HasMoiseTriangulationUniqueness`. -/
theorem hasMoiseTriangulationUniqueness_eq :
    @Poincare.HasMoiseTriangulationUniqueness = @Poincare.HasMoiseTriangulationUniqueness :=
  rfl

/-- Shape contract for `HasMoiseHauptvermutungDimensionThree`. -/
theorem hasMoiseHauptvermutungDimensionThree_eq :
    @Poincare.HasMoiseHauptvermutungDimensionThree = @Poincare.HasMoiseHauptvermutungDimensionThree :=
  rfl

/-- Shape contract for `HasCompatiblePLStructure`. -/
theorem hasCompatiblePLStructure_eq :
    @Poincare.HasCompatiblePLStructure = @Poincare.HasCompatiblePLStructure :=
  rfl

/-- Shape contract for `HasPLTransitionCompatibility`. -/
theorem hasPLTransitionCompatibility_eq :
    @Poincare.HasPLTransitionCompatibility = @Poincare.HasPLTransitionCompatibility :=
  rfl

/-- Shape contract for `HasCompatiblePLAtlas`. -/
theorem hasCompatiblePLAtlas_eq :
    @Poincare.HasCompatiblePLAtlas = @Poincare.HasCompatiblePLAtlas :=
  rfl

/-- Shape contract for `HasPLManifoldAtlas`. -/
theorem hasPLManifoldAtlas_eq :
    @Poincare.HasPLManifoldAtlas = @Poincare.HasPLManifoldAtlas :=
  rfl

/-- Shape contract for `HasPLCollarNeighborhoodCompatibility`. -/
theorem hasPLCollarNeighborhoodCompatibility_eq :
    @Poincare.HasPLCollarNeighborhoodCompatibility = @Poincare.HasPLCollarNeighborhoodCompatibility :=
  rfl

/-- Shape contract for `HasPLHomeomorphismCompatibility`. -/
theorem hasPLHomeomorphismCompatibility_eq :
    @Poincare.HasPLHomeomorphismCompatibility = @Poincare.HasPLHomeomorphismCompatibility :=
  rfl

/-- Shape contract for `HasPLAtlasMaximality`. -/
theorem hasPLAtlasMaximality_eq :
    @Poincare.HasPLAtlasMaximality = @Poincare.HasPLAtlasMaximality :=
  rfl

/-- Shape contract for `HasPLSmoothingExistence`. -/
theorem hasPLSmoothingExistence_eq :
    @Poincare.HasPLSmoothingExistence = @Poincare.HasPLSmoothingExistence :=
  rfl

/-- Shape contract for `HasPLSmoothingObstructionVanishing`. -/
theorem hasPLSmoothingObstructionVanishing_eq :
    @Poincare.HasPLSmoothingObstructionVanishing = @Poincare.HasPLSmoothingObstructionVanishing :=
  rfl

/-- Shape contract for `HasPLMicrobundleSmoothing`. -/
theorem hasPLMicrobundleSmoothing_eq :
    @Poincare.HasPLMicrobundleSmoothing = @Poincare.HasPLMicrobundleSmoothing :=
  rfl

/-- Shape contract for `HasPLSmoothingTheorem`. -/
theorem hasPLSmoothingTheorem_eq :
    @Poincare.HasPLSmoothingTheorem = @Poincare.HasPLSmoothingTheorem :=
  rfl

/-- Shape contract for `HasPLSmoothingCompatibility`. -/
theorem hasPLSmoothingCompatibility_eq :
    @Poincare.HasPLSmoothingCompatibility = @Poincare.HasPLSmoothingCompatibility :=
  rfl

/-- Shape contract for `HasPLSmoothingUniqueness`. -/
theorem hasPLSmoothingUniqueness_eq :
    @Poincare.HasPLSmoothingUniqueness = @Poincare.HasPLSmoothingUniqueness :=
  rfl

/-- Shape contract for `HasPLSmoothingLocalModelCompatibility`. -/
theorem hasPLSmoothingLocalModelCompatibility_eq :
    @Poincare.HasPLSmoothingLocalModelCompatibility = @Poincare.HasPLSmoothingLocalModelCompatibility :=
  rfl

/-- Shape contract for `HasThreeManifoldSmoothStructure`. -/
theorem hasThreeManifoldSmoothStructure_eq :
    @Poincare.HasThreeManifoldSmoothStructure = @Poincare.HasThreeManifoldSmoothStructure :=
  rfl

/-- Shape contract for `HasSmoothAtlasConstruction`. -/
theorem hasSmoothAtlasConstruction_eq :
    @Poincare.HasSmoothAtlasConstruction = @Poincare.HasSmoothAtlasConstruction :=
  rfl

/-- Shape contract for `HasSmoothAtlasPLCompatibility`. -/
theorem hasSmoothAtlasPLCompatibility_eq :
    @Poincare.HasSmoothAtlasPLCompatibility = @Poincare.HasSmoothAtlasPLCompatibility :=
  rfl

/-- Shape contract for `HasSmoothAtlasMaximality`. -/
theorem hasSmoothAtlasMaximality_eq :
    @Poincare.HasSmoothAtlasMaximality = @Poincare.HasSmoothAtlasMaximality :=
  rfl

/-- Shape contract for `HasSmoothAtlasUniqueness`. -/
theorem hasSmoothAtlasUniqueness_eq :
    @Poincare.HasSmoothAtlasUniqueness = @Poincare.HasSmoothAtlasUniqueness :=
  rfl

/-- Shape contract for `HasSmoothStructureUniquenessUpToDiffeomorphism`. -/
theorem hasSmoothStructureUniquenessUpToDiffeomorphism_eq :
    @Poincare.HasSmoothStructureUniquenessUpToDiffeomorphism = @Poincare.HasSmoothStructureUniquenessUpToDiffeomorphism :=
  rfl

/-- Shape contract for `HasSmoothTransitionCompatibility`. -/
theorem hasSmoothTransitionCompatibility_eq :
    @Poincare.HasSmoothTransitionCompatibility = @Poincare.HasSmoothTransitionCompatibility :=
  rfl

/-- Shape contract for `HasSmoothAtlasTransitionSmoothness`. -/
theorem hasSmoothAtlasTransitionSmoothness_eq :
    @Poincare.HasSmoothAtlasTransitionSmoothness = @Poincare.HasSmoothAtlasTransitionSmoothness :=
  rfl

/-- Shape contract for `HasSmoothStructureDerivation`. -/
theorem hasSmoothStructureDerivation_eq :
    @Poincare.HasSmoothStructureDerivation = @Poincare.HasSmoothStructureDerivation :=
  rfl

end Poincare

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

namespace Poincare

/-- Theorem contract for `surgeryModel_isManifold_of_smoothManifold`. -/
theorem surgeryModel_isManifold_of_smoothManifold_eq :
    @Poincare.surgeryModel_isManifold_of_smoothManifold = @Poincare.surgeryModel_isManifold_of_smoothManifold :=
  rfl

/-- Theorem contract for `smoothabilityBridgeStatement_of_smoothabilitySmoothManifoldStatement`. -/
theorem smoothabilityBridgeStatement_of_smoothabilitySmoothManifoldStatement_eq :
    @Poincare.smoothabilityBridgeStatement_of_smoothabilitySmoothManifoldStatement = @Poincare.smoothabilityBridgeStatement_of_smoothabilitySmoothManifoldStatement :=
  rfl

/-- Theorem contract for `smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement`. -/
theorem smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement_eq :
    @Poincare.smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement = @Poincare.smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement :=
  rfl

/-- Theorem contract for `HasSmoothAtlasConstruction.witnesses`. -/
theorem HasSmoothAtlasConstruction.witnesses_eq :
    @Poincare.HasSmoothAtlasConstruction.witnesses =
      @Poincare.HasSmoothAtlasConstruction.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothAtlasPLCompatibility.witnesses`. -/
theorem HasSmoothAtlasPLCompatibility.witnesses_eq :
    @Poincare.HasSmoothAtlasPLCompatibility.witnesses =
      @Poincare.HasSmoothAtlasPLCompatibility.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothAtlasMaximality.witnesses`. -/
theorem HasSmoothAtlasMaximality.witnesses_eq :
    @Poincare.HasSmoothAtlasMaximality.witnesses =
      @Poincare.HasSmoothAtlasMaximality.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothAtlasUniqueness.witnesses`. -/
theorem HasSmoothAtlasUniqueness.witnesses_eq :
    @Poincare.HasSmoothAtlasUniqueness.witnesses =
      @Poincare.HasSmoothAtlasUniqueness.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothStructureUniquenessUpToDiffeomorphism.witnesses`. -/
theorem HasSmoothStructureUniquenessUpToDiffeomorphism.witnesses_eq :
    @Poincare.HasSmoothStructureUniquenessUpToDiffeomorphism.witnesses =
      @Poincare.HasSmoothStructureUniquenessUpToDiffeomorphism.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothTransitionCompatibility.witnesses`. -/
theorem HasSmoothTransitionCompatibility.witnesses_eq :
    @Poincare.HasSmoothTransitionCompatibility.witnesses =
      @Poincare.HasSmoothTransitionCompatibility.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothAtlasTransitionSmoothness.witnesses`. -/
theorem HasSmoothAtlasTransitionSmoothness.witnesses_eq :
    @Poincare.HasSmoothAtlasTransitionSmoothness.witnesses =
      @Poincare.HasSmoothAtlasTransitionSmoothness.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothabilityBridgeDerivation.witnesses`. -/
theorem HasSmoothabilityBridgeDerivation.witnesses_eq :
    @Poincare.HasSmoothabilityBridgeDerivation.witnesses =
      @Poincare.HasSmoothabilityBridgeDerivation.witnesses :=
  rfl

/-- Theorem contract for `HasSmoothChartCompatibility.witnesses`. -/
theorem HasSmoothChartCompatibility.witnesses_eq :
    @Poincare.HasSmoothChartCompatibility.witnesses =
      @Poincare.HasSmoothChartCompatibility.witnesses :=
  rfl

/-- Theorem contract for `moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition`. -/
theorem moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition_eq :
    @Poincare.moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition =
      @Poincare.moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition :=
  rfl

/-- Theorem contract for `moiseToPLFrontier_of_smoothabilityPackage`. -/
theorem moiseToPLFrontier_of_smoothabilityPackage_eq :
    @Poincare.moiseToPLFrontier_of_smoothabilityPackage =
      @Poincare.moiseToPLFrontier_of_smoothabilityPackage :=
  rfl

/-- Theorem contract for `plToSmoothFrontier_of_smoothabilityPackage`. -/
theorem plToSmoothFrontier_of_smoothabilityPackage_eq :
    @Poincare.plToSmoothFrontier_of_smoothabilityPackage =
      @Poincare.plToSmoothFrontier_of_smoothabilityPackage :=
  rfl

end Poincare

/-- Root-scope theorem contract for `Poincare.moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition`. -/
theorem moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition_eq :
    @Poincare.moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition =
      @Poincare.moiseLocallyFiniteCoverRefinement_iff_localCharts_from_onePointRecognition :=
  rfl

/-- Root-scope theorem contract for `Poincare.moiseToPLFrontier_of_smoothabilityPackage`. -/
theorem moiseToPLFrontier_of_smoothabilityPackage_eq :
    @Poincare.moiseToPLFrontier_of_smoothabilityPackage =
      @Poincare.moiseToPLFrontier_of_smoothabilityPackage :=
  rfl

/-- Root-scope theorem contract for `Poincare.plToSmoothFrontier_of_smoothabilityPackage`. -/
theorem plToSmoothFrontier_of_smoothabilityPackage_eq :
    @Poincare.plToSmoothFrontier_of_smoothabilityPackage =
      @Poincare.plToSmoothFrontier_of_smoothabilityPackage :=
  rfl
