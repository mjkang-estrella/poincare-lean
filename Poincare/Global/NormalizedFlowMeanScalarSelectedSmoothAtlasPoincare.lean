import Poincare.Global.NormalizedFlowMeanScalarCanonicalRootedSphereBridge

/-!
# One selected smooth atlas for the mean-scalar Poincare route

The earlier fixed-target interfaces quantify analytic and canonical-rooted
completion data over every smooth atlas that might be selected on `M`.  The
proof only consumes one atlas.  This module records the weaker, coherent
quantifier order:

1. select one `C∞` charted-space instance;
2. place the forward-only mean-scalar analytic data under that exact instance;
   and
3. place derived-terminal canonical-rooted homotopy-grid completion data
   under the same instance.

Second countability is derived from compactness of the selected charted
space, connectedness is derived from simple connectivity, and the measurable
structure is fixed locally to the Borel structure.  None of those instances
is stored as an independent package field.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanAtlasRootedPathSkeleton
open CartanCanonicalRootedEndpointAssembly

/-- A selected closed-smooth atlas on a compact target makes that target
second countable.  The atlas is an explicit argument so the result can be
reused inside dependent package fields without installing a global instance.
-/
@[reducible] noncomputable def selectedClosedSmoothAtlasSecondCountableTopology3
    (M : Type u) [TopologicalSpace M] [CompactSpace M]
    (chartedSpace : ChartedSpace (ClosedSmoothModel 3) M) :
    SecondCountableTopology M := by
  letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
  exact
    secondCountableTopology_for_normalizedFlow_of_compact_chartedSpace M

/-- One coherent selected-smooth-atlas package for the strongest mean-scalar
route.

`analytic` and `completion` are not providers quantified over arbitrary
smooth instances.  Both fields live under the exact `chartedSpace` and
`smoothManifold` stored immediately above them.  The analytic record itself
uses `Ici 0` for every time-dependent geometric datum.  The remaining target
instances are derived canonically inside each field.  Restricted-domain
membership supplies both terminal paths.  The completion field retains only
the honest realized-grid, boundary-trace, and smallness payload on each
overlap; it does not ask one endpoint path to refine another. -/
structure SelectedSmoothAtlasMeanScalarCanonicalRootedPackage3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  chartedSpace : ChartedSpace (ClosedSmoothModel 3) M
  smoothManifold :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    IsManifold (closedSmoothModelWithCorners 3) ∞ M
  analytic :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
      smoothManifold
    letI : SecondCountableTopology M :=
      selectedClosedSmoothAtlasSecondCountableTopology3 M chartedSpace
    letI : ConnectedSpace M :=
      connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    NormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M
  completion :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
      smoothManifold
    letI : SecondCountableTopology M :=
      selectedClosedSmoothAtlasSecondCountableTopology3 M chartedSpace
    letI : ConnectedSpace M :=
      connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
    ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                Nonempty
                  (CanonicalRootedRealizationPackage.DerivedTerminalHomotopyGridOverlapCoherence
                    package hcurv hmesh)

/-- The former all-smooth-atlases providers imply the selected package after
one smooth atlas has been chosen.  This is only a compatibility direction:
the selected package itself contains no data for any other atlas. -/
noncomputable def SelectedSmoothAtlasMeanScalarCanonicalRootedPackage3.of_fixedTargetProviders
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (chartedSpace : ChartedSpace (ClosedSmoothModel 3) M)
    (smoothManifold :
      letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
      IsManifold (closedSmoothModelWithCorners 3) ∞ M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedDerivedTerminalHomotopyGridOverlapCompletion3 M) :
    SelectedSmoothAtlasMeanScalarCanonicalRootedPackage3.{u, v} M := by
  letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
  letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
    smoothManifold
  letI : SecondCountableTopology M :=
    selectedClosedSmoothAtlasSecondCountableTopology3 M chartedSpace
  letI : ConnectedSpace M :=
    connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact
    { chartedSpace := chartedSpace
      smoothManifold := smoothManifold
      analytic := analytic
      completion := completion }

/-- The analytic and canonical-rooted fields on one selected smooth atlas
give the round-sphere conclusion for that target manifold. -/
theorem SelectedSmoothAtlasMeanScalarCanonicalRootedPackage3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      SelectedSmoothAtlasMeanScalarCanonicalRootedPackage3.{u, v} M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  letI : ChartedSpace (ClosedSmoothModel 3) M := data.chartedSpace
  letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
    data.smoothManifold
  letI : SecondCountableTopology M :=
    selectedClosedSmoothAtlasSecondCountableTopology3 M data.chartedSpace
  letI : ConnectedSpace M :=
    connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have unitRecognition : UnitConstantCurvatureSphereRecognition3 M :=
    CanonicalRootedRealizationPackage.unitConstantCurvatureSphereRecognition3_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
      data.completion
  exact data.analytic.sphereConclusion unitRecognition

/-- Universal existence of one coherent selected package on each target
manifold.  The ambient topological atlas in the project statement is not
required to equal the package's selected smooth atlas. -/
def UniversalSelectedSmoothAtlasMeanScalarCanonicalRootedPackage3 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (SelectedSmoothAtlasMeanScalarCanonicalRootedPackage3.{u, v} M)

/-- The coherent selected-atlas provider proves exactly the repository's
canonical topological `PoincareConjectureStatement`. -/
theorem poincareConjectureStatement_of_universalSelectedSmoothAtlasMeanScalarCanonicalRootedPackage3
    (provider :
      UniversalSelectedSmoothAtlasMeanScalarCanonicalRootedPackage3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
