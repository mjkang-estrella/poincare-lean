import Poincare.Global.NormalizedFlowMeanScalarTopologicalSphereBridge
import Poincare.Global.CartanCanonicalRootedRestrictedEndpointAssembly
import Poincare.Global.CartanCanonicalRootedHomotopyGridEndpointAssembly
import Poincare.Global.CartanCanonicalRootedDerivedTerminalHomotopyGridAssembly

/-!
# Canonical-rooted recognition for the mean-scalar topological bridge

This module replaces the opaque unit-curvature recognition provider in the
fixed-target mean-scalar sphere bridge by the explicit canonical rooted
completion payload:

* a rooted Cartan path skeleton for every constructed unit-curvature metric;
* a canonical rooted realization package over that skeleton; and
* one explicit overlap-coherence payload for the package.

The completion provider remains quantified underneath the smooth atlas and
derived instances selected by the smoothability bridge.  It is used only
after the mean-scalar route has constructed a unit-curvature metric, so it
does not participate in atlas selection or in the Ricci-flow argument.

The legacy reduced provider uses the canonical terminal-restricted domains
and stores a finite overlap schedule, first-stage closeness, and accumulated
mesh inequalities.  It remains available for compatibility.

The intermediate schedule-free provider keeps restricted domains together
with two explicit terminal paths and a dependent homotopy-grid certificate on
every overlap.  The strongest selected-atlas route now uses the derived-
terminal provider: domain membership canonically supplies both short paths,
so only the honest realized grid and its horizontal/vertical smallness remain
as overlap data.  Grid realization and boundary traces are still explicit.
-/

noncomputable section

open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

open CartanAtlasRootedPathSkeleton
open CartanCanonicalRootedEndpointAssembly

/-- Fixed-target canonical rooted completion data, quantified under exactly
the smooth atlas and derived instances selected by the topological bridge.

For each unit-curvature metric, this provider supplies the actual rooted
skeleton, canonical realization package, and residual adaptive overlap
coherence consumed by
`unitConstantCurvatureSphereRecognition3_of_canonicalRootedAdaptiveOverlapCoherence`.
-/
def FixedTargetCanonicalRootedAdaptiveOverlapCompletion3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        ∀ hcurv : HasConstantSectionalCurvature3 g 1,
          ∃ skeleton : RootedCartanPathSkeleton g,
            ∃ package : CanonicalRootedRealizationPackage skeleton,
              package.AdaptiveOverlapCoherence hcurv

/-- Fixed-target canonical rooted completion data at the reduced,
terminal-domain-only boundary.

For each unit-curvature metric the provider chooses a positive prescribed
mesh and retains only the finite overlap data on the canonical shrunken
domains.  All geometric domain and terminal-path obligations are derived by
`CartanCanonicalRootedRestrictedEndpointAssembly`. -/
def FixedTargetCanonicalRootedTerminalRestrictedAccumulatedMeshOverlapCompletion3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        ∀ hcurv : HasConstantSectionalCurvature3 g 1,
          ∃ skeleton : RootedCartanPathSkeleton g,
            ∃ package : CanonicalRootedRealizationPackage skeleton,
              ∃ mesh : ℝ,
                ∃ hmesh : 0 < mesh,
                  ∃ certificate :
                      PrescribedMeshCertificate package.realization mesh,
                    Nonempty
                      (CanonicalRootedRealizationPackage.TerminalRestrictedAccumulatedMeshOverlapCoherence
                        package hcurv hmesh certificate)

/-- Fixed-target canonical rooted completion data at the sound
terminal-restricted homotopy-grid boundary.

For each unit-curvature metric, the provider chooses a canonical rooted
package and a positive parameter for its terminal-restricted domains.  On
every selected overlap it supplies two independent terminal paths, one fixed
realized homotopy grid, and the horizontal and vertical smallness proofs at
that grid's chosen curvature radius.  No strict-factor schedule or existence
claim for those certificates is hidden in this definition. -/
def FixedTargetCanonicalRootedTerminalRestrictedHomotopyGridOverlapCompletion3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        ∀ hcurv : HasConstantSectionalCurvature3 g 1,
          ∃ skeleton : RootedCartanPathSkeleton g,
            ∃ package : CanonicalRootedRealizationPackage skeleton,
              ∃ mesh : ℝ,
                ∃ hmesh : 0 < mesh,
                  Nonempty
                    (CanonicalRootedRealizationPackage.TerminalRestrictedHomotopyGridOverlapCoherence
                      package hcurv hmesh)

/-- Fixed-target canonical rooted completion at the narrowest schedule-free
derived-terminal homotopy-grid boundary.

The chosen schedule-free restricted domains canonically produce both terminal
paths.  For every actual overlap, the provider must still supply a fully
realized homotopy grid, its boundary predecessor traces, and horizontal and
vertical smallness at that grid's chosen curvature radius. -/
def FixedTargetCanonicalRootedDerivedTerminalHomotopyGridOverlapCompletion3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        ∀ hcurv : HasConstantSectionalCurvature3 g 1,
          ∃ skeleton : RootedCartanPathSkeleton g,
            ∃ package : CanonicalRootedRealizationPackage skeleton,
              ∃ mesh : ℝ,
                ∃ hmesh : 0 < mesh,
                  Nonempty
                    (CanonicalRootedRealizationPackage.DerivedTerminalHomotopyGridOverlapCoherence
                      package hcurv hmesh)

/-- Direct end-to-end fixed-target mean-scalar sphere conclusion from one
selected proof-bearing smooth-transition atlas, with unit-curvature
recognition discharged by explicit canonical rooted completion data.

The completion provider remains downstream of atlas selection and of the
analytic construction of the unit-curvature metric. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedAdaptiveOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion : FixedTargetCanonicalRootedAdaptiveOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_unitRecognition
      smoothData analytic
  intro _charted _smoothManifold _secondCountable _connected
  exact
    unitConstantCurvatureSphereRecognition3_of_canonicalRootedAdaptiveOverlapCoherence
      completion

/-- Direct end-to-end fixed-target mean-scalar sphere conclusion from one
selected smooth atlas and the reduced terminal-domain-only Cartan payload. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedTerminalRestrictedAccumulatedMeshOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedTerminalRestrictedAccumulatedMeshOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_unitRecognition
      smoothData analytic
  intro _charted _smoothManifold _secondCountable _connected
  exact
    CanonicalRootedRealizationPackage.unitConstantCurvatureSphereRecognition3_of_canonicalRootedTerminalRestrictedAccumulatedMeshOverlapCoherence
      completion

/-- Direct end-to-end fixed-target mean-scalar sphere conclusion from one
selected smooth atlas and the schedule-free terminal-restricted homotopy-grid
payload. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedTerminalRestrictedHomotopyGridOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedTerminalRestrictedHomotopyGridOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_unitRecognition
      smoothData analytic
  intro _charted _smoothManifold _secondCountable _connected
  exact
    CanonicalRootedRealizationPackage.unitConstantCurvatureSphereRecognition3_of_canonicalRootedTerminalRestrictedHomotopyGridOverlapCoherence
      completion

/-- Direct end-to-end fixed-target mean-scalar sphere conclusion from one
selected smooth atlas and the derived-terminal homotopy-grid payload. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedDerivedTerminalHomotopyGridOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_unitRecognition
      smoothData analytic
  intro _charted _smoothManifold _secondCountable _connected
  exact
    CanonicalRootedRealizationPackage.unitConstantCurvatureSphereRecognition3_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
      completion

/-- Compatibility corollary for the Moise-shaped split smoothability
boundary, with unit-curvature recognition discharged by explicit canonical
rooted completion data.

Smoothability selects the atlas, the forward-only analytic provider constructs
the unit-curvature metric, and only then does the completion provider construct
the rooted skeleton/package and prove adaptive overlap coherence.  Thus no
recognition data are used to choose the smooth atlas.
-/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_localTransitionSmoothing_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedAdaptiveOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion : FixedTargetCanonicalRootedAdaptiveOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases admits with ⟨c1Atlas, c1Manifold⟩
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  exact
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedAdaptiveOverlapCoherence
      (localSmoothing c1Atlas c1Manifold) analytic completion

/-- Moise-shaped compatibility corollary using the reduced
terminal-domain-only Cartan payload. -/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_localTransitionSmoothing_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedTerminalRestrictedAccumulatedMeshOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedTerminalRestrictedAccumulatedMeshOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases admits with ⟨c1Atlas, c1Manifold⟩
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  exact
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedTerminalRestrictedAccumulatedMeshOverlapCoherence
      (localSmoothing c1Atlas c1Manifold) analytic completion

/-- Moise-shaped compatibility corollary using the sound, schedule-free
terminal-restricted homotopy-grid payload. -/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_localTransitionSmoothing_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedTerminalRestrictedHomotopyGridOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedTerminalRestrictedHomotopyGridOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases admits with ⟨c1Atlas, c1Manifold⟩
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  exact
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedTerminalRestrictedHomotopyGridOverlapCoherence
      (localSmoothing c1Atlas c1Manifold) analytic completion

/-- Moise-shaped compatibility corollary at the narrowest schedule-free
derived-terminal homotopy-grid boundary. -/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_localTransitionSmoothing_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (completion :
      FixedTargetCanonicalRootedDerivedTerminalHomotopyGridOverlapCompletion3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases admits with ⟨c1Atlas, c1Manifold⟩
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  exact
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
      (localSmoothing c1Atlas c1Manifold) analytic completion

end Poincare
