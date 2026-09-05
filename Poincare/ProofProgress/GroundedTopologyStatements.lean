import Poincare.TopologyExtraction
import Poincare.ProofProgress.GroundedPerelmanSingularityControl

/-!
# Concrete sources for topology after surgery

This module contains the stable input types for the topology consumer. A source
owns one realized surgery trace and the finite-extinction package selected by
that trace. The retained Perelman production source is indexed by that exact
package's flow. Matching uses this shared flow and actual trace data. Equality
between the older proof-valued control records would add no such guarantee.

The covering-construction statement below remains an open mathematical
obligation. Neither a trace nor its finite component partition supplies the
neck/cap gluing and recognition argument by itself. The legacy extinction
proposition is retained only as the index required by the existing trace API.
The consumer receives all the concrete data as its argument.

The inherited trace has a nonempty finite event prefix. Its component regions
are subsets of the original manifold, and are not modeled as the physical
surviving time slices. Existence of such traces, including the separate question
of how to handle flows without surgery events, is not proved here.
The component payloads supply no connectedness or carrier homeomorphisms, and
the trace does not identify its event regions with the Perelman high-curvature
regions. Those geometric obligations remain open.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Poincare

universe u

/-- A concrete topology input with one shared surgery construction, component
decomposition, trace, and grounded Perelman production source. The analytic and
surgery data live in `trace.decompositionSource.package`; there is no second
independently selected construction. -/
structure GroundedTopologySource
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] : Type (u + 1) where
  extinction : FiniteExtinctionByRicciFlowWithSurgery M
  decomposition : HasExtinctionTopologyDecomposition M extinction
  traceStage : Type u
  trace :
    ExtinctionSurgeryTraceRealizationSource M extinction decomposition traceStage
  perelmanSource :
    letI := trace.smooth
    PerelmanSingularityControlProductionSource
      (ricci_flow_data_of_surgery_package trace.decompositionSource.package)

/-- A topology source at a chosen compatible atlas on the same topological
space. Smoothability may replace the supplied topological atlas; it does not
assert that every supplied atlas is already differentiable. -/
structure GroundedTopologyPresentation
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M] : Type (u + 1) where
  chartedSpace : ChartedSpace ThreeManifoldModel M
  source : @GroundedTopologySource M _ _ chartedSpace _ _

/-- The analytic, surgery, component-decomposition, and finite-trace existence
obligation at a chosen compatible atlas. The supplied atlas witnesses the
topological manifold hypothesis and need not equal the chosen smooth atlas.
This statement does not include a covering or a homeomorphism. -/
def GroundedTopologyUniversalSourceStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (GroundedTopologyPresentation M)

/-- The unresolved topological reconstruction obligation on a fixed concrete
source. Its proof must build the spherical covering from the surgery and
component data carried by the argument. -/
def GroundedTopologyThreeSphereCoveringStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_source : GroundedTopologySource M),
      ∃ p : ThreeSphere → M, IsCoveringMap p

end Poincare
