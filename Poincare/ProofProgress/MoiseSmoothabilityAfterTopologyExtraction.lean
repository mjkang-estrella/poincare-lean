import Poincare.ProofProgress.MoiseSmoothabilityTarget

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
Recognition by the project three-sphere supplies an actual surgery-model
smooth structure.  The proof first moves to the one-point compactification
model and then transports its concrete smooth atlas back to the source.
-/
theorem admitsSurgeryModelSmoothStructure_of_homeomorph_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    AdmitsSurgeryModelSmoothStructure M :=
  admitsSurgeryModelSmoothStructure_of_homeomorph_onePoint
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)

/--
At a fixed finite-extinction witness, a completed topology-extraction package
therefore closes the corrected, existence-shaped smoothability target for the
same source manifold.
-/
theorem admitsSurgeryModelSmoothStructure_of_topologyPackage
    (package : ExtinctionTopologyExtractionPackage.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    AdmitsSurgeryModelSmoothStructure M :=
  admitsSurgeryModelSmoothStructure_of_homeomorph_threeSphere
    (homeomorphism_of_topology_package package M extinction)

/--
Universal finite extinction together with a completed topology-extraction
package implies the corrected Moise smoothability statement.  This is an
existence theorem for a transported smooth atlas; it makes no false claim that
an arbitrary ambient topological atlas is already smooth.
-/
theorem moiseSmoothabilityStatement_of_universalFiniteExtinction_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    MoiseSmoothabilityStatement.{u} := by
  intro M _top _t2 _charted _simple _compact
  exact admitsSurgeryModelSmoothStructure_of_topologyPackage
    package M (finiteExtinction M)

end Poincare
