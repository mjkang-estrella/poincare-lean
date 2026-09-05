import Poincare.TopologyExtraction

/-!
# Backward ancestry in an extinction surgery trace

A terminal active component has a canonical ancestor at each represented
event index, obtained by reverse induction through the trace's actual
`successorParent` maps.  The construction is unique and its dependent vertex
type is finite.

This direction is deliberate.  Nothing here says that every earlier component
has a terminal descendant, and no cancellation or homeomorphism package is
introduced.
-/

noncomputable section

namespace Poincare

universe u

/-- The canonical trace stage carrying a given finite event index. -/
def ExtinctionSurgeryTraceRealizationSource.stageAt
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (i : Fin (source.terminalEventIndex + 1)) : traceStage :=
  source.stageEventIndex.symm i

@[simp] theorem ExtinctionSurgeryTraceRealizationSource.stageEventIndex_stageAt
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (i : Fin (source.terminalEventIndex + 1)) :
    source.stageEventIndex (source.stageAt i) = i :=
  source.stageEventIndex.apply_symm_apply i

@[simp] theorem ExtinctionSurgeryTraceRealizationSource.eventIndex_stageAt
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (i : Fin (source.terminalEventIndex + 1)) :
    source.eventIndex (source.stageAt i) = i.val := by
  rw [source.eventIndex_eq]
  simp

/-- Consecutive canonical finite indices name consecutive trace stages. -/
theorem ExtinctionSurgeryTraceRealizationSource.stageAt_succ_eventIndex
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (i : Fin source.terminalEventIndex) :
    source.eventIndex (source.stageAt i.succ) =
      source.eventIndex (source.stageAt i.castSucc) + 1 := by
  simp

/-- The distinguished terminal stage is the canonical stage at the last
finite event index. -/
theorem ExtinctionSurgeryTraceRealizationSource.terminalStage_eq_stageAt_last
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage) :
    source.terminalStage = source.stageAt (Fin.last source.terminalEventIndex) := by
  apply source.eventIndex_injective
  rw [source.terminalStage_eventIndex, source.eventIndex_stageAt]
  exact Fin.val_last source.terminalEventIndex

/-- Reindex a terminal component as a component of the canonical last stage. -/
def ExtinctionSurgeryTraceRealizationSource.terminalComponentAtLast
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.activeComponentIndex source.terminalStage) :
    source.activeComponentIndex
      (source.stageAt (Fin.last source.terminalEventIndex)) :=
  Eq.mp
    (congrArg source.activeComponentIndex
      source.terminalStage_eq_stageAt_last)
    component

/-- Iterating `successorParent` backwards gives the canonical ancestor of a
terminal component at every represented event index. -/
noncomputable def ExtinctionSurgeryTraceRealizationSource.terminalAncestorAt
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.activeComponentIndex source.terminalStage)
    (i : Fin (source.terminalEventIndex + 1)) :
    source.activeComponentIndex (source.stageAt i) :=
  Fin.reverseInduction
    (source.terminalComponentAtLast component)
    (fun j child =>
      source.successorParent (source.stageAt_succ_eventIndex j) child)
    i

@[simp] theorem ExtinctionSurgeryTraceRealizationSource.terminalAncestorAt_last
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.activeComponentIndex source.terminalStage) :
    source.terminalAncestorAt component (Fin.last source.terminalEventIndex) =
      source.terminalComponentAtLast component := by
  simp [ExtinctionSurgeryTraceRealizationSource.terminalAncestorAt]

@[simp] theorem ExtinctionSurgeryTraceRealizationSource.terminalAncestorAt_castSucc
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.activeComponentIndex source.terminalStage)
    (i : Fin source.terminalEventIndex) :
    source.terminalAncestorAt component i.castSucc =
      source.successorParent (source.stageAt_succ_eventIndex i)
        (source.terminalAncestorAt component i.succ) := by
  simp [ExtinctionSurgeryTraceRealizationSource.terminalAncestorAt]

/-- The backwards parent path of a terminal component is unique: any other
dependent component path with the same terminal value and the same parent
recursion agrees at every stage. -/
theorem ExtinctionSurgeryTraceRealizationSource.terminalAncestorAt_unique
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.activeComponentIndex source.terminalStage)
    (ancestry : (i : Fin (source.terminalEventIndex + 1)) →
      source.activeComponentIndex (source.stageAt i))
    (hterminal : ancestry (Fin.last source.terminalEventIndex) =
      source.terminalComponentAtLast component)
    (hparent : ∀ i : Fin source.terminalEventIndex,
      ancestry i.castSucc =
        source.successorParent (source.stageAt_succ_eventIndex i)
          (ancestry i.succ)) :
    ∀ i, ancestry i = source.terminalAncestorAt component i := by
  apply Fin.reverseInduction
  · simpa using hterminal
  · intro i ih
    rw [hparent i, source.terminalAncestorAt_castSucc component i, ih]

/-- A fixed decomposition component determines a canonical component at every
represented surgery stage by first identifying its terminal component and
then following the actual parent maps backwards. -/
noncomputable def ExtinctionSurgeryTraceRealizationSource.decompositionComponentAncestorAt
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.decompositionData.componentIndex)
    (i : Fin (source.terminalEventIndex + 1)) :
    source.activeComponentIndex (source.stageAt i) :=
  source.terminalAncestorAt
    (source.terminalComponentEquiv.symm component) i

/-- At the last canonical stage, the decomposition ancestry is the transported
terminal component selected by `terminalComponentEquiv`. -/
@[simp] theorem ExtinctionSurgeryTraceRealizationSource.decompositionComponentAncestorAt_last
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.decompositionData.componentIndex) :
    source.decompositionComponentAncestorAt component
        (Fin.last source.terminalEventIndex) =
      source.terminalComponentAtLast
        (source.terminalComponentEquiv.symm component) := by
  simp [ExtinctionSurgeryTraceRealizationSource.decompositionComponentAncestorAt]

/-- The decomposition-component ancestry obeys the same actual parent
recursion at every preceding event index. -/
@[simp] theorem ExtinctionSurgeryTraceRealizationSource.decompositionComponentAncestorAt_castSucc
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.decompositionData.componentIndex)
    (i : Fin source.terminalEventIndex) :
    source.decompositionComponentAncestorAt component i.castSucc =
      source.successorParent (source.stageAt_succ_eventIndex i)
        (source.decompositionComponentAncestorAt component i.succ) := by
  simp [ExtinctionSurgeryTraceRealizationSource.decompositionComponentAncestorAt]

/-- Along the canonical decomposition-component lineage, the union of the
next-stage children can differ from its parent only inside the actual surgery
event region. -/
theorem ExtinctionSurgeryTraceRealizationSource.decompositionComponentAncestor_children_symmDiff_parent_subset_eventRegion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage)
    (component : source.decompositionData.componentIndex)
    (i : Fin source.terminalEventIndex) :
    symmDiff
        (⋃ child : { child : source.activeComponentIndex (source.stageAt i.succ) //
            source.successorParent (source.stageAt_succ_eventIndex i) child =
              source.decompositionComponentAncestorAt component i.castSucc },
          source.activeComponentSet (source.stageAt i.succ) child.1)
        (source.activeComponentSet (source.stageAt i.castSucc)
          (source.decompositionComponentAncestorAt component i.castSucc)) ⊆
      source.eventRegion (source.stageAt i.castSucc) :=
  source.successor_children_symmDiff_parent_subset_eventRegion
    (source.stageAt_succ_eventIndex i)
    (source.decompositionComponentAncestorAt component i.castSucc)

/-- The full stage-component ancestry graph has finitely many vertices. -/
theorem ExtinctionSurgeryTraceRealizationSource.finite_ancestryVertices
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {extinction : FiniteExtinctionByRicciFlowWithSurgery M}
    {decomposition : HasExtinctionTopologyDecomposition M extinction}
    {traceStage : Type u}
    (source : ExtinctionSurgeryTraceRealizationSource
      M extinction decomposition traceStage) :
    Nonempty
      (Fintype
        (Σ i : Fin (source.terminalEventIndex + 1),
          source.activeComponentIndex (source.stageAt i))) := by
  letI (i : Fin (source.terminalEventIndex + 1)) :
      Fintype (source.activeComponentIndex (source.stageAt i)) :=
    source.finiteActiveComponentIndex (source.stageAt i)
  exact ⟨inferInstance⟩

end Poincare
