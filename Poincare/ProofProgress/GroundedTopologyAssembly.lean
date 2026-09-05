import Poincare.ProofProgress.GroundedTopologyStatements
import Poincare.ProofProgress.ExtinctionSurgeryTraceAncestry
import Poincare.Global.CoveringSkeleton

/-!
# Consequences of a concrete surgery source

The component and event claims below follow from the actual trace. The final
assembly passes that same source to the explicitly assumed covering
construction, then applies simply connected covering-space rigidity.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Poincare

universe u

namespace GroundedTopologySource

variable
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (source : GroundedTopologySource M)

/-- The terminal active components cover the initial manifold, because their
regions are the regions of the source's fixed decomposition. -/
theorem terminal_components_cover :
    (⋃ component,
      source.trace.activeComponentSet source.trace.terminalStage component) =
        Set.univ := by
  letI := source.trace.smooth
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ component,
      (source.trace.decompositionSource.componentTopologyPayload component).componentSet := by
    rw [source.trace.decompositionSource.components_cover]
    exact Set.mem_univ x
  obtain ⟨component, hcomponent⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨source.trace.terminalComponentEquiv.symm component, ?_⟩
  simpa only [source.trace.terminalComponentSet_eq, Equiv.apply_symm_apply]
    using hcomponent

/-- Every point has exactly one terminal component. This uses both coverage
and the trace's disjointness condition. -/
theorem unique_terminal_component (x : M) :
    ∃! component,
      x ∈ source.trace.activeComponentSet source.trace.terminalStage component := by
  have hx : x ∈ ⋃ component,
      source.trace.activeComponentSet source.trace.terminalStage component := by
    rw [source.terminal_components_cover]
    exact Set.mem_univ x
  obtain ⟨component, hcomponent⟩ := Set.mem_iUnion.mp hx
  refine ⟨component, hcomponent, ?_⟩
  intro other hother
  by_contra hne
  exact Set.disjoint_left.mp
    (source.trace.activeComponents_pairwise source.trace.terminalStage
      (Set.mem_univ other) (Set.mem_univ component) hne)
    hother hcomponent

/-- A point in a child component outside the event region already lies in
that child's actual parent. -/
theorem mem_parent_of_mem_child_off_event
    {stage nextStage : source.traceStage}
    (hnext : source.trace.eventIndex nextStage = source.trace.eventIndex stage + 1)
    (child : source.trace.activeComponentIndex nextStage)
    {x : M}
    (hx : x ∈ source.trace.activeComponentSet nextStage child)
    (hoff : x ∉ source.trace.eventRegion stage) :
    x ∈ source.trace.activeComponentSet stage
      (source.trace.successorParent hnext child) := by
  have hmem :
      x ∈ (⋃ sibling : { sibling : source.trace.activeComponentIndex nextStage //
            source.trace.successorParent hnext sibling =
              source.trace.successorParent hnext child },
          source.trace.activeComponentSet nextStage sibling.1) \
        source.trace.eventRegion stage :=
    ⟨Set.mem_iUnion.mpr ⟨⟨child, rfl⟩, hx⟩, hoff⟩
  rw [source.trace.successor_children_agree_off_event] at hmem
  exact hmem.1

/-- Every stage's recorded component regions cover the original manifold.
These regions do not assert that the physical flow slice survives extinction.
Backwards induction uses the terminal cover; points inside the event lie in an active
component, and points outside it pass from a child to its parent. -/
theorem active_components_cover (stage : source.traceStage) :
    (⋃ component, source.trace.activeComponentSet stage component) =
      Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hterminal : ∃ component,
      x ∈ source.trace.activeComponentSet source.trace.terminalStage component := by
    apply Set.mem_iUnion.mp
    rw [source.terminal_components_cover]
    exact Set.mem_univ x
  have hstageAt : ∀ i : Fin (source.trace.terminalEventIndex + 1),
      ∃ component,
        x ∈ source.trace.activeComponentSet (source.trace.stageAt i) component := by
    apply Fin.reverseInduction
    · rw [← source.trace.terminalStage_eq_stageAt_last]
      exact hterminal
    · intro i ih
      by_cases hxEvent : x ∈ source.trace.eventRegion (source.trace.stageAt i.castSucc)
      · exact Set.mem_iUnion.mp
          (source.trace.eventRegion_subset_activeComponents
            (source.trace.stageAt i.castSucc) hxEvent)
      · obtain ⟨child, hxChild⟩ := ih
        exact ⟨source.trace.successorParent (source.trace.stageAt_succ_eventIndex i) child,
          source.mem_parent_of_mem_child_off_event
            (source.trace.stageAt_succ_eventIndex i) child hxChild hxEvent⟩
  apply Set.mem_iUnion.mpr
  have hstage : source.trace.stageAt (source.trace.stageEventIndex stage) = stage :=
    source.trace.stageEventIndex.symm_apply_apply stage
  have h := hstageAt (source.trace.stageEventIndex stage)
  rw [hstage] at h
  exact h

/-- At every stage, each point belongs to exactly one active component. -/
theorem unique_active_component (stage : source.traceStage) (x : M) :
    ∃! component, x ∈ source.trace.activeComponentSet stage component := by
  have hx : x ∈ ⋃ component, source.trace.activeComponentSet stage component := by
    rw [source.active_components_cover stage]
    exact Set.mem_univ x
  obtain ⟨component, hcomponent⟩ := Set.mem_iUnion.mp hx
  refine ⟨component, hcomponent, ?_⟩
  intro other hother
  by_contra hne
  exact Set.disjoint_left.mp
    (source.trace.activeComponents_pairwise stage
      (Set.mem_univ other) (Set.mem_univ component) hne)
    hother hcomponent

/-- The retained Perelman source supplies a positive high-Ricci spacetime
point on the trace's actual surgery-payload flow, and the trace locates it in a
unique recorded component at every stage. The flow identity transfers the
curvature statement; the proved partition supplies component membership. -/
theorem highRicciPoint_in_unique_active_component (stage : source.traceStage) :
    letI := source.trace.smooth
    ∃ t : ℝ, ∃ x : M,
      0 < source.perelmanSource.spacetime.highCurvatureThreshold ∧
      source.perelmanSource.spacetime.highCurvatureThreshold ≤
        perelmanRicciTensorNormAt
          source.trace.surgeryPayloadSource.flow t x ∧
      ∃! component, x ∈ source.trace.activeComponentSet stage component := by
  letI := source.trace.smooth
  obtain ⟨point⟩ :=
    source.perelmanSource.spacetime.highRicciCurvatureSpacetimePoint_nonempty
  refine ⟨point.1.1, point.1.2,
    source.perelmanSource.spacetime.highCurvatureThresholdPositive,
    ?_, source.unique_active_component stage point.1.2⟩
  rw [source.trace.surgeryPayloadFlow_eq]
  exact point.2

end GroundedTopologySource

/-- Conditional assembly through the concrete source. The covering theorem
receives the complete source, including the shared surgery trace and Perelman
production data; the proof does not project it to legacy extinction first. -/
theorem poincare_statement_of_groundedTopologySources_and_covering
    (sources : GroundedTopologyUniversalSourceStatement.{u})
    (covering : GroundedTopologyThreeSphereCoveringStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  intro M _top _t2 _charted _simple _compact
  obtain ⟨presentation⟩ := sources M
  letI : ChartedSpace ThreeManifoldModel M := presentation.chartedSpace
  letI : LocPathConnectedSpace M :=
    ChartedSpace.locPathConnectedSpace ThreeManifoldModel M
  obtain ⟨p, hp⟩ := covering M presentation.source
  exact ⟨(GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected hp).symm⟩

end Poincare
