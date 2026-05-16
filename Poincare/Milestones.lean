/-
This file records proof obligations that would have to be discharged before the
statement in `Poincare.Statement` can become a theorem.

It contains no axioms, no theorem claims, and no proof placeholders. The entries
are data, not propositions, so they cannot be used as proofs of mathematical
obligations.
-/

import Poincare.Statement

namespace Poincare

universe u

/-- Named missing dependency layers for a future proof. -/
inductive DependencyMilestone where
  /--
  Smoothability/compatibility bridge from the topological 3-manifold target to
  the smooth model used by Ricci flow with surgery.
  -/
  | smoothabilityBridge
  /--
  Riemannian metrics, curvature, Ricci curvature, scalar curvature, and the
  Ricci flow equation at the level needed for closed 3-manifolds.
  -/
  | ricciFlowAnalyticFoundation
  /-- Existence and control of Ricci flow with surgery for closed 3-manifolds. -/
  | ricciFlowWithSurgery
  /--
  Perelman non-collapsing, canonical-neighborhood, and singularity-analysis
  inputs needed by the surgery argument.
  -/
  | perelmanSingularityControl
  /--
  Finite extinction for compact simply connected 3-manifolds under Ricci flow
  with surgery.
  -/
  | finiteExtinction
  /--
  The topological extraction step: finite extinction implies the manifold is
  homeomorphic to the standard 3-sphere.
  -/
  | extinctionToSphereHomeomorphism
  deriving DecidableEq, Repr

/-- A data ledger of the currently missing dependency layers. -/
def dependencyMilestoneLedger : List DependencyMilestone :=
  [ DependencyMilestone.smoothabilityBridge
  , DependencyMilestone.ricciFlowAnalyticFoundation
  , DependencyMilestone.ricciFlowWithSurgery
  , DependencyMilestone.perelmanSingularityControl
  , DependencyMilestone.finiteExtinction
  , DependencyMilestone.extinctionToSphereHomeomorphism
  ]

/-- The dependency milestone ledger is exactly the six-entry list literal. -/
theorem dependencyMilestoneLedger_eq :
    dependencyMilestoneLedger =
      [ DependencyMilestone.smoothabilityBridge
      , DependencyMilestone.ricciFlowAnalyticFoundation
      , DependencyMilestone.ricciFlowWithSurgery
      , DependencyMilestone.perelmanSingularityControl
      , DependencyMilestone.finiteExtinction
      , DependencyMilestone.extinctionToSphereHomeomorphism
      ] :=
  rfl

/-- The dependency ledger has exactly the six named missing layers. -/
theorem dependencyMilestoneLedger_length :
    dependencyMilestoneLedger.length = 6 :=
  rfl

/-- The dependency-ledger length theorem is the direct `rfl` proof. -/
theorem dependencyMilestoneLedger_length_eq :
    dependencyMilestoneLedger_length =
      (rfl : dependencyMilestoneLedger.length = 6) := by
  apply Subsingleton.elim

/-- The smoothability bridge milestone is present in the dependency ledger. -/
theorem smoothabilityBridge_mem_dependencyMilestoneLedger :
    DependencyMilestone.smoothabilityBridge ∈ dependencyMilestoneLedger := by
  simp [dependencyMilestoneLedger]

/-- The smoothability membership theorem is the direct list-membership proof. -/
theorem smoothabilityBridge_mem_dependencyMilestoneLedger_eq :
    smoothabilityBridge_mem_dependencyMilestoneLedger =
      (by
        simp [dependencyMilestoneLedger] :
        DependencyMilestone.smoothabilityBridge ∈ dependencyMilestoneLedger) := by
  apply Subsingleton.elim

/-- The Ricci-flow analytic-foundation milestone is present in the dependency ledger. -/
theorem ricciFlowAnalyticFoundation_mem_dependencyMilestoneLedger :
    DependencyMilestone.ricciFlowAnalyticFoundation ∈ dependencyMilestoneLedger := by
  simp [dependencyMilestoneLedger]

/-- The analytic-foundation membership theorem is the direct list-membership proof. -/
theorem ricciFlowAnalyticFoundation_mem_dependencyMilestoneLedger_eq :
    ricciFlowAnalyticFoundation_mem_dependencyMilestoneLedger =
      (by
        simp [dependencyMilestoneLedger] :
        DependencyMilestone.ricciFlowAnalyticFoundation ∈
          dependencyMilestoneLedger) := by
  apply Subsingleton.elim

/-- The Ricci-flow-with-surgery milestone is present in the dependency ledger. -/
theorem ricciFlowWithSurgery_mem_dependencyMilestoneLedger :
    DependencyMilestone.ricciFlowWithSurgery ∈ dependencyMilestoneLedger := by
  simp [dependencyMilestoneLedger]

/-- The Ricci-flow-with-surgery membership theorem is the direct list-membership proof. -/
theorem ricciFlowWithSurgery_mem_dependencyMilestoneLedger_eq :
    ricciFlowWithSurgery_mem_dependencyMilestoneLedger =
      (by
        simp [dependencyMilestoneLedger] :
        DependencyMilestone.ricciFlowWithSurgery ∈ dependencyMilestoneLedger) := by
  apply Subsingleton.elim

/-- The Perelman singularity-control milestone is present in the dependency ledger. -/
theorem perelmanSingularityControl_mem_dependencyMilestoneLedger :
    DependencyMilestone.perelmanSingularityControl ∈ dependencyMilestoneLedger := by
  simp [dependencyMilestoneLedger]

/-- The Perelman-control membership theorem is the direct list-membership proof. -/
theorem perelmanSingularityControl_mem_dependencyMilestoneLedger_eq :
    perelmanSingularityControl_mem_dependencyMilestoneLedger =
      (by
        simp [dependencyMilestoneLedger] :
        DependencyMilestone.perelmanSingularityControl ∈
          dependencyMilestoneLedger) := by
  apply Subsingleton.elim

/-- The finite-extinction milestone is present in the dependency ledger. -/
theorem finiteExtinction_mem_dependencyMilestoneLedger :
    DependencyMilestone.finiteExtinction ∈ dependencyMilestoneLedger := by
  simp [dependencyMilestoneLedger]

/-- The finite-extinction membership theorem is the direct list-membership proof. -/
theorem finiteExtinction_mem_dependencyMilestoneLedger_eq :
    finiteExtinction_mem_dependencyMilestoneLedger =
      (by
        simp [dependencyMilestoneLedger] :
        DependencyMilestone.finiteExtinction ∈ dependencyMilestoneLedger) := by
  apply Subsingleton.elim

/-- The post-extinction topology milestone is present in the dependency ledger. -/
theorem extinctionToSphereHomeomorphism_mem_dependencyMilestoneLedger :
    DependencyMilestone.extinctionToSphereHomeomorphism ∈ dependencyMilestoneLedger := by
  simp [dependencyMilestoneLedger]

/-- The topology-extraction membership theorem is the direct list-membership proof. -/
theorem extinctionToSphereHomeomorphism_mem_dependencyMilestoneLedger_eq :
    extinctionToSphereHomeomorphism_mem_dependencyMilestoneLedger =
      (by
        simp [dependencyMilestoneLedger] :
        DependencyMilestone.extinctionToSphereHomeomorphism ∈
          dependencyMilestoneLedger) := by
  apply Subsingleton.elim

/-- The dependency ledger contains exactly the listed milestones. -/
theorem dependencyMilestoneLedger_mem (milestone : DependencyMilestone) :
    milestone ∈ dependencyMilestoneLedger ↔
      milestone = DependencyMilestone.smoothabilityBridge ∨
      milestone = DependencyMilestone.ricciFlowAnalyticFoundation ∨
      milestone = DependencyMilestone.ricciFlowWithSurgery ∨
      milestone = DependencyMilestone.perelmanSingularityControl ∨
      milestone = DependencyMilestone.finiteExtinction ∨
      milestone = DependencyMilestone.extinctionToSphereHomeomorphism := by
  cases milestone <;> simp [dependencyMilestoneLedger]

/--
The milestone-ledger membership characterization is exactly the case split over
the six listed milestones.
-/
theorem dependencyMilestoneLedger_mem_eq :
    dependencyMilestoneLedger_mem =
      (by
        intro milestone
        cases milestone <;> simp [dependencyMilestoneLedger]) := by
  funext milestone
  apply Subsingleton.elim

/-- The dependency milestone ledger contains no duplicate milestone entries. -/
theorem dependencyMilestoneLedger_nodup :
    dependencyMilestoneLedger.Nodup := by
  decide

/-- The no-duplicate theorem is the direct decidable proof for the six-entry ledger. -/
theorem dependencyMilestoneLedger_nodup_eq :
    dependencyMilestoneLedger_nodup =
      (by decide : dependencyMilestoneLedger.Nodup) := by
  apply Subsingleton.elim

/--
External formalization blockers reported by the completion audit.

These are data labels, not propositions and not assumptions. They record the
remaining upstream/library surfaces that must become theorem-producing Lean
developments before the local conditional assembly can be replaced by an
unconditional proof.
-/
inductive ExternalFormalizationBlocker where
  /--
  Mathlib's canonical 3D Poincare shortcut statements are still marked as
  requested-but-unproved upstream, so the project cannot close by importing
  those names.
  -/
  | mathlibThreeDimensionalPoincareProofWanted
  /--
  Ricci-specific Riemannian geometry declarations needed by the analytic
  foundation are not available as reusable mathlib theorem surfaces.
  -/
  | ricciSpecificGeometrySurface
  /--
  Ricci flow with surgery, Perelman control, and finite-extinction declarations
  are not available as reusable mathlib theorem surfaces.
  -/
  | ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface
  deriving DecidableEq, Repr

/-- The checked ledger of current external formalization blockers. -/
def externalFormalizationBlockerLedger : List ExternalFormalizationBlocker :=
  [ ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted
  , ExternalFormalizationBlocker.ricciSpecificGeometrySurface
  , ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface
  ]

/-- The external blocker ledger is exactly the three-entry audit-blocker list. -/
theorem externalFormalizationBlockerLedger_eq :
    externalFormalizationBlockerLedger =
      [ ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted
      , ExternalFormalizationBlocker.ricciSpecificGeometrySurface
      , ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface
      ] :=
  rfl

/-- The external blocker ledger has exactly three entries. -/
theorem externalFormalizationBlockerLedger_length :
    externalFormalizationBlockerLedger.length = 3 :=
  rfl

/-- The external-blocker ledger length theorem is the direct `rfl` proof. -/
theorem externalFormalizationBlockerLedger_length_eq :
    externalFormalizationBlockerLedger_length =
      (rfl : externalFormalizationBlockerLedger.length = 3) := by
  apply Subsingleton.elim

/-- The external blocker ledger contains no duplicate blocker labels. -/
theorem externalFormalizationBlockerLedger_nodup :
    externalFormalizationBlockerLedger.Nodup := by
  decide

/-- The external-blocker no-duplicate theorem is the direct decidable proof. -/
theorem externalFormalizationBlockerLedger_nodup_eq :
    externalFormalizationBlockerLedger_nodup =
      (by decide : externalFormalizationBlockerLedger.Nodup) := by
  apply Subsingleton.elim

/-- The external blocker ledger contains exactly the audit-blocker labels. -/
theorem externalFormalizationBlockerLedger_mem
    (blocker : ExternalFormalizationBlocker) :
    blocker ∈ externalFormalizationBlockerLedger ↔
      blocker =
        ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted ∨
      blocker = ExternalFormalizationBlocker.ricciSpecificGeometrySurface ∨
      blocker =
        ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface := by
  cases blocker <;> simp [externalFormalizationBlockerLedger]

/-- The external-blocker membership theorem is exactly the three-case split. -/
theorem externalFormalizationBlockerLedger_mem_eq :
    externalFormalizationBlockerLedger_mem =
      (by
        intro blocker
        cases blocker <;> simp [externalFormalizationBlockerLedger]) := by
  funext blocker
  apply Subsingleton.elim

/--
Statement-adapter surfaces that match the upstream 3D Poincare statement shapes.

These are data labels for the local adapters in `Poincare.Statement`; they are
not theorem claims and do not import the unavailable upstream shortcut names.
-/
inductive MathlibPoincareStatementAdapter where
  /-- Adapter for `MathlibTopologicalPoincareThreeStatement`. -/
  | topologicalThreeSphere
  /-- Adapter for `MathlibSmoothPoincareThreeStatement`. -/
  | smoothThreeSphere
  deriving DecidableEq, Repr

/-- The checked ledger of mathlib-shaped statement adapters. -/
def mathlibPoincareStatementAdapterLedger :
    List MathlibPoincareStatementAdapter :=
  [ MathlibPoincareStatementAdapter.topologicalThreeSphere
  , MathlibPoincareStatementAdapter.smoothThreeSphere
  ]

/-- The adapter ledger is exactly the topological and smooth 3-sphere adapters. -/
theorem mathlibPoincareStatementAdapterLedger_eq :
    mathlibPoincareStatementAdapterLedger =
      [ MathlibPoincareStatementAdapter.topologicalThreeSphere
      , MathlibPoincareStatementAdapter.smoothThreeSphere
      ] :=
  rfl

/-- The adapter ledger has exactly two entries. -/
theorem mathlibPoincareStatementAdapterLedger_length :
    mathlibPoincareStatementAdapterLedger.length = 2 :=
  rfl

/-- The adapter-ledger length theorem is the direct `rfl` proof. -/
theorem mathlibPoincareStatementAdapterLedger_length_eq :
    mathlibPoincareStatementAdapterLedger_length =
      (rfl : mathlibPoincareStatementAdapterLedger.length = 2) := by
  apply Subsingleton.elim

/-- The adapter ledger contains no duplicate adapter labels. -/
theorem mathlibPoincareStatementAdapterLedger_nodup :
    mathlibPoincareStatementAdapterLedger.Nodup := by
  decide

/-- The adapter-ledger no-duplicate theorem is the direct decidable proof. -/
theorem mathlibPoincareStatementAdapterLedger_nodup_eq :
    mathlibPoincareStatementAdapterLedger_nodup =
      (by decide : mathlibPoincareStatementAdapterLedger.Nodup) := by
  apply Subsingleton.elim

/-- The adapter ledger contains exactly the two mathlib-shaped adapter labels. -/
theorem mathlibPoincareStatementAdapterLedger_mem
    (adapter : MathlibPoincareStatementAdapter) :
    adapter ∈ mathlibPoincareStatementAdapterLedger ↔
      adapter = MathlibPoincareStatementAdapter.topologicalThreeSphere ∨
      adapter = MathlibPoincareStatementAdapter.smoothThreeSphere := by
  cases adapter <;> simp [mathlibPoincareStatementAdapterLedger]

/-- The adapter-ledger membership theorem is exactly the two-case split. -/
theorem mathlibPoincareStatementAdapterLedger_mem_eq :
    mathlibPoincareStatementAdapterLedger_mem =
      (by
        intro adapter
        cases adapter <;> simp [mathlibPoincareStatementAdapterLedger]) := by
  funext adapter
  apply Subsingleton.elim

/--
The actual local proposition represented by each mathlib-shaped statement
adapter label.
-/
def mathlibPoincareStatementAdapterStatement :
    MathlibPoincareStatementAdapter → Prop
  | MathlibPoincareStatementAdapter.topologicalThreeSphere =>
      MathlibTopologicalPoincareThreeStatement.{u}
  | MathlibPoincareStatementAdapter.smoothThreeSphere =>
      MathlibSmoothPoincareThreeStatement.{u}

/-- The adapter-to-statement map is exactly the local statement case split. -/
theorem mathlibPoincareStatementAdapterStatement_eq :
    mathlibPoincareStatementAdapterStatement.{u} =
      (fun
        | MathlibPoincareStatementAdapter.topologicalThreeSphere =>
            MathlibTopologicalPoincareThreeStatement.{u}
        | MathlibPoincareStatementAdapter.smoothThreeSphere =>
            MathlibSmoothPoincareThreeStatement.{u}) :=
  rfl

/-- The topological adapter names the local topological mathlib-shaped statement. -/
theorem mathlibPoincareStatementAdapterStatement_topologicalThreeSphere :
    mathlibPoincareStatementAdapterStatement.{u}
        MathlibPoincareStatementAdapter.topologicalThreeSphere =
      MathlibTopologicalPoincareThreeStatement.{u} :=
  rfl

/-- The topological adapter statement theorem is the direct `rfl` proof. -/
theorem mathlibPoincareStatementAdapterStatement_topologicalThreeSphere_eq :
    mathlibPoincareStatementAdapterStatement_topologicalThreeSphere =
      (rfl :
        mathlibPoincareStatementAdapterStatement.{u}
            MathlibPoincareStatementAdapter.topologicalThreeSphere =
          MathlibTopologicalPoincareThreeStatement.{u}) :=
  rfl

/-- The smooth adapter names the local smooth mathlib-shaped statement. -/
theorem mathlibPoincareStatementAdapterStatement_smoothThreeSphere :
    mathlibPoincareStatementAdapterStatement.{u}
        MathlibPoincareStatementAdapter.smoothThreeSphere =
      MathlibSmoothPoincareThreeStatement.{u} :=
  rfl

/-- The smooth adapter statement theorem is the direct `rfl` proof. -/
theorem mathlibPoincareStatementAdapterStatement_smoothThreeSphere_eq :
    mathlibPoincareStatementAdapterStatement_smoothThreeSphere =
      (rfl :
        mathlibPoincareStatementAdapterStatement.{u}
            MathlibPoincareStatementAdapter.smoothThreeSphere =
          MathlibSmoothPoincareThreeStatement.{u}) :=
  rfl

/--
The project target proposition corresponding to each mathlib-shaped statement
adapter.
-/
def mathlibPoincareStatementAdapterProjectTarget :
    MathlibPoincareStatementAdapter → Prop
  | MathlibPoincareStatementAdapter.topologicalThreeSphere =>
      PoincareConjectureStatement.{u}
  | MathlibPoincareStatementAdapter.smoothThreeSphere =>
      SmoothPoincareConjectureStatement.{u}

/-- The adapter-to-project-target map is exactly the local target case split. -/
theorem mathlibPoincareStatementAdapterProjectTarget_eq :
    mathlibPoincareStatementAdapterProjectTarget.{u} =
      (fun
        | MathlibPoincareStatementAdapter.topologicalThreeSphere =>
            PoincareConjectureStatement.{u}
        | MathlibPoincareStatementAdapter.smoothThreeSphere =>
            SmoothPoincareConjectureStatement.{u}) :=
  rfl

/-- Each mathlib-shaped adapter statement is equivalent to its project target. -/
theorem mathlibPoincareStatementAdapterStatement_iff_projectTarget
    (adapter : MathlibPoincareStatementAdapter) :
    mathlibPoincareStatementAdapterStatement.{u} adapter ↔
      mathlibPoincareStatementAdapterProjectTarget.{u} adapter := by
  cases adapter <;> exact Iff.rfl

/-- The adapter statement/project-target iff is exactly the adapter case split. -/
theorem mathlibPoincareStatementAdapterStatement_iff_projectTarget_eq :
    mathlibPoincareStatementAdapterStatement_iff_projectTarget.{u} =
      (by
        intro adapter
        cases adapter <;> exact Iff.rfl) := by
  funext adapter
  apply Subsingleton.elim

/-- A proof of an adapter statement gives the corresponding project target. -/
theorem projectTarget_of_mathlibPoincareStatementAdapterStatement
    {adapter : MathlibPoincareStatementAdapter}
    (h : mathlibPoincareStatementAdapterStatement.{u} adapter) :
    mathlibPoincareStatementAdapterProjectTarget.{u} adapter :=
  (mathlibPoincareStatementAdapterStatement_iff_projectTarget adapter).1 h

/-- A proof of a project target gives the corresponding adapter statement. -/
theorem mathlibPoincareStatementAdapterStatement_of_projectTarget
    {adapter : MathlibPoincareStatementAdapter}
    (h : mathlibPoincareStatementAdapterProjectTarget.{u} adapter) :
    mathlibPoincareStatementAdapterStatement.{u} adapter :=
  (mathlibPoincareStatementAdapterStatement_iff_projectTarget adapter).2 h

/-- The adapter-statement-to-project-target route is propositionally direct. -/
theorem projectTarget_of_mathlibPoincareStatementAdapterStatement_eq
    {adapter : MathlibPoincareStatementAdapter}
    (h : mathlibPoincareStatementAdapterStatement.{u} adapter) :
    projectTarget_of_mathlibPoincareStatementAdapterStatement h =
      (by
        cases adapter <;> exact h) := by
  cases adapter <;> apply Subsingleton.elim

/-- The project-target-to-adapter-statement route is propositionally direct. -/
theorem mathlibPoincareStatementAdapterStatement_of_projectTarget_eq
    {adapter : MathlibPoincareStatementAdapter}
    (h : mathlibPoincareStatementAdapterProjectTarget.{u} adapter) :
    mathlibPoincareStatementAdapterStatement_of_projectTarget h =
      (by
        cases adapter <;> exact h) := by
  cases adapter <;> apply Subsingleton.elim

/--
Map each external blocker to the local mathlib-shaped statement adapters whose
eventual theorem route it blocks.
-/
def statementAdaptersBlockedByExternalBlocker :
    ExternalFormalizationBlocker → List MathlibPoincareStatementAdapter
  | ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =>
      mathlibPoincareStatementAdapterLedger
  | ExternalFormalizationBlocker.ricciSpecificGeometrySurface =>
      []
  | ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =>
      []

/-- The blocker-to-adapter map is exactly the audit-derived case split. -/
theorem statementAdaptersBlockedByExternalBlocker_eq :
    statementAdaptersBlockedByExternalBlocker =
      (fun
        | ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =>
            mathlibPoincareStatementAdapterLedger
        | ExternalFormalizationBlocker.ricciSpecificGeometrySurface =>
            []
        | ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =>
            []) :=
  rfl

/-- The mathlib shortcut blocker covers both local statement adapters. -/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_statementAdapters :
    statementAdaptersBlockedByExternalBlocker
        ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
      mathlibPoincareStatementAdapterLedger :=
  rfl

/-- The mathlib shortcut-to-adapter theorem is the direct `rfl` proof. -/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_statementAdapters_eq :
    mathlibThreeDimensionalPoincareProofWanted_blocks_statementAdapters =
      (rfl :
        statementAdaptersBlockedByExternalBlocker
            ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
          mathlibPoincareStatementAdapterLedger) :=
  rfl

/-- The Ricci-specific geometry blocker does not name a statement adapter. -/
theorem ricciSpecificGeometrySurface_blocks_no_statementAdapters :
    statementAdaptersBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciSpecificGeometrySurface = [] :=
  rfl

/-- The Ricci-specific no-adapter theorem is the direct `rfl` proof. -/
theorem ricciSpecificGeometrySurface_blocks_no_statementAdapters_eq :
    ricciSpecificGeometrySurface_blocks_no_statementAdapters =
      (rfl :
        statementAdaptersBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciSpecificGeometrySurface = []) :=
  rfl

/-- The surgery-side blocker does not name a statement adapter. -/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_no_statementAdapters :
    statementAdaptersBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
      [] :=
  rfl

/-- The surgery-side no-adapter theorem is the direct `rfl` proof. -/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_no_statementAdapters_eq :
    ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_no_statementAdapters =
      (rfl :
        statementAdaptersBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
          []) :=
  rfl

/--
Every statement adapter named by an external blocker is one of the checked
mathlib-shaped adapter labels.
-/
theorem externalBlocker_statementAdapters_mem_adapterLedger
    (blocker : ExternalFormalizationBlocker)
    {adapter : MathlibPoincareStatementAdapter} :
    adapter ∈ statementAdaptersBlockedByExternalBlocker blocker →
      adapter ∈ mathlibPoincareStatementAdapterLedger := by
  cases blocker <;> cases adapter <;> simp
    [statementAdaptersBlockedByExternalBlocker,
      mathlibPoincareStatementAdapterLedger]

/--
The theorem asserting that externally blocked statement adapters are ledger
adapters is exactly the blocker/adapter case split.
-/
theorem externalBlocker_statementAdapters_mem_adapterLedger_eq :
    externalBlocker_statementAdapters_mem_adapterLedger =
      (by
        intro blocker adapter
        cases blocker <;> cases adapter <;> simp
          [statementAdaptersBlockedByExternalBlocker,
            mathlibPoincareStatementAdapterLedger]) := by
  funext blocker adapter
  apply Subsingleton.elim

/--
Map each external audit blocker to the dependency milestones it prevents from
being discharged unconditionally.
-/
def dependencyMilestonesBlockedByExternalBlocker :
    ExternalFormalizationBlocker → List DependencyMilestone
  | ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =>
      dependencyMilestoneLedger
  | ExternalFormalizationBlocker.ricciSpecificGeometrySurface =>
      [ DependencyMilestone.ricciFlowAnalyticFoundation ]
  | ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =>
      [ DependencyMilestone.ricciFlowWithSurgery
      , DependencyMilestone.perelmanSingularityControl
      , DependencyMilestone.finiteExtinction
      ]

/--
The external-blocker-to-milestone map is exactly the explicit audit-derived
case split.
-/
theorem dependencyMilestonesBlockedByExternalBlocker_eq :
    dependencyMilestonesBlockedByExternalBlocker =
      (fun
        | ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =>
            dependencyMilestoneLedger
        | ExternalFormalizationBlocker.ricciSpecificGeometrySurface =>
            [ DependencyMilestone.ricciFlowAnalyticFoundation ]
        | ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =>
            [ DependencyMilestone.ricciFlowWithSurgery
            , DependencyMilestone.perelmanSingularityControl
            , DependencyMilestone.finiteExtinction
            ]) :=
  rfl

/--
The mathlib shortcut blocker covers every dependency milestone, because relying
on that shortcut would bypass the whole local proof program.
-/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyMilestoneLedger :
    dependencyMilestonesBlockedByExternalBlocker
        ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
      dependencyMilestoneLedger :=
  rfl

/-- The mathlib shortcut blocker route is the direct `rfl` proof. -/
theorem mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyMilestoneLedger_eq :
    mathlibThreeDimensionalPoincareProofWanted_blocks_dependencyMilestoneLedger =
      (rfl :
        dependencyMilestonesBlockedByExternalBlocker
            ExternalFormalizationBlocker.mathlibThreeDimensionalPoincareProofWanted =
          dependencyMilestoneLedger) :=
  rfl

/-- The Ricci-specific geometry blocker is the analytic-foundation milestone. -/
theorem ricciSpecificGeometrySurface_blocks_analyticFoundation :
    dependencyMilestonesBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciSpecificGeometrySurface =
      [DependencyMilestone.ricciFlowAnalyticFoundation] :=
  rfl

/-- The Ricci-specific geometry blocker route is the direct `rfl` proof. -/
theorem ricciSpecificGeometrySurface_blocks_analyticFoundation_eq :
    ricciSpecificGeometrySurface_blocks_analyticFoundation =
      (rfl :
        dependencyMilestonesBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciSpecificGeometrySurface =
          [DependencyMilestone.ricciFlowAnalyticFoundation]) :=
  rfl

/--
The Ricci-flow-with-surgery/Perelman/finite-extinction blocker covers the three
surgery-side milestones it names.
-/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryMilestones :
    dependencyMilestonesBlockedByExternalBlocker
        ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
      [ DependencyMilestone.ricciFlowWithSurgery
      , DependencyMilestone.perelmanSingularityControl
      , DependencyMilestone.finiteExtinction
      ] :=
  rfl

/-- The surgery-side external blocker route is the direct `rfl` proof. -/
theorem ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryMilestones_eq :
    ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface_blocks_surgeryMilestones =
      (rfl :
        dependencyMilestonesBlockedByExternalBlocker
            ExternalFormalizationBlocker.ricciFlowWithSurgeryPerelmanFiniteExtinctionSurface =
          [ DependencyMilestone.ricciFlowWithSurgery
          , DependencyMilestone.perelmanSingularityControl
          , DependencyMilestone.finiteExtinction
          ]) :=
  rfl

/--
Every milestone named by an external blocker is one of the checked dependency
milestones.
-/
theorem externalBlocker_milestones_mem_dependencyMilestoneLedger
    (blocker : ExternalFormalizationBlocker) {milestone : DependencyMilestone} :
    milestone ∈ dependencyMilestonesBlockedByExternalBlocker blocker →
      milestone ∈ dependencyMilestoneLedger := by
  cases blocker <;> cases milestone <;> simp [dependencyMilestonesBlockedByExternalBlocker,
    dependencyMilestoneLedger]

/--
The theorem asserting that externally blocked milestones are ledger milestones
is exactly the three-case blocker split.
-/
theorem externalBlocker_milestones_mem_dependencyMilestoneLedger_eq :
    externalBlocker_milestones_mem_dependencyMilestoneLedger =
      (by
        intro blocker milestone
        cases blocker <;> cases milestone <;> simp [dependencyMilestonesBlockedByExternalBlocker,
          dependencyMilestoneLedger]) := by
  funext blocker milestone
  apply Subsingleton.elim

end Poincare
