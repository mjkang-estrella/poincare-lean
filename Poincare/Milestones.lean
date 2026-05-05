/-
This file records proof obligations that would have to be discharged before the
statement in `Poincare.Statement` can become a theorem.

It contains no axioms, no theorem claims, and no proof placeholders. The entries
are data, not propositions, so they cannot be used as proofs of mathematical
obligations.
-/

import Poincare.Statement

namespace Poincare

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

end Poincare
