import Poincare.Global.DifferentialSuccessorFiniteRealizedGridCommonRadius
import Poincare.Global.DifferentialSuccessorAdaptiveMeshCoordinates

/-!
# Post-realization mesh certificates for differential homotopy grids

Curvature supplies a common mesh radius only after the finite grid histories
and their cross-cell differential data have been realized.  This module makes
the strongest non-circular use of that quantifier order.

For a fixed node grid, the resulting radius is stable under replacing every
realized row chain by any other realized row chain on the same nodes:
differential successors are canonical, so the row states agree.  The actual
grid therefore has a finite certificate: either all such realizations have the
same boundary endpoint, or a concrete horizontal or vertical edge violates
the post-realization radius.

The adaptive subdivision theorem also produces a new geometric grid whose
edges are smaller than that radius.  We deliberately do not transfer the old
certificate to the new node grid: its recursively realized histories, and
therefore its curvature equality radii, may change.  Proving stability under
that change is exactly the remaining adaptive feedback problem.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorPostRealizationMeshCertificate

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorFiniteRealizedHomotopyGrid
open DifferentialSuccessorFiniteRealizedGridCommonRadius
open DifferentialSuccessorAdaptiveMeshCoordinates

/--
The post-realization common radius is independent of the differential-data
choices used to realize the rows, as long as the geometric node grid is kept
fixed.

The original `rowChain` and cross-cell data are used only to obtain the
curvature radius.  Once its two actual mesh bounds hold, successor canonicity
transfers the endpoint equality to every other family of realized row chains
on the same node sequences.  No `StepAvailable` policy at counterfactual
states occurs in the statement.
-/
theorem exists_history_stable_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (htzero : t 0 = 0)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (rowChain : ∀ m : Fin (k + 2),
      DifferentialInducedSuccessor.Chain.ReachableChain
        (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      DifferentialInducedSuccessor.Data
        (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      (∀ m : Fin (k + 2), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t m (j + 1))
          (homotopyGridRow F t m j) < eta) →
      (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m (j + 1)) < eta) →
      ∀ alternateRowChain : ∀ m : Fin (k + 2),
          DifferentialInducedSuccessor.Chain.ReachableChain
            (homotopyGridRow F t m) initial,
        (alternateRowChain 0).state (k + 1) =
          (alternateRowChain (Fin.last (k + 1))).state (k + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature
        hcurv F initial hinitial t htzero k htone rowChain rungData
          bottomAtUpper rungAtNext with
    ⟨eta, heta, hvalidate⟩
  refine ⟨eta, heta, ?_⟩
  intro hhorizontal hvertical alternateRowChain
  have horiginal := hvalidate hhorizontal hvertical
  have hleft :=
    (alternateRowChain 0).state_eq (rowChain 0) (k + 1)
  have hright :=
    (rowChain (Fin.last (k + 1))).state_eq
      (alternateRowChain (Fin.last (k + 1))) (k + 1)
  exact hleft.trans (horiginal.trans hright)

/--
A completely actual post-realization certificate, together with one adaptive
geometric response.

For the fixed realized grid, either endpoint equality holds for every row
realization on the same nodes, or the theorem returns a specific edge whose
length is at least the computed curvature radius.  In all cases it also
constructs a fresh adaptive grid whose horizontal and vertical edges are
strictly smaller than that old-history radius.

The fresh grid is intentionally called a candidate rather than a validated
refinement: no claim is made that the equality radius computed from the old
histories remains valid after the node sequence changes.
-/
theorem exists_postRealization_mesh_certificate_and_adapted_candidate_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (htzero : t 0 = 0)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (rowChain : ∀ m : Fin (k + 2),
      DifferentialInducedSuccessor.Chain.ReachableChain
        (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      DifferentialInducedSuccessor.Data
        (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      (((∀ alternateRowChain : ∀ m : Fin (k + 2),
            DifferentialInducedSuccessor.Chain.ReachableChain
              (homotopyGridRow F t m) initial,
          (alternateRowChain 0).state (k + 1) =
            (alternateRowChain (Fin.last (k + 1))).state (k + 1)) ∨
        (∃ m : Fin (k + 2), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t m (j + 1))
            (homotopyGridRow F t m j)) ∨
        (∃ m : Fin (k + 1), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)))) ∧
      ∃ (candidate : ℕ → unitInterval) (candidateK : ℕ),
        candidate 0 = 0 ∧ Monotone candidate ∧
          (∀ n ≥ candidateK, candidate n = 1) ∧
          (∀ n m : ℕ,
            dist (homotopyGridRow F candidate n (m + 1))
              (homotopyGridRow F candidate n m) < eta) ∧
          ∀ n m : ℕ,
            dist (homotopyGridRow F candidate (n + 1) (m + 1))
              (homotopyGridRow F candidate n (m + 1)) < eta) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_history_stable_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature
        hcurv F initial hinitial t htzero k htone rowChain rungData
          bottomAtUpper rungAtNext with
    ⟨eta, heta, hvalidate⟩
  let Horizontal : Prop :=
    ∀ m : Fin (k + 2), ∀ j : Fin (k + 1),
      dist (homotopyGridRow F t m (j + 1))
        (homotopyGridRow F t m j) < eta
  let Vertical : Prop :=
    ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      dist (homotopyGridRow F t (m + 1) (j + 1))
        (homotopyGridRow F t m (j + 1)) < eta
  have hcertificate :
      ((∀ alternateRowChain : ∀ m : Fin (k + 2),
            DifferentialInducedSuccessor.Chain.ReachableChain
              (homotopyGridRow F t m) initial,
          (alternateRowChain 0).state (k + 1) =
            (alternateRowChain (Fin.last (k + 1))).state (k + 1)) ∨
        (∃ m : Fin (k + 2), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t m (j + 1))
            (homotopyGridRow F t m j)) ∨
        (∃ m : Fin (k + 1), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)))) := by
    by_cases hhorizontal : Horizontal
    · by_cases hvertical : Vertical
      · exact Or.inl (hvalidate hhorizontal hvertical)
      · right
        right
        dsimp [Vertical] at hvertical
        push Not at hvertical
        exact hvertical
    · right
      left
      dsimp [Horizontal] at hhorizontal
      push Not at hhorizontal
      exact hhorizontal
  rcases exists_homotopy_grid_adjacent_dist_lt g F heta with
    ⟨candidate, candidateK, hcandidateZero, hcandidateMono,
      hcandidateOne, hcandidateHorizontal, hcandidateVertical⟩
  exact ⟨eta, heta, hcertificate, candidate, candidateK,
    hcandidateZero, hcandidateMono, hcandidateOne,
    hcandidateHorizontal, hcandidateVertical⟩

end DifferentialSuccessorPostRealizationMeshCertificate
end Poincare
