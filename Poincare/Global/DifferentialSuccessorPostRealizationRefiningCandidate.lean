import Poincare.Global.DifferentialSuccessorPostRealizationMeshCertificate
import Poincare.Global.DifferentialSuccessorAdaptiveGridRefinement

/-!
# Post-realization certificates with a genuinely refining response grid

The earlier post-realization certificate returned a cover-small candidate
whose node set was unrelated to the realized grid.  The common-refinement
subdivision theorem removes that loss: the response grid below retains every
old parameter value through a monotone factor map while satisfying the same
strict horizontal and vertical mesh bounds.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorPostRealizationRefiningCandidate

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorPostRealizationMeshCertificate
open DifferentialSuccessorAdaptiveGridRefinement

/-- A fixed realized homotopy grid has the usual radius certificate and a
cover-small response grid which is an actual common refinement of the fixed
grid.

The remaining analytic feedback is now isolated to transporting the realized
successor histories through the finite insertions recorded by `e`; no old
geometric node is discarded. -/
theorem exists_postRealization_mesh_certificate_and_refining_candidate_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (htzero : t 0 = 0) (htmono : Monotone t)
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
      ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
        0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
          Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
          (∀ n, r (e n) = t n) ∧
          (∀ n m : ℕ,
            dist (homotopyGridRow F r n (m + 1))
              (homotopyGridRow F r n m) < eta) ∧
          ∀ n m : ℕ,
            dist (homotopyGridRow F r (n + 1) (m + 1))
              (homotopyGridRow F r n (m + 1)) < eta) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_postRealization_mesh_certificate_and_adapted_candidate_of_curvature
        hcurv F initial hinitial t htzero k htone rowChain rungData
          bottomAtUpper rungAtNext with
    ⟨eta, heta, hcertificate, _candidate, _candidateK,
      _hcandidateZero, _hcandidateMono, _hcandidateOne,
      _hcandidateHorizontal, _hcandidateVertical⟩
  rcases exists_refining_homotopy_grid_adjacent_dist_lt
      g F heta t htzero htmono k htone with
    ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
      heBound, heValue, hhorizontal, hvertical⟩
  exact ⟨eta, heta, hcertificate, r, K, e, hK, hrZero, hrMono,
    hrOne, heMono, heZero, heBound, heValue, hhorizontal, hvertical⟩

end DifferentialSuccessorPostRealizationRefiningCandidate
end Poincare
