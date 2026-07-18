import Poincare.Global.DifferentialSuccessorAdaptiveMeshCoordinates

/-!
# Uniform differential-successor balls close the adaptive mesh loop

The adaptive homotopy-grid construction produces a subdivision whose
horizontal and vertical edges are smaller than any prescribed positive
metric radius.  The finite grid consumer, on the other hand, needs equality
patches for the recursively reached successor states.

This file records the exact missing interface between those two results.  If
one positive radius works for every predecessor state and every successor
datum whose new anchor is within that radius, then the subdivision may be
chosen first and all finite equality-patch premises follow.  No compactness
argument over the (noncompact and recursively generated) state space is
hidden in the statement.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialUniformSuccessorMesh

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveHomotopyGrid
open DifferentialSuccessorAdaptiveMeshCoordinates

/-- One metric radius works for the germ equality of every sufficiently
short differential-induced successor, independently of the predecessor
state.  Packaging the metric instance here keeps the geometric hypothesis
usable as a named interface. -/
def UniformSuccessorEqOnBall
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (eta : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z),
    dist z s.anchor < eta →
      EqOn s.germ d.successor.germ (Metric.ball z eta)

/-- A genuinely state-uniform successor equality radius closes the feedback
loop in the adaptive homotopy-grid argument.

The hypothesis is deliberately global over predecessor states: whenever the
new anchor of an actual differential-successor datum is less than `eta` from
the predecessor anchor, the old and successor germs agree on the whole
`eta`-ball about that new anchor.  The resulting grid is chosen only from
`eta` and the homotopy.  Consequently the endpoint comparison holds for
every differential data policy on the chosen rows.

Besides endpoint equality, the conclusion retains the geometric information
about the selected grid (zero start, monotonicity, eventual stationarity, and
both global adjacent-edge bounds), so downstream consumers do not have to
reconstruct the subdivision witness. -/
theorem exists_homotopy_grid_endpoint_eq_of_uniform_successor_eqOn_ball
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (hinitial : initial.anchor = x)
    (eta : ℝ) (heta : 0 < eta)
    (huniform : UniformSuccessorEqOnBall g eta) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ (t : ℕ → unitInterval) (k : ℕ),
      t 0 = 0 ∧ Monotone t ∧ (∀ n ≥ k, t n = 1) ∧
        (∀ n m : ℕ,
          dist (homotopyGridRow F t n (m + 1))
            (homotopyGridRow F t n m) < eta) ∧
        (∀ n m : ℕ,
          dist (homotopyGridRow F t (n + 1) (m + 1))
            (homotopyGridRow F t n (m + 1)) < eta) ∧
        ∀ (step : ∀ r : ℕ,
          DifferentialInducedSuccessor.Chain.StepAvailable (g := g)
            (homotopyGridRow F t r)),
          DifferentialInducedSuccessor.Chain.chainState
              (homotopyGridRow F t 0) initial (step 0) (k + 1) =
            DifferentialInducedSuccessor.Chain.chainState
              (homotopyGridRow F t (k + 1)) initial (step (k + 1))
                (k + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  change ∀ (s : CartanChain.ChainState g) {z : M}
      (d : DifferentialInducedSuccessor.Data s z),
      dist z s.anchor < eta →
        EqOn s.germ d.successor.germ (Metric.ball z eta) at huniform
  rcases exists_homotopy_grid_adjacent_dist_lt g F heta with
    ⟨t, k, htzero, htmono, htone, hhorizontal, hvertical⟩
  refine ⟨t, k, htzero, htmono, htone, ?_, ?_, ?_⟩
  · simpa using hhorizontal
  · simpa using hvertical
  · intro step
    have hrowZero : ∀ r : ℕ,
        initial.anchor = homotopyGridRow F t r 0 := by
      intro r
      simpa [homotopyGridRow, htzero] using hinitial
    apply
      differentialHomotopyGrid_chain_endpoint_eq_of_finite_metricBall_patches
        F initial t step k htone
        (fun _ _ ↦ eta) (fun _ _ ↦ eta)
    · intro r j
      let b := DifferentialInducedSuccessor.Chain.chainState
        (homotopyGridRow F t r) initial (step r) j
      let hstep := step r j b
      let d : DifferentialInducedSuccessor.Data b
          (homotopyGridRow F t r (j + 1)) := Classical.choice hstep
      have hbAnchor : b.anchor = homotopyGridRow F t r j := by
        simpa [b] using
          differentialChain_chainState_anchor_eq_node
            (homotopyGridRow F t r) initial (step r) (hrowZero r) j
      have hdist :
          dist (homotopyGridRow F t r (j + 1)) b.anchor < eta := by
        simpa [hbAnchor] using hhorizontal r j
      have hEq := huniform b d hdist
      have hsuccessor : d.successor =
          DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t r) initial (step r) (j + 1) := by
        calc
          d.successor =
              DifferentialInducedSuccessor.successorOfNonempty b
                (homotopyGridRow F t r (j + 1)) hstep :=
            (DifferentialInducedSuccessor.successorOfNonempty_eq
              hstep d).symm
          _ = DifferentialInducedSuccessor.Chain.chainState
                (homotopyGridRow F t r) initial (step r) (j + 1) := by
            simpa [b, hstep] using
              (DifferentialInducedSuccessor.Chain.chainState_succ
                (homotopyGridRow F t r) initial (step r) j).symm
      simpa [b, hsuccessor] using hEq
    · intro r j
      rw [Metric.mem_ball]
      exact hvertical r j
    · intro r j
      let b := DifferentialInducedSuccessor.Chain.chainState
        (homotopyGridRow F t r) initial (step r) (j + 1)
      let hstep := step (r + 1) j b
      let d : DifferentialInducedSuccessor.Data b
          (homotopyGridRow F t (r + 1) (j + 1)) := Classical.choice hstep
      have hbAnchor : b.anchor = homotopyGridRow F t r (j + 1) := by
        simpa [b] using
          differentialChain_chainState_anchor_eq_node
            (homotopyGridRow F t r) initial (step r) (hrowZero r) (j + 1)
      have hdist :
          dist (homotopyGridRow F t (r + 1) (j + 1)) b.anchor < eta := by
        simpa [hbAnchor] using hvertical r j
      have hEq := huniform b d hdist
      have hsuccessor : d.successor =
          DifferentialInducedSuccessor.successorOfNonempty b
            (homotopyGridRow F t (r + 1) (j + 1)) hstep :=
        (DifferentialInducedSuccessor.successorOfNonempty_eq hstep d).symm
      simpa [b, hstep, hsuccessor] using hEq
    · intro r j
      rw [Metric.mem_ball]
      exact hhorizontal (r + 1) (j + 1)

end DifferentialUniformSuccessorMesh
end Poincare
