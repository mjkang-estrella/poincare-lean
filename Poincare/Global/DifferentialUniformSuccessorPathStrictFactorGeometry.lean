import Poincare.Global.DifferentialUniformSuccessorStrictFactorGeometry

/-!
# Path geometry for uniform strict-factor transport

A strict refinement of path parameters supplies the geometric package needed
by `DifferentialUniformSuccessorStrictFactorGeometry` without storing any
realized chain.  The only analytic input is a uniform metric-diameter bound on
each cell of the coarse parameter subdivision.

The central combinatorial lemma says that every intermediate single-insertion
schedule consists of a refined prefix followed by the untouched coarse tail.
Consequently each adjacent scheduled edge is either a refined edge, the one
bridge across the current coarse cell, or a coarse edge.  All three cases are
controlled by the same coarse-cell diameter hypothesis.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialUniformSuccessorPathStrictFactorGeometry

set_option linter.unusedSectionVars false

open CartanCanonicalRootedUniformSuccessorMeshRecognition
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorStrictFactorInsertionTransport
open DifferentialUniformSuccessorStrictFactorGeometry

universe u v

/-! ## The insertion schedule is a refined prefix and a coarse tail -/

/-- After inserting the first `i` nodes of one strict-factor gap, the prefix
through `factor n + i` is the refined sequence and the remaining tail is the
coarse sequence starting at `n + 1`.

This bounded form is the induction principle behind the path-geometric
constructor below. -/
theorem factorGapSchedule_prefix_tail_of_le
    {X : Type v} (seed refined : ℕ → X) (factor : ℕ → ℕ)
    (hfactor_zero : factor 0 = 0)
    (hfactor_strict : ∀ n : ℕ, factor n < factor (n + 1))
    (hfactor_value : ∀ n : ℕ, refined (factor n) = seed n)
    (n i : ℕ) (hi : i ≤ (factorGapNodes refined factor n).length) :
    (∀ j ≤ factor n + i,
        insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) i j = refined j) ∧
      (∀ q : ℕ,
        insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) i
            (factor n + i + 1 + q) = seed (n + 1 + q)) := by
  induction i with
  | zero =>
      have hstage := factorRefinementStage_prefix_tail seed refined factor n
        hfactor_zero (fun m _hm ↦ hfactor_strict m)
        (fun m _hm ↦ hfactor_value m) n le_rfl
      constructor
      · intro j hj
        simpa only [insertNodeListSchedule_zero, Nat.add_zero] using
          hstage.1 j hj
      · intro q
        simpa only [insertNodeListSchedule_zero, Nat.add_zero,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hstage.2 (q + 1)
  | succ i ih =>
      have hi' : i < (factorGapNodes refined factor n).length := by omega
      have hprevious := ih (Nat.le_of_lt hi')
      constructor
      · intro j hj
        by_cases hjold : j ≤ factor n + i
        · rw [factorGapSchedule_succ seed refined factor n i hi']
          rw [insertNodeSequence_eq_of_le _ _ _ hjold]
          exact hprevious.1 j hjold
        · have hjnew : j = factor n + i + 1 := by omega
          subst j
          rw [factorGapSchedule_succ seed refined factor n i hi']
          rw [insertNodeSequence_inserted]
          have hget := factorGapNodes_get refined factor n
            ⟨i, hi'⟩
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hget
      · intro q
        calc
          insertNodeListSchedule
                (factorRefinementStage seed refined factor n) (factor n)
                (factorGapNodes refined factor n) (i + 1)
                (factor n + (i + 1) + 1 + q) =
              insertNodeListSchedule
                (factorRefinementStage seed refined factor n) (factor n)
                (factorGapNodes refined factor n) i
                (factor n + i + 1 + q) := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              insertNodeListSchedule_succ_shifted
                (factorRefinementStage seed refined factor n) (factor n)
                (factorGapNodes refined factor n) i q hi'
          _ = seed (n + 1 + q) := hprevious.2 q

/-- The unrestricted schedule is the bounded schedule at the minimum of the
requested insertion count and the finite gap length. -/
theorem factorGapSchedule_prefix_tail
    {X : Type v} (seed refined : ℕ → X) (factor : ℕ → ℕ)
    (hfactor_zero : factor 0 = 0)
    (hfactor_strict : ∀ n : ℕ, factor n < factor (n + 1))
    (hfactor_value : ∀ n : ℕ, refined (factor n) = seed n)
    (n i : ℕ) :
    let r := min i (factorGapNodes refined factor n).length
    (∀ j ≤ factor n + r,
        insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) i j = refined j) ∧
      (∀ q : ℕ,
        insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) i
            (factor n + r + 1 + q) = seed (n + 1 + q)) := by
  let gap := factorGapNodes refined factor n
  let r := min i gap.length
  have hr : r ≤ gap.length := min_le_right _ _
  have hshape := factorGapSchedule_prefix_tail_of_le seed refined factor
    hfactor_zero hfactor_strict hfactor_value n r hr
  have hschedule :
      insertNodeListSchedule
          (factorRefinementStage seed refined factor n) (factor n) gap i =
        insertNodeListSchedule
          (factorRefinementStage seed refined factor n) (factor n) gap r := by
    unfold insertNodeListSchedule
    congr 1
    by_cases hi : i ≤ gap.length
    · simp [r, Nat.min_eq_left hi]
    · have hgap : gap.length ≤ i := le_of_not_ge hi
      simp [r, Nat.min_eq_right hgap, List.take_of_length_le hgap]
  dsimp only [r]
  constructor
  · intro j hj
    rw [hschedule]
    exact hshape.1 j hj
  · intro q
    rw [hschedule]
    exact hshape.2 q

/-! ## Extending a finite factor by a strict stationary tail -/

/-- Preserve a finite factor through `k`, then advance linearly from its
terminal value.  This is the canonical globally strict index map for path
parameter sequences that are stationary at `1` after their finite terminal
indices. -/
def strictTailFactor (e : ℕ → ℕ) (k n : ℕ) : ℕ :=
  if n ≤ k then e n else e k + (n - k)

@[simp]
theorem strictTailFactor_of_le (e : ℕ → ℕ) (k n : ℕ) (hn : n ≤ k) :
    strictTailFactor e k n = e n := by
  simp [strictTailFactor, hn]

theorem strictTailFactor_of_lt (e : ℕ → ℕ) (k n : ℕ) (hn : k < n) :
    strictTailFactor e k n = e k + (n - k) := by
  simp [strictTailFactor, Nat.not_le.mpr hn]

@[simp]
theorem strictTailFactor_zero (e : ℕ → ℕ) (k : ℕ)
    (heZero : e 0 = 0) :
    strictTailFactor e k 0 = 0 := by
  rw [strictTailFactor_of_le e k 0 (Nat.zero_le k), heZero]

/-- Finite strictness becomes global strictness after attaching the linear
tail. -/
theorem strictTailFactor_strict (e : ℕ → ℕ) (k : ℕ)
    (heStrict : ∀ n < k, e n < e (n + 1)) :
    ∀ n : ℕ, strictTailFactor e k n < strictTailFactor e k (n + 1) := by
  intro n
  by_cases hn : n < k
  · rw [strictTailFactor_of_le e k n hn.le,
      strictTailFactor_of_le e k (n + 1) (by omega)]
    exact heStrict n hn
  · have hkn : k ≤ n := le_of_not_gt hn
    by_cases hnk : n = k
    · subst n
      rw [strictTailFactor_of_le e k k le_rfl,
        strictTailFactor_of_lt e k (k + 1) (Nat.lt_succ_self k)]
      omega
    · have hklt : k < n := lt_of_le_of_ne hkn (Ne.symm hnk)
      rw [strictTailFactor_of_lt e k n hklt,
        strictTailFactor_of_lt e k (n + 1) (hklt.trans (Nat.lt_succ_self n))]
      omega

/-- Every tail value lies at or beyond the retained terminal factor index. -/
theorem strictTailFactor_terminal_le (e : ℕ → ℕ) (k n : ℕ)
    (hn : k ≤ n) :
    e k ≤ strictTailFactor e k n := by
  rcases hn.eq_or_lt with rfl | hn
  · simp
  · rw [strictTailFactor_of_lt e k n hn]
    exact Nat.le_add_right _ _

/-- If the seed parameters are eventually `1` and the monotone refined
parameters have already reached `1` at `e k`, extending the factor linearly
preserves the factor-value identity at every later index. -/
theorem strictTailFactor_value_of_eventually_one
    (e : ℕ → ℕ) (k : ℕ)
    (seedParam refinedParam : ℕ → unitInterval)
    (heValue : ∀ n ≤ k, refinedParam (e n) = seedParam n)
    (hseedOne : ∀ n ≥ k, seedParam n = 1)
    (hrefinedMonotone : Monotone refinedParam)
    (hrefinedTerminal : refinedParam (e k) = 1) :
    ∀ n : ℕ,
      refinedParam (strictTailFactor e k n) = seedParam n := by
  intro n
  by_cases hn : n ≤ k
  · rw [strictTailFactor_of_le e k n hn]
    exact heValue n hn
  · have hkn : k ≤ n := le_of_not_ge hn
    have hterminalLe :
        refinedParam (e k) ≤ refinedParam (strictTailFactor e k n) :=
      hrefinedMonotone (strictTailFactor_terminal_le e k n hkn)
    have hrefinedOne : refinedParam (strictTailFactor e k n) = 1 := by
      apply le_antisymm
      · exact (refinedParam (strictTailFactor e k n)).property.2
      · simpa only [hrefinedTerminal] using hterminalLe
    rw [hrefinedOne, hseedOne n hkn]

/-- A terminal-pinned variant used by the canonical homotopy-grid assembly.
It preserves `e` through the last nonterminal source index `T`; after that it
starts at the fixed refined terminal index `K` and advances linearly. -/
def terminalPinnedStrictFactor (e : ℕ → ℕ) (T K n : ℕ) : ℕ :=
  if n ≤ T then e n else K + (n - T)

@[simp]
theorem terminalPinnedStrictFactor_of_le (e : ℕ → ℕ) (T K n : ℕ)
    (hn : n ≤ T) :
    terminalPinnedStrictFactor e T K n = e n := by
  simp [terminalPinnedStrictFactor, hn]

theorem terminalPinnedStrictFactor_of_lt (e : ℕ → ℕ) (T K n : ℕ)
    (hn : T < n) :
    terminalPinnedStrictFactor e T K n = K + (n - T) := by
  simp [terminalPinnedStrictFactor, Nat.not_le.mpr hn]

@[simp]
theorem terminalPinnedStrictFactor_zero (e : ℕ → ℕ) (T K : ℕ)
    (heZero : e 0 = 0) :
    terminalPinnedStrictFactor e T K 0 = 0 := by
  rw [terminalPinnedStrictFactor_of_le e T K 0 (Nat.zero_le T), heZero]

/-- The first stationary-tail source node is pinned exactly one index after
the chosen refined terminal node. -/
@[simp]
theorem terminalPinnedStrictFactor_terminal_succ
    (e : ℕ → ℕ) (T K : ℕ) :
    terminalPinnedStrictFactor e T K (T + 1) = K + 1 := by
  rw [terminalPinnedStrictFactor_of_lt e T K (T + 1)
    (Nat.lt_succ_self T)]
  omega

/-- Monotonicity of the finite factor becomes strictness when its retained
parameter values are strictly increasing. -/
theorem finiteFactor_strict_of_parameter_strict
    (e : ℕ → ℕ) (T : ℕ)
    (seedParam refinedParam : ℕ → unitInterval)
    (heMonotone : Monotone e)
    (heValue : ∀ n ≤ T, refinedParam (e n) = seedParam n)
    (hseedStrict : ∀ n < T, seedParam n < seedParam (n + 1)) :
    ∀ n < T, e n < e (n + 1) := by
  intro n hn
  apply lt_of_le_of_ne (heMonotone (Nat.le_succ n))
  intro heq
  apply (ne_of_lt (hseedStrict n hn))
  calc
    seedParam n = refinedParam (e n) := (heValue n hn.le).symm
    _ = refinedParam (e (n + 1)) := by rw [heq]
    _ = seedParam (n + 1) := heValue (n + 1) (by omega)

/-- A strict finite factor bounded by `K` extends to a globally strict
terminal-pinned factor. -/
theorem terminalPinnedStrictFactor_strict_of_strict
    (e : ℕ → ℕ) (T K : ℕ)
    (heStrict : ∀ n < T, e n < e (n + 1))
    (heTerminalBound : e T ≤ K) :
    ∀ n : ℕ,
      terminalPinnedStrictFactor e T K n <
        terminalPinnedStrictFactor e T K (n + 1) := by
  intro n
  by_cases hn : n < T
  · rw [terminalPinnedStrictFactor_of_le e T K n hn.le,
      terminalPinnedStrictFactor_of_le e T K (n + 1) (by omega)]
    exact heStrict n hn
  · have hTn : T ≤ n := le_of_not_gt hn
    by_cases hnT : n = T
    · subst n
      rw [terminalPinnedStrictFactor_of_le e T K T le_rfl,
        terminalPinnedStrictFactor_terminal_succ]
      exact heTerminalBound.trans_lt (Nat.lt_succ_self K)
    · have hTlt : T < n := lt_of_le_of_ne hTn (Ne.symm hnT)
      rw [terminalPinnedStrictFactor_of_lt e T K n hTlt,
        terminalPinnedStrictFactor_of_lt e T K (n + 1)
          (hTlt.trans (Nat.lt_succ_self n))]
      omega

/-- The canonical finite hypotheses imply global strictness of the pinned
factor. -/
theorem terminalPinnedStrictFactor_strict
    (e : ℕ → ℕ) (T K : ℕ)
    (seedParam refinedParam : ℕ → unitInterval)
    (heMonotone : Monotone e)
    (heValue : ∀ n ≤ T, refinedParam (e n) = seedParam n)
    (heBound : ∀ n ≤ T, e n ≤ K)
    (hseedStrict : ∀ n < T, seedParam n < seedParam (n + 1)) :
    ∀ n : ℕ,
      terminalPinnedStrictFactor e T K n <
        terminalPinnedStrictFactor e T K (n + 1) := by
  apply terminalPinnedStrictFactor_strict_of_strict e T K
    (finiteFactor_strict_of_parameter_strict e T seedParam refinedParam
      heMonotone heValue hseedStrict)
    (heBound T le_rfl)

/-- Eventual endpoint values make the terminal-pinned factor preserve every
parameter value, including the newly exposed endpoint `T + 1 ↦ K + 1`. -/
theorem terminalPinnedStrictFactor_value
    (e : ℕ → ℕ) (T K : ℕ)
    (seedParam refinedParam : ℕ → unitInterval)
    (heValue : ∀ n ≤ T, refinedParam (e n) = seedParam n)
    (hseedOne : ∀ n ≥ T + 1, seedParam n = 1)
    (hrefinedOne : ∀ j ≥ K, refinedParam j = 1) :
    ∀ n : ℕ,
      refinedParam (terminalPinnedStrictFactor e T K n) = seedParam n := by
  intro n
  by_cases hn : n ≤ T
  · rw [terminalPinnedStrictFactor_of_le e T K n hn]
    exact heValue n hn
  · have hTlt : T < n := lt_of_not_ge hn
    rw [terminalPinnedStrictFactor_of_lt e T K n hTlt,
      hrefinedOne (K + (n - T)) (Nat.le_add_right K (n - T)),
      hseedOne n (by omega)]

/-! ## Pure path-parameter geometry -/

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Parameter-only input for strict-factor transport along a path.

The global strictness/value hypotheses match the infinite stationary-tail
encoding used by canonical paths: indices continue to increase after the
terminal parameter has become `1`.  The refined adjacent-edge bound is taken
directly from the final fine homotopy grid; no unavailable seed-cell bracket
for that refined grid is required.

No differential successor datum or reached chain is a field of this
structure. -/
structure PathStrictFactorGeometry
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (gamma : C(unitInterval, M))
    (seedParam refinedParam : ℕ → unitInterval)
    (initial : CartanChain.ChainState g) (length : ℕ) where
  factor : ℕ → ℕ
  factor_zero : factor 0 = 0
  factor_strict : ∀ n : ℕ, factor n < factor (n + 1)
  factor_value : ∀ n : ℕ,
    refinedParam (factor n) = seedParam n
  seed_monotone : Monotone seedParam
  refined_monotone : Monotone refinedParam
  refined_small :
    letI : MetricSpace M := g.toMetricSpace
    ∀ j : ℕ,
      dist (gamma (refinedParam (j + 1))) (gamma (refinedParam j)) <
        certificate.meshRadius
  cellDiameter :
    letI : MetricSpace M := g.toMetricSpace
    ∀ (n : ℕ) {u v : unitInterval},
      u ∈ Icc (seedParam n) (seedParam (n + 1)) →
      v ∈ Icc (seedParam n) (seedParam (n + 1)) →
        dist (gamma u) (gamma v) < certificate.meshRadius
  initial_anchor : initial.anchor = gamma (seedParam 0)

namespace PathStrictFactorGeometry

variable {certificate : JointUniformSuccessorRadiusCertificate g}
variable {gamma : C(unitInterval, M)}
variable {seedParam refinedParam : ℕ → unitInterval}
variable {initial : CartanChain.ChainState g} {length : ℕ}

/-- Build the globally indexed path-geometry package from the finite factor
normally produced by subdivision refinement.

The seed subdivision is stationary from `length` onward.  At the terminal
factor index the refined subdivision is therefore already `1`; refined
monotonicity forces its whole later tail to remain `1`.  `strictTailFactor`
then supplies global strictness and global factor-value equality without
requiring the finite factor `e` to carry any data past `length`. -/
noncomputable def ofFiniteFactor
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (gamma : C(unitInterval, M))
    (seedParam refinedParam : ℕ → unitInterval)
    (initial : CartanChain.ChainState g) (length : ℕ)
    (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < length, e n < e (n + 1))
    (heValue : ∀ n ≤ length,
      refinedParam (e n) = seedParam n)
    (hseedMonotone : Monotone seedParam)
    (hrefinedMonotone : Monotone refinedParam)
    (hseedOne : ∀ n ≥ length, seedParam n = 1)
    (hrefinedSmall :
      letI : MetricSpace M := g.toMetricSpace
      ∀ j : ℕ,
        dist (gamma (refinedParam (j + 1))) (gamma (refinedParam j)) <
          certificate.meshRadius)
    (hcellDiameter :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (n : ℕ) {u v : unitInterval},
        u ∈ Icc (seedParam n) (seedParam (n + 1)) →
        v ∈ Icc (seedParam n) (seedParam (n + 1)) →
          dist (gamma u) (gamma v) < certificate.meshRadius)
    (hinitial : initial.anchor = gamma (seedParam 0)) :
    PathStrictFactorGeometry certificate gamma seedParam refinedParam initial
      length := by
  have hrefinedTerminal : refinedParam (e length) = 1 :=
    (heValue length le_rfl).trans (hseedOne length le_rfl)
  exact
    { factor := strictTailFactor e length
      factor_zero := strictTailFactor_zero e length heZero
      factor_strict := strictTailFactor_strict e length heStrict
      factor_value := strictTailFactor_value_of_eventually_one e length
        seedParam refinedParam heValue hseedOne hrefinedMonotone
        hrefinedTerminal
      seed_monotone := hseedMonotone
      refined_monotone := hrefinedMonotone
      refined_small := hrefinedSmall
      cellDiameter := hcellDiameter
      initial_anchor := hinitial }

/-- Canonical constructor aligned with a homotopy grid's terminal boundary.

`T` is the last nonterminal source index and `K` is the pinned refined
terminal index.  The resulting path geometry ends at source index `T + 1`,
whose factor is definitionally controlled by
`terminalPinnedStrictFactor_terminal_succ` and hence equals `K + 1`.
Only the fine-grid adjacent metric bound is requested for refined edges; no
seed-cell bracket for the final fine grid is needed. -/
noncomputable def ofTerminalPinnedFiniteFactor
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (gamma : C(unitInterval, M))
    (seedParam refinedParam : ℕ → unitInterval)
    (initial : CartanChain.ChainState g) (T K : ℕ)
    (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heMonotone : Monotone e)
    (heValue : ∀ n ≤ T, refinedParam (e n) = seedParam n)
    (heBound : ∀ n ≤ T, e n ≤ K)
    (hseedStrict : ∀ n < T, seedParam n < seedParam (n + 1))
    (hseedMonotone : Monotone seedParam)
    (hrefinedMonotone : Monotone refinedParam)
    (hseedOne : ∀ n ≥ T + 1, seedParam n = 1)
    (hrefinedOne : ∀ j ≥ K, refinedParam j = 1)
    (hrefinedSmall :
      letI : MetricSpace M := g.toMetricSpace
      ∀ j : ℕ,
        dist (gamma (refinedParam (j + 1))) (gamma (refinedParam j)) <
          certificate.meshRadius)
    (hcellDiameter :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (n : ℕ) {u v : unitInterval},
        u ∈ Icc (seedParam n) (seedParam (n + 1)) →
        v ∈ Icc (seedParam n) (seedParam (n + 1)) →
          dist (gamma u) (gamma v) < certificate.meshRadius)
    (hinitial : initial.anchor = gamma (seedParam 0)) :
    PathStrictFactorGeometry certificate gamma seedParam refinedParam initial
      (T + 1) :=
  { factor := terminalPinnedStrictFactor e T K
    factor_zero := terminalPinnedStrictFactor_zero e T K heZero
    factor_strict := terminalPinnedStrictFactor_strict e T K seedParam
      refinedParam heMonotone heValue heBound hseedStrict
    factor_value := terminalPinnedStrictFactor_value e T K seedParam
      refinedParam heValue hseedOne hrefinedOne
    seed_monotone := hseedMonotone
    refined_monotone := hrefinedMonotone
    refined_small := hrefinedSmall
    cellDiameter := hcellDiameter
    initial_anchor := hinitial }

private theorem seed_small
    (geometry : PathStrictFactorGeometry certificate gamma seedParam
      refinedParam initial length) (n : ℕ) :
    letI : MetricSpace M := g.toMetricSpace
    dist (gamma (seedParam (n + 1))) (gamma (seedParam n)) <
      certificate.meshRadius := by
  letI : MetricSpace M := g.toMetricSpace
  apply geometry.cellDiameter n
  · exact ⟨geometry.seed_monotone (Nat.le_succ n), le_rfl⟩
  · exact ⟨le_rfl, geometry.seed_monotone (Nat.le_succ n)⟩

private theorem factor_cell_mem
    (geometry : PathStrictFactorGeometry certificate gamma seedParam
      refinedParam initial length) (n r : ℕ)
    (hr : r ≤ (factorGapNodes refinedParam geometry.factor n).length) :
    refinedParam (geometry.factor n + r) ∈
      Icc (seedParam n) (seedParam (n + 1)) := by
  have hstrict := geometry.factor_strict n
  have hrIndex : geometry.factor n + r ≤ geometry.factor (n + 1) := by
    rw [factorGapNodes_length] at hr
    omega
  constructor
  · rw [← geometry.factor_value n]
    exact geometry.refined_monotone (Nat.le_add_right _ _)
  · rw [← geometry.factor_value (n + 1)]
    exact geometry.refined_monotone hrIndex

/-- Pure subdivision geometry constructs the complete uniform strict-factor
package for the sampled path node sequences.  In particular, all intermediate
schedule bounds are proved here and no insertion chain is retained. -/
noncomputable def toUniformStrictFactorGeometry
    (geometry : PathStrictFactorGeometry certificate gamma seedParam
      refinedParam initial length) :
    UniformStrictFactorGeometry certificate
      (gamma ∘ seedParam) (gamma ∘ refinedParam) initial length := by
  letI : MetricSpace M := g.toMetricSpace
  let seed : ℕ → M := gamma ∘ seedParam
  let refined : ℕ → M := gamma ∘ refinedParam
  have hfactorValue : ∀ n : ℕ,
      refined (geometry.factor n) = seed n := by
    intro n
    exact congrArg gamma (geometry.factor_value n)
  refine
    { factor := geometry.factor
      factor_zero := geometry.factor_zero
      factor_strict := fun n _hn ↦ geometry.factor_strict n
      factor_value := fun n _hn ↦ hfactorValue n
      initial_anchor := geometry.initial_anchor
      coarse_small := ?_
      refined_small := ?_
      schedule_zero := ?_
      schedule_small := ?_
      insertion_opposite_small := ?_ }
  · intro j
    exact geometry.seed_small j
  · intro j
    exact geometry.refined_small j
  · intro n i
    let gap := factorGapNodes refined geometry.factor n
    let r := min i gap.length
    have hr : r ≤ gap.length := min_le_right _ _
    have hshape := factorGapSchedule_prefix_tail seed refined geometry.factor
      geometry.factor_zero geometry.factor_strict hfactorValue n i
    change insertNodeListSchedule
        (factorRefinementStage seed refined geometry.factor n)
        (geometry.factor n) gap i 0 = seed 0
    calc
      insertNodeListSchedule
            (factorRefinementStage seed refined geometry.factor n)
            (geometry.factor n) gap i 0 = refined 0 :=
        hshape.1 0 (Nat.zero_le _)
      _ = seed 0 := by
        simpa only [geometry.factor_zero] using hfactorValue 0
  · intro n i j
    let gap := factorGapNodes refined geometry.factor n
    let r := min i gap.length
    have hr : r ≤ gap.length := min_le_right _ _
    have hshape := factorGapSchedule_prefix_tail seed refined geometry.factor
      geometry.factor_zero geometry.factor_strict hfactorValue n i
    change dist
        (insertNodeListSchedule
          (factorRefinementStage seed refined geometry.factor n)
          (geometry.factor n) gap i (j + 1))
        (insertNodeListSchedule
          (factorRefinementStage seed refined geometry.factor n)
          (geometry.factor n) gap i j) < certificate.meshRadius
    by_cases hprefix : j + 1 ≤ geometry.factor n + r
    · rw [hshape.1 (j + 1) hprefix,
        hshape.1 j (Nat.le_trans (Nat.le_succ j) hprefix)]
      exact geometry.refined_small j
    · by_cases hbridge : j = geometry.factor n + r
      · subst j
        rw [hshape.2 0]
        simp only [Nat.add_zero]
        rw [hshape.1 (geometry.factor n + r) le_rfl]
        have hrParam :
            r ≤ (factorGapNodes refinedParam geometry.factor n).length := by
          simpa only [gap, factorGapNodes_length] using hr
        apply geometry.cellDiameter n
        · exact ⟨geometry.seed_monotone (Nat.le_succ n), le_rfl⟩
        · exact geometry.factor_cell_mem n r hrParam
      · have hjtail : geometry.factor n + r + 1 ≤ j := by omega
        let q := j - (geometry.factor n + r + 1)
        have hj : j = geometry.factor n + r + 1 + q := by
          dsimp [q]
          omega
        have hjnext : j + 1 = geometry.factor n + r + 1 + (q + 1) := by
          rw [hj]
          omega
        have hcurrent :
            insertNodeListSchedule
                (factorRefinementStage seed refined geometry.factor n)
                (geometry.factor n) gap i j = seed (n + 1 + q) := by
          rw [hj]
          exact hshape.2 q
        have hnext :
            insertNodeListSchedule
                (factorRefinementStage seed refined geometry.factor n)
                (geometry.factor n) gap i (j + 1) =
              seed (n + 1 + (q + 1)) := by
          rw [hjnext]
          exact hshape.2 (q + 1)
        rw [hcurrent, hnext]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          geometry.seed_small (n + 1 + q)
  · intro n _hn i hi
    let gap := factorGapNodes refined geometry.factor n
    have hshape := factorGapSchedule_prefix_tail_of_le seed refined
      geometry.factor geometry.factor_zero geometry.factor_strict hfactorValue
      n i (Nat.le_of_lt hi)
    change dist
        (insertNodeListSchedule
          (factorRefinementStage seed refined geometry.factor n)
          (geometry.factor n) gap i (geometry.factor n + i + 1))
        (insertNodeListSchedule
          (factorRefinementStage seed refined geometry.factor n)
          (geometry.factor n) gap (i + 1)
            (geometry.factor n + i + 1)) < certificate.equalityRadius
    rw [hshape.2 0]
    simp only [Nat.add_zero]
    rw [factorGapSchedule_succ seed refined geometry.factor n i hi]
    rw [insertNodeSequence_inserted]
    have hget := factorGapNodes_get refined geometry.factor n ⟨i, hi⟩
    rw [show gap[i] = refined (geometry.factor n + i + 1) by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hget]
    have hmem : refinedParam (geometry.factor n + i + 1) ∈
        Icc (seedParam n) (seedParam (n + 1)) := by
      have hiParam :
          i + 1 ≤ (factorGapNodes refinedParam geometry.factor n).length := by
        simpa only [factorGapNodes_length] using hi
      simpa only [Nat.add_assoc] using
        geometry.factor_cell_mem n (i + 1) hiParam
    exact (geometry.cellDiameter n
      ⟨geometry.seed_monotone (Nat.le_succ n), le_rfl⟩ hmem).trans_le
        certificate.meshRadius_le_equalityRadius

end PathStrictFactorGeometry

end DifferentialUniformSuccessorPathStrictFactorGeometry
end Poincare
