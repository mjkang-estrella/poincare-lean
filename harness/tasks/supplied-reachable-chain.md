# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-reachable-chain`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-reachable-chain_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-2.md` (the whole specification; your task is reproduced below
verbatim), then the landed modules of tasks 6-9 and their assembly: `CartanSuppliedDifferentialSuccessor.lean`,
`CartanSuppliedDifferentialTransfer.lean`, `FixedChartLocalSuccessorExistence.lean`,
`FixedChartLocalSuccessorEquality.lean`, `FixedChartMovingPositionJacobi.lean` (`exists_radius`),
`FixedChartMappedGeodesicAssembly.lean` (`FixedChartLocalSuccessorEquality.exists_radii`: the H1 and H2
replacements on a patch, proved). Both H1 and H2 patch statements are now THEOREMS; use them.

# Task supplied-reachable-chain

## Shared contract and verification convention

Task 6 starts at the recorded base. Each later implementation task freezes a new base containing its accepted predecessors. Tasks 6→7→8→9→10 are the requested dependency order; task 10's abstract recursion only needs tasks 6–7, while the later geometric dispatcher will need 8–9. Each task owns exactly the one new file named in its heading. All existing Lean files, `Poincare.lean`, audit wiring, and the other tasks' files are forbidden. This report-only attempt owns only this Markdown file; it does not update `HANDOFF.md`.

The following blocks give complete definitions and full theorem signatures. The signatures intentionally have no proof bodies. For declaration/type checking, each `theorem name : P` is transformed into `def name_spec : Prop := P`; no proof placeholder, axiom, or implementation of a target is introduced. Concatenating the blocks in order is the checked scratch contract. The broad existing import envelope below is for that scratch file. Each task's intended imports are specified separately.

```lean
import Poincare.Global.FixedChartUniformPreferredGermAgreement
import Poincare.Global.DifferentialSuccessorIntervalNaturality
import Poincare.Global.DifferentialSuccessorAdjacentContinuation
import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

```


## 10. `Poincare/Global/CartanSuppliedReachableChain.lean`

Namespace: `Poincare.CartanSuppliedReachableChain`.
Imports: task 7. Tasks 8–9 are the preceding geometric contracts, but abstract recursion should not import their proof modules unnecessarily.

Objective: realize and compare chains under an explicit state-dependent patch policy. `Q n s` selects an interpretation at the actually reached geometric state, including its target. The policy is external to `ChainState`; otherwise equality of states would falsely require equality of patch indices. `ReachableChain` only stores data at reached states, as in S5.`Chain.ReachableChain`. `StepAvailable` is an explicit sufficient recursion hypothesis at nodes, not something this task claims from curvature.

Reuse the induction/choice proofs in S5.`Chain.reachableChainOfStepAvailable`, `Chain.ReachableChain.state_anchor_eq_node`, and `Chain.ReachableChain.state_eq`, substituting task 7's witness-independence theorem. Equal states feed the same policy. Different policies require the open-map agreement in `state_eq_of_open_agreement`, using task 7's cross-interpretation theorem. No patch-label equality is needed.

Tasks 8–9 alone do not instantiate `StepAvailable`: their targets range over `H`, and H1 keeps a successor in the open target patch, not necessarily in the same compact `H`. A later covering/mesh task must choose patches and compact cores covering the reached target, and obtain uniform bounds before recursion. S9's existing whole-cell theorem consumes a joint certificate and chooses subdivision before constructing the chain. This task preserves that ordering but does not claim a new whole-cell theorem. The two remaining chain/mesh/overlap files, restricted-atlas file, and final development adapter remain outside this dispatch.

```lean
namespace CartanSuppliedReachableChain
open CartanSuppliedDifferentialSuccessor
structure ReachableChain (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g) where
  state : ℕ → CartanChain.ChainState g
  initial_eq : state 0 = initial
  data : ∀ n, Data (Q n (state n)) (state n) (nodes (n + 1))
  successor_eq : ∀ n, state (n + 1) = (data n).successor

def StepAvailable (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) : Prop :=
  ∀ (n : ℕ) (s : CartanChain.ChainState g), s.anchor = nodes n →
    Nonempty (Data (Q n s) s (nodes (n + 1)))
-- TARGET 10.1
theorem exists_reachableChain :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g),
    initial.anchor = nodes 0 → StepAvailable Q nodes → Nonempty (ReachableChain Q nodes initial)
-- TARGET 10.2
theorem state_anchor_eq_node :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial), initial.anchor = nodes 0 →
    ∀ n, (c.state n).anchor = nodes n
-- TARGET 10.3
theorem node_mem_predecessor_source :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial) (n : ℕ),
    nodes (n + 1) ∈ (germ (Q n (c.state n)) (c.state n)).source
-- TARGET 10.4
theorem state_eq :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c e : ReachableChain Q nodes initial), ∀ n, c.state n = e.state n
-- TARGET 10.5
theorem state_eq_of_open_agreement :
  ∀ (Q R : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial) (e : ReachableChain R nodes initial),
    (∀ n, ∃ W : Set M, IsOpen W ∧ nodes (n + 1) ∈ W ∧
      EqOn (map (Q n (c.state n)) (c.state n)) (map (R n (e.state n)) (e.state n)) W) →
    ∀ n, c.state n = e.state n
end CartanSuppliedReachableChain
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedReachableChain.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedReachableChain.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: All five targets compile for the displayed state-dependent policies, with data stored only at reached states. Otherwise record the exact dependent-recursion or cross-policy equality goal. Do not claim mesh, overlap, restricted-atlas, or recognition acceptance from this chain file.

```lean
end Poincare
```

