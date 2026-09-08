# Supplied reachable chain worker result

Date: 2026-09-08. Status: done at the worker gate, pending independent orchestrator review.
Branch: `worker/supplied-reachable-chain`.
Frozen base: `4213325850f54b939d14550f1331bb41c56c52f6`.
Verified proof head: `903d16d969322a5f32a0a382d157e249d2974c23`.

All five frozen targets are proved in the one new Lean file
`Poincare/Global/CartanSuppliedReachableChain.lean`. Its only import is
`Poincare.Global.CartanSuppliedDifferentialTransfer`. No existing Lean file,
root import, audit, task, ledger, or `HANDOFF.md` changed. This report is the
only additional repository file, as required by the worker's file scope.
The worktree was clean at the recorded base before editing.

## Proof content

`ReachableChain` and `StepAvailable` have the frozen definitions. The policy
is external to `CartanChain.ChainState`, and the chain stores data only at
reached states.

- `exists_reachableChain` recurses in the subtype of states whose anchor is
  `nodes n`. Classical choice supplies each next datum using precisely the
  anchor equation required by `StepAvailable`. The same chosen datum defines
  both the recursive successor and the stored data.
- `state_anchor_eq_node` uses the initial equation at zero and the actual
  successor's anchor at positive indices.
- `node_mem_predecessor_source` projects the actual datum's supplied-source
  membership.
- `state_eq` inducts on the node index. Substitution of equal predecessor
  states aligns both the state and its policy interpretation, then task 7's
  `successor_eq` identifies the differential successors.
- `state_eq_of_open_agreement` uses the common initial state at zero and task
  7's `successor_eq_of_eqOn_open` at positive indices. That theorem compares
  different predecessor states directly, so the given open agreement at each
  reached pair suffices without an induction hypothesis or patch-label equality.

There are no additional instance assumptions. In particular, the two task-7
comparison theorems omit `T2Space M`, preserving the frozen task-10 context.

The landed H1 theorem is `FixedChartMovingPositionJacobi.exists_radius`; the
landed H1+H2 theorem is `FixedChartLocalSuccessorEquality.exists_radii` in
`FixedChartMappedGeodesicAssembly.lean`. Their source statements and imports
were read. Abstract recursion does not require importing those proof modules.
Their conclusions do not establish compact-core retention for all reached
targets, so `StepAvailable` remains an explicit recursion hypothesis.

## Separate verified commits

Each theorem was compiled successfully before its commit. Each staged diff
also passed `git diff --cached --check`.

| Target | Commit |
| --- | --- |
| 10.1 `exists_reachableChain` | `c81bbda1` |
| 10.2 `state_anchor_eq_node` | `4649ccda` |
| 10.3 `node_mem_predecessor_source` | `f14f36ef` |
| 10.4 `state_eq` | `67818b8a` |
| 10.5 `state_eq_of_open_agreement` | `903d16d9` |

## Commands and actual outputs

At each of the five successive source versions:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedReachableChain.lean
```

Every run exited 0 with no output. The five empty logs are
`/tmp/supplied-reachable-chain-evidence/10-1.log` through `10-5.log`.
No failed compiler attempts occurred.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedReachableChain
```

Exit 0. The full output is retained in
`/tmp/supplied-reachable-chain-evidence/build.log`. It replays existing
upstream linter warnings; the new module has no diagnostic. Final output:

```text
✔ [3608/3608] Built Poincare.Global.CartanSuppliedReachableChain (7.4s)
Build completed successfully (3608 jobs).
```

The independent probe contains five `example` declarations at the exact
frozen types extracted from `harness/reports/parametrization-plan-2.md`,
followed by a named axiom probe for each theorem. It imports only the new
module and uses the shared frozen instance context.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-reachable-chain-evidence/signatures.lean
```

Exit 0. Complete output:

```text
'Poincare.CartanSuppliedReachableChain.exists_reachableChain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedReachableChain.state_anchor_eq_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedReachableChain.node_mem_predecessor_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedReachableChain.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedReachableChain.state_eq_of_open_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The module-wide scan follows `harness/gate.sh`: it visits every non-internal
declaration belonging to the new module and calls `Lean.collectAxioms`.
It also throws an error if a nonstandard dependency is found.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-reachable-chain-evidence/axiom-scan.lean
```

Exit 0. Complete output:

```text
GATE_SCAN declarations=22 nonstandard=[]
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedReachableChain.lean
git diff --check
git diff 4213325850f54b939d14550f1331bb41c56c52f6 --check
```

Token scan: exit 1, no matches. Both diff checks: exit 0, no output.
The final base-relative diff is retained at
`/tmp/supplied-reachable-chain-evidence/final.patch`.

## Exact signature probe source

The following source is the actual probe that passed:

```lean
import Poincare.Global.CartanSuppliedReachableChain

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

namespace CartanSuppliedReachableChain
open CartanSuppliedDifferentialSuccessor
example :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g),
    initial.anchor = nodes 0 → StepAvailable Q nodes → Nonempty (ReachableChain Q nodes initial) := exists_reachableChain

#print axioms exists_reachableChain

example :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial), initial.anchor = nodes 0 →
    ∀ n, (c.state n).anchor = nodes n := state_anchor_eq_node

#print axioms state_anchor_eq_node

example :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial) (n : ℕ),
    nodes (n + 1) ∈ (germ (Q n (c.state n)) (c.state n)).source := node_mem_predecessor_source

#print axioms node_mem_predecessor_source

example :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c e : ReachableChain Q nodes initial), ∀ n, c.state n = e.state n := state_eq

#print axioms state_eq

example :
  ∀ (Q R : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial) (e : ReachableChain R nodes initial),
    (∀ n, ∃ W : Set M, IsOpen W ∧ nodes (n + 1) ∈ W ∧
      EqOn (map (Q n (c.state n)) (c.state n)) (map (R n (e.state n)) (e.state n)) W) →
    ∀ n, c.state n = e.state n := state_eq_of_open_agreement

#print axioms state_eq_of_open_agreement

end CartanSuppliedReachableChain
end Poincare
```

## Scope and next action

The task's exact stop condition is met: all five targets compile for the
state-dependent policies, with data stored only at reached states.
No mesh, overlap, restricted-atlas, recognition, or Poincare completion is
claimed. No root integration build or audit suite was run; this worker does
not merge or mark a task accepted.

Exact first orchestrator action, after reviewing the diff against the frozen base:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedReachableChain.lean
```

Then rerun the focused build and the five displayed signature/axiom probes
before deciding acceptance. The later patch-covering and mesh task must still
supply the recursion hypothesis with uniform bounds chosen before the chain.
