# Supplied subdivision transport completed

Date: 2026-09-08. Branch: `worker/supplied-subdivision-transport`.
Frozen base: `a4339b433854fc41cf9a31730bd01e159d857d4c`.
Verified proof head: `c393917f0e1be04a1330aba7d459f68c9a91720b`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`, pinned Mathlib.

Both frozen targets compile with their displayed signatures:
`Poincare.CartanSuppliedSubdivisionTransport.refinement_state_eq` and
`Poincare.CartanSuppliedSubdivisionTransport.endpoint_eq_same_path`.
Their conclusions identify full chain states, including tangent alignments.
The factor map is only monotone and starts at zero. Repeated factor values,
arbitrary inserted block lengths, and terminal tails are included.
There is no simple-connectivity or global path-independence premise.

This is a worker result awaiting independent orchestrator review. It does not
assert homotopy invariance, global recognition, or the Poincare theorem.

## Scope and proof

The only new Lean file is
`Poincare/Global/CartanSuppliedSubdivisionTransport.lean`, with the single import
`Poincare.Global.CartanSuppliedWholeCellRealization`. No existing Lean file,
root import, source definition, audit wiring, or HANDOFF.md changed. The
specific worker scope takes precedence over the general handoff-update rule.
This report is the only harness change. Initial git status was clean, and the
worktree inventory and HEAD confirmed the frozen base before editing.

`block_state_eq` compares every reached state in a finite block with every
direct datum from its initial state in a valid initial patch. H1 produces
the intermediate direct data from buffer membership. Task 12's
`transition_eqOn` compares the direct predecessor map with the currently
selected patch at the intermediate successor. Both sampled points are within
one mesh of the initial anchor, so their distance is below two meshes and
hence inside the four-mesh open agreement ball. S2's
`successor_eq_of_eqOn_open` identifies the actual differential successors.
The zero case uses S2's `patch_successor_at_anchor`.

`refinement_chain_state_eq` applies that block argument on
`[f n, f (n + 1)]`. Monotonicity places every inserted time in the original
whole cell. This stronger helper permits an arbitrary monotone sampled
chain, without requiring strict inserted times or a terminal index.
`refinement_state_eq` specializes it to the second realization.

`state_eq_of_constant_nodes` proves full state constancy across repeated
nodes with S2's zero-step law. `endpoint_eq_same_path` reuses S11's
`exists_common_monotone_refinement_strict_factor` directly. Its bracket
clauses provide the mesh bound for a supplied chain on the common samples.
Task 13's `exists_sticky_chain` produces that chain. Both input realizations
transport to it using the generalized refinement helper. Monotonicity and
the upper bound of the unit interval make all nodes after either represented
terminal time constant, so both represented terminal states equal the state
at the common bound K. The common sampled chain need not be repackaged as a
strict Realization; the stronger helper handles the repeated samples
already allowed by S11.

## Verified proof commits

Each lemma was directly elaborated before its separate commit.

| Commit | Theorem |
| --- | --- |
| `12ef4544` | `block_state_eq` |
| `a64e04a6` | `refinement_chain_state_eq` |
| `eaf3b4d5` | `refinement_state_eq` |
| `8f08f43f` | `state_eq_of_constant_nodes` |
| `c393917f` | `endpoint_eq_same_path` |

## Commands and actual results

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSubdivisionTransport.lean
```

Final invocation: exit 0, no output. Successful intermediate logs are
`block-03.log`, `refinement-chain-02.log`, `refinement-01.log`, and
`constant-02.log`; final direct log is `endpoint-01.log`. All are under
`/tmp/supplied-subdivision-transport-evidence` and all are empty.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedSubdivisionTransport
```

Exit 0. Final output:

```text
✔ [3624/3624] Built Poincare.Global.CartanSuppliedSubdivisionTransport (2.9s)
Build completed successfully (3624 jobs).
```

The build replayed existing dependency linter warnings, including the unused
`hcurv` in `CartanSuppliedBufferedPairAgreement.lean`. The new module emitted
no warnings. Full output is preserved in the 10,038-line
`/tmp/supplied-subdivision-transport-evidence/build.log`.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedSubdivisionTransport.lean
git diff --check
git diff a4339b433854fc41cf9a31730bd01e159d857d4c --check
```

Token scan: exit 1, no matches. Both diff checks: exit 0, no output.
The committed proof diff has exactly one added Lean file, 212 lines.
The final proof diff is also preserved in
`/tmp/supplied-subdivision-transport-evidence/final.diff` and reproducible by:

```sh
git diff a4339b433854fc41cf9a31730bd01e159d857d4c c393917f -- Poincare/Global/CartanSuppliedSubdivisionTransport.lean
```

No root build or integration audits were run. Those remain the orchestrator's
integration checkpoint.

## Exact target probes and dependency closures

The two example signatures below were extracted from task 15 in
`harness/reports/parametrization-plan-3.md`. The probe has
`autoImplicit false` and checks every new theorem's dependency closure.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-subdivision-transport-evidence/probe.lean
```

Exit 0. Exact probe:

```lean
import Poincare.Global.CartanSuppliedSubdivisionTransport

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain
namespace CartanSuppliedSubdivisionTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

example : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R T : Realization S initial p)
    (f : ℕ → ℕ), f 0 = 0 → Monotone f →
  (∀ n, R.subdivision.time n = T.subdivision.time (f n)) →
  ∀ n, R.chain.state n = T.chain.state (f n)
 := refinement_state_eq

example : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R T : Realization S initial p),
  R.endpoint = T.endpoint := endpoint_eq_same_path

end CartanSuppliedSubdivisionTransport
end Poincare
#print axioms Poincare.CartanSuppliedSubdivisionTransport.block_state_eq
#print axioms Poincare.CartanSuppliedSubdivisionTransport.refinement_chain_state_eq
#print axioms Poincare.CartanSuppliedSubdivisionTransport.refinement_state_eq
#print axioms Poincare.CartanSuppliedSubdivisionTransport.state_eq_of_constant_nodes
#print axioms Poincare.CartanSuppliedSubdivisionTransport.endpoint_eq_same_path
```

Actual output:

```text
'Poincare.CartanSuppliedSubdivisionTransport.block_state_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedSubdivisionTransport.refinement_chain_state_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedSubdivisionTransport.refinement_state_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedSubdivisionTransport.state_eq_of_constant_nodes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedSubdivisionTransport.endpoint_eq_same_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Compiler retries

The failed compiler output is preserved below and in the named temporary
logs. These were dependent substitution and index-normalization errors, not
unproved geometric assumptions. The first two shell wrappers ended with
`cat`, so their outer shell exit was 0 despite the displayed compiler errors;
those attempts were failures. All later wrappers propagated Lean's exit code.
`refinement-chain-01.log` and `constant-01.log` exited 1. All successful
checks listed above exited 0.

### block-01.log

```text
Poincare/Global/CartanSuppliedSubdivisionTransport.lean:59:66: error: Application type mismatch: The argument
  d
has type
  Data (S.cover.interp a) (c.state m) (nodes (m + 0))
but is expected to have type
  Data (patch (S.cover.source.patch a.1) (S.cover.target.patch a.2)) ?m.667 (CartanChain.ChainState.anchor ?m.667)
in the application
  CartanSuppliedDifferentialTransfer.patch_successor_at_anchor (S.cover.source.center a.1) (S.cover.target.center a.2)
    (S.cover.source.zone a.1) (S.cover.target.zone a.2) (S.cover.source.patch a.1) (S.cover.target.patch a.2)
    (S.cover.source.cutoff a.1) (S.cover.target.cutoff a.2) ?m.667 d
Poincare/Global/CartanSuppliedSubdivisionTransport.lean:87:8: error: Type mismatch: After simplification, term
  c.successor_eq (m + k)
 has type
  c.state (m + (k + 1)) = (c.data (m + k)).successor
but is expected to have type
  c.state (m + (k + 1)) = hdata.successor
```

### block-02.log

```text
Poincare/Global/CartanSuppliedSubdivisionTransport.lean:86:10: error: Tactic `rewrite` failed: motive is not type correct:
  fun _a => c.state _a = d✝.successor
Error: Application type mismatch: The argument
  d✝
has type
  Data (S.cover.interp a) (c.state m) (nodes (m + (k + 1)))
but is expected to have type
  Data (S.cover.interp a) (c.state m) (nodes _a)
in the application
  d✝.successor

Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that 'congrArg' implies that 'm a = m b', which can be used with lemmas such as 'Eq.mpr' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.

Possible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and 'Decidable' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).

case succ
M : Type u
inst✝⁴ : TopologicalSpace M
inst : ChartedSpace E M
inst✝³ : IsManifold I ∞ M
inst✝² : T2Space M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
g : ClosedSmoothRiemannianMetric 3 M
S : System g
initial : CartanChain.ChainState g
nodes : ℕ → M
preferred : ℕ → S.cover.Label
c : ReachableChain (policy S.cover preferred) nodes initial
hinitial : initial.anchor = nodes 0
m N : ℕ
a : S.cover.Label
ha : S.cover.Valid a (c.state m)
this : MetricSpace M := g.toMetricSpace
hsmall : ∀ k ≤ N, dist (nodes (m + k)) (c.state m).anchor < S.mesh
hpos : 0 < S.mesh
hbound :
  4 * S.mesh ≤ S.cover.step ∧
    4 * S.mesh ≤ S.cover.evaluation ∧ 4 * S.mesh ≤ S.cover.retention ∧ 4 * S.mesh ≤ S.switch.radius
hdirect : ∀ k ≤ N, Nonempty (Data (S.cover.interp a) (c.state m) (nodes (m + k)))
hanchor : (c.state m).anchor = nodes m
k : ℕ
ih : k ≤ N → ∀ (d : Data (S.cover.interp a) (c.state m) (nodes (m + k))), c.state (m + k) = d.successor
hk : k + 1 ≤ N
d✝ : Data (S.cover.interp a) (c.state m) (nodes (m + (k + 1)))
d : Data (S.cover.interp a) (c.state m) (nodes (m + k + 1))
e : Data (S.cover.interp a) (c.state m) (nodes (m + k))
he : c.state (m + k) = e.successor
b : S.cover.Label := select S.cover (preferred (m + k)) (c.state (m + k))
hb : S.cover.Valid b e.successor
hagree :
  EqOn (CartanSuppliedDifferentialSuccessor.map (S.cover.interp a) (c.state m))
    (CartanSuppliedDifferentialSuccessor.map (S.cover.interp b) e.successor) (ball (nodes (m + k)) (4 * S.mesh))
hz : nodes (m + (k + 1)) ∈ ball (nodes (m + k)) (4 * S.mesh)
heq :
  EqOn (CartanSuppliedDifferentialSuccessor.map (S.cover.interp a) (c.state m))
    (CartanSuppliedDifferentialSuccessor.map (policy S.cover preferred (m + k) (c.state (m + k))) (c.state (m + k)))
    (ball (nodes (m + k)) (4 * S.mesh))
⊢ c.state (m + (k + 1)) = d✝.successor
```

### refinement-chain-01.log

```text
Poincare/Global/CartanSuppliedSubdivisionTransport.lean:125:32: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  t (f (n + 1))
in the target expression
  ∀
    (d :
      Data (S.cover.interp (select S.cover (R.preferred n) (R.chain.state n))) (c.state (f n))
        ((fun k => p (t k)) (f (n + 1)))),
    c.state (f (n + 1)) = d.successor

case succ
M : Type u
inst✝⁴ : TopologicalSpace M
inst : ChartedSpace E M
inst✝³ : IsManifold I ∞ M
inst✝² : T2Space M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
g : ClosedSmoothRiemannianMetric 3 M
S : System g
initial : CartanChain.ChainState g
y : M
p : Path initial.anchor y
R : Realization S initial p
t : ℕ → ↑I
htzero : t 0 = 0
htmono : Monotone t
preferred : ℕ → S.cover.Label
c : ReachableChain (policy S.cover preferred) (fun k => p (t k)) initial
f : ℕ → ℕ
hfzero : f 0 = 0
hfmono : Monotone f
htimes : ∀ (n : ℕ), R.subdivision.time n = t (f n)
this : MetricSpace M := g.toMetricSpace
hinitial : initial.anchor = p (t 0)
n : ℕ
ih : R.chain.state n = c.state (f n)
hf : f n ≤ f (n + 1)
hsmall : ∀ k ≤ f (n + 1) - f n, dist (p (t (f n + k))) (c.state (f n)).anchor < S.mesh
hblock :
  ∀
    (d :
      Data (S.cover.interp (select S.cover (R.preferred n) (R.chain.state n))) (c.state (f n))
        ((fun k => p (t k)) (f (n + 1)))),
    c.state (f (n + 1)) = d.successor
⊢ R.chain.state (n + 1) = c.state (f (n + 1))
```

### constant-01.log

```text
Poincare/Global/CartanSuppliedSubdivisionTransport.lean:152:15: error: invalid 'by' tactic, expected type has not been provided
```

## Exact next action

The orchestrator should independently review the diff from the frozen base
and run:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSubdivisionTransport.lean
```

Then rerun the focused build and embedded exact-signature/dependency probe
before deciding acceptance and integration. No task was marked accepted and
no merge was performed by this worker.
