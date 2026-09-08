# Supplied homotopy endpoints: worker result

Date: 2026-09-08. Task 16 of `parametrization-plan-3.md`.
Base: `ec8ab087872d3c5b0bb587c8227432e4d18857b9`.
Branch: `worker/supplied-homotopy-endpoints`.
Verified proof head: `e82d2a0652abe5aa84453fc35ed687f2e9de2411`.

All four frozen targets compile in the one new module
`Poincare/Global/CartanSuppliedHomotopyEndpoints.lean`:

- `exists_grid`
- `grid_endpoint_eq`
- `endpoint_eq_of_homotopy`
- `endpoint_eq`

The result compares full `CartanChain.ChainState` values for arbitrary boundary
subdivisions and policies. No equality-ball, boundary-transport, or homotopy
invariance premise remains. `SimplyConnectedSpace M` occurs only in
`endpoint_eq`, where `SimplyConnectedSpace.paths_homotopic` supplies the
relative-endpoint homotopy. This is a worker result awaiting independent
orchestrator acceptance. It does not assert global recognition or the reserved
Poincare theorem.

## Proof content

`exists_grid` applies the landed compact-square metric-ball theorem to balls
of radius `S.mesh / 2` centered on the homotopy image. Triangle inequality
proves the frozen `GridSmall` definition for all points of every closed cell,
including boundary and eventual constant cells.

`ladder_state_eq` is the new supplied ladder invariant. H1 produces vertical
data at each actual lower-row state in its selected interpretation. H2 and
`transition_eqOn` compare the lower predecessor with both the lower successor
and the vertical successor, retaining the separately selected labels. The
intersection of their open four-mesh balls contains the opposite upper
vertex. `successor_eq_of_eqOn_open` then identifies the upper edge's actual
successor with every vertical datum's successor. The induction starts with
`patch_successor_at_anchor`, and `grid_endpoint_eq` uses the same zero-rung
law at the common terminal node before iterating adjacent-row equality.

`exists_grid_refining` first forms a common monotone refinement of both input
subdivisions and then refines that sequence with the small homotopy grid.
The composed factor maps retain every original sample, are monotone, start
at zero, and are bounded by the new terminal index. Cell-bracketing clauses
preserve `GridSmall`; no equality of the old and new sample sequences is
assumed.

`endpoint_eq_sampled_chain` applies task 15's
`refinement_chain_state_eq`, then its `state_eq_of_constant_nodes` to bridge
the embedded terminal sample to the new grid endpoint. `endpoint_eq_of_homotopy`
constructs actual sticky supplied chains on every refined row and combines
this boundary transport with `grid_endpoint_eq`. The input realizations
remain arbitrary, including non-sticky policies.

No existing Lean file, root import, audit wiring, source definition, or
`HANDOFF.md` changed. The specific worker scope permits only the new Lean
module and this report, so this report carries the handoff facts. The assigned
`worker/` branch was retained as explicitly instructed.

## Verification

All commands ran in the isolated worktree. The runner stored stdout/stderr
without filtering and recorded each exit code under
`/tmp/supplied-homotopy-endpoints-evidence/`. Its `EXIT` lines report process
status and are not Lean output.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedHomotopyEndpoints.lean
```

Final direct check: exit 0, no output. Evidence: `lean-09.log`, `lean-09.exit`.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedHomotopyEndpoints
```

Exit 0. The final two output lines were:

```text
✔ [3625/3625] Built Poincare.Global.CartanSuppliedHomotopyEndpoints (2.0s)
Build completed successfully (3625 jobs).
```

Lake replayed existing dependency warnings; the new module emitted none.
The complete 727,622-byte output is retained as `build.log`, with `build.exit`.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedHomotopyEndpoints.lean
git diff ec8ab087872d3c5b0bb587c8227432e4d18857b9 --check
```

Token scan: exit 1, no matches and no output. Diff check: exit 0, no output.
Evidence: `token-scan.log`, `token-scan.exit`, `diff-check.log`, `diff-check.exit`.
The exact proof diff is retained in `proof.diff` and in the seven commits below.

### Exact signatures

`signatures.lean` was generated from the task-16 Lean block in the frozen
report, preserving all four displayed binder-bearing signatures and replacing
each declaration with an `example` proved by the corresponding new theorem.
It imports the new module and enables `autoImplicit false`. No signatures were
inferred from the implementation to construct this probe.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-homotopy-endpoints-evidence/signatures.lean
```

Exit 0, no output. Evidence: `signatures.log`, `signatures.exit`.
Reproduce the scratch probe from the specification:

```python
from pathlib import Path
import re
source = Path('Poincare/Global/CartanSuppliedHomotopyEndpoints.lean').read_text()
report = Path('harness/reports/parametrization-plan-3.md').read_text()
task = report.split('## 16. ')[1].split('## 17. ')[0]
block = re.search(r'```lean\n(.*?)\n```', task, re.S).group(1)
targets = re.findall(
    r'theorem (\w+)(.*?)(?=\ntheorem |\nend CartanSuppliedHomotopyEndpoints)',
    block, re.S)
assert len(targets) == 4
prefix = source[source.index('set_option autoImplicit false'):source.index('def GridSmall')]
probe = 'import Poincare.Global.CartanSuppliedHomotopyEndpoints\n' + prefix
for name, signature in targets:
    probe += 'example' + signature + ' := ' + name + '\n\n'
probe += 'end CartanSuppliedHomotopyEndpoints\nend Poincare\n'
Path('/tmp/supplied-homotopy-endpoints-signatures.lean').write_text(probe)
```

### Axiom closure

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-homotopy-endpoints-evidence/axioms.lean
```

Exit 0. The probe imports the new module and runs `#print axioms` on all
seven new theorem names. Actual output:

```text
'Poincare.CartanSuppliedHomotopyEndpoints.exists_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedHomotopyEndpoints.ladder_state_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedHomotopyEndpoints.grid_endpoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedHomotopyEndpoints.exists_grid_refining' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedHomotopyEndpoints.endpoint_eq_sampled_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedHomotopyEndpoints.endpoint_eq_of_homotopy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedHomotopyEndpoints.endpoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

```

Every closure is exactly `[propext, Classical.choice, Quot.sound]`.
No root build or root integration audits were run; those remain the
orchestrator's integration checkpoint.

## Commits

Each theorem was committed after a successful direct Lean check:

```text
4576a4ff Prove closed homotopy grids with supplied mesh control
02a65a8d Prove supplied ladder invariant with actual patch switches
45890f30 Prove full supplied state equality across homotopy grids
0fccc1bb Retain both boundary subdivisions in a small homotopy grid
00a6521b Transport supplied boundary endpoints through terminal grid tails
170acef9 Prove supplied endpoint equality for arbitrary homotopic realizations
e82d2a06 Derive supplied path independence from source simple connectivity

```

## Compiler retries

`lean-01.log` was empty; the first shell invocation did not independently
record Lean's exit status, so it was not used as gate evidence. `lean-02`
reran the first theorem with an explicit exit record and passed.

`lean-03` failed on tactic indentation in the H1 rung-supply argument.
The next attempt made the node argument explicit and put the tactics on
separate correctly indented lines. `lean-04` passed. The complete failed
compiler output is preserved below and in `lean-03.log`:

```text
Poincare/Global/CartanSuppliedHomotopyEndpoints.lean:80:47: error: unexpected token 'have'; expected ')', ',' or ':'
Poincare/Global/CartanSuppliedHomotopyEndpoints.lean:80:31: error: unsolved goals
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
u v : ℕ → M
a b : ℕ → S.cover.Label
c : ReachableChain (policy S.cover a) u initial
e : ReachableChain (policy S.cover b) v initial
hu : initial.anchor = u 0
hv : initial.anchor = v 0
this : MetricSpace M := g.toMetricSpace
hbottom : ∀ (n : ℕ), dist (u (n + 1)) (u n) < S.mesh
hvertical : ∀ (n : ℕ), dist (v n) (u n) < S.mesh
htop : ∀ (n : ℕ), dist (v (n + 1)) (v n) < S.mesh
hpos : 0 < S.mesh
hanchor : ∀ (n : ℕ), (c.state n).anchor = u n
n : ℕ
label : S.cover.Label := select S.cover (a n) (c.state n)
hvalid : S.cover.Valid (select S.cover (a n) (c.state n)) (c.state n)
⊢ dist ?m.478 (u n) < S.cover.step
Poincare/Global/CartanSuppliedHomotopyEndpoints.lean:67:33: error: unsolved goals
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
u v : ℕ → M
a b : ℕ → S.cover.Label
c : ReachableChain (policy S.cover a) u initial
e : ReachableChain (policy S.cover b) v initial
hu : initial.anchor = u 0
hv : initial.anchor = v 0
this : MetricSpace M := g.toMetricSpace
hbottom : ∀ (n : ℕ), dist (u (n + 1)) (u n) < S.mesh
hvertical : ∀ (n : ℕ), dist (v n) (u n) < S.mesh
htop : ∀ (n : ℕ), dist (v (n + 1)) (v n) < S.mesh
hpos : 0 < S.mesh
hanchor : ∀ (n : ℕ), (c.state n).anchor = u n
hsupply : ∀ (n : ℕ), Nonempty (Data (policy S.cover a n (c.state n)) (c.state n) (v n))
⊢ ∀ (n : ℕ) (d : Data (policy S.cover a n (c.state n)) (c.state n) (v n)), e.state n = d.successor

```

Direct attempts `lean-04` through `lean-09` all exited 0 without output.
One invocation before `lean-06` misspelled the runner directory as
`supplied-homopy-endpoints-evidence`; Python exited 2 with `No such file or
directory`, and Lean did not run. The corrected invocation passed. No
mathematical target was changed during these retries.

## Next action

From the recorded base, independently inspect the seven proof commits and run:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedHomotopyEndpoints.lean
```

Then rerun the focused build, four frozen signature probes, seven axiom
probes, token scan, and base-relative diff check. Acceptance and root import
integration belong to the orchestrator. The next dependent task is task 17's
supplied terminal transport; this worker has not modified it.
