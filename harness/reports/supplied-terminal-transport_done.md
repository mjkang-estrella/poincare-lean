# Supplied terminal transport: worker result

Date: 2026-09-08. Branch: `worker/supplied-terminal-transport`.
Frozen base: `34754e24c441d88468bb99976a8f495a9a358d62`.
Verified proof head: `81a9f8194c3aab640afdee47dab26fe684fe936f`.

All three frozen targets in task 17 compile at their displayed signatures:
`exists_short_paths`, `short_path_endpoint`, and `endpoint_trans`.
This is a worker result awaiting independent orchestrator review. It does not
assert homotopy invariance, global recognition, or the Poincare endpoint.

## Proof content

The new file is `Poincare/Global/CartanSuppliedTerminalTransport.lean`.
It imports only `CartanSuppliedSubdivisionTransport`. Task 16 is not imported.

The path component of the positive mesh ball is open by manifold local path
connectedness and supplies the short paths. The landed `block_state_eq`
identifies the full endpoint with every actual datum in the initial fallback
patch. An explicit dependent transport retains the exact initial state and
terminal point in that datum type.

`exists_trans_subdivision` embeds the two given subdivisions into the first
and second halves of the unit interval. It proves strictness, the combined
terminal index, both sample equations, and whole-cell diameter control,
including the shared midpoint. `segment_state_eq` applies the landed block
theorem to compare a finite segment with a chain beginning at its actual
middle state.

For concatenation, a supplied chain is realized on this combined subdivision.
Its first segment agrees with `R`, so its midpoint is exactly `R.endpoint`.
Its second segment agrees with the actual dependent chain `T` on `q.cast h rfl`.
The landed same-path comparison then identifies this combined endpoint with
`C.endpoint`. No path-homotopy premise is used.

## Verification

All commands below ran in the isolated worktree. The final direct Lean check
was saved as `/tmp/supplied-terminal-transport-evidence/lean-09.log`.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedTerminalTransport.lean
```

Exit 0, no output.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedTerminalTransport
```

Exit 0. Final output:

```text
✔ [3625/3625] Built Poincare.Global.CartanSuppliedTerminalTransport (4.0s)
Build completed successfully (3625 jobs).
```

The build replayed existing dependency linter warnings. The new module emitted
no warnings. Full output is preserved in
`/tmp/supplied-terminal-transport-evidence/build.log`.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedTerminalTransport.lean
git diff --check
git diff 34754e24c441d88468bb99976a8f495a9a358d62 HEAD --check
```

The scan exited 1 with no matches. Both diff checks exited 0 with no output.

The probe uses the task-17 signatures extracted verbatim from
`harness/reports/parametrization-plan-3.md`, replacing each theorem header by
an `example` proved by the fully qualified implementation. It retains
`autoImplicit false`. It also prints every new theorem's axiom closure.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-terminal-transport-evidence/signatures-and-axioms.lean
```

Exit 0. Actual output:

```text
'Poincare.CartanSuppliedTerminalTransport.exists_short_paths' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedTerminalTransport.short_path_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedTerminalTransport.trans_halfTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedTerminalTransport.trans_secondTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedTerminalTransport.exists_trans_subdivision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedTerminalTransport.segment_state_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedTerminalTransport.endpoint_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Commits and evidence

Each verified theorem was committed separately:

```text
5a2aa381 Prove short supplied terminal paths in a mesh ball
c58c23fe Identify every short-path terminal datum with the full reached state
be7a42cd Recover the first path at concatenated half-times
14e5b7f8 Recover the second path including the concatenation midpoint
ff8cc800 Concatenate strict whole-cell subdivisions with exact sample embeddings
0aebe5b9 Compare finite supplied chain segments from an exact middle state
81a9f819 Prove supplied endpoint concatenation from the actual reached middle state
```

The proof diff is preserved at
`/tmp/supplied-terminal-transport-evidence/verified-proof.diff` and is
reproducible with:

```sh
git diff 34754e24c441d88468bb99976a8f495a9a358d62 81a9f8194c3aab640afdee47dab26fe684fe936f -- Poincare/Global/CartanSuppliedTerminalTransport.lean
```

Failed compiler outputs remain in that evidence directory:

- `lean-02.log` through `lean-04.log`: simplification did not transport the
  dependent datum type. `lean-05.log`: direct dependent elimination failed.
  The explicit transport lemma compiled in `lean-06.log`.
- `geometry-01.log`: the path-extension rewrite needed
  `Path.extend_extends'`. The corrected proof passed in `geometry-02.log`.
- `segment-01.log`: an unnecessary `dsimp` reported no progress.
  Removing it passed in `segment-02.log`.
- `full-01.log`: one natural-number index needed simplification and one
  function application needed beta reduction before rewriting.
  Both fixes passed in `full-02.log` and the final source check.

Only the named new Lean file and this report are changed. Existing Lean files,
`Poincare.lean`, audit wiring, and `HANDOFF.md` remain untouched under the
explicit worker file scope. Root integration audits were not run by this worker.

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedTerminalTransport.lean
```
