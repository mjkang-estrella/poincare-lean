# Poincare Lean Formalization

This repository is a Lean 4 formalization project targeting the Poincare
conjecture. It is not a completed proof.

The current development proves and audits many intermediate route, package, and
contract lemmas. The final theorem is deliberately not exposed as an
unconditional result until the remaining mathematical inputs are formalized.

## Current Boundary

- Final reserved theorem: `Poincare.poincare_conjecture`
- Current status: not complete
- Main open gap: the remaining dependency package still needs proof-bearing
  Lean formalizations of the analytic, surgery, smoothability, and topology
  inputs used by the final assembly route.
- Current checked route: conditional final routes through
  `PoincareProofDependenciesWithEquationBoundary`, not an unconditional
  Poincare proof.

See [CURRENT_STATUS.md](CURRENT_STATUS.md) for the latest repository snapshot.

## Repository Layout

- `Poincare/Statement.lean` defines the theorem statement, target 3-sphere
  model, completion criterion, and statement-level contracts.
- `Poincare/FullAssembly.lean` assembles the dependency packages into the final
  conditional routes.
- `Poincare/ProofProgress/` contains proof-progress modules and ledgers for the
  major proof surfaces.
- `Poincare/AnalyticFoundation.lean`, `Poincare/RicciFlow*.lean`,
  `Poincare/Surgery.lean`, and the curvature modules track the analytic and
  Ricci-flow boundary.
- `Poincare/TopologyExtraction.lean` and related proof-progress files track the
  topology extraction and one-point compactification boundary.
- `scripts/` contains build, interface, theorem-contract, semantic-surface,
  root-import, axiom, and completion audits.

## Major Proof Tasks

The remaining work is organized around seven independent surfaces:

1. Smoothability bridge
2. Grounded finite extinction and Ricci flow with surgery
3. Perelman analytic foundation
4. Topology extraction and recognition
5. One-point compactification topology
6. Final certificate collapse
7. Audit and status infrastructure

Progress should reduce one of these boundaries with proof-bearing Lean changes,
not only aliases or ledger entries.

## Verification

For narrow proof work:

```sh
lake env lean Poincare/<changed-file>.lean
rg "\b(sorry|admit|axiom)\b" Poincare/<changed-file>.lean
git diff --check
```

For integration or pre-merge verification:

```sh
lake build
bash scripts/interface_audit.sh
bash scripts/semantic_surface_audit.sh
bash scripts/theorem_contract_audit.sh
bash scripts/root_import_audit.sh
bash scripts/axiom_audit.sh
bash scripts/completion_audit.sh
git diff --check
```

The completion audit is expected to fail until the reserved theorem is present
and typechecks unconditionally.

## Branch Hygiene

Use `codex/<task-name>` branches for proof-progress work. Merge only verified
branches into `main`, then delete merged local branches and stale worktrees.
Do not delete dirty worktrees unless their work is intentionally discarded or
has been recovered elsewhere.
