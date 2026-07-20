# Poincare Lean Formalization

This is a Lean 4 project aimed at formalizing the Poincare conjecture. It is
large, actively developed, and **not a completed proof**.

The repository contains real theorem-bearing progress, conditional assembly
routes, explicit mathematical interfaces, and audits that prevent those
interfaces from being mistaken for the final theorem. The reserved endpoint
is:

```lean
Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement
```

That declaration is intentionally absent until Lean can check an
unconditional proof.

## Start Here

Read these files in order:

1. [HANDOFF.md](HANDOFF.md) — the dated state being handed to the next agent.
2. [docs/PROJECT_MAP.md](docs/PROJECT_MAP.md) — how the proof and support
   surfaces fit together.
3. [AGENTS.md](AGENTS.md) — the working and verification contract for agents.
4. [harness/README.md](harness/README.md) — the legacy history and the
   executable Codex/Pi/Leanstral Harness v2.
5. [CURRENT_STATUS.md](CURRENT_STATUS.md) — the latest generated full audit
   snapshot. Check its timestamp before treating it as current.

`RESEARCHER_VERIFICATION.md` and the other long reports are evidence archives,
not the fastest entry point.

## Repository at a Glance

- `Poincare.lean` is the root import surface. Its successful elaboration means
  the imported graph is coherent; it does not mean the conjecture is proved.
- `Poincare/Statement.lean` defines the canonical target statement.
- `Poincare/FullAssembly.lean`, `Poincare/Dependencies.lean`, and
  `Poincare/CompletionTarget.lean` expose conditional end-to-end routes and
  their remaining dependency boundary.
- `Poincare/Global/` contains the main theorem-bearing geometric, analytic,
  Ricci-flow, and global-recognition work.
- `Poincare/ProofProgress/` contains older package-oriented proof progress and
  reviewer ledgers. It is useful context but is not automatically the active
  frontier.
- `scripts/` contains the verification and completion audits.
- `harness/` contains the first-generation task history plus the executable v2
  Task/Job control plane, bounded Pi `0.80.10` Job adapter, deployment
  launcher, and restart-safe runbook.

## Truth Hierarchy

When two surfaces disagree, use this order:

1. Lean elaboration of the exact changed module or target declaration.
2. The current git diff and commit graph.
3. Live audit output from `scripts/`.
4. A freshly generated `CURRENT_STATUS.md`.
5. Harness ledgers, reports, and prose notes.

The lower surfaces explain history. They do not override the compiler.

## Verification Ladder

For one bounded proof task:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Path/ChangedFile.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Path/ChangedFile.lean
git diff --check
```

For root integration:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare.lean
sh scripts/interface_audit.sh
sh scripts/semantic_surface_audit.sh
sh scripts/theorem_contract_audit.sh
sh scripts/root_import_audit.sh
sh scripts/axiom_audit.sh
git diff --check
```

Run `lake build`, `scripts/completion_audit.sh`, or
`scripts/write_status_summary.sh` for an integration checkpoint, not for every
small worker attempt. The completion audit is expected to exit nonzero while
the reserved theorem is absent.

## Proof Work Rules

- Reduce one explicit mathematical or Lean interface with proof-bearing code.
- Do not claim completion from a green build, a larger import graph, an alias,
  a package constructor, or a passing non-completion audit.
- Do not add `sorry`, `admit`, new axioms, `native_decide`, vacuous certificate
  fields, or alternate declarations of the final target.
- Use a dedicated `codex/<task-name>` branch or isolated worktree.
- Preserve dirty or unmerged worktrees until their proof work is understood.

The immediate handoff and harness rollout are described in
[HANDOFF.md](HANDOFF.md) and [harness/v2/SPEC.md](harness/v2/SPEC.md).

The execution boundary is deliberately narrow:

```text
Codex -> Harness v2 Task/Job control plane -> fresh bounded Pi 0.80.10 Job -> Leanstral
```

Codex alone chooses Tasks, allocates isolated worktrees, independently reruns
Lean gates, accepts results, and commits verified progress. Pi gives Leanstral
only the six scoped Job tools documented in the v2 specification; it is not a
second project orchestrator. Model-requested Lean checks run without network
inside a deny-by-default Bubblewrap namespace over a read-only sparse source
tree and a read-only, commit-keyed Lake cache whose publisher provenance has
been independently recorded and validated. `mj-zima` emits durable evidence
immediately and every 10,800 seconds for the long-running Harness. The setup
thread on this Mac ends after deployment verification and one final handoff;
future evidence can be inspected from the Mac on demand.
