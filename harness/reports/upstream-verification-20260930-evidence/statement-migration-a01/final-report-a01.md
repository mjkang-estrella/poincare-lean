# Statement 4.33 migration candidate

Candidate commit: `1d94e7669e9b37513385d66cbf14024db097de74`.
Branch: `codex/statement-433-migration-a01`.
Base: `a3b03ff7263b9d610de0a86d00a3a0f4b7f30794`.
Only committed file: `Poincare/Statement.lean`. Worktree is clean.

## Verification

Exact acceptance command passed with exit 0 in 68.3235 seconds:
`LEAN_NUM_THREADS=1 lake env lean /Users/mjkang/.codex/worktrees/statement-433-migration/poincare/Poincare/Statement.lean`

Compiler cwd is `/Users/mjkang/.codex/external-reviews/poincare-20260930/dg-v013-verification`.
Lean is 4.33.1, Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`.
The raw forbidden-term scan, nested-comment/string-aware scan and `git diff --check` pass.
No full build, root integration check or root audit was run by this helper.

The corrected diagnostic counts are 236, 212, 70, 27, 3, 0 for attempts 000 through 005. Both attempt 005 and acceptance 006 exit 0. Complete sources, argv, environment, logs, exit codes, timings and diffs are preserved for every scoped compilation.

## Interface preservation

The declaration-name scan finds the same 1498 names as the base. `ThreeSphere` and `PoincareConjectureStatement` source spans are byte-identical to the base; hashes are in `final-source-review-a01.json`. No theorem hypotheses, quantifiers, type/data constructors or computational fields were edited. No new declarations, assumptions, forbidden placeholders or final theorem were added.

Four existing diffeomorphism definitions change only `contMDiff_toFun` Prop proofs, replacing destructive instance simplification with the actual open-embedding theorem. Their `toEquiv` computational data remains unchanged. Six equality-theorem types contain modified embedded Prop proof terms; they are itemized in `final-source-review-a01.json` for independent comparison modulo proof irrelevance.

The file-level `backward.isDefEq.respectTransparency false` option restores earlier elaborator behavior while preserving kernel checking. Explicit Fin reductions, path maps/casts, preimages and subpath normalization resolve the remaining proof mismatches. Mathlib API names are updated only inside proofs. Exactly 118 compiler-confirmed redundant tactics were removed. Itemized edit records are `change-record-001.json` through `change-record-006.json`.

## Next action

The orchestrator independently compiles and reviews the candidate against the recorded base and checks type/data preservation. Integrate only into the separately reviewed 4.33 migration. This result is a statement-layer compatibility prerequisite, not a proof-completion claim.
