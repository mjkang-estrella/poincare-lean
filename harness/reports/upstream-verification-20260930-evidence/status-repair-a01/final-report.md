# Status snapshot contract repair

Implemented at b7701374afd07122fdc5a813bd92b8b5b5176c50 on clean codex/completion-status-contract-a01 from
base a3b03ff7263b9d610de0a86d00a3a0f4b7f30794. This local Codex helper is not a
registered Pi Job. Root acceptance and the actual negative completion
checkpoint remain pending.

Changed only scripts/completion_audit.sh and
scripts/tests/test_completion_status_contract.py. The snapshot validator now
permits the exact achieved/0/proved and not-achieved/1/reserved-theorem-absent
combinations, with all eight scaffold summary statuses zero, unique contract
rows, and one matching completion sentinel. Inconsistent, missing and duplicate
rows/sentinels fail. Existing section-presence, audit-sentinel and current
Lean toolchain checks remain. Generation skip ignores old status content while
retaining file presence and every live mathematical gate.

The three snapshot failure strings filtered by write_status_summary.sh remain
unchanged. All script bytes outside the snapshot contract, after removing only
the obsolete unconditional incomplete-status line, are byte-identical to base.
Normalized SHA-256 is
3012f8a9f269e7725f73bc446964fb68a7226ecf46d503a916933e086a3c23c2.
No Lean files, root imports, targets, contracts, audit payloads, toolchain,
receipt/cache rules, services, worktrees or branches were changed.

Validation:
- Baseline fixture suite failed with 17 regression failures, including coherent
  achieved, duplicate rows/conflicting sentinels, and generation skip cases.
  Baseline 20 tests took 144.955 seconds with bundled ripgrep.
- Final required unittest suite passed 21 tests in 10.255 seconds. It prefers
  available ripgrep and separately exercises both coherent states with the
  bundled fallback.
- sh -n scripts/completion_audit.sh passed.
- git diff --check and git diff --cached --check passed.
- Final staged scope listed exactly the two allowed files.
- Structured source-only commit succeeded; final worktree status is clean.

All code source attempts, baseline failures, final test output, argv, exits,
timings, source preservation hashes, commit metadata and raw worker.patch are
retained in this directory. A snapshot-helper attempt incorrectly treated
Git diff's expected exit 1 as a Python error; that failure and the empty
artifact were retained, and a recorded replacement captured the complete diff.
Positive fixtures validate report consistency only. No fixture or passing
shell test verifies the Poincare theorem. No Lean or full build was run.

Out-of-scope historical gate still present at scripts/completion_audit.sh:154:
External research status must contain 'No complete Lean proof artifact was
found to import'. The current base document still contains the text at line
109. It may become outdated after upstream verification; this repair leaves
that requirement unchanged.

Exact first action for root: git show --stat --oneline b7701374afd07122fdc5a813bd92b8b5b5176c50
Then independently rerun the task acceptance commands and a fresh actual
negative completion checkpoint before deciding acceptance or integration.
