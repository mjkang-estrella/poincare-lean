# Audit payload wiring worker report

Date: 2026-09-08 UTC.
Branch: `worker/audit-payload-wiring`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.
Base: `7acd90a813f558787ddf8de15f7b7b1d1ae75ff1`.
Legacy script copies came from `main` at `aa82826aec916ad9339e2da1049f80009cdf2c7a` and matched all four scripts at the worker base byte for byte.

The engineering task is complete for orchestrator review. No merge or task acceptance was performed. No file under `Poincare/` or `Poincare.lean` was changed in this worktree. The conjecture remains unproved.

## Changes

The four scripts build the checked-in payloads with Lake, capture build output, and print the existing decision lines. Successful builds do not replay Lake output into audit stdout. Failed builds print the captured Lake/Lean diagnostics at the original decision point.

| Legacy block | Lake module |
| --- | --- |
| `axiom.main`, then `axiom.routes` | `PoincareAudit.Axiom.Footprint` |
| `root.main` | `PoincareAudit.Root.Contracts` |
| `semantic.main` | `PoincareAudit.Semantic.Surface` |
| `semantic.routes` | `PoincareAudit.Semantic.CertificateRoutes` |
| `completion.root` | `PoincareAudit.Completion.RootContract` |
| `completion.dependency` | `PoincareAudit.Completion.DependencyContract` |
| `completion.routes` | `PoincareAudit.Completion.CertificateRoutes` |

The completion route module is required alongside each of the three probes that formerly appended that heredoc: generated parser checks, root contract, and dependency contract. Its tokens remain in the explicit-check token union.

A failed footprint build maps to `FAIL: proof-placeholder or final-theorem dependency found in axiom footprint` if diagnostics match `sorryAx`, `_sorry`, `proof_wanted`, or the exact reserved name `Poincare.poincare_conjecture`; otherwise it maps to `FAIL: nonstandard axiom footprint detected`, as requested. This replaces the old generic elaboration-failure category. The mathlib proof-wanted dependency guard and success sentinel remain unchanged.

Semantic coverage reads `audit/PoincareAudit/Semantic/*.lean`. Canonical public-route coverage reads each audit's own module group separately. Each group retains exactly 1,175 canonical route names. The old semantic manual token universe contains 19,607 names; two existed only in shell comments. They now remain comments in `Semantic/Surface.lean`:

- `Poincare.mfderivWithin_extChartAt_symm_target_eq_range`
- `Poincare.mfderivWithin_extChartAt_symm_target_eq_range_eq`

These markers retain their old stale-name coverage role; they were not silently promoted to new Lean checks. The equivalence checker now verifies their token universe against the archived revision too. Duplicate shell comment copies were removed.

`scripts/audit_payload_equivalence.py --check` still reads `LEGACY_REF=b2b96fc28248c2a72cb2e08b4fda946d3b26e6d5` through Git. All 83,887 `#check` commands and 10,210 axiom probes match the legacy ordered payloads and headers. Its writer now places imports before module documentation, so regeneration retains the valid Lean layout. The unused `scripts/audit_legacy_extract.py` was deleted after a repository-wide reference search found no consumers. Stale references to its nonexistent driver were corrected.

README's Verification Ladder, AGENTS' verification section, and the project-map Verification row now describe the cached library.

## Live mechanisms retained

The semantic parser-visible file and completion explicit file remain generated temporary Lean files and are elaborated on every run. Completion combines its generated tokens with the cached certificate-route module tokens, preserving the legacy union exactly. Their generated-token containment/equality checks were already true by construction; they remain as generator consistency checks, with the live Lean elaborations providing the actual declaration-resolution check. No independent module/source coverage check was replaced by a self-comparison or deleted.

The reserved endpoint remains a live `lake env lean` probe with exactly the legacy source, now emitted with `printf` instead of a heredoc. It is expected to fail until the theorem exists, so it cannot be a successful cached scaffold target. The conditional final-theorem axiom probe is unchanged. No other check required a legacy fallback.

## Same-tree output and timing evidence

Audit processes ran sequentially against the same proof sources and cloned warm `.lake` cache. The runtime tests and staged Python tests ran during baseline completion; the final Python suite ran during the after status capture. These are single workstation timing samples, not isolated benchmark medians. Native `rg` was available at `/opt/homebrew/Caskroom/codex/0.153.2/codex-path/rg`; the audit measurements did not prepend the fallback PATH. The runner prepends `$PWD/scripts/bin` only if `rg` is missing.

Before editing the audit scripts, the four `main` versions were copied into `scripts/old_<name>.sh` using:

```python
for name in ['axiom_audit', 'root_import_audit', 'semantic_surface_audit', 'completion_audit']:
    Path(f'scripts/old_{name}.sh').write_bytes(
        subprocess.check_output(['git', 'show', f'main:scripts/{name}.sh']))
```

Both old and new completion runs used the matching version of all their nested gates. The original `CURRENT_STATUS.md` was restored before the new measurements, so the snapshot checks saw the same input. All temporary old-script copies were deleted after comparison, and the original status file was restored again before committing.

The exact measurement commands were:

```sh
python3 /private/tmp/audit-payload-wiring-evidence/run.py before
python3 /private/tmp/audit-payload-wiring-evidence/run.py after
python3 /private/tmp/audit-payload-wiring-evidence/run.py after completion_audit
python3 /private/tmp/audit-payload-wiring-evidence/compare.py
```

`run.py before` invoked `sh scripts/old_axiom_audit.sh`, `sh scripts/old_root_import_audit.sh`, `sh scripts/old_semantic_surface_audit.sh`, `sh scripts/old_completion_audit.sh`, then `sh scripts/write_status_summary.sh`. `run.py after` invoked the four normal script paths, then the same status command. Both runners exited 0 after recording the individual command statuses below.

| Command | Before | After | Exit before / after |
| --- | ---: | ---: | ---: |
| `sh scripts/axiom_audit.sh` | 62.310 s | 41.111 s | 0 / 0 |
| `sh scripts/root_import_audit.sh` | 70.452 s | 46.517 s | 0 / 0 |
| `sh scripts/semantic_surface_audit.sh` | 85.254 s | 42.403 s | 0 / 0 |
| `sh scripts/completion_audit.sh` | 445.330 s | 298.168 s | 1 / 1 |
| `sh scripts/write_status_summary.sh` | 448.222 s | 296.975 s | 0 / 0 |

The payload cache was warmed separately with `lake build PoincareAudit`: 25.995 s, exit 0. A second identical command took 1.521 s, exit 0. These setup builds are excluded from the after audit timings.

Stdout and stderr were captured separately. The comparison sorted every PASS/FAIL/MISSING/STALE/INFO line, every uppercase sentinel including GAP/AXIOMS/SEMANTIC SURFACE, and all `==` headers. It then ran `diff -u` for each before/after `.results` pair and compared the captured exit codes. All diffs were empty:

| Audit | Compared lines, including headers | `diff -u` exit |
| --- | ---: | ---: |
| `axiom_audit` | 112 | 0 |
| `root_import_audit` | 979 | 0 |
| `semantic_surface_audit` | 124 | 0 |
| `completion_audit` | 13397 | 0 |

The first new completion attempt exposed an overly broad token regex: it read the comment `-- Explicit whole-surface declaration #check coverage.` as a check of `coverage`, producing an extra FAIL and `STALE: coverage`. The scanner now requires a line-start check command with an optional guard prefix. The regression test executes the actual shell pipeline and verifies that comment text contributes no token. That attempt's stdout, stderr, timing, and result lines remain in the evidence archive under `after-completion_audit-initial.*`.

The status run had not started its completion gate when this was corrected and therefore used the final scanner. The affected standalone completion measurement was repeated after the status run, with the original status snapshot restored first. The table and comparison above use that final measurement.

The old and final new standalone completion runs returned 1 with exactly these FAIL lines:

```text
FAIL: local reserved theorem name poincare_conjecture is absent
FAIL: Lean cannot confirm Poincare.poincare_conjecture : PoincareConjectureStatement
```

Both generated status snapshots record scaffold gates at 0, completion at 1, and `reserved theorem absent only`. Their bodies differ where the axiom audit no longer prints raw axiom listings; the audited result lines and sentinels match.

## Tests and Lean checks

Commands and actual results:

```text
python3 scripts/audit_payload_equivalence.py --check
exit 0; all seven payload modules, semantic manual markers, and legacy reserved probe match

python3 -m unittest discover -s scripts/tests
initial exit 1: 55 tests, one existing native-ripgrep output-order comparison failure
final exit 0: 55 tests in 12.986s, OK

python3 -m unittest discover -s harness/v2/tests
exit 0: 66 tests in 25.277s, OK

LEAN_NUM_THREADS=1 lake env lean audit/PoincareAudit/Guard.lean
exit 0

LEAN_NUM_THREADS=1 lake env lean audit/PoincareAudit/Semantic/Surface.lean
exit 0

lake build PoincareAudit
exit 0, twice

sh -n scripts/axiom_audit.sh
sh -n scripts/root_import_audit.sh
sh -n scripts/semantic_surface_audit.sh
sh -n scripts/completion_audit.sh
exit 0 each

rg -n '\b(sorry|admit|axiom)\b|native_decide' audit/PoincareAudit/Guard.lean audit/PoincareAudit/Semantic/Surface.lean
exit 0: five matches, all pre-existing prose or the guard's error string containing "axiom"; no forbidden declaration or proof placeholder added

git diff --check
exit 0

git diff --exit-code HEAD -- Poincare Poincare.lean
exit 0, empty diff

git diff --exit-code HEAD -- CURRENT_STATUS.md
exit 0, empty diff
```

The initial version of the new 10-test suite passed against staged script copies before installation. The final suite includes the corrected exact-pipeline regression above. It exercises ordered payload/ascription loss, regeneration layout, the comment-only marker, exact per-audit route universes, semantic declaration coverage, explicit route-token preservation, missing public-root exposure, and both axiom error categories. The existing ripgrep reference test now uses native `rg --sort path` because parallel file completion order is unspecified; match content and per-file ordering are still compared exactly. No production fallback behavior changed.

Baseline and current build output includes replayed `LibrarySuggestions` panic diagnostics while Lake reports successful builds. Their full logs and exit statuses are preserved. A read-only search also reported missing `harness/v2/README.md` with exit 2, and process inspection with `ps` was denied by the sandbox. Neither was an acceptance gate; subsequent checks used the existing SPEC and captured gate logs. Review-only `diff -u` commands returned 1 as expected when inspecting changed shell control flow.

## Scratch fault injection

Executed verbatim:

```sh
python3 /private/tmp/audit-payload-wiring-evidence/fault.py
```

The driver exited 0 after the expected failure and successful recovery. It archived the worker base into `/private/tmp/audit-payload-wiring-fault`, overlaid the new audit implementation, and cloned `.lake` with `cp -cR`. It renamed only the declaration `canonical_statement_payload_iff_aggregate_canonical_statement_payload_eq` to `canonical_statement_payload_iff_aggregate_canonical_statement_payload_eq_audit_fault` in the scratch `Poincare/CanonicalBridges.lean`.

From that scratch root, `sh scripts/root_import_audit.sh` returned 1 after 185.545 s. Lake invalidated the cached dependency and reported the missing checked identifier. The audit printed:

```text
FAIL: Poincare root does not expose canonical target contracts, canonical assembly bridges, and projection assembly
```

The driver restored the exact original bytes in a `finally` block, then ran `lake build PoincareAudit.Root.Contracts`: exit 0 in 129.661 s. The worker's proof sources were never edited.

## Evidence and next action

[Evidence archive](audit-payload-wiring_evidence.tar.gz) contains command drivers, stdout/stderr, exit/timing JSON, sorted result lines, empty equivalence diffs, the initial test failure and completion-token regression, fault diagnostics, restored-build output, both generated status snapshots, and the implementation diff. The unpacked evidence is also at `/private/tmp/audit-payload-wiring-evidence`.

Exact first action for the orchestrator: review this branch's diff from `7acd90a813f558787ddf8de15f7b7b1d1ae75ff1`, then independently run `python3 scripts/audit_payload_equivalence.py --check` before the integration gates. This report records worker verification, not acceptance or proof completion.
