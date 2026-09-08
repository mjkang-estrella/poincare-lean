# Worker contract

You are an engineering worker on the Poincaré Lean project (toolchain leanprover/lean4:v4.30.0-rc2).
You work in an isolated git worktree (branch `worker/audit-payload-wiring`) with a cloned `.lake` cache.
Rules: never edit files under `Poincare/` or `Poincare.lean`; never add sorry/axiom; report the actual
results of every command; commit your work on the branch with descriptive messages; write your report
to `harness/reports/audit-payload-wiring_{done|blocked}.md`.

# Task: make the scaffold audits consume the cached Lean payload library

Read first: HANDOFF.md sections "2026-09-07 Validation refactor" (what was just changed and why),
README.md "Verification Ladder", `scripts/audit_payload_equivalence.py` (docstring and code),
`audit/PoincareAudit.lean` and the eight modules under `audit/PoincareAudit/`, `audit/PoincareAudit/Guard.lean`,
and `lakefile.lean` (the non-default `lean_lib PoincareAudit`). On this branch
`python3 scripts/audit_payload_equivalence.py --check` passes and `lake build PoincareAudit` succeeds
(35 s warm, 2 s no-op rebuild). No script uses the library yet.

Goal. The four Lean-heavy audits (`scripts/axiom_audit.sh`, `scripts/root_import_audit.sh`,
`scripts/semantic_surface_audit.sh`, `scripts/completion_audit.sh`) still write their `#check` /
`#print axioms` payloads from shell heredocs into temp files and elaborate them against `import Poincare`
on every run. Make them build the corresponding checked-in `PoincareAudit.*` modules instead
(`lake build PoincareAudit.Axiom.Footprint` etc., which Lake caches), remove the heredoc payloads from the
scripts, and keep every printed PASS/FAIL/MISSING/STALE/INFO/sentinel line and exit code identical.
Specifically:

1. Map each heredoc block to its module using the BLOCKS/MODULES tables in
   `scripts/audit_payload_equivalence.py`. Where the legacy block was elaborated with `lake env lean` and
   a PASS/FAIL line printed on its exit status, build the module and print the same lines; on failure
   print the Lake/Lean error output where the legacy script printed Lean output.
2. The axiom audit parsed `#print axioms` text. The library replaces that with `#std_axioms`, which errors
   on any nonstandard axiom or `sorryAx`. Map a build failure of `PoincareAudit.Axiom.Footprint` onto the
   legacy FAIL lines (`FAIL: proof-placeholder or final-theorem dependency found in axiom footprint` when the
   error mentions `sorryAx`, `_sorry`, `proof_wanted`, or `Poincare.poincare_conjecture`; otherwise
   `FAIL: nonstandard axiom footprint detected`), keeping the success sentinel unchanged.
3. Several coverage checks read the script's own text (`"$0"`) as the token universe, e.g. the semantic
   audit's `audit_surface_tokens`/`manual_check_tokens` and the completion audit's
   `collect_canonical_completion_certificate_routes` over the four scripts. Rework them to read the tokens
   from the checked-in Lean modules (`audit/PoincareAudit/**/*.lean`) so that the same declarations are
   covered and the same PASS/FAIL lines are printed. Do not weaken a check; if a check becomes tautological,
   say so in the report rather than deleting it silently.
4. The generated "parser-visible" and "explicit" check files (one `#check` per parser-visible declaration)
   may stay as generated temp files, or become a generated-then-compared module; choose the option that keeps
   exact semantics and document it.
5. Keep `scripts/audit_payload_equivalence.py --check` meaningful: after the heredocs are gone it must
   compare the modules against the legacy revision `LEGACY_REF` (it already reads that revision from git),
   so it keeps working. Delete `scripts/audit_legacy_extract.py` if nothing uses it (it references a driver
   that does not exist), or make it consistent; say which in the report.
6. Update README.md (Verification Ladder), AGENTS.md (verification section), and docs/PROJECT_MAP.md
   (Verification row) minimally to describe that the Lean payloads live in `audit/PoincareAudit` and are
   built by Lake. Add or adapt tests under `scripts/tests/` (`python3 -m unittest discover -s scripts/tests`
   must pass; `harness/v2/tests` runtime suite too).

Verification you must run and report verbatim: (a) old vs new on the same tree: copy the four scripts
from `main` into `scripts/old_<name>.sh` (they must live inside `scripts/` so they resolve the repository
root), run old and new with `PATH=$PWD/scripts/bin:$PATH` only if `rg` is missing, capture stdout and
exit codes, and diff the sorted result lines (PASS/FAIL/MISSING/STALE/INFO/sentinels) — they must be
identical; delete the `scripts/old_*.sh` copies before committing; (b) timings before/after for each of the
four audits and for `sh scripts/write_status_summary.sh` (it may overwrite CURRENT_STATUS.md; do not commit
that file); (c) fault injection in a scratch copy: rename one checked theorem in `Poincare/CanonicalBridges.lean`
(not a hash-pinned file) and show that the new audit fails with the corresponding FAIL line; revert.
If exact equivalence is impossible for a specific check, keep the legacy mechanism for that check and list
it in the report.
