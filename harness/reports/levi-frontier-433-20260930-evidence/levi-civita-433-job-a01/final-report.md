# Levi-Civita derivative migration Job a01

Worker gates passed; independent orchestrator acceptance is pending. Base `88f9d463817418be93153be8a137570854b9dad4`, result `495edaec9af03eee3fdc789393a66206f3525d04`, branch `codex/levi-civita-433-a01`.

Only the six reviewed `extDerivFun (fun ...)` to `mvfderiv I (fun ...)` call-site substitutions were applied in `Poincare/LeviCivitaUniqueness.lean`. Original I, scalar codomain, bilinear-form/connection data, hypotheses, norms and tangent families remain unchanged. The sealed source guard proves every other byte, including TorsionFreeAt and all three uniqueness/Koszul proof bodies, is preserved. No successor proof-body scope was needed: direct Lean passed on the first candidate.

`scope-a01`, `lean-a01`, `build-a01`, `frozen-probe-a01`, and `diff-check-a01` record exit 0. The build target was only `Poincare.LeviCivitaUniqueness`; no full build ran. The sealed NormalizedFrozenProbe-a02 passed all ten unapplied original interface types at rigid universes, rejected unresolved metavariables, and passed all ten transitive allowed-axiom/unsafe/partial checks. `token-scan-a01` records exit 1 with empty output, the expected no-match result. Existing deprecated CLM proof API warnings remain untouched.

Each invocation directory preserves source, diff, argv, cwd, timestamps, stdout, stderr and exit. The sealed Task and final source/diff/gate summary are also included. Original/current common-derivative-formula rfl evidence and original ten-type serialization evidence remain in their prior append-only Task artifacts.

This is retained-root compiler compatibility for existing supplied-data uniqueness and Koszul assertions. It constructs no new connection or original Hamilton/core existence result. The final endpoint and full root/completion acceptance remain the orchestrator's responsibility. No merge, push or task acceptance was performed.

Exact first root action: independently inspect the `88f9d463..495edaec9af03eee3fdc789393a66206f3525d04` six-line substitution diff and rerun the sealed six-command Task gate against this candidate and unchanged context before integration. Preserve every original root import and the canonical target.
