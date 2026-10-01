# Complex Gaussian limit Lean 4.33 compatibility Job

Status: ready for orchestrator review. No merge or task acceptance performed.

Base: `88f9d463817418be93153be8a137570854b9dad4`.
Commit: `d8505155870d41803f39c728019ed4cd9f180c17`.
Branch: `codex/heat-integral-433-a01`.
Cwd: `/Users/mjkang/.codex/worktrees/heat-integral-433/poincare`.

The change is a single added exclamation mark in the `gaussianApproxIdentity_heatTimeScale_complex` proof: `simpa only [Function.comp_apply] using!`. This uses expected-type elaboration for the existing composition of the Fourier-normalized Gaussian approximate-identity theorem with the heat-time scale. No mathematical formula, import, definition, hypothesis, measure, norm, time domain or neighboring proof changed.

Attempt 01 passes every frozen gate. Its source, diff, exact argv/cwd/base SHA, outputs, exit statuses and phase timings are preserved under `attempt-01`.

Passed gates:

- Scoped Lean elaboration, exit 0.
- `lake build Poincare.Global.HeatKernelIntegral`, exit 0.
- `FrozenMigrationProbe-a02.lean`, exit 0. All eight exact original declaration types/universe arities pass. Every named declaration's dependency closure passes safe/total and allowed-foundational-axiom checks.
- Whole-file byte guard, exit 0: `PRESERVED_HEAT_INTEGRAL_DATA_AND_OTHER_PROOFS`.
- Scoped forbidden-token scan, exit 1 with no matches.
- `git diff --check`, exit 0.

Final worktree is clean. Final source bytes equal the successful attempt snapshot. The commit changes one line in one allowed proof body, with every surrounding source byte preserved.

This restores the original complex approximate-identity API used by Gaussian/Fourier consumers. It does not identify the complex normalization with the real heatSolution formula, prove real heatSolution initial-data recovery, discharge independent Hamilton inputs, certify the retained full root, or establish the reserved final theorem. The already-discharged smoothability core is unchanged.

Next action: the orchestrator independently replays this commit from the recorded base and reruns the frozen acceptance gate before deciding acceptance or integration.
