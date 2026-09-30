# Chart-geodesic Lean 4.33 compatibility Job

Status: ready for orchestrator review. No merge or task acceptance performed.

Base: `20cdd2f6d589da622d492efb509b3666ab00f8ac`.
Commit: `8159987d5047a98cea00ca1baeb0081979126405`.
Branch: `codex/geodesic-433-a01`.
Cwd: `/Users/mjkang/.codex/worktrees/geodesic-433/poincare`.

The scoped change adds the minimal `Mathlib.Analysis.ODE.ExistUnique` import, which exposes the original moved local-existence and eventual-uniqueness APIs. The regularity proof explicitly changes its goal to the unchanged flow-field formula and applies the existing product regularity proof directly. No hypotheses, public declaration types, universes, flow dynamics, or conditional results changed.

Attempt 01 passes every frozen gate. Its source, diff, exact argv/cwd/base SHA, outputs, exit statuses and phase timings are preserved under `attempt-01`.

Passed gates:

- Scoped Lean elaboration, exit 0.
- `lake build Poincare.Global.GeodesicChart`, exit 0.
- `FrozenMigrationProbe-a02.lean`, exit 0. All twelve exact original declaration types/universe arities pass. Every named declaration's dependency closure passes safe/total and allowed-foundational-axiom checks.
- Scope guard, exit 0: `PRESERVED_GEODESIC_TYPES_AND_FLOW_DATA`.
- Scoped forbidden-token scan, exit 1 with no matches.
- `git diff --check`, exit 0.

Final worktree is clean. Final source bytes equal the successful attempt snapshot. The commit changes one file with 3 insertions and 1 deletion, confined to one added Mathlib import and one existing proof body.

The original local solution/uniqueness and coordinate-component results remain available to GeodesicTransport. This compatibility migration supports retaining the historical root during credited upstream endpoint integration. It does not independently discharge Hamilton or smoothing cores, certify a full root build, or establish the reserved final theorem.

Next action: the orchestrator independently replays this commit from the recorded base and reruns the frozen acceptance gate before deciding acceptance or integration.
