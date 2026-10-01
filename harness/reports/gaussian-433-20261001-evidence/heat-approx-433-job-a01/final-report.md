# Worker result

Task heat-approx-433-preserve revision1 completed its worker gates at base 681e24e8fedf59c21b71747e90835567dc790e43.
Commit ee6da76072f638d189fe6680cd78d320b8542b58 is on codex/heat-approx-433-a01 in /Users/mjkang/.codex/worktrees/heat-approx-433/poincare. The committed worktree is clean.
No acceptance, merge, main edit, root audit, or full build was performed.

## Change

Only HeatApproxIdentity.lean line129 changed. The final proof now uses
`simpa only [Function.comp_def, Complex.ofReal_re] using hreal`.
Function.comp_def exposes the bare composed map in the Tendsto proof as a lambda;
Complex.ofReal_re then reduces its real-valued projection pointwise.
The original complex approximate-identity seed, positive-time eventual equality,
integrable premise and pointwise continuity premise remain used and unchanged.
All public/private headers, other proofs, imports, Gaussian data, canonical volume,
norm, dimension and source/target filters are unchanged under the byte guard.

## Verification

- Fresh direct Lean exit0, candidate-a02-lean result,28.775s.
- Scoped `lake build Poincare.Global.HeatApproxIdentity` exit0,11.896s.
- FrozenMigrationProbe exit0 with three exact type/universe markers and three
  allowed-axiom/transitive unsafe-or-partial markers,6.764s.
- Whole surrounding-source guard exit0.
- Exact token scan exit1 with empty stdout/stderr, which is the no-hit pass.
- `git diff --check` exit0.
- Pinned definition/config/readback hashes all match.
- Only the allowed source path changed; added-token scan also excludes postulate.

## Preserved failed evidence

baseline-lean.stdout/result reproduce the original line129 composition failure.
candidate-a01-lean.stdout/result and candidate-a01-diff.stdout preserve the
first comp_apply candidate. That applied-composition rule did not rewrite the
bare function stored in Tendsto. The final comp_def refinement passed.
worker.patch and candidate-a02.lean preserve final exact source and diff.

## Boundary and next action

This preserves the existing Euclidean real initial-data limit on Lean4.33.
It does not construct an independent universal Hamilton flow or limit.
The next exact action is an independent orchestrator rerun of the frozen Task
commands from base 681e24e8fedf59c21b71747e90835567dc790e43, review of worker.patch, then serial
integration if accepted. Root and final completion verification remain pending.
