# HeatKernelPDE Lean 4.33 proof repair worker report

Commit: `6bb85b1f72d2cf603cae7f97f2d106b9fc558c6f`
Base: `88f9d463817418be93153be8a137570854b9dad4`
Branch: `codex/heat-pde-433-a01`
Changed file: `Poincare/Global/HeatKernelPDE.lean` only. Seven insertions/seven deletions. Working tree clean.

## Outcome

Three convert steps use convert!, and four failing simpa steps use using!, so ordinary elaboration unfolds definitionally equal real scalar/group/module instances instead of leaving irrelevant instance-equality goals. The existing algebraic derivations and private derivative certificates are retained. No elaborator option, data definition, header, hypothesis, instance, norm, time domain, dimension parameter or import changes.

All14 public/private declaration headers are byte-identical. The complete heatKernelReal Gaussian definition is byte-identical. Imported HeatKernel.lean, toolchain, manifest and reviewed definitions have their unchanged sealed hashes. The time derivative remains for arbitrary finite-dimensional real inner-product spaces at positive time, including dimension zero; the closed second-spatial-derivative/Laplacian PDE remains on the real line at positive time. No time-zero extension or arbitrary-manifold flow claim was introduced.

## Exact worker gates

- `env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelPDE.lean`: exit0,16.719354s, attempt-01-lean.
- `env LEAN_NUM_THREADS=1 lake build Poincare.Global.HeatKernelPDE`: exit0,16.341119s, gate-02-scoped-build. Explicit scoped target only.
- `env LEAN_NUM_THREADS=1 lake env lean harness/v2/state/upstream-verification-20260930/heat-pde-433-task-a01/FrozenMigrationProbe.lean`: exit0,10.760419s. All seven FROZEN_CONTRACT_OK and seven AXIOM_CONTRACT_OK markers validated against the immutable Task list. Exact public types/universe arities and whole-dependency unsafe/partial/allowed-axiom checks pass, including the computational Gaussian declaration.
- Exact `python3 .../check-scope.py`: exit0 with PRESERVED_HEAT_PDE_TYPES_AND_GAUSSIAN_DATA.
- Exact scoped forbidden-token scan: exit1, no matches.
- `git diff --check`: exit0.

Every gate and the committed source bind SHA256 `888f20603ac61654678f2e7c54b6adf821e5ef81db39fde46fb1fa82672877e7`. The original recorded failed compiler output, original/final source, immutable Task/context hashes, candidate/committed diffs and every exact cwd/argv/environment override/exit/timing/log are preserved append-only. One proof attempt sufficed and produced no diagnostics. Pinned contexts were checked unchanged before and after gates.

## Boundary and first action

These are the actual existing scalar Gaussian calculus identities used by heat/fundamental-solution consumers. They enable retained full-root compatibility; core S stays discharged and no independent Hamilton input or convergence construction is added here. No full build, helper agent, service operation, outside-scope edit, merge or Task acceptance occurred.

Root's exact first action: independently rerun the frozen Task acceptance commands against this scoped commit, then choose serial integration. Full retained-root and exact final completion audits remain the orchestrator's responsibility.
