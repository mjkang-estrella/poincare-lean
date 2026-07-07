Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-66: centered membership — the CLM package fed

Context: `harness/reports/M5-glob-65_done.md` (READ FIRST — the remaining `HostedCLM` centered-membership boundary VERBATIM). PROVEN: the all-perturbation rescaled Ω with initial values, the linear ODE, additivity, homogeneity (`OmegaRescale.lean`). THE MEMBERSHIP: `HostedCLM.exists_hostedCLMPackage`'s centered-membership fields for the rescaled family — the rigid-85 enlargement: the ball family's membership + the rescaling factor bound the rescaled solutions' membership in an ENLARGED ball (triangle inequality + the homogeneity scaling of norms — `‖c·Ω_ŵ(t)‖ = |c|·‖Ω_ŵ(t)‖ ≤ |c|·radius`; choose the enlarged radius; if `HostedCLM` demands a FIXED radius, check whether its proof accepts any radius (parameterized) or add the additive variant accepting the scaled radius). FEED → the CLM package at every hosted `q` → `TheSelector`'s D unconditional + the transfer → the indexed packages → `IndexedSelection/ContinuityPackages`' consumers → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-66_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/CenteredMembership.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.CenteredMembership` and report the actual result. Commit your work.
