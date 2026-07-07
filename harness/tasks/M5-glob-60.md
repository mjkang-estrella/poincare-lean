Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-60: the hosted CLM and the continuity package — final packaging

Context: `harness/reports/M5-glob-59_blocked.md` (READ FIRST — the VERBATIM demands: the hosted third-variation endpoint CLM `D` + the source/target canonical endpoint-continuity packages). PROVEN: the endpoint derivatives at both levels with the eventual residual bridge (`TransitionLands.lean`); the Grönwall bound (`OmegaGronwall.lean`); the CLM construction pattern (`SecondFrechet.lean` — linearity by uniqueness + finite-dim). THE PACKAGING: (1) THE CLM `D`: the third-variation endpoint map is linear in its perturbation slot (the linear system — the `SecondFrechet` uniqueness pattern at level three) + finite-dim ⟹ the CLM; its defining lemma; (2) THE CONTINUITY PACKAGE: `q ↦ D_q` continuous — the Grönwall bound IS the Lipschitz estimate (`OmegaGronwall`'s `‖D₂ − D₁‖ ≤ C·δ` — convert to `Continuous/ContinuousAt`); (3) assemble the canonical endpoint-continuity packages (source + target — the sphere identically) in `EndpointContinuity.lean`'s exact demanded shapes. FEED → the bridge chain → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-60_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/HostedCLM.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.HostedCLM` and report the actual result. Commit your work.
