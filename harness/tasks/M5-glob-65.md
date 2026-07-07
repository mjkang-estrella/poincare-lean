Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-65: the Ω rescale — solutions replace centered PL, level three

Context: `harness/reports/M5-glob-64_blocked.md` (READ FIRST — the VERBATIM Ω-to-CLM gap: PL-ball-local Ω vs all-perturbation uniform hypotheses). PROVEN: Ξ selected (`TwoConnectors.lean`); Ω on the ball (`OmegaGronwall/TheSelector.lean`); THE DISSOLUTION PATTERN (rigid-85's `SolutionsFeed.lean` — READ IT: centered PL demands dissolved by SOLUTION ADDITIVITY of the linear system). REPLAY AT LEVEL THREE: the third-variation system is LINEAR in its perturbation slot — (1) additivity/homogeneity of Ω's solutions (`linearODE` uniqueness — the `LinearizedAdditivity/LinearizedRescale` pattern); (2) the all-perturbation family from the ball family by rescaling (`w = ‖w‖·ŵ` — the homogeneous extension); (3) the membership/centered fields from the individual ones (triangle inequality — the rigid-85 enlargement); (4) feed `HostedCLM.exists_hostedCLMPackage` with the rescaled family → the CLM package at every hosted `q` → `TheSelector`'s D-selector unconditional → the transfer → `IndexedSelection` → 🎯 THE F-TRANSITION LAW. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-65_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/OmegaRescale.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.OmegaRescale` and report the actual result. Commit your work.
