Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-64: the two connectors — Ξ selector and the Ω-to-CLM bridge

Context: `harness/reports/M5-glob-63_blocked.md` (READ FIRST — the VERBATIM two connectors). PROVEN: the selectors ζ/Ω/D with specs + the conditional Grönwall transfer (`TheSelector.lean`). THE CONNECTORS: (1) THE Ξ_q SELECTOR: the neighborhood-indexed SECOND-variation family at `q` — the per-point existential EXISTS (`SecondVariation.lean`'s PL package + the `LinearizedFamilyExport/LinearizedRescale` construction pattern at each hosted `q` — or `TheSelector`'s own ζ pattern applied to the second-variation system) — select it and export the specs feeding ζ's construction; (2) THE Ω-TO-CLM BRIDGE: `OmegaGronwall`'s local Ω satisfies `HostedCLM.exists_hostedCLMPackage`'s hypotheses — CHECK the hypothesis gap (the report says "all-perturbation" vs local: the CLM package quantifies over all perturbations `w`; Ω's family covers the PL ball — RESCALE by linearity to all `w` (the `LinearizedRescale/BoundedPackage` homogeneous-extension pattern — the third-variation system is linear in its perturbation slot)). ASSEMBLE both → `TheSelector`'s transfer fires unconditionally → the indexed packages → `IndexedSelection`'s consumer → 🎯 THE F-TRANSITION LAW. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-64_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TwoConnectors.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TwoConnectors` and report the actual result. Commit your work.
