Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-42: the exp charts are C² — the augmented flow's C¹ concretely

Context: `harness/reports/M5-glob-41_blocked.md` (READ FIRST — the VERBATIM chart-side C² demands: `eS` target exp chart and `eM.symm` source inverse). PROVEN: the composition assembly (`ContDiffTwo.lean`). THE CONCRETE ANALYSIS: (1) THE EXP CHART IS C²: the exp chart = the fixed-time flow map of the geodesic ODE; its C¹ = the flow derivative (PROVEN — `GeodesicFlowDerivative/ExponentialStrictClose`); its C² = the AUGMENTED flow's C¹ — REPLAY the first-order dependence chain at the augmented system (`SecondVariation.lean`'s field; the chain: Lipschitz dependence `GeodesicDependence` pattern → uniform remainders `GeodesicDerivative` pattern → the flow derivative `GeodesicFlowDerivative` pattern — the proofs are structural; the augmented field is C¹-with-bounded-derivatives on the compact tube since Γ is smooth) ⟹ the derivative field of the exp chart is C¹ ⟹ `ContDiffAt 2` via `contDiffAt_succ_iff_hasFDerivAt`; (2) THE INVERSE IS C²: the inverse of a C² map with invertible derivative is C² (the inverse function theorem's regularity — Mathlib's `PartialHomeomorph.contDiffAt_symm`/`HasStrictFDerivAt.to_localInverse` C^n versions — the exp homeo + the C² from (1) + the invertible derivative (proven)); (3) the sphere side identically. FEED `ContDiffTwo`'s assembly → `EndpointBridge` → 🎯 THE F-TRANSITION LAW. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-42_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ExpChartC2.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ExpChartC2` and report the actual result. Commit your work.
