Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-104: instantiate the sin² pullbacks — THE THEOREM

Context: `harness/reports/M5-rigid-103_done.md` (READ FIRST). PROVEN: `exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pullbacks` (`ScaledUpgrade.lean` — equivalences + the consumer, GIVEN the sin²-scaled hosted anchor pullbacks with `θ ∈ Ioo 0 π`). THE LAST INSTANTIATION: the sin²-scaled pullback identities at the selector's datum — the corrected two-sided adapter (`ScalarPin.lean`) + the decomposed blocks: radial (selector ray identities + `SpeedReconcile`), mixed (`OneSidedPayload/BundleDischarge`), transverse (`AssemblyDone` blocks + `ScalarPin`'s hplNorm constructors + `GronwallMembership/UniformShrink` side conditions) — assembled by `PullbackFeed.lean`'s adapters; the `θ ∈ Ioo 0 π` condition from the shrunk hosted data (`sT < π` — shrink the `v`-ball per the `UniformShrink` pattern if needed). FEED → 🎯 `cartanMap_isLocalIsometry` — for every closed simply-connected `g` with `HasConstantSectionalCurvature3 g 1`, anchors, some alignment: the pullback equality on a punctured shrunk normal ball — CURVATURE-ONLY. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/SinSqInstantiate.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-104_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.SinSqInstantiate` and report the actual result. Commit your work.
