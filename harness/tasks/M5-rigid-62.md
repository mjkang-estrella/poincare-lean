Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-62: the bilinearity rescale — unscaled feed, the chain fires

Context: `harness/reports/M5-rigid-61_blocked.md` (READ FIRST). PROVEN: the target pinned formulas in the honest RESCALED hosted form — `target_hosted_rescaled_endpoint_pairing_eq_pinned_of_interval_norm_package` with `(T⁻¹ • w)` anchors (`TargetPackage.lean`); `EqualityChain.lean` wants the UNSCALED `(L a)` feed. THE CONVERSION IS BILINEARITY: chart-metric pairings are bilinear in both slots — `G(x)(T⁻¹•w, T⁻¹•w') = T⁻²·G(x)(w,w')` (the pairing definitions; `smul` lemmas) — and the linearized families are homogeneous (`LinearizedAdditivity.lean` smul; `Ψ_{T⁻¹w} = T⁻¹·Ψ_w`), so the rescaled formula × `T²` = the unscaled formula; the `sin²(sT)/s²`-normalization factors match by rigid-47's scale normalization (`CartanFinalComposition.lean`) and the chain's own factor bookkeeping (`EqualityChain.lean` — READ what exact function it expects). ALSO mirror on the SOURCE side if its feed has the same rescaled/unscaled mismatch. Then FIRE: feed both sides → the chain (`EqualityChain.lean`) → the consumer (`PairingFeed.lean`) → 🎯 `cartanMap_isLocalIsometry`. If ONE scalar identity resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/UnscaledFeed.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-62_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.UnscaledFeed` and report the actual result. Commit your work.
