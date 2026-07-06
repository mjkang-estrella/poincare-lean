Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-13: GOAL 9 — richer `expAt` spec (sanctioned single-file edit), full ray law

Context: `harness/reports/M5-geo-12_blocked.md` — the full closed-interval ray law is blocked ONLY because `Poincare/Global/ExponentialFixedTime.lean`'s `Classical.choose` packaging of `expAt` exports the eventual ray law but not the PL-flow/germ interval identification or uniform closed-ball control that its own proof possessed.

SANCTIONED EXCEPTION for this task ONLY: you MAY edit `Poincare/Global/ExponentialFixedTime.lean` — strengthening its spec exports (add lemmas / enrich the chosen-witness spec), WITHOUT changing the `expAt` definition's type or breaking any existing exported name (downstream: `Poincare/Global/ExponentialRayLaw.lean` imports it — keep it compiling). You may NOT edit any other existing file (incl. `Poincare.lean`).

Deliverables:
1. In `ExponentialFixedTime.lean`: export the richer spec (interval flow/germ identification and/or uniform ball control) as named lemmas.
2. In a NEW file `Poincare/Global/ExponentialRayLawFull.lean`: the full ray law `expAt g x₀ (t • v) = geodesicGermAt g x₀ v t` for all `t ∈ Set.Icc 0 τ'` (honest uniform `τ' > 0`, `‖v‖` small), upgrading `expAt_eventually_eq_geodesicGermAt_nhdsGE` / reusing `expAt_chart_hasDerivWithinAt_of_norm_lt` (in `ExponentialRayLaw.lean`).
3. Report `harness/reports/M5-geo-13_{done|blocked}.md`.

Verify: `lake build Poincare.Global.ExponentialFixedTime Poincare.Global.ExponentialRayLaw Poincare.Global.ExponentialRayLawFull` (ALL must pass — the edit must not break the existing modules) and report the actual result. Commit your work.
