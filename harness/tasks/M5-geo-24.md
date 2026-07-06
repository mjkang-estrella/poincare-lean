Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-24: resume the re-anchoring thread with the new templates

Context: the parked re-anchoring/transition thread (`Poincare/Global/GeodesicOverlap.lean`, `GeodesicReanchor.lean`, `GeodesicReanchorLaw.lean`; blocked reports M5-geo-8/10/11) stalled on the double-good transition ODE law. SINCE THEN, two template assets landed that change the game: (a) the COMPLETE curvature bridge (`ChartCurvatureBridge*.lean`, esp. the transported-section/hom `congr_of_eventuallyEq` + `_apply_chart` naturality lemmas in `ChartCurvatureBridge3/4/5.lean` — these are exactly the transport identities the ODE law needed); (b) interval uniqueness + endpoint control (`ExponentialMap.lean`) and the flow derivative machinery. Read `harness/reports/M5-geo-11_blocked.md` (the 5-step Koszul plan) and reassess with the new toolkit.

Deliverables, in a NEW file `Poincare/Global/GeodesicReanchorClose.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE TRANSITION LAW (`htransport_solves` input of `GeodesicReanchor.lean`'s conditional theorem): the transported state solves `y₀`'s chart system in the double-good zone — via the Koszul-pairing plan (chart-metric transport identity `chartMetric_chartTransitionMFDeriv` is proven in `GeodesicReanchorLaw.lean`; the pairing characterizations in `GeodesicReanchor.lean`; the naturality lemmas from the curvature bridge files as the missing transport glue).
2. UNCONDITIONAL RE-ANCHORING: instantiate the conditional theorem — `geodesicGermAt g x₀ v₀ (t₀ + s)` agrees near `s = 0` with the germ through `c t₀` (transported velocity), for small `t₀ > 0`.
3. If 1 still resists: strict-partial with the sharpest single sub-lemma; note explicitly what the curvature-bridge templates did and did not supply.
4. Report `harness/reports/M5-geo-24_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicReanchorClose` and report the actual result. Commit your work.
