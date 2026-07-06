Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-11: GOAL 9 — the double-good transition law via Koszul pairing

Context: `Poincare/Global/GeodesicReanchor.lean` (report `harness/reports/M5-geo-10_blocked.md`) proved: cutoff-1 blended metric = transported chart metric (`blendedChartMetric_eq_chartMetric_of_cutoff_eq_one`, `…_eventuallyEq_…`), the Christoffel/Koszul PAIRING characterization on cutoff-1 germs (`chartChristoffelField_pairing_eq_chartMetric_…` family), `reanchoredVelocity`, and a CONDITIONAL re-anchor uniqueness theorem waiting on one input: the shifted `chartTransitionState` of an `x₀`-chart geodesic solves `y₀`'s chart ODE in the double-good zone (`htransport_solves`). `Poincare/Global/GeodesicOverlap.lean` has `chartTransitionState_eventually_solves_of_components` (the component-level boundary).

THE TASK: discharge `htransport_solves` — WITHOUT the raw Christoffel transformation computation if possible. Intended route (adapt freely; document): both chart Christoffel fields are characterized on their cutoff-1 zones by the KOSZUL PAIRING against the transported chart metric (proven!). Verify the transported state solves `y₀`'s ODE by checking the pairing characterization: differentiate the transported metric pairing along the curve (chain rule through the transition map), use that the `x₀`-side curve solves its own pairing identity, and that the two transported chart metrics correspond under the transition derivative (both are chart representations of the SAME `g.inner` — a `PartialEquiv` transport identity to state and prove). Nondegeneracy of the chart metric then converts pairing equality to the ODE. Second derivatives of the transition enter only through `fderiv` of the transition-derivative field — acceptable.

Deliverables, in a NEW file `Poincare/Global/GeodesicReanchorLaw.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. TRANSPORT IDENTITY of chart metrics: on the double-good zone, `chartMetric`(y₀-side) at `τ z` applied to `(Dτ u, Dτ v)` equals `chartMetric`(x₀-side) at `z` applied to `(u, v)` (both = `g.inner` at the underlying point; spelling free).
2. THE TRANSITION LAW: the shifted/transported state solves `y₀`'s system eventually (discharging the conditional input of geo-10's re-anchor theorem), for `y₀` in an honest double-good neighborhood of `x₀`.
3. RE-ANCHORING, unconditional: instantiate geo-10's conditional theorem — `geodesicGermAt g x₀ v₀ (t₀ + s)` agrees near `s = 0` with `geodesicGermAt g y₀ (reanchoredVelocity …)` for small `t₀ > 0`. If arranging the double-good hypotheses for `y₀ := c t₀` costs too much, deliver 1-2 and isolate 3's remaining glue precisely.
4. Report `harness/reports/M5-geo-11_{done|blocked}.md`.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.GeodesicReanchorLaw` and report the actual result. Commit your work.
