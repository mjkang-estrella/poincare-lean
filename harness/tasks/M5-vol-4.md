Read harness/worker_contract.md first and obey it strictly.

# Task M5-vol-4: GOAL 10 — the inverse-chart Lipschitz comparison, then volume finiteness

Context: `harness/reports/M5-vol-3_blocked.md` (READ FIRST) isolates ONE missing lemma behind `IsFiniteMeasure (volumeMeasure g)`: the local Lipschitz comparison for the inverse chart against the induced Riemannian distance, with a 5-step route following the INTERNAL proof pattern of Mathlib's `eventually_riemannianEDist_le_edist_extChartAt` (`Mathlib/Geometry/Manifold/Riemannian/Basic.lean` / `PathELength.lean`): segment paths in the chart, `pathELength` bounded by a derivative bound times `edist`, conversion to the `g.toMetricSpace` Lipschitz statement consumed by `LipschitzOnWith.hausdorffMeasure_image_le`. Proven reductions live in `Poincare/Global/VolumeFiniteness.lean` (`exists_compact_lipschitz_extChartAt_symm_image_nhds`, `hausdorffMeasure_image_lt_top_of_lipschitzOnWith`, + the assembly).

Deliverables, in a NEW file `Poincare/Global/VolumeFinitenessComparison.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE COMPARISON LEMMA exactly as isolated in the report (spelling adaptations documented) — following the 5-step route.
2. THE TARGET: `volumeMeasure_isFiniteMeasure` (or the report's exact name/shape) by feeding 1 into the existing reductions.
3. Report `harness/reports/M5-vol-4_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.VolumeFinitenessComparison` and report the actual result. Commit your work.
