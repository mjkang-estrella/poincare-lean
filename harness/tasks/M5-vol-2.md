Read harness/worker_contract.md first and obey it strictly.

# Task M5-vol-2: GOAL 10 opener — the Riemannian volume measure, Hausdorff route

Context: `harness/reports/M5-vol-1_assets.md` (READ FIRST) surveyed the pinned Mathlib and recommends: the induced metric space (`g.toMetricSpace`, `Poincare/Global/RiemannianContext.lean:190`; complete by `Poincare/Global/MetricCompleteness.lean`) carries Mathlib's Hausdorff measure `μH[n]` — a candidate `volumeMeasure g : Measure M`. Chart-level density machinery landed in `Poincare/Global/VolumeDensity.lean` (namespace `Poincare.VolumeDensity`).

Deliverables, in a NEW file `Poincare/Global/VolumeMeasure.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE DEFINITION: `noncomputable def volumeMeasure (g : ClosedSmoothRiemannianMetric n M) : MeasureTheory.Measure M := letI := g.toMetricSpace; μH[(n : ℝ)]` (adapt spelling: `MeasureTheory.Measure.hausdorff` needs a `MeasurableSpace` — use the Borel σ-algebra of the induced topology; the induced topology is DEFINITIONALLY the manifold topology, so `[MeasurableSpace M] [BorelSpace M]` hypotheses or a `letI` Borel construction both work — choose and document).
2. BASIC SANITY, whichever are within reach (commit what closes; isolate the rest): (a) `volumeMeasure` is a Borel measure / measurable-set API usable; (b) positivity on nonempty open sets OR finiteness on the compact `M` (Mathlib has Hausdorff-measure lemmas for metric spaces — `μH` finiteness needs bounded geometry; if general finiteness is hard, state it as the isolated next lemma with the Lipschitz-charts route sketched); (c) the scaling behavior under `constSMul` at the METRIC-SPACE level if the distance-scaling lemma exists (likely needs `constSMul` distance transport — if absent, note it).
3. Report `harness/reports/M5-vol-2_{done|blocked}.md`: what Mathlib's `μH` API gives for free, what needs the chart-density comparison (the local `sqrt(det G)` equivalence from the vol-1 roadmap), and the integration-of-scalar-curvature roadmap (toward normalized flow / mean scalar).

No vacuous wrappers. Verify: `lake build Poincare.Global.VolumeMeasure` and report the actual result. Commit your work.
