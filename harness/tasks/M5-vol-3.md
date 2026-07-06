Read harness/worker_contract.md first and obey it strictly.

# Task M5-vol-3: GOAL 10 — finiteness of the volume measure on closed manifolds

Context: `Poincare/Global/VolumeMeasure.lean` defines `volumeMeasure g` as the Hausdorff measure `μH[n]` of the induced metric space (`g.toMetricSpace`; complete + compact). `harness/reports/M5-vol-2_done.md` roadmap step 3: `IsFiniteMeasure (volumeMeasure g)`.

Classical route: compact `M` is covered by finitely many chart domains; on compact subsets, smooth charts of the induced metric are Lipschitz (the induced distance is controlled by chart-Euclidean distance on compact sets — HONESTLY assess what the repo/Mathlib provides here: `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean` has local chart distance estimates per the M5-geo-1 inventory — mine it); Hausdorff measure of a Lipschitz image is bounded (`MeasureTheory` Hausdorff API: `Measure.hausdorff`, Lipschitz image lemmas like `LipschitzOnWith.hausdorffMeasure_image_le`); Euclidean balls have finite `μH[n]`.

Deliverables, in a NEW file `Poincare/Global/VolumeFiniteness.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. Whatever local comparison lemmas the route needs (chart-Lipschitz control of the induced distance on compact subsets — each standalone).
2. THE TARGET: `theorem volumeMeasure_isFiniteMeasure (g : ClosedSmoothRiemannianMetric n M) : letI := <the measurable/Borel context used in VolumeMeasure.lean>; MeasureTheory.IsFiniteMeasure (volumeMeasure g)` (adapt the instance plumbing to match `VolumeMeasure.lean` exactly).
3. If the distance-comparison input is genuinely missing from both repo and Mathlib, strict-partial: commit the reductions + isolate the ONE comparison lemma precisely (statement + suggested route via `PathELength`'s local estimates). Report `harness/reports/M5-vol-3_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.VolumeFiniteness` and report the actual result. Commit your work.
