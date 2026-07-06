Read harness/worker_contract.md first and obey it strictly.

# Task M5-model-1: GOAL 9 — the round metric on the statement-layer S³

Context: every theorem in `Poincare/Global/` quantifies over abstract metrics; the repo contains NO concrete nontrivial `ClosedSmoothRiemannianMetric`. The statement-layer sphere `Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)` (see `Poincare/Global/Statement.lean`) already has the needed `ChartedSpace (EuclideanSpace ℝ (Fin 3))` + `IsManifold (𝓡 3) ∞` instances. Goal: construct its round metric — the model space for the eventual Killing–Hopf recognition and the non-vacuity witness for `HamiltonConvergencePinchedLimit3`-type interfaces.

Frozen final target, in a NEW file `Poincare/Global/RoundSphereMetric.lean` (do NOT edit existing files incl. `Poincare.lean`):

`noncomputable def roundSphereMetric3 : ClosedSmoothRiemannianMetric 3 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))`

with defining lemma

`roundSphereMetric3_inner_eq : ∀ x v w, roundSphereMetric3.inner x v w = inner ℝ (mfderiv (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((↑) : _ → EuclideanSpace ℝ (Fin 4)) x v) (mfderiv (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((↑) : _ → EuclideanSpace ℝ (Fin 4)) x w)`

(pullback of the ambient inner product along the inclusion derivative; spelling adaptation sanctioned, semantics frozen).

Recall `ClosedSmoothRiemannianMetric 3 M = ContMDiffRiemannianMetric (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3))` (`Poincare/Global/RiemannianContext.lean:44`), so you must supply the structure fields: `inner`, `symm`, `pos`, `isVonNBounded`, `contMDiff` (structure `ContMDiffRiemannianMetric`, `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:244`).

Leads: `Mathlib/Geometry/Manifold/Instances/Sphere.lean` (search: `contMDiff_coe_sphere`, `mfderiv_coe_sphere`, `range_mfderiv_coe_sphere`, injectivity of the sphere-inclusion `mfderiv`); `ContMDiff.mfderiv` (`Mathlib/Geometry/Manifold/ContMDiffMFDeriv.lean`) for smoothness of the derivative family; positivity from injectivity of the inclusion derivative; `isVonNBounded` from positive-definiteness on a finite-dimensional fiber (continuity + compactness of the unit sphere — check how Mathlib's canonical inner-product-space Riemannian instance in `Mathlib/Geometry/Manifold/Riemannian/Basic.lean` handles this field and mirror it).

Acceptable strict-partial outcome (if the full structure is out of reach): commit the proven fields as standalone lemmas (bilinear family + `symm` + `pos` + whichever of `isVonNBounded`/`contMDiff` you complete), NO placeholder/sorry def, and write `harness/reports/M5-model-1_blocked.md` isolating each missing field as a single precisely-stated lemma with a decomposition plan. Full success report: `harness/reports/M5-model-1_done.md`.

Verify: `lake build Poincare.Global.RoundSphereMetric` and report the actual result. Commit your work.
