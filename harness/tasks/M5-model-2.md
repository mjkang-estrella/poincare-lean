Read harness/worker_contract.md first and obey it strictly.

# Task M5-model-2: GOAL 9 — finish the round S³ metric (the `contMDiff` field)

Context: M5-model-1 (report: `harness/reports/M5-model-1_blocked.md`) landed the pullback tensor and three of five structure fields in `Poincare/Global/RoundSphereMetric.lean`: `roundSphereMetric3_inner` (+ `_apply`, `_mfderiv_eq`), `_symm`, `_pos` (via `mfderiv_coe_sphere_injective`), `_isVonNBounded` (antilipschitz route). The ONLY missing field is smoothness of the operator-valued section.

Frozen targets, by EDITING `Poincare/Global/RoundSphereMetric.lean` (you may edit THIS file only; do NOT touch any other existing file, incl. `Poincare.lean`):

1. ```lean
   theorem roundSphereMetric3_inner_contMDiff :
       ContMDiff (𝓡 3)
         ((𝓡 3).prod
           𝓘(ℝ, (EuclideanSpace ℝ (Fin 3)) →L[ℝ]
             (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ))
         ∞
         (fun x : RoundSphere3 =>
           TotalSpace.mk'
             ((EuclideanSpace ℝ (Fin 3)) →L[ℝ]
               (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ)
             x (roundSphereMetric3_inner x))
   ```
2. ```lean
   noncomputable def roundSphereMetric3 : ClosedSmoothRiemannianMetric 3 RoundSphere3
   ```
   assembled from the five fields (the blocked report gives the exact `where` skeleton), plus the defining lemma `roundSphereMetric3_inner_eq : roundSphereMetric3.inner = roundSphereMetric3_inner` (or the pointwise `= inner ℝ (mfderiv … x v) (mfderiv … x w)` form via `_mfderiv_eq`; spelling free, semantics frozen).

Follow the predecessor's decomposition plan (in the blocked report):
(a) smoothness of the inclusion derivative in tangent coordinates via `contMDiff_coe_sphere` + `ContMDiffAt.mfderiv_const` (`Mathlib/Geometry/Manifold/ContMDiffMFDeriv.lean`) with `inTangentCoordinates`; (b) the local trivialization equation for the hom-bundle section; (c) `ContDiff ℝ ∞` of the model-space operation `D ↦ ((precomp D).comp innerSL).comp D` (use `ContinuousLinearMap.precomp`, `compL`, `ContinuousLinearMap.contDiff`, `ContDiff.clm_apply`); (d) glue via `contMDiffAt_section`. The repo's Levi-Civita regularity chain (`Poincare/Global/LeviCivitaRegularity.lean`, hom-bundle `EventuallyEq` lift + `inCoordinates` gluing) contains working examples of exactly this section-smoothness pattern — mine it.

If truly blocked: commit whatever standalone smoothness lemmas you proved, NO placeholder def, and write `harness/reports/M5-model-2_blocked.md` isolating the single remaining sub-lemma with a finer decomposition. Success report: `harness/reports/M5-model-2_done.md` (mention follow-up candidates: Einstein/constant-curvature computation for `roundSphereMetric3`).

Verify: `lake build Poincare.Global.RoundSphereMetric` and report the actual result. Commit your work.
