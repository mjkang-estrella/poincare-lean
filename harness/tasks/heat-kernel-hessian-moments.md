# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/heat-kernel-hessian-moments`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/heat-kernel-hessian-moments_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact unmatched integral or scaling identity and the strongest compiled partial result; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/parabolic-schauder-decomposition-survey_done.md` (sections 1.1-1.2, 3.2, 4 (K1), Appendix D2) first. Landed heat-kernel material: `Poincare/Global/HeatKernel.lean` (`heatKernel`, `heatKernel_pos`, `contDiff_heatKernel_spatial`), `HeatKernelIntegral.lean` (`heatKernel_integrable`, `integral_heatKernel_eq_one`), `HeatCauchyNext2.lean` (existing Hessian formula and envelopes), `HeatSemigroupBUCPositiveGenerator.lean` (time-scaling integral). Find the exact names by grep before use.

# Task heat-kernel-hessian-moments

Module: `Poincare/Global/HeatKernelHessianMoments.lean`. Namespace: `Poincare.HeatKernelHessianMoments`. Imports: `Poincare.Global.HeatCauchyNext2`, `Poincare.Global.HeatSemigroupBUCPositiveGenerator`, `Mathlib.Analysis.SpecificLimits.Normed` (add what you need).

Objective: prove the K1 target exactly as probed in Appendix D2 of the survey. With `E := Poincare.ClosedSmoothModel 3` and `Hess t x := fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x` (use the same local instance `NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance` as the probe if needed for the Bochner integrability instance):

```lean
theorem hessian_moments :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
    Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0
```

Route: (i) explicit Hessian of the Gaussian: `Hess t x = K_t(x) • ( (1/(4t²)) x⊗x - (1/(2t)) id )` in the sense of bilinear forms (derive from the landed Hessian formula in `HeatCauchyNext2`, or by differentiating twice); (ii) dilation: `K_t(x) = t^{-3/2} K_1(x/√t)` and `Hess t x = t^{-5/2} (Hess 1)(x/√t)`, with the volume change `dx = t^{3/2} dy` (Mathlib: `MeasureTheory.Measure.addHaar_smul`, `integral_comp_smul` / `MeasureTheory.integral_comp_smul_deriv`-type lemmas on finite-dimensional real spaces; verify names); (iii) integrability of `‖Hess 1 y‖ ‖y‖^α` from Gaussian decay times polynomial growth (`integrable_exp_neg_mul_sq`-type lemmas, `Integrable.mono` with a polynomial-times-Gaussian majorant; landed `heatKernel_integrable` may already carry the moment machinery); then `∫ ‖Hess t x‖ ‖x‖^α dx = t^{-5/2} · t^{3/2} · t^{α/2} ∫ ‖Hess 1 y‖ ‖y‖^α dy = C₀ t^{α/2 - 1}`, so `C := max 1 C₀` works; (iv) cancellation: `∫ Hess t x dx = 0` either by differentiating `∫ K_t(x - ·) = 1` twice under the integral sign, or directly: the integral of `K_t · x⊗x` equals `2t · id` (Gaussian second moments) and of `K_t · id` equals `id`, so `(1/(4t²))·2t·id - (1/(2t))·id = 0`. Record which route compiled.

Exact stop condition: `hessian_moments` compiles with exactly the displayed statement and passes the gate; or a blocked report displays the exact unmatched integral or scaling identity with the compiled partial lemmas committed.
