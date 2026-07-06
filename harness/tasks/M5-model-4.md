Read harness/worker_contract.md first and obey it strictly.

# Task M5-model-4: GOAL 9 — round-metric chart coefficients (the bundle tie-in)

Context: `Poincare/Global/RoundSphereChart.lean` (report `harness/reports/M5-model-3_done.md`) proved the ambient conformal pullback formula: `inner_fderiv_stereoInvFunAux_comp_subtype` — `⟪fderiv ℝ (stereoInvFunAux v ∘ (↑)) z u, fderiv … z w⟫ = stereoInvFunAuxConformalFactor z * ⟪u,w⟫` on `(ℝ ∙ v)ᗮ`, factor `16 / (‖z‖² + 4)²`. `Poincare/Global/RoundSphereMetric.lean` has the complete `roundSphereMetric3` with `roundSphereMetric3_inner_mfderiv_eq` / `_apply` and `roundSphereMetric3_inclusionDeriv`.

Goal: express `roundSphereMetric3`'s coefficients in Mathlib's sphere chart — the concrete conformal form that the curvature computation will consume.

Frozen semantic target, in a NEW file `Poincare/Global/RoundSphereChartMetric.lean` (do NOT edit existing files, incl. `Poincare.lean`): a theorem expressing, for `x₀ : RoundSphere3` and a point `p` in the source of `chartAt (EuclideanSpace ℝ (Fin 3)) x₀` (equivalently a chart coordinate `z`), the value `roundSphereMetric3.inner p v w` as `(conformal factor at the chart coordinate) * ⟪(model identification of v), (model identification of w)⟫`. The spelling of the identification is free; per the M5-model-3 report the route is: `chartAt _ x₀ = stereographic' 3 (-x₀)` (check Mathlib's actual instance — `ChartedSpace` on spheres uses `stereographic'` at `-x₀`), whose inverse composed with the inclusion is `stereoInvFunAux (-x₀.val) ∘ Subtype.val ∘ U.symm` with `U = (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero-of the unit vector)).repr`; combine `roundSphereMetric3_inner_mfderiv_eq`, the `mfderiv` chain rule along `(↑) ∘ (chartAt _ x₀).symm` (relate `mfderiv` on the chart source to the `fderiv` of the ambient parametrization — `mfderiv_coe_sphere`-adjacent lemmas and `PartialHomeomorph`/`extChartAt` plumbing), `fderiv_stereoInvFunAux_comp_subtype`, `inner_stereoInvFunAuxFDeriv_of_mem_orthogonal`, and `LinearIsometryEquiv.inner_map_map`.

Deliverables:
1. Whatever intermediate `mfderiv`-vs-`fderiv` identification lemmas the route needs (each as a standalone named lemma — they are reusable assets).
2. The chart-coefficient theorem (frozen semantics above; document the final exact statement in the report).
3. If the full tie-in blocks: commit the proven intermediates, NO placeholder, and write `harness/reports/M5-model-4_blocked.md` isolating the single missing identification with a finer plan. Success: `harness/reports/M5-model-4_done.md` + the curvature-computation roadmap refined against the actual final statement.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.RoundSphereChartMetric` and report the actual result. Commit your work.
