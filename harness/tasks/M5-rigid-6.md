Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-6: the chart-constant-field transport — the zone bridge closes

Context: `harness/reports/M5-rigid-5_blocked.md` (READ FIRST). Proven in `ChartCurvatureBridgeZone.lean`: the arbitrary-`z` model-side bridge, `chartInverseTangent`, the zone lowered KN identity, and the final composition WITH the remaining bridge as hypothesis. THE LAST LEMMA: at zone points `z` away from the anchor, relate curvature evaluated on INVERSE-CHART-PUSHED fields (what the model-side bridge produces) to curvature on the canonical `extend` fields based at `(extChartAt I x₀).symm z` (what `HasConstantSectionalCurvature3` speaks about) — a field-choice naturality. KEY TOOL: curvature at a point is TENSORIAL in the field arguments (depends only on the pointwise values — the repo proved curvature germ-locality and `ricciBilinearAt_eq_of_agree`-style agreement lemmas; check `CurvatureTensoriality.lean` and the `constSMul_curvatureOp_extend_apply` technique: if two field tuples AGREE NEAR the evaluation point, curvatures agree; if they agree only AT the point, use the tensoriality/pointwise-dependence theorems — `CovariantDerivative.curvatureOp` pointwise-value dependence lemmas exist in the repo's tensoriality layer — FIND them). The inverse-chart-pushed field and the extend field at `c(z)` have the SAME VALUE at `c(z)` by construction — arrange the tensoriality theorem to conclude.

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridgeZoneClose.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE FIELD-CHOICE NATURALITY at zone points (exact hypothesis spelling from rigid-5's composition theorem).
2. THE UNCONDITIONAL ZONE BRIDGE + zone KN identity for constant-curvature-1 metrics (instantiate rigid-5's composition).
3. If reachable: the interval oscillator `J'' = −J` along the chart geodesic (rigid-4's machinery + the zone identity); else isolate.
4. Report `harness/reports/M5-rigid-6_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.ChartCurvatureBridgeZoneClose` and report the actual result. Commit your work.
