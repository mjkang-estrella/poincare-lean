Read harness/worker_contract.md first and obey it strictly.

# Task M5-bridge-3: GOAL 9 — the last link: curvature naturality under chart transport

Context: the chain to the sphere witness is now: `chartCurvatureOf (chartChristoffelField g x₀)` = model-space `curvatureOp (chartLeviCivita g x₀)` on `extend` fields at the anchor image (PROVEN — `Poincare/Global/ChartCurvatureBridge2.lean`, `chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature`). The LAST missing link (read `harness/reports/M5-bridge-2_blocked.md` FIRST for the precise remaining statement): the manifold pushforward — `curvatureOp (GeodesicTransport.chartLeviCivita g x₀)` (a connection on the model space `E`) versus `curvatureOp g.leviCivita` on `M`-side `extend` fields at `x₀`, through the chart identification.

Intended route (adapt; document): `chartLeviCivita` is CONSTRUCTED by transporting `CovariantDerivative.chartTransportedLeviCivitaHom …` — inspect the definitional relationship in the underlying `CovariantDerivative.chartLeviCivita` machinery (`Poincare/Global/LeviCivitaTransport.lean` and the `CovariantDerivative` chart API): the E-side connection applied to a transported field should be, definitionally or by an existing lemma, the transport of the M-side hom applied to the field. Then: (i) curvature of the E-side connection on transported `extend` fields = transport of curvature of the M-side transported hom (unfold `curvatureOp` — second covariant derivatives — through that relationship; the bracket/second-derivative bookkeeping is the real work); (ii) M-side transported hom eventually agrees with `g.leviCivita` near `x₀` (`chartLeviCivita_eventuallyEq_closed`) and curvature is germ-local (`constSMul_curvatureOp_extend_apply`'s technique, `MetricRescale.lean:226`; also `christoffelOneForm_congr_of_eventuallyEq` in `RoundSphereCurvature.lean`), so the M-side curvature is `curvatureOp g.leviCivita` on `extend` fields at `x₀`.

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridge3.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE LINK: `curvatureOp (chartLeviCivita g x₀)` on the anchor's model `extend` fields = (chart identification of) `curvatureOp g.leviCivita (extend E u) (extend E w) (extend E a) x₀` — general closed `g`, general `n` preferred; identification spelling documented.
2. THE ASSEMBLED BRIDGE: compose with ChartCurvatureBridge2's theorem into the single statement `chartCurvatureOf (chartChristoffelField g x₀) … = (identification of) curvatureOp g.leviCivita …`.
3. If cheap, the sphere witness: `HasConstantSectionalCurvature3 roundSphereMetric3 1` (assembly pieces listed in `harness/reports/M5-bridge-2_blocked.md` §next-steps); else isolate its final glue precisely.
4. Report `harness/reports/M5-bridge-3_{done|blocked}.md`.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ChartCurvatureBridge3` and report the actual result. Commit your work.
