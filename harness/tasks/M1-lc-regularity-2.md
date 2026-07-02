Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-regularity-2: chart transport of Levi-Civita regularity (sublemmas 1-2)

Context on main: `harness/reports/M1-lc-regularity_blocked.md` decomposes the remaining work for `closedLeviCivitaConnection_contMDiff` into 4 sublemmas. `CovariantDerivative.leviCivitaConnection_contMDiff` (model space, any order, Poincare/ModelChristoffel.lean:519) is proven. `Poincare/ChartTransport.lean` has `chartMetric` (with symm/nondegenerate/posDef/smoothness) and `chartLeviCivita` + `chartLeviCivita_contMDiff`.

Deliverable: sublemmas 1 and 2 ONLY (scope discipline — 3 and 4 are a separate task), in a NEW file `Poincare/Global/LeviCivitaTransport.lean` (+ root import) or extending ChartTransport.lean if more natural:

1. (Sublemma 1) Define the chart-transported connection value near x₀: for a tangent section σ on M and y in `(extChartAt I x₀).source`, pull σ back to the model space through `(extChartAt I x₀).symm` (using `mfderiv`/tangent chart maps — the repo's ChartTransport/ChartIdentification files have the tangent-map plumbing; reuse it), apply the model `chartLeviCivita` (or the model Koszul connection of `chartMetric g x₀` — choose whichever the identification in sublemma 2 makes cleanest), and push back to `TangentSpace I y`. Prove basic well-definedness lemmas.

2. (Sublemma 2) The local identification: for σ differentiable at y in a neighborhood of x₀, the transported value equals `(LeviCivitaExistence.closedLeviCivitaConnection g) σ y` — via the UNIQUENESS route if direct computation is heavy: both are torsion-free and metric-compatible at y (chart transport preserves both — chartMetric was built to pull g back isometrically), so `levi_civita_unique`/`leviCivita_unique_at` closes it. Check whether ChartTransport.lean already proves the transported operator is Levi-Civita for chartMetric; if only halves exist, prove the missing halves.

Commit each verified lemma separately. If a sublemma stalls, commit greens + update `harness/reports/M1-lc-regularity_blocked.md` with the refined obstruction. No sorry/axiom. `lake build`, commit, report declaration names.
