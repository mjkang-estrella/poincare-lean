# Actual local solver construction

Core assumption helped: UniversalHamiltonConvergenceStatement, via actual
general Ricci-flow inputs rather than a supplied flow or sphere witness.
Subsequent consumer of both helper tasks is
MetricAdaptedLocalParametrix.exists_metric_adapted_local_parametrix.
The inverse regularity task supplies the actual frozen positive matrix and
smooth variable entries required by exists_single_chart_parametrix.
Finite bounds supplies one positive lifespan and uniform constants after the
finite atlas has been selected. It also handles zero charts.

Choose the single-chart solver's own epsilon at each anchor BEFORE applying
MetricAdaptedBufferedAtlas.exists_metric_adapted_buffered_atlas. Do not replace
it by a tolerance from another existential solver. Local estimates and signed
residual are restricted to forcing supported in coordSupport; P support alone
is unconditional. Do not assert an unconditional R norm/support estimate.

Still open: actual global tensor L/P/R identity and norm contraction, nonlinear
DeTurck inversion, matched initial-time extension and ordinary joint C3, general
Ricci flow, continuation/surgery and favorable metric/limit production. The
smoothability core is separate and remains open. No core is discharged here.
