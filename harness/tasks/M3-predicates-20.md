Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-20: neighborhood C² vocabulary + the moving-frame identity → close the contraction side

Read `harness/reports/M3-predicates-19_blocked.md`. On main: closed Schwarz lemmas, `traceMetricVariationExtSecondDifferentiableAt_of_contMDiffAt` (the ContMDiffAt-2 bridge), the full first-order chain, and the contraction-side reduction (`deltaGammaFirstSlotTraceFieldHessianAt_of_trace_extSecond` waiting on the trace-C² predicate + `DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt`).

Deliverables (each its own commit):

1. **Neighborhood-form regularity class**: define the honest strengthened vocabulary the report requests — e.g. `CovTensor2ExtContMDiffAt gt t₀ x 2`-style: the canonical scalar entries `y ↦ h y (extend p) (extend q)` (and metric entries) are `ContMDiffAt ... 2` at x (NOT just twice-differentiable-at-x). Satisfiability witnesses: static/zero + note that for h = timeDerivAt of a jointly-smooth flow this is the natural hypothesis. Adapters: the new class implies ALL the older point-at-x classes (each older class's fields follow from ContMDiffAt 2 — mechanical).
2. **Trace C² discharge**: via the class + `traceMetricVariationExtSecondDifferentiableAt_of_contMDiffAt` — ContMDiffAt-2 of the anchored Gram RHS entries: products/inverses of ContMDiffAt-2 scalars are ContMDiffAt-2 (`ContMDiffAt.mul`, `.div`/inverse via det-nonvanishing on a neighborhood — the Gram invertibility neighborhood from predicates-12).
3. **The moving-frame identity** `DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt`: field-level first-slot trace identity — identify the moving-basis derivative with `deltaGammaContractionDerivAt` + Levi-Civita cancellation (the report's own description; the first-order cancellation lemmas + the new Schwarz lemmas are the tools).
4. **Chain**: discharge `DeltaGammaContractionTraceHessianDerivativeAt` (adapters on main fire) — the CONTRACTION-SIDE ASSEMBLY CLOSES. Restate the Hamilton wrappers with one fewer predicate; notes.

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
