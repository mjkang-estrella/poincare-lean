Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-17: the two second-order field-derivative bridges (Gram route, one derivative higher)

Read the latest `harness/reports/M3-scalar-variation_notes.md` status. On main: the Hamilton chain is complete modulo `DeltaGammaContractionTraceHessianDerivativeAt` and `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` (Global/ScalarVariation.lean — read their exact statements FIRST; they demand differentiability + derivative identification for the closed δΓ trace-form FIELDS), plus the algebraic ClosedContractedBianchiAt/substitution predicates (separate task).

Strategy — the EXACT pattern that won at first order, applied to the derived fields:
1. The δΓ trace-form field at y is built from: h-entries on extend sections, Gram-inverse entries, and first-derivative entries (extDerivFun of the scalar entries). Its own derivative therefore needs SECOND-derivative entries: `extDerivFun (extDerivFun scalar-entry)`-shapes. The honest regularity classes on main (`CovTensor2ExtDifferentiableAt` etc.) may need a C²-variant — add it honestly (fields: second-order differentiability of the scalar entries h(ext,ext) and g(ext,ext); witnesses: zero/static + note the flow case).
2. Express the trace-form field near x via the Gram formula AT EACH y (the identities on main are mostly pointwise-at-x with extend-frame anchored at x; for the FIELD version anchor the frame at x and let y vary in the invertibility neighborhood — `gramMatrix g x y` is already the two-point object, and `traceMetricVariationAt_eq_sum_gram_inv`-style identities near x exist from predicates-12; mirror them for the δΓ trace forms).
3. Differentiate the resulting scalar formula (products/inverses of C¹/C² scalar entries — plain calculus), then identify with the frozen bridge statements.
4. If ONE bridge closes and the other stalls, that's still success — commit + exact goal state.

No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
