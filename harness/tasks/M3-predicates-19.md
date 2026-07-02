Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-19: the closed Schwarz lemma + finish the contraction-side field predicate

Read `harness/reports/M3-predicates-18_blocked.md`. Three named obligations remain for the contraction side; the central new one is the SCHWARZ STEP: mixed-derivative symmetry for closed `extDerivFun` second derivatives of canonical-extension scalar entries:
`extDerivFun (fun y => extDerivFun f y (extend E v y)) x u` vs the (u,v)-swapped version, for f = the scalar entries (h/g on extend sections) under the C² classes.

Deliverables (each its own commit):
1. **Closed Schwarz lemma**: route through the chart — `extDerivFun` of a scalar on M is defined via the chart representative (read its definition in Mathlib `MFDeriv/NormedSpace.lean` or wherever `extDerivFun` lives); the second mixed derivative of f pulls back to the flat second derivative of the chart representative PLUS first-order chart-correction terms; flat Schwarz is `ContDiffAt.isSymmSndFDerivAt` (used 4+ times in ModelChristoffel/ModelLaplacian — lines 760, 2207, 3129, 5527 — mine the exact usage pattern). The extend-direction fields add first-derivative-of-extend corrections — these are the SAME on both sides or cancel in the antisymmetrization (work it out against the actual definitions; if the correction terms don't obviously cancel, the honest statement may be Schwarz-modulo-Christoffel — i.e. the symmetric part identity that the Hessian machinery (`hessianAt_symm'`) already encodes: check whether `hessianAt_symm'` + `extDerivFun_extDerivFun_extend_eq_hessianAt_add` (on main, new) ALREADY yields the needed swap — that may make this a 10-line corollary rather than a new chart computation. TRY THAT FIRST.)
2. **Trace-C² from the entry vocabulary**: derive `TraceMetricVariationExtSecondDifferentiableAt` from the C² entry classes via the Gram formula (differentiate `traceMetricVariationAt_eq_sum_gram_inv` twice — products/inverses of C² scalars).
3. **The moving-frame covariant fact** `DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt` per the report, using 1+2 + the existing cancellation lemmas.
4. Chain: discharge `DeltaGammaContractionTraceHessianDerivativeAt` (adapters on main); if budget, start the divergence-side analogue.

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
