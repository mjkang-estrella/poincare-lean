# M3 scalar variation notes

`Poincare/Global/ScalarVariation.lean` adds the first closed-manifold layer:
scalar differentiability follows from a genuine `HasDerivAt` hypothesis on the
raised Ricci endomorphism, the derivative of scalar curvature is reduced to a
trace of that endomorphism derivative, and `deltaGammaAt` is defined as the
time derivative of the canonical Levi-Civita connection value on canonical
`extend` sections.

Status from task `M3-scalar-variation-2`:

- Done: `ricciEndoHasDerivAt_of_ricciBilinearHasDerivAt` lifts pointwise
  Ricci component derivatives to the raised Ricci endomorphism, with an honest
  derivative hypothesis for `metricRaiseContinuousAt`.
- Done: `extend_tangent_add`, `extend_tangent_smul`,
  `deltaGammaAt_add_right`, and `deltaGammaAt_smul_right` establish
  second-slot linearity for `deltaGammaAt` using canonical-extension
  linearity.
- Partial for subtask 3: added `ricciAt_eq_curvature_contraction`,
  `covDeltaGammaDerivAt`, `curvatureVariationByDeltaGammaAt`,
  `deltaGammaDivergenceAt`, `deltaGammaContractionDerivAt`, `deltaRicciAt`,
  `deltaRicciAt_eq_curvatureVariation_contraction`, and
  `ricciVariation_eq_deltaGamma_contractions`.  The last theorem is proved
  under the explicit curvature-variation hypothesis
  `hCurv : ∀ a, HasDerivAt (fun t => curvatureOp (gt t).leviCivita ...) ... t₀`.
  This is the remaining bridge: prove the time derivative of the closed
  curvature operator is the antisymmetrized covariant derivative of
  `deltaGammaAt`, analogous to model `curvatureDerivOp_eq_covDeltaGamma`.

Status from task `M3-scalar-variation-3`:

- Done in commit `07bf4550`: added the closed vocabulary requested by subtask
  4 in `Poincare/Global/ScalarVariation.lean`:
  `metricDualVectorAt`, `traceMetricVariationAt`,
  `metricVariationRicciPairingAt`, `covTensor2DerivAt`,
  `tensorDivergenceOneFormAt`, and `tensorDoubleDivergenceAt`.
- Sanity lemmas proved: additivity, homogeneity, and zero for
  `traceMetricVariationAt`; additivity, homogeneity, and zero for
  `metricVariationRicciPairingAt`; zero lemmas for `covTensor2DerivAt`,
  `tensorDivergenceOneFormAt`, and `tensorDoubleDivergenceAt`.
  I did not state fake unconditional additivity/homogeneity lemmas for the
  divergence/double-divergence in the raw `h : ∀ y, TM y → TM y → ℝ` argument:
  those need linearity of `extDerivFun` under differentiability hypotheses.
- Verified: `lake build Poincare.Global.ScalarVariation` succeeds after the
  vocabulary commit.
- Blocked for `hCurv`: the model path is
  `hasDerivAt_coordCurvatureOp` followed by
  `curvatureDerivOp_eq_covDeltaGamma`, but the closed layer currently only has
  `ConnectionValueTimeDifferentiableAt` for pointwise connection values.  That
  is not enough to differentiate the defining closed curvature expression
  termwise, because the proof also needs time differentiability of the iterated
  connection-value paths
  `fun t => (gt t).leviCivita (fun y => (gt t).leviCivita ...) x ...` and the
  commutation data that identifies the time derivative of spatial covariant
  derivatives with `covDeltaGammaDerivAt`.  Discharging `hCurv` honestly should
  therefore either port the model's coordinate proof into a chart-transport
  theorem for closed metrics, or strengthen the closed hypotheses with those
  mixed time/spatial differentiability facts and then prove the cancellation
  computation.
- Subtask 5 assessment: `einstein_tensor_divergence_free_of_contDiff` exists in
  `ModelLaplacian.lean` for coordinate metrics.  Reusing it for the closed
  Lichnerowicz/Ricci-flow layer requires a chart-transport bridge identifying
  closed `ricciAt`, `scalarAt`, the divergence of Ricci, the metric trace, and
  the raised double-divergence vocabulary with the model objects under a chart.
  Existing Levi-Civita transport lemmas identify connection values, but there
  is no turnkey closed contracted-Bianchi wrapper yet.  This is likely a
  dedicated chart-transport task or a native manifold Bianchi proof.

Remaining work, with exact Lean statement targets:

1. Completed in `M3-scalar-variation-2`: component Ricci-to-endomorphism lift:
   `theorem ricciEndoHasDerivAt_of_ricciBilinearHasDerivAt ... : ClosedSmoothRiemannianMetric.RicciEndoHasDerivAt gt t₀ x A'`
   where the hypotheses are pointwise `HasDerivAt (fun t => (gt t).ricciAt x u w) ... t₀` plus differentiability of the metric dual/inverse.
2. Completed in `M3-scalar-variation-2`: second-slot tensoriality of the connection variation:
   `theorem deltaGammaAt_add_right (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x) (v w w' : TM x) : deltaGammaAt gt t₀ x v (w + w') = deltaGammaAt gt t₀ x v w + deltaGammaAt gt t₀ x v w'`
   after establishing linearity of the canonical `extend` section, or replacing it with a tensorial local-frame definition.
3. Partially completed in `M3-scalar-variation-2`: connect `deltaGammaAt` to Ricci variation:
   `theorem ricciVariation_eq_deltaGamma_contractions ... : HasDerivAt (fun t => (gt t).ricciAt x u w) (deltaRicciAt gt t₀ x u w) t₀`
   mirroring `ricciDeriv_eq_deltaGamma_contractions` and `hasDerivAt_coordRicci`.
   Remaining refinement: discharge the explicit curvature-variation hypothesis
   from time differentiability of the Levi-Civita connection/curvature.
4. Completed in `M3-scalar-variation-3`: define the closed double-divergence vocabulary:
   `noncomputable def tensorDoubleDivergenceAt (g : ClosedSmoothRiemannianMetric n M) (h : ∀ y, TM y → TM y → ℝ) (x : M) : ℝ`
   as the trace of the covariant divergence of the raised metric-variation tensor,
   plus `traceMetricVariationAt` and `metricVariationRicciPairingAt`.
5. State and prove the Lichnerowicz scalar variation formula:
   `theorem scalarVariation_lichnerowicz_shape ... : deriv (fun t => (gt t).scalarAt x) t₀ = tensorDoubleDivergenceAt (gt t₀) h x - (gt t₀).laplacianAt (fun y => traceMetricVariationAt (gt t₀) h y) x - metricVariationRicciPairingAt (gt t₀) h x`
   matching the model `lichnerowiczLaplacian_*` and `g_covDeltaGammaDeriv_lichnerowicz` route.
6. Specialize the formula to Ricci flow:
   `theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation ... : IsClosedRicciFlowSolutionAt gt t₀ x -> SatisfiesHamiltonScalarEvolutionAt gt t₀ x`
   by substituting `timeDerivAt gt t₀ x = -2 Ric` and using the closed Bianchi identity, as in `hamilton_scalar_evolution_of_bianchi`.

Status from task `M3-scalar-variation-5`:

- Done: added verified theorem `scalarVariation_lichnerowicz_shape` in
  `Poincare/Global/ScalarVariation.lean`.  It assembles the existing scalar
  derivative trace theorem with the Lichnerowicz RHS vocabulary and uses
  `h = timeDerivAt gt t₀`.
- The theorem keeps two explicit open obligations, both used in the proof:
  `hRaiseTrace`, identifying the derivative of metric raising with
  `-metricVariationRicciPairingAt`, and `hDeltaGammaTrace`, identifying the
  raised `deltaRicciAt` trace with `tensorDoubleDivergenceAt - laplacianAt
  (traceMetricVariationAt ...)`.
- The closed `deltaGamma_koszul` master identity and its inner-trace
  contractions remain the real next proof target.  The current theorem is the
  honest assembly point they should discharge, mirroring the model chain
  `deltaGamma_innerTrace_eq` ->
  `ricciDeriv_raised_trace_contracted_lichnerowicz`.
- Verified: `lake build Poincare.Global.ScalarVariation` succeeds after this
  assembly theorem.

Status from task `M3-scalar-variation-7`:

- Done: added verified trace-unpack lemmas
  `trace_metricRaise_ricciDerivativeDualContinuousAt`,
  `trace_metricRaise_deltaRicciAt_eq_sum`, and
  `deltaRicciAt_raised_trace_eq_deltaGamma_contractions`.  These expose the
  current `hDeltaGammaTrace` LHS as the explicit raised-basis sum of
  `deltaRicciAt`, then split that sum into the two `δΓ` contractions from the
  definition of `deltaRicciAt`.
- Done: added verified `deltaGamma_innerTrace_eq`, contracting
  `deltaGamma_koszul` over `(eᵢ, ♯eⁱ)` and proving the algebraic collapse to
  `div h - 1/2 d(tr h)`.  It carries exactly two named first-order trace
  obligations: `hTraceSwap` (contracted derivative/first-slot swap) and
  `hTraceDeriv` (contracted `∇h` trace equals derivative of `tr_g h`).  Both
  are used directly; they are the next metric-compatibility facts to port,
  not curvature commutation facts.
- Verified: `lake build Poincare.Global.ScalarVariation` succeeds after these
  lemmas.

Status from task `M3-scalar-variation-8`:

- Done: added verified fiberwise linear-algebra theorem
  `sum_metricDualVectorAt_contraction_swap`, the closed `hTraceSwap` adapter,
  and the exact obligation predicate `CovTensor2DerivTraceSwapAt`.
  The adapter proves the trace swap from slot-linearity of
  `covTensor2DerivAt`; discharging that slot-linearity from spatial
  differentiability of the metric variation remains analytic regularity work.
- Done: named the exact `hTraceDeriv` obligation as
  `TraceMetricVariationDerivAt`, with verified zero sanity lemma
  `traceMetricVariationDerivAt_zero`.  The fully analytic proof still needs
  a smooth-varying-frame/metric-compatibility bridge for differentiating
  `traceMetricVariationAt`.
- Done: added `deltaGamma_innerTrace_eq'`, restating the inner trace using
  the named trace regularity predicates.
- Done: added divergence assembly predicates
  `DeltaGammaDivergenceTraceAssemblyAt` and
  `DeltaGammaContractionTraceAssemblyAt`, proved
  `deltaRicciAt_raised_trace_eq_doubleDivergence_sub_laplacian`, proved
  `hDeltaGammaTrace`, and added final wrapper
  `scalarVariation_lichnerowicz` under those two exact divergence sub-identities.
- Verified: `lake build Poincare.Global.ScalarVariation` succeeds after the
  divergence assembly and final wrapper.

Status from task `M3-predicates-1`:

- Done: added honest closed regularity vocabulary for the first-order
  `covTensor2DerivAt` slot-linearity proof:
  `Tensor2AddLeft`, `Tensor2SMulLeft`, `Tensor2AddRight`,
  `Tensor2SMulRight`, and `CovTensor2ExtDifferentiableAt`.
- Done: proved additivity and homogeneity of `covTensor2DerivAt` in the
  derivative slot and both tensor slots under those hypotheses:
  `covTensor2DerivAt_add_deriv`, `covTensor2DerivAt_smul_deriv`,
  `covTensor2DerivAt_add_left`, `covTensor2DerivAt_smul_left`,
  `covTensor2DerivAt_add_right`, and `covTensor2DerivAt_smul_right`.
- Done: discharged `CovTensor2DerivTraceSwapAt` from those hypotheses via
  `covTensor2DerivTraceSwapAt_of_regular`; for metric variations, the
  fiberwise bilinearity side conditions are discharged from
  `TimeDifferentiableAt` by `covTensor2DerivTraceSwapAt_timeDeriv_of_regular`,
  leaving only the scalar-field differentiability hypothesis
  `CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x`.
- Done: propagated this to `deltaGamma_innerTrace_eq_of_covTensor2Regular`,
  eliminating the `hTraceSwap` argument from the inner-trace wrapper.  The
  remaining input is the genuine trace-commutation predicate
  `TraceMetricVariationDerivAt`.
- Done: added satisfiability witnesses for the new regularity and trace
  predicates in the zero/static case, including
  `covTensor2DerivTraceSwapAt_zero` and
  `traceMetricVariationDerivAt_const_timeDeriv`.
- Blocked for full nonzero `TraceMetricVariationDerivAt`: the closed layer
  still lacks a spatial analogue of the existing time `metricRaiseDerivAt`
  machinery, i.e. a smooth raised-basis vector-field derivative theorem for
  `y ↦ metricDualVectorAt g y ((Module.finBasis ℝ (TM y)).coord i)` and its
  metric-compatibility cancellation against the Levi-Civita correction terms.
  The model proof `fderiv_tensorMetricTrace_eq` uses exactly this inverse-raise
  derivative plus Christoffel cancellation; the closed vocabulary currently
  only has the time-raise derivative, not the needed spatial moving-frame
  bridge.
- Verified: `lake build Poincare.Global.ScalarVariation
  Poincare.Global.ScalarEvolution` succeeds after these changes.

Status from task `M3-predicates-5`:

- Done: added the fixed-vector spatial regularity vocabulary
  `VariationSpatiallyDifferentiableAt`, plus the time-variation specialization
  `TimeVariationSpatiallyDifferentiableAt` and the adapter
  `variationSpatiallyDifferentiableAt_timeDeriv_of_regular`.
- Done: added satisfiability witnesses for static/zero fields and static metric
  time derivatives:
  `variationSpatiallyDifferentiableAt_static`,
  `variationSpatiallyDifferentiableAt_zero`,
  `timeVariationSpatiallyDifferentiableAt_const`, and
  `variationSpatiallyDifferentiableAt_const_timeDeriv`.
- Blocked for nonzero `TraceMetricVariationDerivAt`: the remaining honest proof
  is the chart transport bridge from closed `traceMetricVariationAt` and
  `covTensor2DerivAt` to the model `tensorMetricTrace`/`covTensor2Deriv`
  theorem `fderiv_tensorMetricTrace_eq`.  The model cancellation is already
  proved, but the closed file still lacks the theorem identifying the canonical
  Levi-Civita/canonical-extension expression with the chart-model expression.

Status from task `M3-predicates-6`:

- Done: added native closed spatial metric-compatibility vocabulary:
  `spatialMetricDerivAt` and `spatialMetricDerivAt_eq_leviCivita`.  This avoids
  the prior closed-to-model route and states `∂ᵥ g(p,q)` directly in the
  canonical-extension connection vocabulary used by `covTensor2DerivAt`.
- Done: added native closed inverse-raise cancellation algebra:
  `leviCivitaRightCovectorLinearAt`, `leviCivitaRightCovectorAt`,
  `spatialMetricDualVectorDerivAt`, and
  `spatialMetricDualVectorDerivAt_inner_apply`.  The last theorem proves that
  pairing the candidate spatial derivative of `♯φ` with `g` gives
  `-∂ᵥ g(♯φ,-)`, matching the metric-compatibility cancellation used in the
  model proof.
- Still blocked for full nonzero `TraceMetricVariationDerivAt`: the remaining
  closed theorem is not the old model-transport bridge, but an actual manifold
  derivative/product-rule layer showing that
  `y ↦ metricDualVectorAt g y φ` has derivative
  `spatialMetricDualVectorDerivAt g x v φ`, and that
  `VariationSpatiallyDifferentiableAt h x` plus slot-linearity feeds the
  canonical-extension derivative in `covTensor2DerivAt`.
- Verified: `lake env lean Poincare/Global/ScalarVariation.lean` and
  `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`
  both succeed after these native lemmas.

Status from task `M3-predicates-12`:

- Done: abandoned the raw constant tangent-section route and added the
  canonical-extension Gram matrix:
  `gramMatrix`, `gramMatrix_at_base`, `gramMatrix_at_base_det_ne_zero`,
  `gramMatrix_at_base_isUnit`, and `gramMatrix_entry_mdiffAt`.
- Done: proved local invertibility and inverse-entry differentiability:
  `gramMatrix_det_mdiffAt`, `gramMatrix_eventually_isUnit`,
  `gramMatrix_adjugate_entry_mdiffAt`, and
  `gramMatrix_inv_entry_mdiffAt`.
- Done: constructed the canonical extension frame basis from Gram
  invertibility:
  `gramFrame`, `gramFrame_linearIndependent_of_isUnit`, and
  `gramFrameBasis`.
- Done: proved the raised-dual coframe formula and Gram-inverse trace identity:
  `metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv` and
  `traceMetricVariationAt_eq_sum_gram_inv`.
- Done: proved the scalar differentiability half of the Gram route:
  `traceMetricVariationAt_mdiffAt_of_covTensor2ExtDifferentiableAt` and
  `traceMetricVariationAt_extDerivFun_eq_gram_rhs`.
- Still blocked for full nonzero `TraceMetricVariationDerivAt`: the scalar
  functions are now differentiable, but the remaining proof is the explicit
  product-rule expansion of the Gram RHS plus the covariant cancellation of
  inverse-Gram derivative terms against the Levi-Civita corrections in
  `covTensor2DerivAt`.  See `M3-predicates-12_blocked.md` for the exact reduced
  goal.

Status from task `M3-predicates-14`:

- Done: proved the finite-dimensional inverse-Gram derivative identity via
  differentiating `(gramMatrix g x y)⁻¹ * gramMatrix g x y = 1`, exposed as
  `gramMatrix_inv_extDerivFun_eq_neg_sum`.
- Done: proved the displayed inverse-Gram cancellation from
  `M3-predicates-13_blocked.md` as
  `gram_inv_deriv_contraction_eq_leviCivita_corrections`.
- Done: added the fixed-frame product contraction
  `gram_h_extDerivFun_contraction_eq_covTensor2DerivAt_add_corrections` and the
  direct trace bridge
  `traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt`, so the
  Gram-RHS product rule plus the inverse-Gram cancellation now discharge
  `TraceMetricVariationDerivAt`.
- Verified: `lake build Poincare.Global.ScalarVariation` succeeds.  The build
  reports only existing linter warnings.

Status from task `M3-predicates-15`:

- Done: propagated the discharged Gram-route theorem
  `traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt` to the
  time-variation case as
  `traceMetricVariationDerivAt_timeDeriv_of_covTensor2ExtDifferentiableAt`.
  This gives the inner-trace wrapper
  `deltaGamma_innerTrace_eq_of_covTensor2ExtDifferentiableAt`, so the first
  contraction no longer needs the older trace-product/cancellation inputs once
  `CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x` is available.
- Done: proved the linear-algebraic Laplacian trace bridge
  `laplacianAt_eq_sum_hessianAt`, exposing `laplacianAt` as the finite raised
  trace of `hessianAt` in the same basis/dual-basis vocabulary used by the
  divergence assemblies.
- Partial/fallback: the two named general assemblies
  `DeltaGammaDivergenceTraceAssemblyAt` and
  `DeltaGammaContractionTraceAssemblyAt` are not fully discharged.  The exact
  remaining second-derivative obligations are now named as
  `DeltaGammaDivergenceTraceHessianAssemblyAt` and
  `DeltaGammaContractionTraceHessianAssemblyAt`; verified adapters
  `deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly` and
  `deltaGammaContractionTraceAssemblyAt_of_hessianAssembly` convert them to the
  original target predicates using only `laplacianAt_eq_sum_hessianAt`.
- Done: added Hessian-assembly consumer wrappers:
  `deltaRicciAt_raised_trace_eq_doubleDivergence_sub_laplacian_of_hessianAssemblies`,
  `hDeltaGammaTrace_of_hessianAssemblies`, and
  `scalarVariation_lichnerowicz_of_hessianAssemblies`; and the Hamilton-side
  package/adapters `HamiltonScalarEvolutionHessianPredicatesAt`,
  `hamiltonScalarEvolutionPredicatesAt_of_hessianPredicates`,
  `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_hessian_variation`, and
  `hamiltonScalarEvolutionProgram_of_hessianPredicates`.
- Exact next proof state: prove the two Hessian-trace assemblies by expanding
  `covDeltaGammaDerivAt` and differentiating the already-propagated
  `δΓ` trace identities; after that the original assembly predicates and
  `scalarVariation_lichnerowicz` follow by the adapters above.
- Verified: `lake build Poincare.Global.ScalarVariation
  Poincare.Global.ScalarEvolution` succeeds.  The build reports only existing
  linter warnings.

Status from task `M3-predicates-16`:

- Done in commit `dae985db`: added the closed first-slot trace theorem
  `deltaGamma_firstSlot_trace_eq_of_covTensor2ExtDifferentiableAt`, plus the
  supporting symmetry lemma `covTensor2DerivAt_timeDeriv_symm`.  This proves
  the first-order identity `Σᵢ eⁱ(δΓ(eᵢ,w)) = 1/2 d(tr_g h)(w)` from the
  existing Koszul identity, trace-swap adapter, and discharged Gram-route
  `TraceMetricVariationDerivAt`.
- Done in commit `dae985db`: introduced the honest second-order bridge
  `DeltaGammaContractionTraceHessianDerivativeAt` and proved
  `deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative`,
  so `DeltaGammaContractionTraceHessianAssemblyAt` is discharged once the
  trace-form covariant derivative is identified with the Hessian.
- Done in commit `49f483db`: introduced the honest divergence-side
  second-order bridge `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` and
  proved `deltaGammaDivergenceTraceHessianAssemblyAt_of_innerHessianDerivative`,
  recognizing the explicit covariant divergence sum as
  `tensorDoubleDivergenceAt` and the scalar trace part as the Hessian trace.
- Done after those commits: added downstream cleaned wrappers
  `scalarVariation_lichnerowicz_of_traceHessianDerivatives`,
  `HamiltonScalarEvolutionTraceDerivativePredicatesAt`,
  `hamiltonScalarEvolutionHessianPredicatesAt_of_traceDerivativePredicates`,
  `hamiltonScalarEvolutionPredicatesAt_of_traceDerivativePredicates`,
  `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_trace_derivative_variation`,
  and `hamiltonScalarEvolutionProgram_of_traceDerivativePredicates`.
- Exact next proof state: discharge the two second-order field-derivative
  bridges `DeltaGammaContractionTraceHessianDerivativeAt` and
  `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` from a genuine
  differentiability theorem for the closed `δΓ` trace-form fields.  The
  frozen Hessian assembly predicates now follow from those bridge facts by
  verified adapters.
- Verified: `lake build Poincare.Global.ScalarVariation
  Poincare.Global.ScalarEvolution` succeeds.  The build reports only existing
  linter warnings.

Status from task `M3-predicates-17`:

- Done: added the C² scalar-entry vocabulary needed by the Gram route one
  derivative higher:
  `CovTensor2ExtSecondDifferentiableAt`, `MetricExtSecondDifferentiableAt`,
  and `TimeVariationExtSecondDifferentiableAt`.  The time-variation zero/static
  witness is verified as `timeVariationExtSecondDifferentiableAt_const`, with
  the raw zero tensor witness `covTensor2ExtSecondDifferentiableAt_zero`.
- Done: named the two actual closed `δΓ` trace-form fields as
  `deltaGammaFirstSlotTraceFieldAt` and `deltaGammaInnerTraceFieldAt`, plus
  their differentiability predicates
  `DeltaGammaFirstSlotTraceFieldDifferentiableAt` and
  `DeltaGammaInnerTraceFieldDifferentiableAt`.
- Done: added field-derivative adapter predicates
  `DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt`,
  `DeltaGammaFirstSlotTraceFieldHessianAt`, and
  `DeltaGammaInnerTraceFieldCovariantDerivativeAt`, with verified adapters
  `deltaGammaContractionTraceHessianDerivativeAt_of_firstSlotTraceField` and
  `deltaGammaDivergenceTraceInnerHessianDerivativeAt_of_innerTraceField` into
  the frozen bridge predicates.
- Done: proved static sanity witnesses for both frozen bridges:
  `deltaGammaContractionTraceHessianDerivativeAt_const` and
  `deltaGammaDivergenceTraceInnerHessianDerivativeAt_const`, using the new
  static reductions
  `covDeltaGammaDerivAt_const`, `deltaGammaDivergenceAt_const`, and
  `deltaGammaContractionDerivAt_const`.
- Remaining non-static goal: prove the new trace-field derivative predicates
  from the Gram RHS near `x`, using the C² scalar-entry hypotheses and the same
  inverse-Gram cancellation pattern as the first-order trace proof.  This is now
  isolated from the frozen Hamilton consumers: once those field predicates are
  proved, the existing adapters discharge
  `DeltaGammaContractionTraceHessianDerivativeAt` and
  `DeltaGammaDivergenceTraceInnerHessianDerivativeAt`.
- Verified: `lake build Poincare.Global.ScalarVariation
  Poincare.Global.ScalarEvolution` succeeds.  The build reports only existing
  linter warnings.

Status from task `M3-predicates-22`:

- Done: added the δΓ scalar-entry derivative bridge vocabulary
  `DeltaGammaEntryDerivativeBridgeAt`, with static witness
  `deltaGammaEntryDerivativeBridgeAt_const`.  The bridge states the exact
  derivative of
  `y ↦ g(δΓ_y(extend p, extend w), extend q)` as
  `g(covDeltaGammaDerivAt ..., q)` plus the three Levi-Civita slot
  corrections.
- Done: proved
  `deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_of_entryBridge`.  For
  fixed `w`, the proof packages
  `hδ_y(p,q) = g(δΓ_y(p, extend w), q)` as a bilinear scalar tensor, uses the
  existing Gram/product-rule trace derivative theorem, and identifies the
  covariant derivative of `hδ` through the new entry bridge.
- Done: added contraction-side cascade wrappers
  `deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_trace_extSecond`
  and
  `deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_entries_contMDiffAt`.
  These feed the new first-slot field theorem into the existing Hessian
  adapter, discharging `DeltaGammaContractionTraceHessianDerivativeAt` from the
  δΓ-entry bridge plus the already-recorded trace C² data.
- Verified: `lake build Poincare.Global.ScalarVariation
  Poincare.Global.ScalarEvolution` succeeds.  The build reports only existing
  linter warnings.

Status from task `M3-predicates-24`:

- Done: added the lower-slot inner-trace anchored Gram infrastructure
  `deltaGammaInnerTraceFieldAt_eq_trace_in_basis` and
  `deltaGammaInnerTraceFieldAt_eq_sum_gram_inv`.
- Done: recorded that the inner-trace entries are the same scalar
  `g(δΓ(extend p, extend q), extend w)` entries handled by the existing
  `DeltaGammaEntryDerivativeBridgeAt`, via
  `deltaGammaInnerTraceEntry_mdiffAt_of_entryBridge` and
  `deltaGammaInnerTraceEntry_extDeriv_eq_of_entryBridge`.
- Done: proved the verified derivative reduction
  `deltaGammaInnerTraceFieldDerivativeTraceAt_of_entryBridge`, identifying the
  covariant derivative of the moving inner-trace field with
  `Σᵢ g((∇_u δΓ)(eᵢ,eⁱ), w)` after the expected test-slot Levi-Civita
  correction is subtracted.
- Blocked: the frozen target
  `DeltaGammaInnerTraceFieldCovariantDerivativeAt` needs the different cyclic
  divergence trace `Σᵢ g((∇_{eᵢ} δΓ)(w,u), eⁱ)`.  No existing theorem derives
  the required cyclic trace identity for `covDeltaGammaDerivAt` from the
  current regularity and scalar-entry bridge hypotheses.
- M3-predicates-28 correction: the frozen pointwise target
  `DeltaGammaInnerTraceFieldCovariantDerivativeAt` is false in the flat
  2-torus model with `h_11 = cos y`, evaluated at `y = 0` and `u = w = e_1`.
  Its left side is the divergence-order trace
  `Σᵢ ∂ᵢ δΓⁱ_11 = 1/2`, while its right side is the derivative of
  `div h - 1/2 d tr(h)`, which is `0`.  The valid route is to bypass this
  pointwise predicate and prove the summed divergence trace directly from
  `covDeltaGamma_koszul`, targeting
  `DeltaGammaDivergenceTraceHessianAssemblyAt` or a direct proof of the summed
  `DeltaGammaDivergenceTraceInnerHessianDerivativeAt`.
- Exact remaining non-regularity predicate list:
  direct `DeltaGammaDivergenceTraceHessianAssemblyAt` (or direct summed
  `DeltaGammaDivergenceTraceInnerHessianDerivativeAt`),
  `TensorDoubleDivergenceTimeDerivNegTwoRicciAt`,
  `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt`,
  `TensorDoubleDivergenceNegTwoRicciLinearityAt`, and
  `ClosedContractedBianchiAt`.
- Verified so far: `lake env lean Poincare/Global/ScalarVariation.lean`
  succeeds with existing linter warnings and `simp` suggestions only.
