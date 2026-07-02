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
