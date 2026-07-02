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
4. Define the closed double-divergence vocabulary:
   `noncomputable def tensorDoubleDivergenceAt (g : ClosedSmoothRiemannianMetric n M) (h : ∀ y, TM y → TM y → ℝ) (x : M) : ℝ`
   as the trace of the covariant divergence of the raised metric-variation tensor.
5. State and prove the Lichnerowicz scalar variation formula:
   `theorem scalarVariation_lichnerowicz_shape ... : deriv (fun t => (gt t).scalarAt x) t₀ = tensorDoubleDivergenceAt (gt t₀) h x - (gt t₀).laplacianAt (fun y => traceMetricVariationAt (gt t₀) h y) x - metricVariationRicciPairingAt (gt t₀) h x`
   matching the model `lichnerowiczLaplacian_*` and `g_covDeltaGammaDeriv_lichnerowicz` route.
6. Specialize the formula to Ricci flow:
   `theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation ... : IsClosedRicciFlowSolutionAt gt t₀ x -> SatisfiesHamiltonScalarEvolutionAt gt t₀ x`
   by substituting `timeDerivAt gt t₀ x = -2 Ric` and using the closed Bianchi identity, as in `hamilton_scalar_evolution_of_bianchi`.
