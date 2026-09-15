# Hamilton residual estimates survey

Date: 2026-09-15. Base: `2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df`.

> Orchestrator note (2026-09-15): this landed copy keeps sections 1-5, Appendix C6 (the compiled Eta-only scratch program) and Appendix D (exact registration expressions) from the worker report. Appendices A-B, C1-C5 and any later evidence stay unmerged on branch `worker/hamilton-residual-estimates-survey` at its head commit because of their size.

Branch: `worker/hamilton-residual-estimates-survey`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

The survey is complete. The residual estimates are not proved. Eleven named scratch theorems are compiled and reproduced here, including a construction of the unchanged `HamiltonReactionCore3Final` from the uniform `Eta` gap alone, with the retained compact realization, flow and initial pinching. No repository Lean file was added, edited, or deleted.

The main findings are:

- The literal normalized estimate `|∇R|² ≤ η R³ + Cη` already follows from the retained compact third-jet realization. A scratch proof even supplies one additive constant for every nonnegative η. This is not the scale-effective gradient estimate needed to make the scalar ratio converge to one.
- The preserved quotient constant need not permit a strict reaction gap even when the scalar ratio is one. At initial pinching `epsilon = 1/4`, the largest permitted `delta = 2/9` gives zero gap at `C = 1`.
- `V ≤ 6E` is precisely the nonnegative-mean-derivative condition in dimension three. It is not the general almost-Schur inequality. The sharp general comparison under nonnegative Ricci is `V ≤ 24E`, with violations of smaller constants among small perturbations of the round sphere.
- The Bianchi/Poincaré chain proposed in the task leaves a derivative energy on its right side, not `E`. There is no verified closed-manifold Poincaré inequality or first-eigenvalue theorem in the searched source. There is a genuine coordinate Bochner inequality, whose full signature is printed below.
- Keep the existing frozen core unchanged. A uniform `Eta` gap alone replaces both analytic residuals in a sufficient route to the final core: its nonnegative Ricci term immediately gives `r≥3*eta/4>0`, and the landed reaction theorem gives rate eta. Both deductions and the full final-core construction compile. No separate R2 or tail floor is needed.

The scope-specific worker contract overrides the generic branch naming and HANDOFF-edit instructions. Only this report is delivered. Frozen contracts, missions, ledgers, HANDOFF, and the root import are unchanged. The worker has not accepted or merged the result. This survey does not establish existence of positively pinched initial data, a global flow, or its compact realization on every manifold.

## 1. Landed inventory and probed signatures

### 1.1 Notation and exact current boundary

On a slice write `R(x) = g.scalarAt x`, `r = meanScalar g`, `N(x) = g.ricciNormSqAt x`, and `U(x) = g.tracelessRicciNormSqAt x`. Set `E = ∫ U dμg` and `V = ∫ (R-r)² dμg`. These are unnormalized integrals. The exponent in `R ^ (2-delta)` is real power; `R ^ 2` is the natural square. Positivity is supplied before division or comparison of powers.

The current core is exactly `Poincare.HamiltonStokesFreeReactionCore.HamiltonReactionCore3InitialPinchingNS`. Its printed expansion retains the compact parameter space, continuous orbit parameter, actual metric realization, continuous complete third-jet profiles, all-real-time joint C³ entries, the forward normalized flow, initial scalar positivity, `1/6 < epsilon ≤ 1/3`, the initial eigenbasis floor, and `0 < delta ≤ 1` admissible for `2*epsilon-1/3`. Its last clauses are exactly R2, R1, and the coefficient gap specified in the task. The complete expansion and the endpoint consumer are in Appendix B.

`GlobalRicciEigenvalueFloor3` is an eigenbasis statement. `GlobalPinchingQuotientBound3 g kappa` bounds the ordinary quotient `N/R²`, not the traceless quotient. The preserved coefficients are

```text
e = 2*epsilon - 1/3
kappa = 1 - 4*epsilon + 6*epsilon²
deltaMax(e) = 6*e² / (1 - 2*e + 3*e²).
```

The exact registered parent in `harness/v2/missions/hamilton-front.json` is `hamilton-reaction-core-stokes-free`, with intended declaration `Poincare.universal_hamilton_reaction_core_stokes_free` and expected type `Poincare.HamiltonStokesFreeReactionCore.UniversalHamiltonReactionCoreInitialPinchingNSStatement`. The mission marks this as an obligation, not a checked theorem. This report does not register child obligations. Section 4 gives exact elaborated residual expressions for the orchestrator to use in a reviewed decomposition.

### 1.2 Relevant source and what it actually supplies

Every name in this table was found in source and printed by Lean. `Poincare.` is omitted in the table unless another namespace is required. Appendix B has full universe parameters, instances, hypotheses, and definitions.

| Source | Probed declaration | Content and limitation |
| --- | --- | --- |
| `NormalizedFlowInitialPinchingPreservation` | `NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos` | Initial positivity persists at each forward time; no uniform positive numerical floor is concluded. |
| Same | `initial_pinching_preserved` in that namespace | Forward eigenfloor `2*epsilon-1/3` and quotient bound `1-4*epsilon+6*epsilon²`. |
| Same | `initial_pinching_improvement` in that namespace | Improved quotient maximum is bounded by its initial value. It is not a gradient estimate or a decay theorem. |
| `NormalizedFlowImprovedPinchingDecay` | `tracelessPinchingAt_le_tracelessPinchingMaximumTrack` | Point value below the maximum, assuming spatial C² of the quotient. |
| Same | `ClosedSmoothRiemannianMetric.pinchingQuotientAt_sub_one_third_eq_relativeTracelessRicciAt` | `Q - 1/3 = U/R²` for positive scalar. |
| Same | `pinchingQuotientAt_eventually_uniformly_close_one_third_of_improvedMaximum_of_scalarProfile_atTop` | Requires a positive scalar lower profile tending to infinity. It concerns the Ricci quotient, not scalar max/min. This hypothesis is incompatible with a uniformly bounded normalized scalar orbit. |
| Same | `tracelessPinchingAt_eventually_uniformly_small_of_hamilton_forward_improvement_of_integrableMaximum` | Requires integrability of the improved maximum. Cannot use it to prove energy decay without first proving that input. |
| `ScalarEvolution` | `ClosedSmoothRiemannianMetric.scalarGradNormSqAt_le_three_covRicciNormSqAt` | `|∇R|² ≤ 3|∇Ric|²`. No η, scalar cubic bound, or time decay. |
| `RicciNorm` | `ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq` | `U=N-R²/n`; dimension three gives the requested orthogonal decomposition. |
| `ScalarVariation` | `eventually_closedContractedBianchiOneFormAt_canonical` | Actual canonical one-form Bianchi, locally `div Ric = (1/2)dR`. It is proved, despite older source comments describing an obligation. |
| Same | `tensorDivergenceOneFormAt_scalar_metric` | `div(fg)=df`, with manifold differentiability of f. |
| Same | `closedContractedBianchiAt_canonical` | Double-divergence identity with explicit scalar regularity. Distinguish it from one-form Bianchi. |
| `NormalizedFlowEnergyConcentrationCurvatureDerivative` | `tracelessCovRicciNormSqAt` | Defined as `|∇Ric|²-|∇R|²/n`. It is a derivative energy, not U. |
| Same | `extDerivFun_tracelessRicciNormSqAt_eq_two_tracelessCovRicciRicciPairingAt` | Derivative of U is twice the traceless contraction. Does not estimate the scalar variance by E. |
| `ClosedMetricThirdJetTopology`, `ClosedMetricThirdJetOrbitCompactness` | `continuous_closedMetricFamily_of_entryThirdJetProfileJointContinuous`, `isCompact_closedMetricThirdJetOrbitClosure_of_compact_realization`, `exists_uniformCovariantRicciDerivativeNormBound_of_compact_closedMetricThirdJetOrbitClosure` | The retained compact realization supplies a genuine uniform full covariant-Ricci derivative bound. Scratch item 2 below contracts this into an additive scalar-gradient bound. |
| `NormalizedFlowEnergyConcentrationLipschitzBridge` | `uniformClosedRiemannianLipschitzBound_of_mfderivBound` | Derivative-to-path/Lipschitz conversion with its actual uniform derivative premise. It is not Bonnet–Myers or Hamilton's gradient estimate. |
| `ScalarEvolution` | `scalarMinimumAt`, `scalarMinimumTrack`, `exists_scalarAt_isMinOn`, `scalarMinimumAt_le_scalarAt` | Minimum is an infimum, attained under the printed regularity/compactness hypotheses. No ordinary derivative of the minimum track is asserted. |
| `ScalarMeanLowerBound` | `le_meanScalar_of_forall_le_scalarAt`, `meanScalar_le_of_forall_scalarAt_le` | Integrate a pointwise lower or upper bound; useful for max/min-to-mean conversion. |
| `NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient` | `exists_pos_uniform_abs_scalarAt_bound_of_compact_joint_scalar` | A finite scalar upper bound on a compact family. No smallness relative to r. |
| `NormalizedFlowCompactScalarMeanComparison` | `exists_pos_uniform_scalarAt_le_mul_meanScalar_of_compact_parameterization_of_meanLower` | Gives some `C>0`, constructed as `S/rho`, from compact realization and a positive mean floor. Gives no strict coefficient gap. |
| `NormalizedFlowScalarVarianceConcentration` | `scalarAt_sub_meanScalar_eventually_uniformly_small_of_variance_tendsto_zero`, `scalarAt_eventually_gt_half_of_centeredScalar_uniform_decay_of_meanLower` | Uniform scalar oscillation and positivity consumers; the printed premises include variance decay, concentration controls, or a positive mean floor. They do not produce those inputs. |
| `NormalizedFlowCompactScalarVarianceContinuity`, `HausdorffScalarVarianceContinuity` | See filename inventory and imports in Appendix A | Time continuity/measurability and chart-density domination results, not a Poincaré inequality. |
| `NormalizedFlowScalarIntegralVariation` | `normalizedMeanScalarEnergyNumerator_three`, `hasDerivAt_meanScalar_three_of_normalizedFlow` | Exact numerator `2E-V/3` and derivative `(2E-V/3)/Vol`, with moving integral derivatives. |
| `HamiltonMeanFloorFromEnergyDomination` | `movingDerivatives`, `meanFloorFromEnergy` in its namespace | Differentiation from joint C³ and Stokes; positive nondecreasing mean from R2. |
| `IntrinsicLaplacianCoordinateForm` | `closedLaplacianStokes_scalarAt_of_normalizedRicciFlow`, `closedLaplacianStokes_of_contMDiff_two` in its namespace | Stokes now landed. Earlier reports' Stokes blocker is stale. |
| `NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination` | `meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack` | S9 consumes `V≤6E`. It does not prove that inequality. |
| `NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination` | `normalizedFlowScalarVarianceTrack_le_six_tracelessRicciEnergyTrack_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq` | Integrates a stronger pointwise inequality. Initial pinching does not give that pointwise premise. |
| `NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination` | `normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap`, `normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching` | Exact Eta and coefficient-gap consumers. |
| `NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay` | `normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici` | S6 requires one constant positive rate throughout the ray, plus the printed volume/measurability/regularity hypotheses. |
| `NormalizedFlowCompactFiniteDissipationBoundedVariation` | `normalizedFlowScalarVarianceTrack_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower_of_continuousTracks` | Finite E plus any uniform mean lower bound gives finite V. The lower bound need not be positive for this theorem. |
| Same | `normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower_of_continuousTracks` | Also gives finite absolute mean/variance dissipation, without R2 or monotone mean. The endpoint separately needs a positive mean floor. |
| `HamiltonMeanFloorReduction` | `meanScalar_floor_on_Icc_of_initial_scalar_pos` | Every finite interval has a positive floor. Quantifiers do not give an infinite-ray floor. |
| `ModelLaplacian` | `RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_eigenfunction_refined` | A genuine curved coordinate Bochner integrand for a supplied eigenfunction; all metric regularity and positivity hypotheses are printed. The doubled namespace is real. No closed integration, eigenfunction existence, or global first-eigenvalue bound is concluded. |

### 1.3 Search scope and negative findings

The filename search covered every repository Lean module containing `Gradient`, `Harnack`, `ScalarVariance`, `TracelessRicciEnergy`, `PoincareInequality`, `Bianchi`, `DivRic`, `ScalarMax`, or `Ratio`. It returned seven files, listed with declarations and imports in Appendix A. Bare `Poincare` in the thousands of endpoint filenames means the conjecture; those names do not establish a Poincaré inequality. Content searches therefore separately targeted the inequality, first eigenvalues, Poisson, Harnack, and scalar maximum/minimum/ratio terminology in the repository and pinned Mathlib.

No closed-manifold Poincaré constant producer, first-positive-eigenvalue producer, closed Poisson solver, Hamilton scalar max/min ratio theorem, or Bonnet–Myers diameter theorem was located by these searches. This is a scoped absence finding, not a Lean theorem of nonexistence. The pointwise Bochner declaration above is the closest spectral building block found. The Lichnerowicz assembly predicates in flow proofs concerns Ricci variation regularity, not a spectral gap.

The three `...MeanScalarGradient...` modules in the filename inventory are endpoint/concentration adapters with derivative hypotheses. `BianchiIdentity.lean` supplies first Bianchi for a connection; the contracted identities relevant here are in `ScalarVariation.lean`. `NormalizedFlowImprovedPinchingDecay.lean` concerns the Ricci quotient and an assumed growing scalar profile or integrable improved maximum, not `Rmax/Rmin`.

## 2. Lemma-level mathematical decomposition

A means proved now or demonstrated by a compiled scratch proof. B means a named missing geometric/analytic estimate is needed. C means a proposed implication is not established or needs its hypotheses corrected. A conditional A adapter does not turn its B input into a theorem.

### 2.1 R1: scalar comparison with a strict gap

The route should separate the unnormalized flow approaching its singular time from the normalized infinite ray. Hamilton's paper is the historical source. The requested §§11–13 cover gradient and derivative analysis; scalar ratio and normalized estimates occur later in §§15–17. The publisher endpoint was blocked during this run, so the sequence below is a mathematical reconstruction, not a claim to have verified every original lemma number or normalization convention against the PDF. [Hamilton, Three-manifolds with positive Ricci curvature](https://doi.org/10.4310/jdg/1214436922).

| Step | Class | Precise work |
| --- | --- | --- |
| R1.1 | A | Preserve the initial quotient/eigenfloor and improved maximum. `improvedPointwiseBound` proves the actual pointwise `U(t,x) ≤ F0 R(t,x)^(2-delta)` from the landed preservation theorem. |
| R1.2 | A for the literal normalized additive bound | Compact third jets give `|∇Ric|≤D`, hence `|∇R|²≤3D²`. The compiled `normalizedAdditiveGradientBoundOfCompactJets` gives `|∇R|²≤ηR³+3D²` for every η≥0 on the positive normalized orbit. This is weaker than the asymptotic input needed next. |
| R1.3 | B | First missing estimate on the historical route: **scale-effective Hamilton Bernstein scalar-gradient estimate** on an unnormalized pinched flow, with `Cη` independent of time up to the singular time. Its exact target shape is in the obligation probes. A bounded normalized additive estimate cannot replace this. The evolution of the gradient quantity, second-derivative estimates, maximum principle, and normalization transfer must use actual curvature derivatives. |
| R1.4 | B | **Scalar blow-up and rescaling transfer**: establish the unnormalized high-curvature regime and track the additive error under normalization. Under `gtilde=a*g`, `Rtilde=a⁻¹R`, `Utilde=a⁻²U`, and the squared scalar gradient scales by `a⁻³`. The additive error becomes `a⁻³Cη`. A suitable asymptotic conclusion is the probed normalized target `∀η>0, eventually ∀x, |∇R|²≤ηR³`. None of those scaling/blow-up steps is supplied merely by normalized compactness. |
| R1.5 | B | **Gradient-to-global scalar oscillation under positive Ricci pinching**. Integrate a gradient bound along metric paths, and use a minimizing-geodesic/second-variation argument in the region where scalar is close to its maximum. A global diameter bound in terms of an unknown small minimum is not a shortcut: its insertion can leave powers of the unknown max/min ratio. The searched path/Lipschitz theorem supplies a conversion once the metric derivative bound is present, not this geometric length estimate. |
| R1.6 | B then A | Missing output: **eventualScalarTwoPointComparison**, `∀z>0, ∃T≥0, ∀t≥T, ∀x y, R(t,x)≤(1+z)R(t,y)`. Once supplied, `scalarCompareOfTwoPoint` integrates it to `R≤(1+z)r` on that same tail. No need to define a new scalar maximum track for this adapter. |
| R1.7 | C without additional hypotheses | A tail comparison does not prove the frozen all-ray comparison with the same small C. Compactness of an initial time interval yields a finite comparison constant but not a suitably small one. A time-shifted/restarted core needs a separate checked flow/parameterization transport and admissible improved pinching at the restart time. |
| R1.8 | A conditional on quantitative data | `etaFromComparison` combines `Q≤kappa`, `R≤Cr`, `r≥c>0`, and `gamma=4/3-2(2-delta)kappa*C>0` into the exact all-ray Eta premise, with `eta=gamma*c`. The landed reaction theorem then applies. |

There are two separate quantitative restrictions. First, `comparisonConstantGeOne` proves that a positive mean and an all-point comparison force `C≥1`. Second, closeness to one only helps when the baseline coefficient `4/3-2(2-delta)kappa` is already positive. The exact rational calibration at `epsilon=1/4` gives `e=1/6`, `kappa=3/8`, `deltaMax=2/9`, and baseline zero. Reducing delta or increasing C worsens the gap. These are scalar coefficient computations, not a counterexample to Hamilton convergence.

Thus the first missing normalized output can be named directly as `eventualScalarTwoPointComparison`; its intended gradient proof first lacks the scale-effective estimate and its time/scale transfer. Do not dispatch “derive R1 from the additive gradient bound” as an A task. It is missing exactly the asymptotic information that the additive constant erases.

The Eta residual itself also supplies the positive mean floor, as section 3.1 proves. It is algebraically weaker than the kappa/C overestimate together with the floor used to make its rate uniform. It uses the actual `N/R` at each point. This can avoid loss from a crude fixed preserved kappa. It is not known to be analytically easier to prove on the whole ray: it still asks for a single strictly positive lower gap at every point and time. A still weaker sufficient premise is direct negative domination of the actual reaction, which retains favorable derivative terms that the Eta estimate discards. Neither of these premises follows from initial pinching in the current survey.

### 2.2 R2: exact content and the failed derivative route

Dimension three gives the following distinct statements:

```text
N = U + R²/3
(div Ric)(w) = (1/2)dR(w)
div(Ric - (R/3)g) = (1/6)dR
r' = (2E - V/3)/Vol.
```

The first, second, and fourth are landed; a direct intrinsic traceless-divergence identity needs the tensor-field subtraction/linearity assembly. The precise actual-tensor target elaborates in Appendix D. Do not replace that target by merely naming `div Ric - dR/3` and claiming it is the divergence of the actual traceless tensor.

The task's derivative chain needs correction. From the traceless Bianchi identity, `∫|∇R|² = 36∫|div Ric°|²`. Generic contraction of a three-tensor only gives the safe bound `|div T|²≤3|∇T|²`; a factor one needs additional structure and its own proof. With a Poincaré constant this route therefore gives at best

```text
V ≤ 108 CP ∫|∇Ric°|².
```

It does not give `V≤6E`, or even `V≤C E`. It still needs a reverse derivative-energy estimate `∫|∇Ric°|²≤D∫|Ric°|²`. Ordinary Poincaré controls a function by its derivative, in the opposite direction. No such uniform reverse estimate follows from a scalar spectral gap, and high-frequency perturbations are precisely a reason to avoid assuming it.

For comparison, if `Ric≥rho*g`, the usual Lichnerowicz normalization would give `lambda1≥(3/2)rho`. With `Ric≥epsilon*R*g` and a positive scalar lower bound this becomes `lambda1≥(3/2)*epsilon*Rmin`, so `CP≤2/(3*epsilon*Rmin)`. At the Einstein coefficient `epsilon=1/3`, this is `lambda1≥Rmin/2`. There is no extra universal factor making it `3Rmin/4`. These are normalizations for a prospective global spectral task; the printed coordinate Bochner result does not already prove them. A decaying Rmin also does not give a uniform CP.

The relevant literature result is the almost-Schur inequality. De Lellis–Topping prove `V≤4n(n-1)/(n-2)² E` for nonnegative Ricci; in dimension three the coefficient is 24. They prove sharpness using small conformal perturbations of the round sphere. Hence 6 is not a valid general slice bound even for metrics arbitrarily close to round and positively Ricci-pinched. Their proof solves `Δf=R-r`, uses Bianchi and integration by parts to obtain `V=6∫⟨Ric°,Hess°f⟩`, and uses integrated Bochner to bound `∫|Hess°f|²≤(2/3)V`. Cauchy–Schwarz then gives `V≤24E`. This is a literature obstruction, not a Lean-constructed counterexample in this report. [De Lellis–Topping, Almost-Schur lemma, Theorem 1.1 and §§2–3](https://www.math.ias.edu/delellis/sites/math.ias.edu.delellis/files/almost_schur.pdf).

In particular, there is no justified attribution of `V≤6E` to Hamilton here. The 6 is forced by the repository's chosen monotone-mean route, not an adjustable spectral constant. This does not refute the existing conditional S9 theorem or show the existential NS core is uninhabitable. It refutes treating R2 as an automatic consequence of general positive pinching. A selected family might satisfy R2; proving existence of such a family is a different obligation.

| Step | Class | Smallest meaningful lemma or obstruction |
| --- | --- | --- |
| R2.1 | A, landed | The norm decomposition `N=U+R²/3`, scalar integrability, and one-form contracted Bianchi. |
| R2.2 | A assembly candidate, target elaborated but proof not attempted | Divergence of the actual field `Ric-(R/3)g` equals `(1/6)dR`. Required local work is linearity in the tensor field and the scalar-metric divergence identity. No global estimate follows yet. |
| R2.3 | B | **Closed mean-zero Poisson solvability** for `Δf=R-r`, with sufficient regularity. This is the first missing analytic producer on the almost-Schur route. A full Poincaré/elliptic solvability library is one way to obtain it; no producer was found. |
| R2.4 | B | **Closed tensor integration by parts and integrated Bochner estimate** for that f. General scalar Stokes is landed, but the intrinsic tensor/Hessian integration identities and the regularity needed to apply Stokes to the gradient norm still need proof. |
| R2.5 | A after R2.3–4 | Cauchy–Schwarz and scalar arithmetic give 24. This is the correct target of that route, not 6. No new geometric theorem for 24 is claimed. |
| R2.6 | C / invalid universal inference | Replacing 24 by 6 from positive pinching or a first-eigenvalue lower bound. The sharpness result rules out this general slice claim. Do not create a proof task pretending a missing library lemma alone will establish it. |
| R2.7 | A, compiled | `meanDerivativeIffSix` proves the exact equivalence between R2 and `r'≥0`, with moving derivatives and Stokes produced from the current flow hypotheses. `meanDerivativeLowerOfConstant` gives the correct formula for any constant A. |

There are A items for both residuals, but no A item here produces either the strict all-ray R1 estimate or R2 from the retained initial-pinching assumptions alone.

## 3. Replacements and their exact limits

### 3.1 Eta alone closes the unchanged final core

This is the strongest reduction found in the survey. On a positive-scalar slice, `N≥0`, and `delta≤1` makes `2(2-delta)N/R≥0`. Hence the exact Eta residual implies

```text
eta ≤ (4/3)r, so r ≥ (3/4)eta > 0.
```

`HamiltonResidualSurvey.meanFloorFromEta` proves this using the actual Ricci norm decomposition and a point of the nonempty manifold. It does not use R2, Stokes, moving derivatives, or mean monotonicity. `HamiltonResidualSurvey.finalCoreOfEta` then takes the retained compact realization, joint third jets, forward normalized flow, initial scalar positivity, initial pinching, positive admissible delta with `delta≤1`, and only the residual

```lean
∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
  2*(2-delta)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
    (4/3 : ℝ)*meanScalar (gt t)
```

The exact tested signature exposes eta as a witness. It constructs literally `HamiltonReactionCore3Final.{u,v} M`, with mean floor `3*eta/4` and reaction rate eta. The existing endpoint theorem therefore applies. The old landed `HamiltonReactionCore3InitialPinchingEta` still includes R2 and Stokes; this new construction demonstrates that those hypotheses are unnecessary for an Eta-based sufficient route. No existing definition was changed.

Eta is still an unproved uniform analytic estimate. The simplification removes the need to prove R2 on this route; it does not prove Eta from initial pinching or merely eventual scalar-ratio closeness. A tail Eta estimate also supplies a tail mean floor, but transporting the flow and compact realization to a shifted core remains a separate task.

For alternative routes using a direct actual-reaction bound or R1 rather than Eta, the compiled `meanFloorOfTailFloor` remains useful: combine any positive tail mean floor with the landed finite-interval floor, taking the minimum of the constants. The earlier scratch `finalCoreOfEtaAndTailFloor` is retained as an intermediate verified probe. It is superseded by `finalCoreOfEta`, which removes the unnecessary tail-floor hypothesis.

### 3.2 Replacing 6 by an arbitrary constant

The compiled `meanDerivativeLowerOfConstant` says exactly

```text
V≤A E  ⇒  r' ≥ (2-A/3) E / Vol.
```

For `A≤6`, this is enough for the same monotonicity argument because E is nonnegative. At `A=24` the lower bound is `-6E/Vol`; it does not give a positive uniform mean floor. Integrating it can give one if the total possible mean loss is strictly smaller than the initial positive mean. That smallness is an additional residual, not a consequence of `A<∞`.

For finite dissipation, the situation is better. The landed bounded-variation theorem proves finite V from finite E and any mean lower bound, even without `V≤A E`. Initial scalar positivity supplies a nonnegative mean on each forward slice, which suffices for that particular integrability consumer. However, finite E still needs proof, and the positive Einstein/Hamilton endpoint still needs a uniform positive mean floor. Using R1-to-rate via such a floor, then claiming energy finiteness proves that same floor, would be circular.

Another sufficient floor residual is a strict uniform deficit budget:

```text
∃ B < 3 Vol(0) r(0), ∀ t≥0,
  ∫₀ᵗ max(V(s)-6E(s),0) ds ≤ B.
```

Together with the derivative identity it gives `r(t)≥r(0)-B/(3Vol(0))>0`. The target elaborates in Appendix D, but this integration adapter was not proved in this survey. The first probe used only a strict inequality separately for every t; it was corrected to a single uniform B. Pointwise strictness below a fixed threshold would not by itself keep a positive distance from that threshold.

### 3.3 A time-dependent reaction rate

The printed S6 theorem accepts a real constant `rate>0`. It has no time-dependent-rate parameter. A new comparison theorem might use `a(t)` and an envelope `exp(-∫₀ᵗ a)`, but finite energy then requires that envelope to be integrable. Positivity of a(t), and even divergence of its cumulative integral, do not suffice. For example, `a(t)=1/(1+t)` produces the nonintegrable envelope `1/(1+t)`. An eventually uniform positive rate is a plausible replacement after finite-prefix integration and time-shift transport are proved. None of these alternatives silently discharges the frozen S6 premise.

## 4. Numbered dispatch plan and exact open targets

### 4.1 Shared contract

All proposed tasks start from base `2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df`, or an explicitly recorded descendant after prerequisite integration. They may add only their named new module plus a worker report. Existing Lean modules, `Poincare.lean`, frozen contracts, and mission files stay read-only. Future import wiring is an orchestrator decision. No full build is needed for these report-backed focused tasks.

The source blocks in Appendix C are the exact tested target signatures and proofs. Names are in the scratch namespace `HamiltonResidualSurvey`; a future task must freeze its intended module namespace. Every named scratch theorem has exactly `[propext, Classical.choice, Quot.sound]`. Acceptance for each actual future module is:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/<NewModule>.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/<NewModule>.lean
git diff --check
```

The scan must have empty output, normally exit 1. Add exact target assignments and `#print axioms` for every new declaration, requiring exactly the three foundations above. Compile imports before dependent workers use them. The orchestrator independently reviews and accepts; this survey is not acceptance of any proof module.

### 4.2 Item 1: pointwise improved pinching, A and compiled

Proposed module: `Poincare/Global/HamiltonImprovedPointwisePinching.lean`.
Target: `improvedPointwiseBound`, printed in Appendix C.
Minimal source imports: `NormalizedFlowInitialPinchingPreservation` and `NormalizedFlowImprovedPinchingDecay`. Scratch probes used `import Poincare`; a dispatched worker must confirm these narrower imports before changing the namespace.

For every forward slice and point, conclude `U≤F0*R^(2-delta)` with the exact initial maximum F0. Use automatic quotient regularity, point-to-maximum comparison, preserved maximum, and positive real power. Stop if an attempt needs a new gradient or scalar-growth premise. This task exposes a real pointwise estimate needed in subsequent differential inequalities.

### 4.3 Item 2: normalized additive gradient bound from compact jets, A and compiled

Proposed module: `Poincare/Global/HamiltonCompactScalarGradientBound.lean`.
Target: `normalizedAdditiveGradientBoundOfCompactJets`, Appendix C.
Source imports: `ClosedMetricThirdJetOrbitCompactness`, `ClosedMetricThirdJetTopology`, and `ScalarEvolution`.

Use the retained exact K realization and third-jet continuity, with forward scalar nonnegativity. Produce `∃A≥0, ∀η≥0, ∀t≥0, ∀x, |∇R|²≤ηR³+A`. No evolution equation is needed once compact jets are given. Acceptance must preserve the additive constant; this theorem must not be renamed as asymptotic gradient decay. Its purpose is to separate an already accessible bound from the genuinely missing scale-effective estimate.

### 4.4 Item 3: spatial comparison and coefficient necessity, A and compiled

Proposed module: `Poincare/Global/HamiltonScalarMeanComparisonAdapters.lean`.
Targets: `scalarCompareOfTwoPoint` and `comparisonConstantGeOne`, Appendix C.
Source import: `ScalarMeanLowerBound` plus the regularity needed for the metric vocabulary.

Integrate `∀x y, R(x)≤C R(y)` with `C>0` to obtain `∀x, R(x)≤Cr`. Then prove that the latter inequality and positive mean force `1≤C`. Both statements use the actual manifold mean. No new max/min definitions or duplicate compact-family bound is required.

### 4.5 Item 4: comparison to the direct Eta residual, A and compiled

Proposed module: `Poincare/Global/HamiltonScalarMeanEtaGap.lean`.
Target: `etaFromComparison`, Appendix C.
Source imports: `NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination` and the quotient definitions.

Inputs are `delta≤2`, nonnegative kappa, a positive mean floor c, positive scalar, `Q≤kappa`, `R≤Cr`, and a strictly positive gamma. Output one uniform positive Eta with explicit value `gamma*c`. The statement does not require the eigenvalue floor because it only proves the scalar coefficient estimate; the later reaction consumer retains its own eigenfloor and admissibility hypotheses. Stop if gamma positivity cannot be proved from the supplied numerical assumptions. Do not assume it from C being finite or close to one.

### 4.6 Item 5: exact mean-derivative threshold, A and compiled

Proposed module: `Poincare/Global/HamiltonMeanDerivativeVarianceThreshold.lean`.
Targets: `meanDerivativeIffSix` and `meanDerivativeLowerOfConstant`, Appendix C.
Source imports: `HamiltonMeanFloorFromEnergyDomination`, `IntrinsicLaplacianCoordinateForm`.

Produce moving derivatives and Stokes from joint C³ and the forward flow. Prove both `r'≥0 ↔ V≤6E` and `V≤A E → (2-A/3)E/Vol≤r'`. The latter accepts any real A. These lemmas pin the obstruction to replacing 6 and supply the input for a future integrated-deficit proof. Stop with the exact derivative formula rather than changing the variance normalization or mean definition.

### 4.7 Item 6: tail floor to global floor, A and compiled, optional

Proposed module: `Poincare/Global/HamiltonMeanFloorFromTail.lean`.
Target: `meanFloorOfTailFloor`, Appendix C.
Source import: `HamiltonMeanFloorReduction`.

Use initial scalar positivity and the existing finite-interval theorem on `[0,T]`, then take `min cFront cTail`. Output `∃b>0, ∀t:Ici 0, b≤meanScalar(gt t)`. The tail floor remains the explicit B input. This does not require monotone mean, finite energy, R2, or a bounded normalization primitive.

### 4.8 Item 7: Eta supplies the floor and the existing final core, A and compiled

Proposed module: `Poincare/Global/HamiltonEtaCoreReduction.lean`.
Targets: `meanFloorFromEta` and `finalCoreOfEta`, Appendix C6.
Source imports: `NormalizedFlowInitialPinchingPreservation`, `HamiltonReactionCoreFinal`, and `NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination`. No dependency on item 6 is required.

First deduce the explicit mean floor `3*eta/4` by discarding the nonnegative `2(2-delta)N/R` term in the Eta inequality. Next retain the selected K, gt, metric, parameter, all third-jet profiles, forward flow, and initial pinching, and use the preserved eigenfloor with the landed normalization-gap reaction theorem. Conclude the literal existing `HamiltonReactionCore3Final.{u,v} M` with rate eta and that mean floor. The full-core statement retains `0<delta≤1`; the floor lemma alone only needs `delta≤2`.

No new core predicate or endpoint alias is required. This is the strongest compiled partial result and the recommended first gated task. Its analytic producer remains B: construct a uniform positive Eta under suitable geometric hypotheses. A task proving R2 is unnecessary for this route.

### 4.9 Open estimates and registration boundaries

Appendix D gives each exact elaborated expression with all manifold instances in its source context. For R1/R2 these expressions are residual goals relative to the retained witnesses and hypotheses in section 1.1; their successful elaboration is not a proof that those retained hypotheses imply them.

| Proposed child ID | Exact target location in Appendix D | Status and first missing work |
| --- | --- | --- |
| `hamilton-scalar-mean-coefficient-gap` | First expression: `∃C, (∀t≥0,x, R≤Cr) ∧ gamma>0` with the exact preserved kappa | Original frozen R1. Requires quantitative oscillation plus feasible coefficients and all-ray control. Do not universally quantify arbitrary allowed epsilon and pretend the gap follows. |
| `hamilton-direct-normalization-gap` | Second expression: `∃eta>0, ∀t≥0,x, 2(2-delta)N/R+eta≤(4/3)r` | Recommended single alternative residual; no producer proved. Avoids fixed kappa/C loss and supplies its own positive mean floor. |
| `hamilton-eventual-scalar-two-point` | Third expression: `∀z>0, ∃T≥0, ∀t≥T,x,y, R(t,x)≤(1+z)R(t,y)` | Missing normalized output of the gradient/geodesic route. It supplies only tail comparison. |
| `hamilton-effective-normalized-gradient` | Fourth expression: eventual `|∇R|²≤z R³` for every z>0 | A stronger asymptotic gradient target; compact jets alone do not give it. |
| `hamilton-variance-six-energy` | Fifth expression: subtype-indexed exact R2 | Preserve as the existing selected-core residual. Do not dispatch a universal positive-pinching slice producer: the literature obstruction rules that out. |
| `hamilton-positive-tail-mean-floor` | Sixth expression: `∃T c, 0≤T ∧ 0<c ∧ ∀t≥T,c≤r(t)` | Optional floor residual for other reaction routes. Input to compiled item 6; unnecessary for item 7 because Eta supplies the floor. |
| `hamilton-actual-reaction-rate` | Seventh expression: uniform positive rate for the actual reaction | Weaker sufficient estimate than Eta, but still unproved. Includes the derivative terms instead of discarding them. |
| `hamilton-unnormalized-bernstein-gradient` | Eighth expression, gu and Tmax: `∀z>0, ∃A≥0, ∀t∈Ico 0 Tmax,x, |∇R|²≤zR³+A` | Must be registered with actual unnormalized-flow, positive-pinching and regularity hypotheses, and a reviewed maximal-time contract. It is not a theorem about arbitrary gu. |
| `closed-traceless-contracted-bianchi-three` | Ninth expression, actual tensor field | A local algebra/derivative assembly candidate, not attempted here. This is separate from missing analytic estimates. |
| `closed-mean-zero-poincare` | Tenth expression, a positive CP for every smooth mean-zero f | Missing closed spectral/coercivity theorem. A task must specify metric curvature assumptions if it seeks an explicit CP. |
| `closed-scalar-poisson-solution` | Eleventh expression, smooth f solving `Δf=R-r` with zero mean | First missing analytic producer for the almost-Schur route. |
| `closed-almost-schur-three` | Twelfth expression: exact `V≤24E` | A valid literature target under nonnegative Ricci, after Poisson and integrated tensor/Bochner work. It cannot replace R2 in S9. |
| `hamilton-uniform-mean-deficit-budget` | Thirteenth corrected expression, one uniform B below `3Vol(0)r(0)` | Optional replacement residual for a positive mean floor. The time-integration adapter remains unproved in this report. |

No file in the registry was modified, and these child IDs are proposals. The registered parent's exact type is printed in Appendix B. For each new producer task, the orchestrator must freeze the full quantified hypotheses and reviewed definitions, not just copy a target expression or a historical theorem label.

First action: independently replay `/tmp/hamilton-residual-survey/eta-only.lean` reconstructed from Appendix C6. Check `meanFloorFromEta` and `finalCoreOfEta`, then dispatch item 7 if accepted. The explicit Eta producer is the remaining analytic target on this sufficient route; a spectral task cannot be justified as an automatic route to R2.

## 5. Verification and evidence guide

The initial worktree was clean on the requested worker branch at the recorded base. No other worktree was changed. There was no full build, root audit, service action, or agent delegation. The following appendices retain every Lean probe from this survey, including the initial namespace errors, a failed proof-layout attempt, and a failed nonnegativity tactic in the first Eta-only attempt. Passing probes only establish the claims stated here.

The first inventory probe guessed a nonexistent `HamiltonMeanFloorReduction` namespace and missed a second `RicciFlow` namespace. The corrected inventory compiled. The first pointwise-improvement proof had a layout/application error in a lambda; splitting out the typed regularity fact fixed it. No mathematical premise was added to fix that error. The first Eta-only probe tried an unavailable Ricci-norm nonnegativity name, then used the already printed traceless norm decomposition. Its first arithmetic proof failed; an explicit nonnegative-quotient transitivity proof fixed it without changing the target. Failed-print dependencies in that failed run are not accepted proof evidence. The initial deficit-budget expression elaborated but was mathematically too weak for a uniform positive floor; the corrected expression explicitly contains a uniform strict margin.

All eleven named scratch theorems have exactly `[propext, Classical.choice, Quot.sound]`. The final source token scans are empty. The detailed command statuses, source index, complete compiler outputs, rational coefficient computation, and final report-scope checks follow. Scratch paths are evidence conveniences; the source and output embedded here make the report self-contained after `/tmp` is cleared.


### C6a. Eta-only first arithmetic attempt, failed and not accepted

Source: `/tmp/hamilton-residual-survey/eta-only-01.lean`.

```lean
import Poincare
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace HamiltonResidualSurvey
open Poincare
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

theorem meanFloorFromEta
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ)
    (hd : d ≤ 2) (heta : 0 < eta)
    (hp : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    0 < (3/4 : ℝ)*eta ∧ ∀ t : Ici (0 : ℝ), (3/4 : ℝ)*eta ≤ meanScalar (gt t.1) := by
  classical
  constructor
  · positivity
  · intro t
    let x : M := Classical.choice (inferInstance : Nonempty M)
    have hU := (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
    rw [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq] at hU
    have hN : 0 ≤ (gt t.1).ricciNormSqAt x := by
      norm_num at hU
      nlinarith [sq_nonneg ((gt t.1).scalarAt x)]
    have hterm : 0 ≤ 2*(2-d)*(gt t.1).ricciNormSqAt x / (gt t.1).scalarAt x :=
      div_nonneg (mul_nonneg (by linarith) hN) (hp t.1 t.2 x).le
    have h := hgap t.1 t.2 x
    linarith

theorem finalCoreOfEta
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (e d eta : ℝ)
    (hparam : Continuous parameter)
    (hreal : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦ metricEntryThirdJetProfile (metric p.1) slot p.2))
    (hj : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hf : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hi : ∀ x, 0 < (gt 0).scalarAt x)
    (he : 1/6 < e) (he' : e ≤ 1/3) (hpin : GlobalRicciEigenvalueFloor3 (gt 0) e)
    (hd : 0 < d) (hd' : d ≤ 1)
    (ha : d ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2*e-1/3))
    (heta : 0 < eta)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    HamiltonReactionCore3Final.{u,v} M := by
  have hp := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos gt hj hf hi
  obtain ⟨hc, hmean⟩ := meanFloorFromEta gt d eta (by linarith) heta hp hgap
  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved gt e hj hf hi he' hpin
  refine ⟨K, inferInstance, inferInstance, gt, metric, parameter, (3/4 : ℝ)*eta, eta,
    hparam, hreal, hc, hmean, hf, hj, heta, ?_, hjet⟩
  intro t ht x
  exact normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
    (gt t) x (by linarith) (by linarith) hd.le ha (hp t ht x) ((hpres t ht).1 x) (hgap t ht x)
end HamiltonResidualSurvey
set_option pp.proofs false
#print HamiltonResidualSurvey.meanFloorFromEta
#print axioms HamiltonResidualSurvey.meanFloorFromEta
#print HamiltonResidualSurvey.finalCoreOfEta
#print axioms HamiltonResidualSurvey.finalCoreOfEta
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-residual-survey/eta-only-01.lean`.

Actual output and exit 1:

```text
/tmp/hamilton-residual-survey/eta-only.lean:33:6: error: linarith failed to find a contradiction
case h
M : Type u
inst✝⁹ : TopologicalSpace M
inst✝⁸ : T2Space M
inst✝⁷ : SecondCountableTopology M
inst✝⁶ : MeasurableSpace M
inst✝⁵ : BorelSpace M
inst✝⁴ : ChartedSpace (ClosedSmoothModel 3) M
inst✝³ : IsManifold (closedSmoothModelWithCorners 3) ∞ M
inst✝² : CompactSpace M
inst✝¹ : ConnectedSpace M
inst✝ : SimplyConnectedSpace M
gt : ℝ → ClosedSmoothRiemannianMetric 3 M
d eta : ℝ
hd : d ≤ 2
heta : 0 < eta
hp : ∀ t ∈ Ici 0, ∀ (x : M), 0 < (gt t).scalarAt x
hgap :
  ∀ t ∈ Ici 0, ∀ (x : M), 2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ 4 / 3 * meanScalar (gt t)
t : ↑(Ici 0)
x : M := Classical.choice ⋯
hU : (gt ↑t).scalarAt x ^ 2 / 3 ≤ (gt ↑t).ricciNormSqAt x
a✝ : (gt ↑t).ricciNormSqAt x < 0
⊢ False
failed
theorem HamiltonResidualSurvey.meanFloorFromEta.{u} : ∀ {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M]
  [SecondCountableTopology M] [inst_3 : MeasurableSpace M] [inst_4 : BorelSpace M]
  [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [inst_7 : CompactSpace M]
  [inst_8 : ConnectedSpace M] [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ),
  d ≤ 2 →
    0 < eta →
      (∀ t ∈ Ici 0, ∀ (x : M), 0 < (gt t).scalarAt x) →
        (∀ t ∈ Ici 0,
            ∀ (x : M),
              2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ 4 / 3 * Poincare.meanScalar (gt t)) →
          0 < 3 / 4 * eta ∧ ∀ (t : ↑(Ici 0)), 3 / 4 * eta ≤ Poincare.meanScalar (gt ↑t) :=
⋯
'HamiltonResidualSurvey.meanFloorFromEta' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
theorem HamiltonResidualSurvey.finalCoreOfEta.{u, v} : ∀ {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M]
  [inst_2 : SecondCountableTopology M] [inst_3 : MeasurableSpace M] [inst_4 : BorelSpace M]
  [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [inst_7 : CompactSpace M]
  [inst_8 : ConnectedSpace M] [inst_9 : SimplyConnectedSpace M] (K : Type v) [inst_10 : TopologicalSpace K]
  [CompactSpace K] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) (parameter : ↑(Ici 0) → K) (e d eta : ℝ),
  Continuous parameter →
    (∀ (t : ↑(Ici 0)), metric (parameter t) = gt ↑t) →
      (∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
          Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) →
        (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
          (∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) →
            (∀ (x : M), 0 < (gt 0).scalarAt x) →
              1 / 6 < e →
                e ≤ 1 / 3 →
                  Poincare.GlobalRicciEigenvalueFloor3 (gt 0) e →
                    0 < d →
                      d ≤ 1 →
                        d ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * e - 1 / 3) →
                          0 < eta →
                            (∀ t ∈ Ici 0,
                                ∀ (x : M),
                                  2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
                                    4 / 3 * Poincare.meanScalar (gt t)) →
                              Poincare.HamiltonReactionCore3Final M :=
⋯
'HamiltonResidualSurvey.finalCoreOfEta' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### C6. Eta alone supplies the floor and final core

Source: `/tmp/hamilton-residual-survey/eta-only.lean`.

```lean
import Poincare
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace HamiltonResidualSurvey
open Poincare
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

theorem meanFloorFromEta
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ)
    (hd : d ≤ 2) (heta : 0 < eta)
    (hp : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    0 < (3/4 : ℝ)*eta ∧ ∀ t : Ici (0 : ℝ), (3/4 : ℝ)*eta ≤ meanScalar (gt t.1) := by
  classical
  constructor
  · positivity
  · intro t
    let x : M := Classical.choice (inferInstance : Nonempty M)
    have hU := (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
    rw [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq] at hU
    have hN : 0 ≤ (gt t.1).ricciNormSqAt x := by
      norm_num at hU
      exact (div_nonneg (by positivity) (by norm_num)).trans hU
    have hterm : 0 ≤ 2*(2-d)*(gt t.1).ricciNormSqAt x / (gt t.1).scalarAt x :=
      div_nonneg (mul_nonneg (by linarith) hN) (hp t.1 t.2 x).le
    have h := hgap t.1 t.2 x
    linarith

theorem finalCoreOfEta
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (e d eta : ℝ)
    (hparam : Continuous parameter)
    (hreal : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦ metricEntryThirdJetProfile (metric p.1) slot p.2))
    (hj : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hf : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hi : ∀ x, 0 < (gt 0).scalarAt x)
    (he : 1/6 < e) (he' : e ≤ 1/3) (hpin : GlobalRicciEigenvalueFloor3 (gt 0) e)
    (hd : 0 < d) (hd' : d ≤ 1)
    (ha : d ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2*e-1/3))
    (heta : 0 < eta)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    HamiltonReactionCore3Final.{u,v} M := by
  have hp := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos gt hj hf hi
  obtain ⟨hc, hmean⟩ := meanFloorFromEta gt d eta (by linarith) heta hp hgap
  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved gt e hj hf hi he' hpin
  refine ⟨K, inferInstance, inferInstance, gt, metric, parameter, (3/4 : ℝ)*eta, eta,
    hparam, hreal, hc, hmean, hf, hj, heta, ?_, hjet⟩
  intro t ht x
  exact normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
    (gt t) x (by linarith) (by linarith) hd.le ha (hp t ht x) ((hpres t ht).1 x) (hgap t ht x)
end HamiltonResidualSurvey
set_option pp.proofs false
#print HamiltonResidualSurvey.meanFloorFromEta
#print axioms HamiltonResidualSurvey.meanFloorFromEta
#print HamiltonResidualSurvey.finalCoreOfEta
#print axioms HamiltonResidualSurvey.finalCoreOfEta
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-residual-survey/eta-only.lean`.

Actual output and exit 0:

```text
theorem HamiltonResidualSurvey.meanFloorFromEta.{u} : ∀ {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M]
  [SecondCountableTopology M] [inst_3 : MeasurableSpace M] [inst_4 : BorelSpace M]
  [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [inst_7 : CompactSpace M]
  [inst_8 : ConnectedSpace M] [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ),
  d ≤ 2 →
    0 < eta →
      (∀ t ∈ Ici 0, ∀ (x : M), 0 < (gt t).scalarAt x) →
        (∀ t ∈ Ici 0,
            ∀ (x : M),
              2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ 4 / 3 * Poincare.meanScalar (gt t)) →
          0 < 3 / 4 * eta ∧ ∀ (t : ↑(Ici 0)), 3 / 4 * eta ≤ Poincare.meanScalar (gt ↑t) :=
⋯
'HamiltonResidualSurvey.meanFloorFromEta' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem HamiltonResidualSurvey.finalCoreOfEta.{u, v} : ∀ {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M]
  [inst_2 : SecondCountableTopology M] [inst_3 : MeasurableSpace M] [inst_4 : BorelSpace M]
  [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [inst_7 : CompactSpace M]
  [inst_8 : ConnectedSpace M] [inst_9 : SimplyConnectedSpace M] (K : Type v) [inst_10 : TopologicalSpace K]
  [CompactSpace K] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) (parameter : ↑(Ici 0) → K) (e d eta : ℝ),
  Continuous parameter →
    (∀ (t : ↑(Ici 0)), metric (parameter t) = gt ↑t) →
      (∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
          Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) →
        (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
          (∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) →
            (∀ (x : M), 0 < (gt 0).scalarAt x) →
              1 / 6 < e →
                e ≤ 1 / 3 →
                  Poincare.GlobalRicciEigenvalueFloor3 (gt 0) e →
                    0 < d →
                      d ≤ 1 →
                        d ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * e - 1 / 3) →
                          0 < eta →
                            (∀ t ∈ Ici 0,
                                ∀ (x : M),
                                  2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
                                    4 / 3 * Poincare.meanScalar (gt t)) →
                              Poincare.HamiltonReactionCore3Final M :=
⋯
'HamiltonResidualSurvey.finalCoreOfEta' depends on axioms: [propext, Classical.choice, Quot.sound]
```


## Appendix D. Elaborated residual goal expressions

These are typechecks of propositions, not proofs. They deliberately create no new named goal predicates. In a registered producer contract, retain the full witness/flow/regularity context described in sections 1 and 4.9. The unnormalized estimate must have its own unnormalized-flow context.

### D1. Initial goal expressions; last expression too weak for a uniform floor

Source: `/tmp/hamilton-residual-survey/obligations.lean`.

```lean
import Poincare
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
open Poincare
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (e d : ℝ)
#check (∃ C : ℝ,
  (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
  0 < (4/3 : ℝ) - 2*(2-d)*(1-4*e+6*e^2)*C)
#check (∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
  2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ (4/3 : ℝ)*meanScalar (gt t))
#check (∀ z : ℝ, 0 < z → ∃ T : ℝ, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ x y,
  (gt t).scalarAt x ≤ (1+z)*(gt t).scalarAt y)
#check (∀ z : ℝ, 0 < z → ∃ T : ℝ, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ x,
  (gt t).scalarGradNormSqAt x ≤ z * (gt t).scalarAt x ^ 3)
#check (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
  6 * normalizedFlowTracelessRicciEnergyTrack gt t.1)
#check (∃ T c : ℝ, 0 ≤ T ∧ 0 < c ∧ ∀ t ∈ Ici T, c ≤ meanScalar (gt t))
#check (∃ rate : ℝ, 0 < rate ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
  normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate*(gt t).tracelessRicciNormSqAt x)
variable (gu : ℝ → ClosedSmoothRiemannianMetric 3 M) (Tmax : ℝ)
#check (∀ z : ℝ, 0 < z → ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Ico (0 : ℝ) Tmax, ∀ x,
  (gu t).scalarGradNormSqAt x ≤ z*(gu t).scalarAt x^3 + A)
variable (g : ClosedSmoothRiemannianMetric 3 M)
#check (∀ x, ∀ w : TangentSpace (closedSmoothModelWithCorners 3) x,
  tensorDivergenceOneFormAt g
    (fun y p q ↦ ricciVariationField g y p q - (g.scalarAt y/3)*g.inner y p q) x w =
    (1/6 : ℝ)*extDerivFun (fun y : M ↦ g.scalarAt y) x w)
#check (∃ CP : ℝ, 0 < CP ∧ ∀ f : M → ℝ,
  ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) ∞ f →
  (∫ x, f x ∂volumeMeasure g) = 0 →
  (∫ x, (f x)^2 ∂volumeMeasure g) ≤
    CP * (∫ x, g.inner x (g.gradientAt f x) (g.gradientAt f x) ∂volumeMeasure g))
#check (∃ f : M → ℝ, ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) ∞ f ∧
  (∫ x, f x ∂volumeMeasure g) = 0 ∧ ∀ x,
  g.laplacianAt f x = g.scalarAt x - meanScalar g)
#check ((∫ x, (g.scalarAt x-meanScalar g)^2 ∂volumeMeasure g) ≤
  24*(∫ x, g.tracelessRicciNormSqAt x ∂volumeMeasure g))
#check (∀ t ∈ Ici (0 : ℝ),
  (∫ s in (0 : ℝ)..t, max (normalizedFlowScalarVarianceTrack gt s -
    6*normalizedFlowTracelessRicciEnergyTrack gt s) 0) <
      3*totalVolume (gt 0)*meanScalar (gt 0))
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-residual-survey/obligations.lean`.

Actual output and exit 0:

```text
∃ C,
  (∀ t ∈ Ici 0, ∀ (x : M), (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
    0 < 4 / 3 - 2 * (2 - d) * (1 - 4 * e + 6 * e ^ 2) * C : Prop
∃ eta,
  0 < eta ∧
    ∀ t ∈ Ici 0,
      ∀ (x : M), 2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ 4 / 3 * meanScalar (gt t) : Prop
∀ (z : ℝ), 0 < z → ∃ T, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ (x y : M), (gt t).scalarAt x ≤ (1 + z) * (gt t).scalarAt y : Prop
∀ (z : ℝ), 0 < z → ∃ T, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ (x : M), (gt t).scalarGradNormSqAt x ≤ z * (gt t).scalarAt x ^ 3 : Prop
∀ (t : ↑(Ici 0)), normalizedFlowScalarVarianceTrack gt ↑t ≤ 6 * normalizedFlowTracelessRicciEnergyTrack gt ↑t : Prop
∃ T c, 0 ≤ T ∧ 0 < c ∧ ∀ t ∈ Ici T, c ≤ meanScalar (gt t) : Prop
∃ rate,
  0 < rate ∧
    ∀ t ∈ Ici 0,
      ∀ (x : M), normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate * (gt t).tracelessRicciNormSqAt x : Prop
∀ (z : ℝ),
  0 < z → ∃ A, 0 ≤ A ∧ ∀ t ∈ Ico 0 Tmax, ∀ (x : M), (gu t).scalarGradNormSqAt x ≤ z * (gu t).scalarAt x ^ 3 + A : Prop
∀ (x : M) (w : TangentSpace (closedSmoothModelWithCorners 3) x),
  tensorDivergenceOneFormAt g (fun y p q => ricciVariationField g y p q - g.scalarAt y / 3 * ((g.inner y) p) q) x w =
    1 / 6 * (extDerivFun (fun y => g.scalarAt y) x) w : Prop
∃ CP,
  0 < CP ∧
    ∀ (f : M → ℝ),
      ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) ∞ f →
        ∫ (x : M), f x ∂volumeMeasure g = 0 →
          ∫ (x : M), f x ^ 2 ∂volumeMeasure g ≤
            CP * ∫ (x : M), ((g.inner x) (g.gradientAt f x)) (g.gradientAt f x) ∂volumeMeasure g : Prop
∃ f,
  ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) ∞ f ∧
    ∫ (x : M), f x ∂volumeMeasure g = 0 ∧ ∀ (x : M), g.laplacianAt f x = g.scalarAt x - meanScalar g : Prop
∫ (x : M), (g.scalarAt x - meanScalar g) ^ 2 ∂volumeMeasure g ≤
  24 * ∫ (x : M), g.tracelessRicciNormSqAt x ∂volumeMeasure g : Prop
∀ t ∈ Ici 0,
  ∫ (s : ℝ) in 0..t, max (normalizedFlowScalarVarianceTrack gt s - 6 * normalizedFlowTracelessRicciEnergyTrack gt s) 0 <
    3 * totalVolume (gt 0) * meanScalar (gt 0) : Prop
```

### D2. Corrected uniform deficit budget and all other goal expressions

Source: `/tmp/hamilton-residual-survey/obligations2.lean`.

```lean
import Poincare
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
open Poincare
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (e d : ℝ)
#check (∃ C : ℝ,
  (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
  0 < (4/3 : ℝ) - 2*(2-d)*(1-4*e+6*e^2)*C)
#check (∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
  2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ (4/3 : ℝ)*meanScalar (gt t))
#check (∀ z : ℝ, 0 < z → ∃ T : ℝ, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ x y,
  (gt t).scalarAt x ≤ (1+z)*(gt t).scalarAt y)
#check (∀ z : ℝ, 0 < z → ∃ T : ℝ, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ x,
  (gt t).scalarGradNormSqAt x ≤ z * (gt t).scalarAt x ^ 3)
#check (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
  6 * normalizedFlowTracelessRicciEnergyTrack gt t.1)
#check (∃ T c : ℝ, 0 ≤ T ∧ 0 < c ∧ ∀ t ∈ Ici T, c ≤ meanScalar (gt t))
#check (∃ rate : ℝ, 0 < rate ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
  normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate*(gt t).tracelessRicciNormSqAt x)
variable (gu : ℝ → ClosedSmoothRiemannianMetric 3 M) (Tmax : ℝ)
#check (∀ z : ℝ, 0 < z → ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Ico (0 : ℝ) Tmax, ∀ x,
  (gu t).scalarGradNormSqAt x ≤ z*(gu t).scalarAt x^3 + A)
variable (g : ClosedSmoothRiemannianMetric 3 M)
#check (∀ x, ∀ w : TangentSpace (closedSmoothModelWithCorners 3) x,
  tensorDivergenceOneFormAt g
    (fun y p q ↦ ricciVariationField g y p q - (g.scalarAt y/3)*g.inner y p q) x w =
    (1/6 : ℝ)*extDerivFun (fun y : M ↦ g.scalarAt y) x w)
#check (∃ CP : ℝ, 0 < CP ∧ ∀ f : M → ℝ,
  ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) ∞ f →
  (∫ x, f x ∂volumeMeasure g) = 0 →
  (∫ x, (f x)^2 ∂volumeMeasure g) ≤
    CP * (∫ x, g.inner x (g.gradientAt f x) (g.gradientAt f x) ∂volumeMeasure g))
#check (∃ f : M → ℝ, ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) ∞ f ∧
  (∫ x, f x ∂volumeMeasure g) = 0 ∧ ∀ x,
  g.laplacianAt f x = g.scalarAt x - meanScalar g)
#check ((∫ x, (g.scalarAt x-meanScalar g)^2 ∂volumeMeasure g) ≤
  24*(∫ x, g.tracelessRicciNormSqAt x ∂volumeMeasure g))
#check (∃ B : ℝ, B < 3*totalVolume (gt 0)*meanScalar (gt 0) ∧
  ∀ t ∈ Ici (0 : ℝ),
  (∫ s in (0 : ℝ)..t, max (normalizedFlowScalarVarianceTrack gt s -
    6*normalizedFlowTracelessRicciEnergyTrack gt s) 0) ≤ B)
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-residual-survey/obligations2.lean`.

Actual output and exit 0:

```text
∃ C,
  (∀ t ∈ Ici 0, ∀ (x : M), (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
    0 < 4 / 3 - 2 * (2 - d) * (1 - 4 * e + 6 * e ^ 2) * C : Prop
∃ eta,
  0 < eta ∧
    ∀ t ∈ Ici 0,
      ∀ (x : M), 2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ 4 / 3 * meanScalar (gt t) : Prop
∀ (z : ℝ), 0 < z → ∃ T, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ (x y : M), (gt t).scalarAt x ≤ (1 + z) * (gt t).scalarAt y : Prop
∀ (z : ℝ), 0 < z → ∃ T, 0 ≤ T ∧ ∀ t ∈ Ici T, ∀ (x : M), (gt t).scalarGradNormSqAt x ≤ z * (gt t).scalarAt x ^ 3 : Prop
∀ (t : ↑(Ici 0)), normalizedFlowScalarVarianceTrack gt ↑t ≤ 6 * normalizedFlowTracelessRicciEnergyTrack gt ↑t : Prop
∃ T c, 0 ≤ T ∧ 0 < c ∧ ∀ t ∈ Ici T, c ≤ meanScalar (gt t) : Prop
∃ rate,
  0 < rate ∧
    ∀ t ∈ Ici 0,
      ∀ (x : M), normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate * (gt t).tracelessRicciNormSqAt x : Prop
∀ (z : ℝ),
  0 < z → ∃ A, 0 ≤ A ∧ ∀ t ∈ Ico 0 Tmax, ∀ (x : M), (gu t).scalarGradNormSqAt x ≤ z * (gu t).scalarAt x ^ 3 + A : Prop
∀ (x : M) (w : TangentSpace (closedSmoothModelWithCorners 3) x),
  tensorDivergenceOneFormAt g (fun y p q => ricciVariationField g y p q - g.scalarAt y / 3 * ((g.inner y) p) q) x w =
    1 / 6 * (extDerivFun (fun y => g.scalarAt y) x) w : Prop
∃ CP,
  0 < CP ∧
    ∀ (f : M → ℝ),
      ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) ∞ f →
        ∫ (x : M), f x ∂volumeMeasure g = 0 →
          ∫ (x : M), f x ^ 2 ∂volumeMeasure g ≤
            CP * ∫ (x : M), ((g.inner x) (g.gradientAt f x)) (g.gradientAt f x) ∂volumeMeasure g : Prop
∃ f,
  ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) ∞ f ∧
    ∫ (x : M), f x ∂volumeMeasure g = 0 ∧ ∀ (x : M), g.laplacianAt f x = g.scalarAt x - meanScalar g : Prop
∫ (x : M), (g.scalarAt x - meanScalar g) ^ 2 ∂volumeMeasure g ≤
  24 * ∫ (x : M), g.tracelessRicciNormSqAt x ∂volumeMeasure g : Prop
∃ B < 3 * totalVolume (gt 0) * meanScalar (gt 0),
  ∀ t ∈ Ici 0,
    ∫ (s : ℝ) in 0..t,
        max (normalizedFlowScalarVarianceTrack gt s - 6 * normalizedFlowTracelessRicciEnergyTrack gt s) 0 ≤
      B : Prop
```

