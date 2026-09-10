# Parabolic Schauder decomposition survey

Date: 2026-09-10. Base: `73b9bb2266283688de5fdafcc9a113f0c99e0873`.

> Orchestrator note (2026-09-10): this landed copy keeps sections 1-4, the verification section, and Appendices D-E (probed targets and the strongest scratch proof) from the worker report (lines 1-327 and 1888-2124). Appendices A-C and F-G (full repo/Mathlib inventories, definition bodies, failed probes, source searches) stay unmerged on branch `worker/parabolic-schauder-decomposition-survey` at its head commit because of their size.

Branch: `worker/parabolic-schauder-decomposition-survey`.
Mathlib: `7175569c842f9164564bd76ff8b207e7b4705522`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

The survey is complete. The first two analytic contracts below elaborate against this tree. A scratch proof also checks the generic correction of a bounded parametrix with error norm less than one. No repository PDE theorem is added, and no Hamilton obligation is discharged.

The shortest justified route retains parabolic Hölder control. The repository has the Gaussian, bounded heat semigroup, semilinear BUC existence, spatial second-derivative formulas and domination, and temporal Dini cancellation. It does not yet have a bounded constant-coefficient solution operator in the parabolic Hölder derivative norm. Neumann inversion itself is already available. The first missing quantitative kernel result is the scaled weighted Hessian integral in task K1; the first missing operator theorem is the full constant-coefficient parabolic estimate in step L3. Task K2 isolates its Hessian sup-bound component without claiming that component closes the nonlinear problem.

Scope follows the task-specific report-only contract. Only this report is a deliverable. All scratch sources and failed attempts are under `/tmp/parabolic-schauder-survey`. No repository Lean source, HANDOFF, root import, mission, audit, frozen contract or ledger is changed. The supplied worker branch is retained, overriding the general branch-prefix instruction. The worktree was clean at the base; the initial status, worktree inventory and commit were checked. HANDOFF's top section, README, PROJECT_MAP, the task, both prior reports, plan-3's task format, the mission and the nearby definitions/imports were read. Current Lean types take precedence over historical comments.

Evidence labels: **repo/proved** is a landed theorem, possibly with substantial hypotheses; **repo/definition** is a type or predicate; **Mathlib** is the pinned source; **absent** means no implementation of the stated content was found in the recorded searches. It is not a claim of logical nonderivability. Proposed targets are not proved by typechecking their statements. Appendix A gives source locations and complete checked types for the relevant public entry points, rather than counting every helper theorem in the heat files. Appendix B does the same for Mathlib. Appendices C–F preserve every scratch probe's input and actual output, including failures.

## 1. Landed Euclidean parabolic material

Names in this section are in `Poincare` unless qualified otherwise. Their full ambient instances, hypotheses and results are printed in Appendix A. In printed types, `⋯` denotes suppressed proof arguments in expressions; no theorem hypothesis is dropped. Definition bodies needed to interpret those types are printed in Appendix C.

### 1.1 Gaussian and homogeneous heat solution

`heatKernel` in `Global/HeatKernel.lean` is

\[
 K_t(x)=(4\pi t)^{-\dim(E)/2}\exp(-\|x\|^2/(4t)).
\]

`heatKernel_pos` proves positivity for `t > 0`; `contDiff_heatKernel_spatial` gives spatial smoothness at every fixed real time. `heatKernel_integrable` and `integral_heatKernel_eq_one` in `HeatKernelIntegral.lean` give integrability and mass one at positive time. `heatKernel_heatEquation_laplacian` in `HeatKernelPDEn.lean` identifies the time derivative with the Euclidean Laplacian. `integral_heatKernel_mul_heatKernel_eq` in `HeatKernelSemigroup.lean` proves the positive-time convolution law.

`heatSolution` is the scalar heat convolution. `vectorHeatSolution` is its Bochner scalar-action version. `vectorHeatSolution_solves_heatEquation_of_bounded_measurable` supplies a genuine positive-time equation for bounded measurable finite-dimensional vector data. `vectorHeatSolution_tendsto_zero_of_integrable_bounded` additionally requires integrability and continuity at the point for its initial limit. The BUC strong-continuity route below avoids demanding spatial integrability of bounded uniformly continuous data.

These are for the identity principal matrix on a finite-dimensional real inner-product space. They do not construct an anisotropic kernel for a varying positive matrix, a lateral-boundary solver, or a tensor heat semigroup on a compact manifold. Transferring a fixed positive matrix to the identity by a linear change of coordinates is a separate, relatively small step, including measure normalization and dependence on ellipticity constants.

### 1.2 Spatial derivative estimates already proved

The first derivative is checked by `hasFDerivAt_heatKernel_spatial` in `HeatCauchyTheorem.lean`. `iteratedFDeriv_two_heatKernel_apply` in `HeatCauchyDirectional.lean` gives the diagonal Hessian formula

\[
 D^2K_t(x)[v,v]=K_t(x)\left(\frac{\langle x,v\rangle^2}{4t^2}-\frac{\|v\|^2}{2t}\right).
\]

The stronger operator-norm bound is already landed as `norm_fderiv_fderiv_heatKernel_le_order_two` in `HeatCauchyNext2.lean`:

\[
 \|D^2K_t(x)\|\le K_t(x)\left(\frac{\|x\|^2}{4t^2}+\frac1{2t}\right),\qquad t>0.
\]

`integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq` in `HeatEnvelopes.lean` and `integrable_heatKernelUniformTranslateEnvelope` in `HeatCauchyUniform.lean` supply Gaussian-polynomial majorants. The latter majorant has an explicit constant depending on fixed positive time and the translate radius. It is suitable for local spatial differentiation at that time; its exponential dependence on inverse time is unsuitable as a sharp bound for integrating down to time zero.

`integrable_smul_fderiv_fderiv_heatKernel_sub_flip`, `heatSolution_hasFDerivAt` and `contDiff_two_heatSolution_of_bounded_measurable`, all in `HeatCauchyNext2.lean`, establish evaluated Hessian-integrand integrability, differentiation under the heat integral and C² smoothing. Thus a task merely reproving spatial C² smoothing or the displayed pointwise Hessian bound would duplicate landed work.

Absent as ready-to-use theorems: the weighted operator integral `∫ ‖D²K_t(x)‖ ‖x‖^α dx ≤ Cα t^(α/2-1)`, its tensor cancellation `∫ D²K_t = 0`, the resulting singular Duhamel Hessian estimate, and a parabolic Hölder bound for that Hessian. The cancellation is a prospective derivation from mass one and the existing differentiation route, not a new analytic assumption. K1 packages this useful quantitative gap.

### 1.3 BUC, Duhamel and semilinear existence

`BoundedUniformContinuousFunction` in `BoundedUniformContinuousHeat.lean` is the uniformly continuous submodule of bounded continuous functions, with the inherited supremum norm. `isClosed_boundedUniformContinuousSubmodule` proves closedness; the file supplies completeness. `vectorHeatSemigroupBUCExtended` in `HeatSemigroupBUCOperator.lean` uses the heat operator at positive time and the identity at nonpositive time. `norm_vectorHeatSemigroupBUCLM_le_one`, `continuous_vectorHeatSemigroupBUCExtended_apply` and `vectorHeatSemigroupBUCExtended_c0_contracting` in `HeatSemigroupBUCC0.lean` give the contraction and strong-continuity facts. The printed C0 statement restricts the semigroup law to nonnegative times; the total extension is not a heat evolution at negative times.

`heatDuhamelBUCValue G t` and `heatMildBUCValue u₀ G t`, in `HeatMildBUCPositiveHolder.lean`, are respectively

\[
 \int_0^t H_{t-s}G(s)\,ds,\qquad H_tu_0+\int_0^t H_{t-s}G(s)\,ds.
\]

`exists_unique_heatDuhamelBUCIntrinsic_mildSolution` in `HeatDuhamelBUCIntrinsic.lean` proves existence/uniqueness on a supplied small interval from a globally Lipschitz BUC nonlinearity with `T*L<1`. Its literal formula is `u(t)=u₀+∫₀ᵗH_(t-s)N(u(s))ds`, with a constant offset `u₀`, not `H_t u₀`. Therefore this particular theorem is a fixed-point result for that formula and must not be advertised as the usual arbitrary-initial-data semilinear heat equation. The later semilinear local-data theorem below contains the actual free heat orbit. `SemilinearHeatBUCLocalData.mk` in `SemilinearHeatBUCLocalUniform.lean` exposes the local version: continuity of `N : BUC → BUC`, finite growth bounds on norm balls, and finite Lipschitz bounds on those balls. `exists_single_time_semilinearHeatBUC_fixedPoints_local` proves a common positive lifespan for all initial data in a prescribed bounded ball; `semilinearHeatBUCUniformLocalSolution_mild` is the variation-of-constants identity.

`semilinearHeatBUCUniformLocalSolution_hasDerivWithinAt_zero` needs an initial heat-generator witness and gives a within-interval derivative at zero. `semilinearHeatBUCUniformLocalSolution_hasDerivAt_interior` in `SemilinearHeatBUCLocalAutomaticClassical.lean` gives an ordinary derivative strictly inside the positive interval, with the explicit interval and exponent parameters in its checked type. These do not give a two-sided derivative at zero or joint spatial C³ regularity.

`AffineRecenteredDeTurckShapedBUCRemainderData.mk` and `.exists_single_time_fixedPoints` in `AffineRecenteredDeTurckSemilinearHeatBUC.lean` instantiate this theory for supplied bounded linear/quadratic/composition operations and forcing. `.exists_positive_reconstructedMetricCoefficient_evolution` in `DeTurckBUCMetricReconstruction.lean` additionally uses symmetry, a positive background, small initial perturbation and a generator witness. This is a positive coordinate-coefficient evolution with the stated initial derivative, not an arbitrary smooth closed-manifold solution.

The geometric principal remainder `(g⁻¹-A₀):D²g` is not locally Lipschitz from the plain BUC space to itself. Neither this expression nor first spatial derivatives are controlled by the value norm. These BUC records cannot be filled merely by substituting the landed coordinate identity.

### 1.4 Temporal Hölder/Dini regularity is substantial but different

`heatKernelTimeDerivativeL1Norm` and `heatKernelTimeDerivativeL1Norm_eq_inv_mul` in `HeatSemigroupBUCPositiveGenerator.lean` give the exact scaling

\[
 \|\partial_t K_t\|_{L^1}=t^{-1}\|\partial_t K_1\|_{L^1}.
\]

`norm_vectorHeatTimeDerivativeBUC_le_inv` turns this into a BUC operator bound. `vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos` proves positive-time generator membership. This is control of the Laplacian generator, not uniform control of each component of the Hessian.

`HasBUCScalarDiniControlAt` and `HasBUCHeatGeneratorDiniControlAt`, in `HeatDuhamelBUCGeneratorDini.lean`, express integrability of `(t-s)⁻¹ ‖G(s)-G(t)‖` and of the corresponding generator-applied difference. `heatDuhamelBUC_mem_heatGeneratorDomain_of_holder` proves generator membership from temporal Hölder control. Its generator value splits the endpoint forcing from the canceling difference. `continuousOn_heatDuhamelBUCGeneratorValue_of_uniformHolder` in `HeatDuhamelBUCGeneratorHolderContinuity.lean` gives continuity on compact positive-time intervals. `exists_positiveHolderConstant_heatMildBUCValue` gives temporal Hölder continuity, in BUC norm, on such intervals for every exponent strictly between zero and one.

These are useful templates for singular-integral truncation and closed-graph arguments. They do not supply spatial Hölder seminorms of the Hessian. The elliptic step from a BUC Laplacian to bounded individual Hessian entries is not a bounded estimate on plain BUC; it cannot be treated as finite-dimensional equivalence of norms because the missing inverse acts on functions.

### 1.5 Reconstruction and the current geometric boundary

`coordinateMetricValue_generator_eq_laplacian_of_contDiffAt_two` in `DeTurckBUCGeneratorLocality.lean` identifies the generator using an already supplied local C² spatial germ. It does not prove that germ from generator membership.

`exists_closedSmoothRiemannianMetricFamily_realizing_chartwiseReconstruction` in `DeTurckBUCJointSpacetimeMetricAssembly.lean` constructs a smooth metric family from supplied reconstructed coefficients, endpoint/differential maps, symmetry, positivity, bounded unit sublevels, smooth tensor-section data and actual chart-transition covariance. Every premise is printed. This theorem assembles compatible data; independently solved Euclidean chart equations do not supply that compatibility.

`exists_pointwise_reconstructedInverseGaugeRicciFlowData_of_metricEntries` in `DeTurckBUCInteriorGlobalRicciData.lean` also assumes an existing global metric family, a common active time below every chosen lifespan, matching coefficient/background germs, the actual geometric remainder identity and joint C³ entries. Its output chooses local inverse-gauge trajectories and differentials at a restart time. It does not construct the missing global metric or a common physical diffeomorphism flow starting at zero.

`DeTurckPrincipalIdentity.principalIdentity` now proves the requested split into `DeTurckPrincipalSecondJet.spatialPrincipal` plus `DeTurckPrincipalIdentity.lowerTerm`. The latter depends on fixed background Christoffel data and its derivative, and on the unknown metric and its first derivative. The second-order cancellation is landed. Quantitative Hölder product/inversion estimates for these formulas remain to be proved.

`CompactCoefficientEllipticity.exists_uniform_coercivity` supplies a uniform positive lower bound for a continuous positive bilinear family on a compact parameter space. One must still apply it to the actual inverse principal coefficient in buffered charts and obtain upper/Hölder coefficient bounds.

The checked definition `HamiltonReactionCore3Final` still asks for an all-forward normalized flow, joint C³ entries, a compact realization with continuous third-jet profiles, a strictly positive uniform mean-scalar floor, and uniform reaction domination. Short-time parabolic existence proves none of the long-time or positive-floor assertions by itself. The prior reaction report's S9/S10 discussion remains relevant: positive initial mean alone does not supply either the variance condition used for monotonicity or the stronger pointwise positivity/normalization-primitive hypotheses. This survey leaves those obligations untouched.

## 2. Pinned Mathlib inventory

Appendix B contains all 36 complete checked signatures. The source column below uses paths relative to `.lake/packages/mathlib/Mathlib`. Source searches are also preserved, including misleading matches for Schauder bases.

| Capability and exact names | Source | What is available and what remains |
| --- | --- | --- |
| `HolderWith`, `HolderOnWith`, `HolderWith.uniformContinuous`, `HolderWith.restrict_iff` | `Topology/MetricSpace/Holder.lean` | Global/on-set Hölder predicates with nonnegative-real constant and exponent; restriction and uniform continuity for positive exponent. Equip the cylinder with the parabolic metric or use an equivalent raw increment predicate. The default product metric is not parabolic. |
| `eHolderNorm`, `nnHolderNorm`, `MemHolder`, `MemHolder.holderWith`, `MemHolder.nnHolderNorm_add_le` | `Topology/MetricSpace/HolderNorm.lean` | Extended Hölder seminorm and finite-Hölder membership, plus seminorm arithmetic. `nnHolderNorm` uses conversion from an extended number and cannot be used as evidence of finiteness without membership. It is a seminorm, vanishing on constants; add the sup norm. No bundled complete parabolic derivative space was found. |
| `ContDiffPointwiseHolderAt`, `ContDiffAt.contDiffPointwiseHolderAt` | `Analysis/Calculus/ContDiffHolder/Pointwise.lean` | Local pointwise Hölder remainder regularity, exponent in the unit interval. This is not a uniform cylinder estimate or a parabolic Banach space. |
| `ContDiff.continuous_iteratedFDeriv`; `norm_iteratedFDeriv_mul_le`, `norm_iteratedFDeriv_comp_le` | `Analysis/Calculus/ContDiff/Defs.lean`; `Analysis/Calculus/ContDiff/Bounds.lean` | Continuity and pointwise product/composition derivative bounds. Neither smoothness nor these inequalities imply a global bound on a noncompact cylinder. They also do not assign parabolic derivative weights or prove PDE estimates. |
| `MeasureTheory.convolution`, `MeasureTheory.Integrable.integrable_convolution`, `MeasureTheory.integral_convolution` | `Analysis/Convolution.lean` | Bochner convolution with a continuous bilinear pairing, L¹ integrability and integral/Fubini identities. No general continuous convolution Young `Lᵖ*Lᑫ→Lʳ` norm theorem was found in the recorded convolution/norm searches. Numerical Young inequalities are a different result. |
| `MeasureTheory.norm_integral_le_integral_norm` | `MeasureTheory/Integral/Bochner/Basic.lean` | Enough, together with integrability and a pointwise product bound, for the needed L¹-kernel/L∞-data endpoint. The repo already proves the positive heat operator's sup contraction. A full general Young theorem need not be built first. |
| `integral_gaussian`, `integrable_rpow_mul_exp_neg_mul_sq` | `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | Scalar Gaussian integral and real-power weighted one-dimensional integrability. The latter is not directly the multidimensional radial weighted Hessian estimate. |
| `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add` | `Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` | Finite-dimensional Gaussian integrability with linear phase. The repo uses it to get real radial Gaussian envelopes. |
| `MeasureTheory.Measure.integral_comp_smul_of_nonneg` | `MeasureTheory/Measure/Haar/NormedSpace.lean` | Scalar dilation and volume factor; directly useful for sharp time scaling. |
| `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`, `MeasureTheory.integral_integral_swap` | `MeasureTheory/Integral/DominatedConvergence.lean`; `MeasureTheory/Integral/Prod.lean` | Dominated convergence and Fubini with actual measurability/integrability hypotheses. A nonintegrable `1/(t-s)` bound does not satisfy them. |
| `hasFDerivAt_integral_of_dominated_of_fderiv_le` | `Analysis/Calculus/ParametricIntegral.lean` | Differentiation under an integral using a common local derivative bound. Spatial cancellation or truncation is needed to create such a bound at the Duhamel endpoint. |
| `ContractingWith.fixedPoint`, `ContractingWith.fixedPoint_isFixedPt`, `ContractingWith.exists_fixedPoint'` | `Topology/MetricSpace/Contracting.lean` | Banach fixed point, including the complete invariant-set form. Completing the analytic spaces, proving invariance and finding a constant less than one are separate inputs. |
| `ContinuousLinearMap.inverse`, `ContinuousLinearMap.IsInvertible.self_comp_inverse` | `Topology/Algebra/Module/Equiv.lean` | A total inverse operation and its right-inverse identity under genuine invertibility. The operation returns zero when the map is not invertible; merely writing it does not prove solvability. |
| `ContinuousLinearMap.isUnit_iff_bijective` | `Analysis/Normed/Operator/Banach.lean` | Endomorphism units versus bijectivity on Banach spaces. |
| `isUnit_one_sub_of_norm_lt_one`, `Units.oneSub`, `hasSum_geom_series_inverse` | `Analysis/SpecificLimits/Normed.lean` | The actual Neumann-series API is a general normed-ring API. No theorem named `ContinuousLinearMap.isUnit_of_norm_lt_one` was found. Apply the generic result to the Banach algebra of continuous linear endomorphisms. |
| `IsBoundedLinearMap`, `IsBoundedLinearMap.toContinuousLinearMap` | `Analysis/Normed/Operator/BoundedLinearMaps.lean` | Unbundled linearity plus `∃ M > 0, ∀ x, ‖f x‖ ≤ M*‖x‖`, and bundling. It neither constructs a PDE solution nor proves this bound. |

The exact analytic absence is parabolic Schauder maximal regularity, not Gaussian integration, Fubini, dominated convergence, or the contraction theorem. The term “Schauder” in `Analysis/Normed/Module/Bases.lean` concerns bases, not the PDE estimate.

## 3. Lemma-level route and consumers

A = a bounded derivation using the audited calculus/algebra/integration infrastructure; a proposed A item is not thereby proved. B = substantive new quantitative PDE/function-space development. C = a claimed implication whose hypotheses do not justify it or whose route remains unresolved. Effort estimates below are planning judgments for experienced Lean work, not measured completion times.

### 3.1 Choose a norm that can actually close the equation

Fix `0 < α < 1`, `0 < T ≤ 1`, `Q_T=[0,T]×ℝ³`, and

\[
 d_p((t,x),(s,y))=\|x-y\|+\sqrt{|t-s|},\qquad
 [f]_{\alpha;p}=\sup_{p\ne q}\frac{\|f(p)-f(q)\|}{d_p(p,q)^\alpha}.
\]

Define `Y_T` as bounded functions with finite displayed seminorm and norm `‖f‖∞+[f]α;p`. Define `X_T` as actual derivative graphs `(u,ut,Du,DDu)` with zero initial value, the three derivative relations of the frozen target, and finite `Y_T` norm for each component; use the sum of their four norms. Use functions on the cylinder, or identify total extensions that agree there, so that the norm is definite. Arbitrary values outside the cylinder must not create a kernel in the norm. Time derivatives at the endpoints are within `[0,T]`, exactly as in the frozen linear target.

This is an implementable carrier definition now, not an already proved Banach instance. Prove completeness by putting the jets in a finite product of complete Hölder spaces and proving that the actual derivative graph and initial trace are closed under uniform convergence. Uniform convergence of values alone is insufficient. Prove uniqueness of derivatives on the nondegenerate time interval and spatial domain. Do not define the space merely as the completion of smooth functions and assume that all big-Hölder forcing is approximable in the same exponent; that would instead impose a little-Hölder restriction.

These norms imply exactly the frozen `parabolicBound` conclusions after a harmless constant comparison. The raw `linearSchauderGoal` is re-elaborated unchanged in Appendix D using local bindings. It gives existence and bounds for each forcing, but does not by itself give uniqueness, linear dependence or operator bounds uniform as `T→0`. All three are needed for tasks 4 and 5 and must be proved by the construction. Preserve constants before the forcing quantifier and obtain a single estimate for restrictions to all sufficiently short intervals.

### 3.2 Constant coefficients, localization and correction

| Step | Exact mathematical target and proof route | Class / new gap / estimated effort |
| --- | --- | --- |
| L0. Hölder spaces and jets | Complete `Y_T` and the zero-trace graph `X_T`; bounded evaluation, trace, restriction and multiplication. Prove `[af]α ≤ ‖a‖∞[f]α+[a]α‖f‖∞`. | A for raw product inequalities; B for the graph/norm package and interpolation. No audited parabolic graph-completeness theorem. Roughly 2–5 weeks. |
| L1. Scaled kernel moments | K1 below: weighted L¹ Hessian bound and zero tensor integral, with constants independent of `0<t≤1`. Use the landed pointwise Hessian bound, Gaussian absorption and dilation. | A candidate, roughly 1–2 weeks. No new general PDE theory, but a nontrivial quantitative integral proof is still required. |
| L2. Canceling Duhamel Hessian | K2 below: actual C² spatial derivative and its integral formula, `‖D²u(t)‖∞ ≤ (2Cα/α) K t^(α/2)` from a uniform spatial Hölder constant `K` for the forcing. Work with truncated time integrals and pass actual derivatives to the limit. | B, bounded subtask, roughly 2–4 weeks. Missing endpoint differentiation/cancellation estimate, not the existing positive-time heat smoothing theorem. |
| L3. Full constant-coefficient inverse | For `u(t)=∫₀ᵗH_(t-s)f(s)ds`, prove the PDE, initial trace, `ut=f+Δu`, and `‖u‖X_T ≤ Cα‖f‖Y_T` uniformly for `T≤1`. In particular `[D²u]α;p` and `[ut]α;p` must be bounded. | B, roughly 1–3 months after L0–L2. Missing parabolic singular-integral Hölder estimate. Split increments at time scale `d_p(p,q)^2`; the far part needs higher spatial/time kernel difference bounds, beyond K1. |
| L4. Frozen elliptic matrix | Transport L3 through a linear coordinate equivalence for a fixed symmetric positive matrix `A₀`; prove measure/derivative/norm comparisons with constants controlled by ellipticity and the upper matrix bound. | B small, roughly 1–3 weeks; a supplied factorization transfer is A. The quantitative anisotropic heat-operator theorem is absent. No unprobed matrix-square-root name is assumed here. |
| L5. Coefficient error | On a localized cylinder, bound `(a-A₀):D²u` in `Y_T`, then compose with the local inverse. Prove an explicit bound less than one using spatial radius, time length, coefficient Hölder bounds and zero-trace interpolation. | B, roughly 3–6 weeks after L3. Uniform continuity alone does not give a Hölder multiplier estimate. The required product and interpolation bounds are not supplied by a BUC contraction. |
| L6. Parametrix on ℝ³ | Use a uniformly locally finite spatial covering with uniform buffers/cutoffs; sum localized frozen solvers and estimate principal errors and cutoff commutators. Construct bounded `P` with `L P=Id-R`, `‖R‖<1`. | B, roughly 1–3 months. A finite covering of all ℝ³ by bounded patches is unavailable. This is required for the literal whole-space task 3. |
| L7. Neumann correction | Set `S=P(Id-R)⁻¹`. Then `L S=Id`. The complete scratch proof in Appendix E compiles; it uses only completeness of the forcing space for the inverse. | A, already proved in scratch from the explicit norm/error hypotheses. This does not manufacture `P` or its error estimate. |
| L8. Uniqueness and time slabs | Prove uniqueness in the stated bounded class and the interval-consistent solution operator; concatenate controlled short intervals with nonzero initial trace estimates if the final prescribed `T` exceeds the first localization time. | B. The literal task 3 permits every `T≤1`; an existence theorem only on an unspecified shorter interval is not its completion. Trace/control and continuation add approximately 2–5 weeks. |

The crucial estimate at L2 is

\[
 D^2u(t,x)=\int_0^t\int D^2K_{t-s}(y)
       [f(s,x-y)-f(s,x)]\,dy\,ds,
\]

whose norm is bounded by `Cα K ∫₀ᵗ(t-s)^(α/2-1) ds`. This integral equals `(2/α)t^(α/2)`. Without the spatial difference, the Hessian-kernel bound has a nonintegrable `(t-s)⁻¹` singularity. A bound for the integral's value must accompany, rather than replace, integrability and passage to the actual derivative.

For L5, write `b=a-A₀`. Even if `‖b‖∞≤ε`, the product estimate contains

\[
 [bD^2u]_{\alpha;p}
 \le \varepsilon[D^2u]_{\alpha;p}+[a]_{\alpha;p}\|D^2u\|_\infty.
\]

The second term does not disappear when the sup oscillation is small. On a radius-`r` cylinder, use scaled Hölder norms `‖b‖∞+r^α[b]α;p` with parabolic time scale at most `r²`; then bounded Hölder coefficients give smallness as `r→0`. Alternatively, retain the unscaled norms and use K2/zero-trace estimates to make the Hessian sup term small after the local inverse, while keeping the full Hölder part controlled. These are estimates to prove, including cutoff terms, not a theorem inferred solely from uniform continuity.

For an explicit local norm target, use the maximum of the nine coefficient-entry norms, and suppose the extended supported error entries satisfy `‖bᵢⱼ‖∞≤ε` and `[bᵢⱼ]α;p≤Λb`. Let the frozen inverse have `‖D²S₀f‖Y_T≤Cs‖f‖Y_T` and K2 give `‖D²S₀f‖∞≤Ck T^(α/2)‖f‖Y_T`. The component contraction estimate to prove is

\[
 \|b:D^2S_0\|_{Y_T\to Y_T}
 \le 9\bigl(\varepsilon C_s+\Lambda_b C_k T^{\alpha/2}\bigr).
\]

Choosing `9 ε Cs≤1/4` and `9 Λb Ck T^(α/2)≤1/4` makes this error at most `1/2`. First choose the spatial support/buffer so the sup oscillation is small; then keep its finite Hölder/cutoff constants fixed while choosing time. The extension, anisotropic transfer and other parametrix commutators still need their own bounds. This displayed bound is a proposed lemma with explicit hypotheses, not a consequence asserted from uniform continuity alone.

Uniform continuity on the whole strip yields a common modulus of *local* oscillation. It does not make `a(t,x)` uniformly close to one fixed matrix as time shrinks: time-independent spatial variation survives. Continuous coefficients with no Hölder modulus also need not preserve `Y_T` under multiplication. Thus “uniform continuity plus short time implies a small endomorphism of the full Hölder space” is C as stated. The frozen target's bounded parabolic Hölder hypothesis is sufficient data for the intended localization proof.

### 3.3 Immediate consumer: task 4, compatible finite-atlas inverse

Use compatible symmetric tensor sections as a closed subspace of a finite product of localized `X_T`/`Y_T` spaces. Prove that the transition law defines a closed condition, all spatial derivatives transform with the actual first/second transition derivatives, and buffered chart changes and cutoff multiplication are bounded. Choose the finite atlas before the forcing. Compact ellipticity supplies a common lower bound after the coefficient has been identified.

Define `L` to be the actual derivative of the geometric operator at the background, including the lower-order coupled terms. A sum of frozen local inverses with cutoffs gives a tentative global `P`. Compute `L P-Id` explicitly. Terms include coefficient differences times second derivatives, cutoff gradients times first derivatives, cutoff Hessians times values, and lower-order tensor coupling. Prove their common operator norm is less than one by first choosing spatial buffers and then shortening time. L7 gives a genuine global right inverse.

This construction ensures compatibility by building global tensor sections and correcting a global residual. Equality of independent chartwise heat solutions cannot be inferred from equal initial data on overlaps: artificial extensions and chart boundaries affect heat propagation immediately. Flat heat propagation is also not covariant under arbitrary nonlinear coordinate changes. Treat either shortcut as C.

Task 4 can use L3/L4 directly in a finite-atlas parametrix; it need not wait for the whole-space uniformly locally finite construction L6. This is a dependency optimization for the compact consumer. It does not prove or replace the frozen whole-space `linearSchauderGoal`. Keep the latter as its own open task until all its quantifiers are met.

The remaining task-4 package is B, approximately 2–6 months after the local Hölder estimates. Its exact final algebraic type remains `∃ S : Y →L[ℝ] X, L.comp S = ContinuousLinearMap.id ℝ Y`, rechecked in Appendix D. Freeze concrete spaces, norms and `L` before dispatching that abstract statement. The scratch L7 proof is useful algebra once these estimates exist, not an acceptable standalone replacement for the global PDE task.

### 3.4 Immediate consumer: task 5, the nonlinear fixed point

Let `Q(g)` be the actual landed DeTurck rate with fixed background. Use the principal identity to account for all occurrences of second derivatives. For `g=g₀+h`, the principal difference contains `(g⁻¹-g₀⁻¹):D²h`, plus changes in coefficients multiplying the background Hessian; the lower term depends on `g` and `Dg`. Prove the following in order:

1. A uniform positive ball for `g₀+h`, using the compact coercivity bound and a sup-norm embedding of `X_T`.
2. Hölder product estimates for tensor contractions; bounded inversion and its difference/remainder estimate on that positive ball. Constants must be common across charts.
3. A bound for the actual nonlinear residual after subtracting `DQ(g₀)h`, including coefficient variation times the unknown Hessian and the first-derivative quadratic terms.
4. A residual Lipschitz estimate `‖N(h)-N(k)‖Y_T ≤ η(r,T)‖h-k‖X_T`, with `‖S‖η(r,T)<1`, and the corresponding invariant-ball bound.
5. Apply the complete-set fixed-point theorem, then recover the actual equation from the right-inverse identity. Keep symmetry by working in the symmetric subspace.

There is an initial-time size issue in the prior abstract `b+S(N v)` plan. In the unweighted norm chosen here, `ut(0)=f(0)`, so `‖S f‖X_T` need not tend to zero as `T→0` for a fixed nonzero background forcing. Shortening time does not automatically make `b=S Q(g₀)` small in the *full* derivative norm.

A concrete repair is to choose a smooth reference family with the correct initial velocity, for example `g*(t)=g₀+t Q(g₀)` in the space of symmetric sections on a sufficiently small positive time interval. Write the unknown as `g*+v`. The known residual `Q(g*)-∂t g*` vanishes at zero, so its `Y_T` norm becomes small by quantitative smoothness bounds as the interval shrinks. For the same reason, the coefficient mismatch between `g*` and `g₀` is small. Prove those estimates; work on zero-initial-trace perturbations, optionally the closed subspace also having zero initial rate. The frozen linear estimate must control all such small intervals uniformly. This repair preserves the actual equation and initial metric; it does not posit a small arbitrary initial curvature.

A plain `C^{2,1}` sup graph is insufficient for the proposed Neumann/fixed-point proof. Its second derivatives are bounded, but the nonlinearity generally gives only bounded continuous forcing, and the inverse need not map that forcing boundedly back to individual bounded second derivatives. Adding weights such as `t‖D²u(t)‖∞` does not cure the singularity at `s=t` for a fixed positive `t`. The minimal sufficient choice on this route is a derivative-sensitive maximal-regularity pair, here `Y=C^{α,α/2}` and zero-trace `X=C^{2+α,1+α/2}` with the stated jet norm. No claim is made that Hölder spaces are the only possible spaces for short-time existence. A Sobolev or mixed spacetime-norm route would require its own product and maximal-regularity theory.

For comparison, Koch–Lamm's Ricci–DeTurck argument uses derivative-sensitive spacetime norms even for small bounded perturbations of the Euclidean metric; it does not justify the existing plain-BUC remainder interface for arbitrary metrics. The paper's heat-kernel derivative estimates and section 4 support that distinction. [Koch–Lamm, *Geometric flows with rough initial data*, sections 2.1 and 4](https://arxiv.org/html/0902.1488v2). All statements about Lean availability here come from the pinned local sources.

Task 5 remains B, approximately 1–4 months after the linear and chart-space infrastructure. Task 6 still has to bootstrap spatial slices to smoothness and joint regularity, and construct an extension through zero appropriate for an ordinary derivative there. The linear within-interval derivative is not such an extension. Even a successful task 6 would not prove the all-forward Hamilton core or its positive mean floor.

## 4. First two gated Lean tasks

These are proposals for separate proof jobs. Both target statements were checked with no proof body; their exact inputs and output are in Appendix D. Allowed files listed here describe future jobs, not changes made by this survey. Use the recorded base or a separately revalidated descendant, one isolated branch per job, and a nonoverlapping file lease. Do not edit existing Lean files or the frozen target. A worker must preserve failed compiler output and report a resisting statement if it stops.

### K1. Scaled weighted Hessian kernel and cancellation

Proposed module: `Poincare/Global/HeatKernelHessianMoments.lean`.
Proposed namespace: `Poincare.HeatKernelHessianMoments`.
Base: `73b9bb2266283688de5fdafcc9a113f0c99e0873`.
Imports: `Poincare.Global.HeatCauchyNext2`, `Poincare.Global.HeatSemigroupBUCPositiveGenerator`, and the Euclidean model context. The first contains the existing Hessian formula/envelopes; the second supplies a working time-scaling integral template.
Allowed: only that new module and `harness/reports/heat-kernel-hessian-moments_{done|blocked}.md`.

Objective: prove the first `#check` proposition in the displayed program below, with `E=ClosedSmoothModel 3` and `Hess t x=D²K_t(x)`. It simultaneously requires real integrability of the norm-weighted kernel, its sharp time exponent, integrability of the tensor kernel and its zero integral. Constants are before time; arbitrary integrals returning zero by totalization do not satisfy the contract.

Use `Cα=1+∫ ‖D²K₁(x)‖ ‖x‖^α dx` as one explicit admissible constant after proving integrability. Show dilation of the Hessian and volume, then obtain the stated exponent. Prove tensor cancellation by differentiating mass one twice with the landed domination lemmas or by evaluated Gaussian moments and extensionality. Auxiliary named lemmas for these steps are useful. Repeating only the landed pointwise Hessian bound is failure.

Class A candidate. Expected 1–2 weeks; this classification reflects the existing Gaussian/calculus infrastructure, not a compiled proof of K1. The exact first missing quantitative theorem is displayed, rather than assigned an imaginary Mathlib name.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelHessianMoments.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatKernelHessianMoments.lean
git diff --check
```

Require compiler exit 0, empty scan with exit 1, diff check exit 0, exact target assignment, and `#print axioms` for every new declaration with exactly `[propext, Classical.choice, Quot.sound]`. Stop with the exact unmatched integral or scaling equality if any conjunct fails. Do not introduce an assumed moment estimate.

### K2. Duhamel Hessian sup estimate from spatial Hölder forcing

Proposed module: `Poincare/Global/HeatDuhamelSpatialHolderHessian.lean`.
Proposed namespace: `Poincare.HeatDuhamelSpatialHolderHessian`.
Base: recorded survey base plus the independently accepted K1 proof commit; that concrete commit must be frozen before dispatch. The target itself already elaborates at the survey base because it refers only to landed operations.
Imports: K1, `Poincare.Global.HeatCauchyNext2`, and the interval-integration calculus already imported by `Poincare.Global.HeatMildBUCPositiveHolder`.
Allowed: only that new module and `harness/reports/heat-duhamel-spatial-holder-hessian_{done|blocked}.md`.

Objective: prove the second `#check` proposition below. For arbitrary bounded continuous forcing on the full strip with one spatial Hölder constant, the *specified heat Duhamel formula* has zero initial trace, actual C² spatial regularity, the canceled tensor integral as its Hessian, and `‖D²u(t,x)‖≤Cα K t^(α/2)` up to both time endpoints. This controls a necessary component of the selected `X_T` norm. It does not assert the full `Y_T` Hölder bound of the Hessian, a time derivative or variable-coefficient solvability.

Take `Cα=2 Cα,K1/α` for the estimate, with a larger positive constant if needed. Prove first-derivative integrability and differentiability of truncated Duhamel integrals, then uniform convergence of the values and first/second derivatives on spatial neighborhoods; pass to actual derivatives. K1 makes the canceled Hessian time integral integrable. Do not pass two derivatives through the unmodified time integral using the nonintegrable norm bound. At `t=0`, use the zero function and the empty integration interval; no forcing compatibility condition `f(0)=0` is required for this spatial statement.

Class B, bounded subtask, roughly 2–4 weeks after K1. The later near/far increment estimates L3 remain mandatory for the nonlinear consumer.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
git diff --check
```

The same exact dependency and target-assignment requirements apply. Stop if only the integral expression is bounded without identifying it with `fderiv ℝ (fderiv ℝ (u t))`, if the constant depends on the forcing, or if the time/space quantifiers are weakened. If full L3 is attempted later, freeze a separate contract for that stronger theorem instead of relabeling K2 as Schauder solvability.

The following is the complete passing target program. The local normed-group instance selects the operator-norm topology for the nested continuous linear map; earlier attempts exposed a topology-instance mismatch for its Bochner integrability. It does not change the Hessian formula or the mathematical target. No open theorem has a proof body in this program.

```lean
import Poincare.Global.HeatCauchyNext2
import Poincare.Global.HeatMildBUCPositiveHolder
import Poincare.Global.CompactCoefficientEllipticity
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
set_option format.width 110
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
#check (∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
    Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0)
#check (∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  (∀ x, u 0 x = 0) ∧
  ∀ t ∈ Icc 0 T, ∀ x : E,
    ContDiff ℝ 2 (u t) ∧
    IntegrableOn (fun s : ℝ => ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y) (Ioo 0 t) ∧
    fderiv ℝ (fderiv ℝ (u t)) x =
      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y ∧
    ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2))
```

## Verification and handoff

The final inventory, definition, frozen-target and proposed-target probes pass. The scratch `ParabolicSchauderSurvey.corrected_right_inverse` proof passes and has exactly the required three foundational dependencies. Its statement assumes an actual bounded parametrix and a proved small error; it is the strongest new compiled proof in this survey. Neither K1, K2 nor `linearSchauderGoal` has been proved.

Three missing Mathlib cache modules required a focused `lake build` of the Hölder norm, derivative bounds and pointwise Hölder modules. Six modules were rebuilt including their missing dependencies; Lake reported 2146 total jobs because cached prerequisites were counted. This was not a root project build, and no source was edited. All scratch Lean failures are preserved below: one unsupported printer option, missing cache imports, nested operator topology and a reversed scalar action, a missing NNReal notation scope, and a unit-coercion annotation in the correction proof. The final source scans are empty. Full project integration audits are not claimed or required by a report-only change.

Next exact action: the orchestrator should freeze K1 at the recorded base after reviewing the target in Appendix D and dispatch only `HeatKernelHessianMoments.lean` with its report allowed. L7 already has a compiled scratch derivation; it should not displace the missing kernel work as a standalone count-increasing job.

```text
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' /tmp/parabolic-schauder-survey/Targets.lean /tmp/parabolic-schauder-survey/Frozen.lean /tmp/parabolic-schauder-survey/Perturbation.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```



## Appendix D. Frozen and proposed statement probes

The first probe reproduces Appendix D's exact linear predicate using local bindings, with the same cylinder, bound, principal contraction, quantifier order and derivative relations. No solution is supplied. The second probe checks K1 and K2. Its local instance selects the standard operator-norm structure; it is not an analytic hypothesis.

### D1. Frozen linear, inverse and residual targets

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-schauder-survey/Frozen.lean`. Actual exit: 0.

```lean
import Poincare.Global.CompactCoefficientEllipticity
set_option autoImplicit false
set_option format.width 110
open Set
open scoped BigOperators NNReal
#check (
let E := Poincare.ClosedSmoothModel 3;
let Bilin := E →L[ℝ] E →L[ℝ] ℝ;
let basis3 := fun (i : Fin 3) => EuclideanSpace.basisFun (Fin 3) ℝ i;
let cylinder : ℝ → Set (ℝ × E) := fun T => Icc 0 T ×ˢ univ;
let parabolicBound := fun {F : Type} [NormedAddCommGroup F]
    (α T C : ℝ) (f : ℝ × E → F) =>
  (∀ p ∈ cylinder T, ‖f p‖ ≤ C) ∧
  ∀ p ∈ cylinder T, ∀ q ∈ cylinder T,
    ‖f p - f q‖ ≤ C * (‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|) ^ α;
let linearRate := fun (a : ℝ × E → Matrix (Fin 3) (Fin 3) ℝ)
    (H : ℝ × E → Bilin) (p : ℝ × E) =>
  ∑ i : Fin 3, ∑ j : Fin 3, a p i j * H p (basis3 i) (basis3 j);

  ∀ (α T ell Λ : ℝ), 0 < α → α < 1 → 0 < T → T ≤ 1 → 0 < ell →
  ∀ a : ℝ × E → Matrix (Fin 3) (Fin 3) ℝ,
    (∀ p ∈ cylinder T, ∀ i j, a p i j = a p j i) →
    (∀ i j, parabolicBound α T Λ (fun p => a p i j)) →
    (∀ p ∈ cylinder T, ∀ ξ : E,
      ell * ‖ξ‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, a p i j * ξ i * ξ j) →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ × E → ℝ) (Fbound : ℝ),
      0 ≤ Fbound → parabolicBound α T Fbound f →
      ∃ u ut : ℝ × E → ℝ, ∃ Du : ℝ × E → E →L[ℝ] ℝ,
        ∃ DDu : ℝ × E → Bilin,
          (∀ x, u (0, x) = 0) ∧
          (∀ p ∈ cylinder T,
            HasDerivWithinAt (fun s => u (s, p.2)) (ut p) (Icc 0 T) p.1 ∧
            HasFDerivAt (fun x => u (p.1, x)) (Du p) p.2 ∧
            HasFDerivAt (fun x => Du (p.1, x)) (DDu p) p.2 ∧
            ut p = linearRate a DDu p + f p) ∧
          parabolicBound α T (C * Fbound) u ∧
          parabolicBound α T (C * Fbound) ut ∧
          parabolicBound α T (C * Fbound) Du ∧
          parabolicBound α T (C * Fbound) DDu
)
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
#check (fun (L : X →L[ℝ] Y) =>
  ∃ S : Y →L[ℝ] X, L.comp S = ContinuousLinearMap.id ℝ Y)
#check (fun (S : Y →L[ℝ] X) (N : X → Y) (b : X) =>
  ∃ r : ℝ, 0 < r ∧ ∃ q : ℝ≥0, (q : ℝ) < 1 ∧
    MapsTo (fun v => b + S (N v)) (Metric.closedBall 0 r) (Metric.closedBall 0 r) ∧
    LipschitzOnWith q (fun v => b + S (N v)) (Metric.closedBall 0 r))
end
```

Actual output:

```text
let E := Poincare.ClosedSmoothModel 3;
let Bilin := E →L[ℝ] E →L[ℝ] ℝ;
let basis3 := fun i => (EuclideanSpace.basisFun (Fin 3) ℝ) i;
let cylinder := fun T => Icc 0 T ×ˢ univ;
let parabolicBound := fun {F} [NormedAddCommGroup F] α T C f =>
  (∀ p ∈ cylinder T, ‖f p‖ ≤ C) ∧
    ∀ p ∈ cylinder T, ∀ q ∈ cylinder T, ‖f p - f q‖ ≤ C * (‖p.2 - q.2‖ + √|p.1 - q.1|) ^ α;
let linearRate := fun a H p => ∑ i, ∑ j, a p i j * ((H p) (basis3 i)) (basis3 j);
∀ (α T ell Λ : ℝ),
  0 < α →
    α < 1 →
      0 < T →
        T ≤ 1 →
          0 < ell →
            ∀ (a : ℝ × E → Matrix (Fin 3) (Fin 3) ℝ),
              (∀ p ∈ cylinder T, ∀ (i j : Fin 3), a p i j = a p j i) →
                (∀ (i j : Fin 3), parabolicBound α T Λ fun p => a p i j) →
                  (∀ p ∈ cylinder T, ∀ (ξ : E), ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a p i j * ξ.ofLp i * ξ.ofLp j) →
                    ∃ C,
                      0 < C ∧
                        ∀ (f : ℝ × E → ℝ) (Fbound : ℝ),
                          0 ≤ Fbound →
                            parabolicBound α T Fbound f →
                              ∃ u ut Du DDu,
                                (∀ (x : E), u (0, x) = 0) ∧
                                  (∀ p ∈ cylinder T,
                                      HasDerivWithinAt (fun s => u (s, p.2)) (ut p) (Icc 0 T) p.1 ∧
                                        HasFDerivAt (fun x => u (p.1, x)) (Du p) p.2 ∧
                                          HasFDerivAt (fun x => Du (p.1, x)) (DDu p) p.2 ∧
                                            ut p = linearRate a DDu p + f p) ∧
                                    parabolicBound α T (C * Fbound) u ∧
                                      parabolicBound α T (C * Fbound) ut ∧
                                        parabolicBound α T (C * Fbound) Du ∧ parabolicBound α T (C * Fbound) DDu : Prop
fun L => ∃ S, L.comp S = ContinuousLinearMap.id ℝ Y : (X →L[ℝ] Y) → Prop
fun S N b =>
  ∃ r,
    0 < r ∧
      ∃ q,
        ↑q < 1 ∧
          MapsTo (fun v => b + S (N v)) (Metric.closedBall 0 r) (Metric.closedBall 0 r) ∧
            LipschitzOnWith q (fun v => b + S (N v)) (Metric.closedBall 0 r) : (Y →L[ℝ] X) → (X → Y) → X → Prop
```

### D2. K1 and K2

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-schauder-survey/Targets.lean`. Actual exit: 0.

```lean
import Poincare.Global.HeatCauchyNext2
import Poincare.Global.HeatMildBUCPositiveHolder
import Poincare.Global.CompactCoefficientEllipticity
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
set_option format.width 110
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
#check (∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
    Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0)
#check (∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  (∀ x, u 0 x = 0) ∧
  ∀ t ∈ Icc 0 T, ∀ x : E,
    ContDiff ℝ 2 (u t) ∧
    IntegrableOn (fun s : ℝ => ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y) (Ioo 0 t) ∧
    fderiv ℝ (fderiv ℝ (u t)) x =
      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y ∧
    ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2))
```

Actual output:

```text
∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (t : ℝ),
            0 < t →
              t ≤ 1 →
                Integrable
                    (fun x => ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x‖ * ‖x‖ ^ α)
                    volume ∧
                  ∫ (x : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x‖ * ‖x‖ ^ α ≤
                      C * t ^ (α / 2 - 1) ∧
                    Integrable (fun x => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x)
                        volume ∧
                      ∫ (x : E), (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x = 0 : Prop
∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × E → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Icc 0 T ×ˢ univ) →
                        (∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M) →
                          (∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            let u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            (∀ (x : E), u 0 x = 0) ∧
                              ∀ t ∈ Icc 0 T,
                                ∀ (x : E),
                                  ContDiff ℝ 2 (u t) ∧
                                    IntegrableOn
                                        (fun s =>
                                          ∫ (y : E),
                                            (f (s, x - y) - f (s, x)) •
                                              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                (t - s) y)
                                        (Ioo 0 t) volume ∧
                                      fderiv ℝ (fderiv ℝ (u t)) x =
                                          ∫ (s : ℝ) in 0..t,
                                            ∫ (y : E),
                                              (f (s, x - y) - f (s, x)) •
                                                (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                  (t - s) y ∧
                                        ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2) : Prop
```

## Appendix E. Strongest compiled scratch proof

This proves L7 from its genuine operator hypotheses. It is included in the report only, with no new Lean module delivered.

### E1. Correction of a bounded parametrix

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-schauder-survey/Perturbation.lean`. Actual exit: 0.

```lean
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach
set_option autoImplicit false
set_option format.width 110
noncomputable section
namespace ParabolicSchauderSurvey
 theorem corrected_right_inverse {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (P : Y →L[ℝ] X) (R : Y →L[ℝ] Y)
    (hLP : L.comp P = ContinuousLinearMap.id ℝ Y - R) (hR : ‖R‖ < 1) :
    ∃ S : Y →L[ℝ] X, L.comp S = ContinuousLinearMap.id ℝ Y := by
  let U := Units.oneSub R hR
  refine ⟨P.comp ((↑(U⁻¹)) : Y →L[ℝ] Y), ?_⟩
  rw [← ContinuousLinearMap.comp_assoc, hLP]
  change U.val * ↑U⁻¹ = 1
  exact U.val_inv
end ParabolicSchauderSurvey
#print axioms ParabolicSchauderSurvey.corrected_right_inverse
```

Actual output:

```text
'ParabolicSchauderSurvey.corrected_right_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

