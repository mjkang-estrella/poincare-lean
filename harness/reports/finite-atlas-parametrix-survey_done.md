# Finite-atlas parametrix and nonlinear DeTurck survey

Date: 2026-09-15. Base: `6a69ba044e45ae9bfc534c2a5b0c43f8adc641a5`.

> Orchestrator note (2026-09-15): this landed copy keeps sections 1-5 and Appendix A (the complete successful definition and target probe) from the worker report (lines 1-719). Appendix B (every probe with output) stays unmerged on branch `worker/finite-atlas-parametrix-survey` at its head commit.

Branch: `worker/finite-atlas-parametrix-survey`.
Pinned Mathlib: `7175569c842f9164564bd76ff8b207e7b4705522`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

## Result and scope

The finite-atlas route is viable in the landed unweighted graph norm, provided a new **full lower-derivative Hölder interpolation estimate** is proved. Sup-norm zero-trace estimates alone do not close the commutator argument. A sufficient, deliberately non-sharp pair of targets is

\[
 \|u\|_{Y_T}\le C_I T^{1-\alpha/2}\|G\|,
 \qquad \|Du\|_{Y_T}\le C_I T^{(1-\alpha)/2}\|G\|.
\]

These are proposed statements, not landed theorems or scratch proofs. The report supplies an elementary proof route and compiled statement definitions. No impossibility of the unweighted norm is claimed. A strengthened weighted norm functional is also probed, with its remaining norm-instance and uniform-solver obligations stated explicitly.

The first three gates should be the compatible tensor carriers, single-chart cutoff/interpolation estimates, and compactly supported coefficient extension plus frozen-solver error. The actual construction of a quantitatively controlled refinement, chart transport, the global operator, and the nonlinear estimates remain subsequent work. In particular, finiteness alone does not justify a radius-independent leading error constant.

Only this report is a tracked deliverable. No tracked Lean file, frozen contract, root import, HANDOFF or ledger was edited. The task-specific report-only scope and supplied worker branch override the general handoff and branch-prefix instructions. Initial status was clean. The current commit and worktree inventory were checked before reading ledgers. README, HANDOFF's top section, PROJECT_MAP, the task and frozen-task files, design review Q1/Q2, decomposition sections 3.2–3.4 and plan-3's dispatch format were read. HANDOFF's “awaits review” prose does not override the modules present at this base.

Evidence labels below:

- **Repo/proved**: an existing theorem at the base, with its actual hypotheses.
- **Repo/definition**: an existing carrier or formula, not an existence theorem.
- **Mathlib**: an existing pinned declaration.
- **Absent/new**: no implementation of the stated content was found in the searches. This does not assert logical nonderivability.
- **Assumed in flight**: only the user-authorized frozen analytic conclusion. No new declaration is attributed to the base.

A/B/C classify proposed work: A is a direct bounded construction or estimate from existing tools; B requires a substantial new analytic/geometric argument; C is an invalid inference or insufficient hypothesis. A does not mean already proved.

## 1. Function spaces on the manifold

### 1.1 Fix the geometric data before the forcing

Let `E = ClosedSmoothModel 3`, `I = closedSmoothModelWithCorners 3`, `0 < α < 1` and `0 < T ≤ 1`. A compact smooth Hausdorff manifold suffices for this analytic construction; connectedness and simple connectivity are not needed.

`FiniteExtendedChartCover` is a **repo definition** with `chartCount`, `anchor`, and `sources_cover`. `exists_finiteExtendedChartCover` is **repo/proved**. `ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover` returns open sets `V i` covering the manifold, closures contained in the corresponding chart sources, compact coordinate images of those closures contained in the targets, and a `SmoothPartitionOfUnity` subordinate to `V`. It does not return quantitative diameters, cutoff derivative constants or bounded overlap numbers.

Write `φᵢ = extChartAt I (C.anchor i)`, and let `χᵢ` be the supplied partition. Its subordination means `tsupport χᵢ ⊆ Vᵢ`. Set

\[
 K_i=\phi_i(\operatorname{tsupport}\chi_i).
\]

These sets are compact and lie inside the chart targets. The compactness and image arguments still need a short adapter for these particular supports. The landed shrinking theorem gives the larger compact coordinate closures directly.

For the PDE, refine inside the **cutoff-one** regions of the host charts. `FiniteFixedAnchorCutoffOneChartCover.compactCoordinateSet_subset_cutoffOneGermLocus` supplies the relevant geometric inclusion, and `compactCoordinateSet_subset_chart_target` supplies the domain inclusion. This is essential because `DeTurckPrincipalIdentity.principalIdentity` has the hypothesis that `GeodesicTransport.cutoff anchor` is locally one. An arbitrary member of `exists_shrunk_chart_cover` need not satisfy it.

Use nested compact buffers and cutoffs

\[
 \operatorname{supp}\chi_i\Subset\{\psi_i=1\},\qquad
 \operatorname{supp}\psi_i\Subset\{\xi_i=1\}\Subset U_i,
 \quad 0\le\psi_i,\xi_i\le1.
\]

`exists_cutoff_of_isCompact` is **repo/proved**, but returns support inside a requested open set, not explicitly compact support. First choose that open set precompact with closure inside the larger chart domain. Then its closed cutoff support is compact. This extra buffer must not be omitted.

A small-radius refinement generally needs many patches in one host chart. Distinguish its fixed host-chart anchor from the patch's freezing point `pᵢ`. One can repeat host anchors in the finite indexing and freeze at points inside their domains. Do not claim that one arbitrarily small neighborhood of each original chart anchor still covers `M`. Using fixed finitely many host charts, then translated small coordinate patches, also avoids uncontrolled coordinate changes as the radius varies. `OscillationData.anchor` in the probe is this freezing point in coordinates.

### 1.2 The actual stored entries and the weighted law

Use nine scalar entries per patch and impose symmetry. This avoids an extra six-component encoding. For a tensor `f`, the stored entry is the zero extension of

\[
 F_i^{ab}(t,z)=\chi_i(\phi_i^{-1}z)
    (f\text{ in chart }i)_{ab}(t,z).
\]

The ambient forcing norm is the ordinary finite-product maximum of the landed scalar sum norms. The ambient solution norm is the finite-product maximum of `Graph` norms. Each `Graph` norm is exactly the sum of the four `Y` norms, for `u`, `ut`, `du`, `ddu`. These are explicit norm choices, not unnamed equivalent norms.

At a point `x` in both chart sources, put

\[
 J_{ji}(x)=D(\phi_j\circ\phi_i^{-1})(\phi_i x).
\]

The correct overlap equation is

\[
 \chi_j(x) F_i^{ab}(t,\phi_i x)
 =\chi_i(x)\sum_{c,d}J_{ji}(x)^c{}_aJ_{ji}(x)^d{}_b
             F_j^{cd}(t,\phi_j x).                 \tag{1}
\]

It is not the ordinary unweighted transition equation on `F_i`. Never divide globally by `χᵢ`. The structure fields probed in Appendix A are:

- `entries`: one scalar `Y`, or one scalar `Graph`, for every `(i,a,b)`;
- `supported`: its value is zero outside `Kᵢ`, for every real time;
- `symmetric`: the `(a,b)` and `(b,a)` values agree;
- `transition`: equation (1) on actual chart-source intersections.

`AtlasData` uses the actual `FiniteExtendedChartCover`, `extChartAt` and `SmoothPartitionOfUnity` types. `jac` is the actual Fréchet derivative of the coordinate transition, evaluated on the Euclidean basis. It is not an independently supplied transition matrix. `CompatibleFields` gives the record presentation. `tensorSubmodule` gives the implementation as the intersection of support, symmetry and overlap kernels. `Y_M` and `X_M` are the corresponding subtypes. All definitions are in the final successful probe in Appendix A.

For `X_M`, impose (1) on `Graph.u`, not the same tensor law on all four jets: spatial differentiation of (1) also differentiates the partition and transition coefficients. Those differentiated identities follow from the actual derivative relations in each graph. Support and symmetry of the derivative entries likewise follow from the value equations and derivative uniqueness. Restrict reconstruction to `T>0`; on the degenerate interval `T=0` the within-time derivative need not be uniquely determined. `Graph.ext_of_u` is **repo/proved** with the positive-time hypothesis, and is the relevant value-to-graph uniqueness tool. It is not uniqueness for a PDE merely from equal initial values.

### 1.3 Why these are closed subspaces

For each fixed point, `evalY` and `evalX` are continuous linear functionals. Their bounds come from `ParabolicHolder.norm_le` and `ParabolicSolutionGraph.sup_u_le`. A finite-product projection followed by either evaluation is continuous linear. Every constraint above is a kernel of a continuous linear functional, with fixed scalar coefficients. Arbitrary intersections of those kernels are closed.

Use **Mathlib** `ContinuousLinearMap.isClosed_ker` and `isClosed_iInter`, then `IsComplete.completeSpace_coe`. The templates already used in the repository are `ParabolicHolder.isClosed_holderSubmodule` and `ParabolicSolutionGraph.isClosed_graphSubmodule`. The scalar `Y` and `Graph` complete-space instances are landed. Task 1 supplies the missing closedness, inherited completeness and equivalence to the record presentation; defining the predicates in a probe does not prove these results.

Closedness of (1) needs **no uniform bound or continuity in `x` of `J`**. For this argument `x` is fixed before taking the kernel. This is quite different from proving that chart pullback is a bounded map between Hölder spaces.

### 1.4 Construction and recognition of genuine fields

`ParabolicHolder.ofFunction` accepts off-cylinder zero, boundedness and Hölder witnesses. It does not prove the zero extension across a spatial chart boundary is Hölder. `ParabolicSolutionGraph.ofDerivatives` additionally asks for actual spatial, second-spatial and within-time derivative identities. The buffered support construction must supply these witnesses, including smooth product rules and zero-near-boundary arguments. Multiplying a graph by a cutoff requires the product jets, not multiplication of all four old entries by the same cutoff.

`TensorField T`, `inverseFrame`, `localizedValue` and `reconstructionGoal` are also probed. `TensorField T` has the genuine type

```lean
(t : Set.Icc (0 : ℝ) T) → (x : M) →
  TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
```

The reconstruction should be the finite sum of pushed localized tensors. On a chart, equation (1) and `∑χᵢ=1` show that localizing that sum recovers every stored entry. Equivalently, locally choose a positive partition member and divide there, then prove independence of that choice. Positivity at each point follows from the nonnegative partition summing to one. The sum construction avoids estimates involving reciprocals of small partition values.

The proposed reconstruction theorem states existence and uniqueness of the field on the time cylinder with exactly those localized values. For `X_M`, the graph identities then give the field's chartwise `C^{2,α}` spatial and `C^{1,α/2}` time regularity. No smooth metric family follows just from this regularity.

### 1.5 Which transition bounds are missing

For scalar composition in `X`, `C^{2,α}` control of a coordinate transition and a Lipschitz inverse on buffered overlap sets is enough. A **covariant 2-tensor** also carries two factors of its transition Jacobian. Taking two derivatives of those factors involves third derivatives of the coordinate transition. Thus tensor `X` transport needs `C^{2,α}` bounds for the Jacobian factors, for example `C^{3,α}` bounds for the transition map itself. Merely saying “the chart transition is `C^{2,α}`” loses a derivative.

The smooth finite atlas has the required bounds on **compact buffered overlaps**, not automatically on the entire open overlaps. A verified **Mathlib route** is:

1. `ModelWithCorners.contDiffOn_extendCoordChange`, using `chart_mem_maximalAtlas`, gives smooth coordinate changes on their actual overlap domains.
2. `ContDiffOn.fderiv_of_isOpen` iterates derivatives there. Local compact buffers or a cutoff extension retain the domain restrictions.
3. `ContDiff.continuous_iteratedFDeriv` and compactness bound the needed derivatives. For Hölder control one may use one further derivative and a smooth compactly supported extension.
4. `ContDiff.lipschitzWith_of_hasCompactSupport` gives a global Lipschitz bound for such an extension. The repo's `DuhamelSolutionOperatorBound.holder_of_bounded_lipschitz` converts bounded Lipschitz spatial data to an `α`-Hölder bound. Its displayed constant is `2A+B`, not the sharper multiplicative interpolation constant.

No packaged finite-atlas tensor `C^{2,α}` pullback bound was found. It is **absent/new**. For arbitrary nonconvex overlap sets, do not apply a convex-set mean-value theorem without buffers, an extension or a finite-neighborhood argument.

## 2. Frozen local solvers and the error

### 2.1 Define the linearization honestly

Fix the background in the DeTurck vector field and the initial metric `g₀`. In a valid host chart write

\[
 Q(g)=a(g):D^2g+\ell(x,g,Dg),\qquad a(g)=g^{-1}.
\]

The identification of the principal part is **repo/proved** by `principalIdentity`; `lowerTerm` is the **repo definition** of the explicit rational first-jet expression with fixed background Christoffel data and its derivative. The probe's `coordinateQ` uses exactly `DeTurckPrincipalSecondJet.inverseEntries` and `DeTurckPrincipalIdentity.lowerTerm`. Its `linearizedJet` defines the candidate sum of metric and first-jet partial Fréchet derivatives plus the explicit second-jet linear term. It is not a theorem identifying the derivative of the geometric operator.

The derivative to establish is

\[
 DQ(g_0)h=a_0:D^2h+
       Da(g_0)[h]:D^2g_0+
       D_G\ell(x,g_0,Dg_0)[h]+D_J\ell(x,g_0,Dg_0)[Dh].       \tag{2}
\]

Package its last three terms as the coupled first/zero-order system `B₀^a ∂ₐh + C₀h`. The term `Da(g₀)[h]:D²g₀` belongs to the zero-order coefficient. Applying the nonlinear `lowerTerm` directly to `h` would not be this linearization.

Thus `L=∂ₜ−DQ(g₀)` has chart expression `∂ₜ−a₀^{ab}∂ₐ∂ᵦ−B₀^a∂ₐ−C₀`. Construction of this operator as a bounded map `X_M →L Y_M`, its chart covariance, and its agreement with (2) are **absent/new**, not supplied by `principalIdentity` alone.

### 2.2 Freeze and solve

At a patch freezing point `pᵢ`, in the chosen host frame, set

\[
 A_{0i}^{ab}=a_0(\phi_i(p_i))^{ab}=g_0^{-1}(p_i)^{ab}.
\]

`CompactCoefficientEllipticity.exists_uniform_coercivity` supplies a common positive quadratic lower bound for a **supplied continuous positive bilinear family on a compact parameter space**. Apply it after identifying the inverse coefficient. Upper and Hölder bounds, and coercivity of a perturbation ball, are additional steps; this module is not already a bounded-inversion theorem.

Choose `Sᵢ⁰` with zero initial trace solving `∂ₜwᵢ−A₀ᵢ:D²wᵢ=fᵢ`, with `‖Sᵢ⁰‖≤C_S`, uniformly for short `T`. There are two valid routes:

- the authorized in-flight elliptic solver plus its continuous-linear-map packaging;
- conjugating `DuhamelSolutionOperatorCLM.duhamelOperator` by the fixed linear coordinate change, with forcing, graph and trace identities and norm comparisons.

The actual frozen task file at this base asks for **existence of a graph and a uniform bound**, not a CLM or a near-variable-coefficient inverse. This is narrower than the conversational description. The user permits assuming the in-flight analytic conclusion, but one must still verify its eventual API. `FrozenSolver` and `frozenCLMGoal` in the probe spell out the extra interface needed here. Choosing an arbitrary graph separately for every forcing does not prove linearity. Use a fixed conjugated Duhamel construction, or a genuine uniqueness theorem for the frozen PDE, before packaging the map. `Graph.ext_of_u` alone is not that uniqueness theorem.

The landed `nearIdentityInverse` solves the identity-plus-small-Hölder-perturbation problem, and its quarter-bound hypotheses and `2 C_S` estimate are real. A corresponding near-`A₀` solver can absorb the oscillation in advance. To display the three errors requested here, use the constant frozen solver `Sᵢ⁰`; if a near-`A₀` solver is used instead, the corresponding principal error vanishes on the patch.

The forcing `fᵢ` is already the scalar entry stored in `Y_M`, including zero extension. For each tensor component set `wᵢ=Sᵢ⁰ fᵢ` and form

\[
 Pf=\sum_i\operatorname{push}_i(\psi_i w_i).
\]

To store this result in `X_M`, localize the entire sum by every `χⱼ`, transform its tensor components, and build the product-rule derivative graphs. Independently placing `wᵢ` in the `i`th slot is not a compatible global parametrix.

### 2.3 Exact error and sign convention

Use `L_i=∂ₜ−a₀:D²−B₀^a∂ₐ−C₀`. In each patch,

\[
 L_i(\psi_i w_i)-\psi_i f_i
 =-\psi_i(a_0-A_{0i}):D^2w_i
   +[L_i,\psi_i]w_i
   -\psi_i(B_0^a\partial_aw_i+C_0w_i),                   \tag{3}
\]

where

\[
 [L_i,\psi_i]w_i
 =-\sum_{a,b}a_0^{ab}
       ((\partial_a\psi_i)\partial_bw_i+
        (\partial_b\psi_i)\partial_aw_i+
        (\partial_a\partial_b\psi_i)w_i)
   -\sum_a B_0^a(\partial_a\psi_i)w_i.                    \tag{4}
\]

There is no `∂ₜψᵢ` term since the cutoff is time independent. With symmetric `a₀`, the first two terms combine to `−2a₀^{ab}∂ₐψᵢ∂ᵦwᵢ`. The zero-order potential commutes with the scalar cutoff, including for the tensor system. Formula (4) is only first order **in `wᵢ`**; it includes second derivatives of `ψᵢ`.

Push and sum (3). Since `ψᵢχᵢ=χᵢ` and `∑χᵢ=1`, the forcing sum is `f`. This gives `LPf−f` as exactly the sum of the three displayed error types. Define `R=Id−LP`, so the right side of (3), after assembly, is **minus** `Rf`.

### 2.4 Oscillation estimate

Extend entries by

\[
 b_i^{ab}(t,z)=\mathbf1_{[0,T]}(t)\,
       \xi_i(z)(a_0^{ab}(z)-A_{0i}^{ab}).
\]

Choose `ξᵢ=1` on `supp ψᵢ`. Its whole support must remain in the small oscillation patch, not just its one-locus. Then `sup|b_i^{ab}|≤ε=ω_a(ρ)` and `[b_i^{ab}]_{α;p}≤Λ_ρ`, uniformly in `T`. The latter includes derivatives of `ξᵢ`; it need not be small. `oscillationExtensionGoal` probes the construction with the actual smooth coefficient on an open set, compactly supported cutoff, local oscillation hypothesis and constants quantified before `T`. `ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn` supplies smoothness of the genuine inverse entries. The scalar cutoff-extension template is `contDiff_cutoff_mul`.

The landed **repo/proved** estimates are exactly

\[
 \|b_i:D^2G\|_{Y_T}
 \le9(\varepsilon+\Lambda_\rho T^{\alpha/2})\|G\|,
\]

from `ParabolicHolderMultiplier.norm_forcing_le`, and

\[
 \|b_i:D^2S_i^0f_i\|_{Y_T}
 \le9C_S(\varepsilon+\Lambda_\rho T^{\alpha/2})\|f_i\|_{Y_T},
\]

from `norm_error_le`. These are scalar component estimates before tensor assembly. All tensor-component counts, transitions and finite-overlap constants must be included when estimating `Y_M`.

### 2.5 What is and is not small in time

| Quantity | Exact present evidence | Consequence |
| --- | --- | --- |
| `u` sup | **Repo/proved** `ParabolicSolutionGraph.time_bound`: `‖G.u(t,x)‖≤t‖G.ut‖` | At most `T‖G‖` on the cylinder. |
| `Du` trace | **Repo/proved** `ParabolicHolderMultiplier.du_zero_trace` | With `holder_le`, comparing time `t` to zero gives the **derived, not separately landed** bound `‖Du(t,x)‖≤t^(α/2)‖G.du‖`. It gives only a sup factor. |
| `D²u` sup | **Repo/proved** `ddu_time_bound` and `supNorm_ddu_le` | At most `T^(α/2)‖G‖`. |
| Duhamel `Du` sup | **Repo/proved** `DuhamelSolutionOperatorBound.duhamel_gradient_bound` | A kernel constant times `sqrt t` times forcing sup, for that integral solution. It is not an arbitrary-graph full-`Y` estimate. |
| Full `u`, `Du` in `Y` | Landed `norm_u_le`, `norm_du_le` | Bounded by `‖G‖`, with **no displayed small time factor**. |

In `norm_mul_split`, the term `sup|b| · ‖Du‖_Y` remains large for a fixed commutator coefficient if only the last row is used. Replacing `sup‖Du‖` by a time factor in the other product term does not fix it. Zero trace of a general Hölder function does not make its Hölder seminorm small: `t^(α/2)` is the basic obstruction. The extra derivative-graph relations are what permit a repair.

Here is a sufficient proof route for the proposed `interpolationGoal`, using only genuine graph relations. Write `M_G=‖G‖` and `δ=|t−s|`.

1. The mean-value estimate from `ut` gives `sup|u(t)−u(s)|≤δ M_G`.
2. Prove the elementary scalar finite-difference bound along unit directions,
   `|Dh(x)v|≤2 sup|h|/η+(η/2)sup‖D²h‖`, for every `η>0`. Obtain the quadratic remainder by integrating, or applying the mean-value bound to, the first derivative along the line segment. The verified **Mathlib** primitives are `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` and its one-dimensional derivative version. No prepackaged Landau interpolation inequality was found.
3. Apply step 2 to `h=u(t)` with `η=sqrt T`, and to `h=u(t)−u(s)` with `η=sqrt δ`. The Hessian bounds `M_G` and `2M_G` give `sup‖Du‖≤C sqrt T M_G` and `sup‖Du(t)−Du(s)‖≤C sqrt δ M_G`. The case `δ=0` is separate.
4. Spatial gradient increments satisfy `‖Du(t,x)−Du(t,y)‖≤M_G‖x−y‖`. Combine this with the gradient sup bound and split at `‖x−y‖=sqrt T`. This gives a spatial `α`-Hölder constant `C T^((1−α)/2)M_G`. Temporal increments from step 3 give the same factor after dividing by `δ^(α/2)`.
5. For values, combine `sup|u|≤TM_G` with spatial Lipschitz bound `C sqrt T M_G`, again splitting at `sqrt T`. Together with the time-Lipschitz estimate, this gives `C T^(1−α/2)M_G`. Split a mixed increment through `(t,y)` to obtain the parabolic bound. Then use `ParabolicHolder.norm_le_of_bounds`.

This proves the desired shape on paper for `0<α<1`, `0<T≤1`; the Lean proof remains **B/new**, beginning at the finite-difference derivative estimate. It does not assume a time derivative of `Du`, and does not try to make the Hessian's full Hölder norm small. The landed bounded-Lipschitz helper uses a fixed unit-scale split, so it does not by itself supply the sharper time powers in steps 4–5.

### 2.6 Commutators, lower-order terms and the global constants

Let `K_{b,i}=∑ₐ‖bᵢᵃ‖_Y`, `K_{c,i}=‖cᵢ‖_Y` for the scalar coefficients in (4), including the fixed cutoff derivatives. The proposed single-chart estimate, from full interpolation and `ParabolicHolder.norm_mul_le`, is

\[
 \|[L_i,\psi_i]G\|_Y
 \le C_I(K_{b,i}T^{(1-\alpha)/2}
           +K_{c,i}T^{1-\alpha/2})\|G\|.
\]

The coupled first/zero-order terms in (3) have the same estimate, summed over input components, with their coefficient norms denoted `K_{B,ρ}` and `K_{C,ρ}`. Constants are finite after buffers are fixed, and independent of `T≤1` for these time-independent smooth coefficients. Neither estimate is landed as a commutator theorem. `CutoffData`, `firstOrderValue`, `localLinearValue`, `cutoffIdentityGoal` and `commutatorGoal` probe the exact scalar algebra and the estimate that a later tensor sum uses.

After controlled assembly one targets

\[
 \|R\|\le C_0 C_S\omega_a(\rho)
       +C_\rho C_S(\Lambda_\rho T^{\alpha/2}
                                +T^{(1-\alpha)/2}).       \tag{5}
\]

Thus one may use `θ=min(α/2,(1−α)/2)>0` in the coarser two-term estimate. For the nonlinear step one may also choose this weaker common exponent.

There is a further **geometric gate** in (5). `C₀` must remain controlled while choosing `ρ`. A crude bound with the number of patches `N(ρ)` or a full cutoff Hölder norm in front of `ω(ρ)` does not suffice. Smooth coefficients give `ω(ρ)=O(ρ)`, whereas an uncontrolled factor such as `N(ρ)` may overwhelm it. Finite cover extraction alone proves none of the required uniformity.

A valid route fixes finitely many host charts and compact buffers, then uses equal-scale coordinate refinements with uniformly bounded neighboring-patch counts and cutoffs bounded in sup by one. In the product norm, use the bounded neighbor count for the leading high-order error. Apply the split product estimate: derivatives/Hölder seminorms of assembly cutoffs and transitions multiply **sup** Hessian errors, so their radius-dependent cost can go into the time-small term. `Y_M` already stores `χᵢf`, so extraction itself is a product projection without a cutoff-derivative cost. Proving this separated estimate and the controlled refinement is **absent/new**. Choose `ρ` only after this radius-independent leading bound is established; then keep all `C_ρ,Λ_ρ` fixed and shorten `T`.

An alternative is a spatially scaled localization norm, together with explicit reconstruction/extraction bounds. Merely choosing a finite atlas and then declaring `C₀ω(ρ)` small is not a proof.

### 2.7 Weighted alternative and its limits

The optional probed functional is

\[
 \|G\|_{X,T,w}=T^{-(1-\alpha/2)}\|u\|_Y
       +T^{-(1-\alpha)/2}\|Du\|_Y+\|ut\|_Y+\|D^2u\|_Y.
\]

For each fixed positive `T` this is a positive weighted sum of component norms, hence equivalent to the original graph norm. A later task can transfer a normed-space and complete-space structure through the weighted product embedding. The probe defines `weightedSize`; it does **not** install or prove that norm instance. A bound on the solver in this stronger norm uniformly as `T→0` still needs the interpolation estimate above, or separate kernel estimates. Renaming a weighted norm does not supply that bound. Weakening the Hessian norm with a vanishing time weight also does not fix the diagonal singularity of bounded-data heat inversion. The unweighted route above is the recommended task sequence.

## 3. Global-to-local equivalence and Neumann correction

The global linear gate must contain all of the following:

1. Construct the buffered pullback, scalar cutoff and finite push/sum maps with their actual derivative formulas. Prove `P : Y_M →L[ℝ] X_M`, with a `T`-uniform bound after the geometry has been fixed.
2. Construct the actual operator (2) as `L : X_M →L[ℝ] Y_M` and prove covariance, support after localization and agreement with the genuine tensor equation. The localized rate is `χᵢLu`; it is not simply `Lᵢ` applied to the stored `χᵢu` without the corresponding commutator corrections.
3. Prove `L.comp P = ContinuousLinearMap.id ℝ Y_M − R` with the error computed in (3)–(4), and then (5) with `‖R‖<1`.
4. Apply the **repo/proved** `ParametrixNeumannCorrection.exists_right_inverse`. Its exact result is `∃ S : Y_M →L[ℝ] X_M, L.comp S = ContinuousLinearMap.id ℝ Y_M`. It requires completeness of `Y_M`; it does not itself construct any of the preceding analytic maps.
5. For `u=Sf`, use the reconstruction theorem and derivative consistency from section 1 to recover a genuine symmetric time-dependent tensor. Equality in `Y_M` gives equality of every localized equation. At each point some partition member is positive, so the original equation follows there, independently of the selected chart. The graph trace gives zero initial tensor value and the graph time derivative is the within-interval one at both endpoints.

For the nonlinear bound also record `‖S‖≤‖P‖/(1−‖R‖)`, or an explicit `2‖P‖` bound when `‖R‖≤1/2`; the existence theorem's statement alone does not print a quantitative constant. The landed near-identity module contains the corresponding one-half Neumann norm argument as a template.

Independent Euclidean heat solutions with matching initial data do not automatically match on chart overlaps. The compatible carrier and construction of the **global** residual are essential. A right inverse also does not prove uniqueness for the whole linear PDE. The survey's L8 uniqueness, restriction consistency and time-slab continuation remain separate obligations if the final task quantifies over all `T≤1`. This report only plans existence on a sufficiently short interval, with constants uniform under shortening; it does not discharge that stronger all-slab contract.

## 4. Nonlinear short-time existence

Let `q₀=Q(g₀)`, `g*(t)=g₀+tq₀` and `g=g*+v`, with `v∈X_M`. The correct equation is

\[
 Lv=N(v),\qquad
 N(v)=Q(g_0+tq_0+v)-q_0-DQ(g_0)v.
\]

Here `L` and its right inverse are those of section 3. The reference family is known data, not an element of the zero-trace graph. Do not subtract `DQ(g₀)(tq₀)` from this definition unless it is restored on the other side.

### 4.1 Lemmas to freeze

| Order | Needed lemma and exact content | Status / class |
| --- | --- | --- |
| N1 | Positive perturbation ball: if `g₀≥κI` on every buffered chart and `sup‖h‖≤κ/2`, then `g₀+h≥(κ/2)I`. Apply the manifold sup embedding to `h=tq₀+v`. | Compact background coercivity is **repo/proved**; its application, the embedding constant and perturbation estimate are A/new. |
| N2 | Uniform inversion and Hölder differences on that ball: `sup‖g⁻¹‖≤2/κ`, `[g⁻¹]α≤(2/κ)²[g]α`, and `‖g⁻¹−h⁻¹‖Y≤C_inv‖g−h‖Y` for fixed coefficient bounds. Also prove the quadratic remainder/difference estimate for inversion after subtracting `Da(g₀)`. | **B/new** as a packaged Hölder-composition result. `exists_uniform_coercivity` does not prove it. `contDiffAt_ringInverse` and `hasFDerivAt_ringInverse` are **Mathlib** pointwise calculus tools, with the derivative `h↦−g⁻¹hg⁻¹`; a matrix/bilinear representation adapter is still needed. |
| N3 | Finite contraction and product estimates for the actual `inverseEntries` and `lowerTerm`, including their first derivative and its local Lipschitz bound on bounded positive metric/first-jet sets. | Scalar product inequality is **repo/proved** by `norm_mul_le` and `norm_mul_split`. Quantitative rational tensor composition and its remainder are B/new. Background Christoffel coefficients and their derivative are fixed, but their norms must appear in the constants. |
| N4 | Identify (2), build `DQ(g₀)`, and bound its actual nonlinear remainder on the ball. | B/new. The pointwise principal identity is landed; a bounded Fréchet linearization on the proposed manifold spaces is absent. |
| N5 | For `F(t)=N(0)(t)=Q(g₀+tq₀)−q₀`, prove `F(0)=0`, the actual time derivative `∂ₜF(t)=DQ(g₀+tq₀)q₀`, and a uniform spatial `C^α` bound for that derivative on a fixed reference interval. | B/new, using quantitative smoothness of the initial metric and fixed background. Zero trace alone is insufficient. |
| N6 | Prove `‖N(v)−N(w)‖Y_M≤C_NL(r+T^θ)‖v−w‖X_M`, and `‖N(0)‖Y_M≤C_ref(T+T^(1−α/2))`. | B/new, with `C_NL,C_ref` independent of `r,T` in fixed prior ranges. `nonlinearGoal` probes exactly this conclusion, not its proof. |
| N7 | Invariant closed ball and contraction for `v↦S(N(v))`; recover the positive metric and its equation. | A once N1–N6 and the global inverse exist. Use **Mathlib** `ContractingWith.fixedPoint_isFixedPt` on the closed ball with its inherited complete metric. |

The exact first missing analytic lemma in this nonlinear ordering, after the elementary positive-ball adapter, is **bounded Hölder inversion with a quadratic difference remainder on a uniformly coercive tensor ball**, not scalar multiplication or the DeTurck principal cancellation. Before dispatching it, the carrier and its geometric sup embedding must have passed. The first missing identification lemma for the actual PDE is (2) together with its covariance on these carriers.

### 4.2 The remainder estimates

Use the algebraic identity `g⁻¹−h⁻¹=g⁻¹(h−g)h⁻¹` and its once-linearized version; these formulas here are proof routes, not unverified theorem names. Product estimates keep coefficient sup norms distinct from their Hölder seminorms.

After subtracting `DQ(g₀)(v−w)`, the top-order pieces contain

\[
 (a(g^*+v)-a(g_0)):D^2(v-w),\quad
 (a(g^*+v)-a(g^*+w)):D^2w,
\]

plus background/reference-Hessian terms with the linearized coefficient contribution removed, and first-jet remainders of `lowerTerm`. The first coefficient is `O(r+T^θ)` in the required sup/Hölder bounds; the second is Lipschitz in `v−w` and multiplies a graph bounded by `r`. The split product estimate and zero-trace Hessian sup factor handle `[a]α sup‖D²(v−w)‖` without claiming smallness of `[D²(v−w)]α. First-order terms use the full interpolation from section 2.5 or their small nonlinear coefficient differences. Every coupled component contraction adds a fixed finite constant.

For N5, suppose the localized `∂ₜF(t)` has both a common spatial sup bound `K_ref` and spatial `α`-Hölder bound `K_ref` for `0≤t≤T_ref`, and the stated derivative is genuine. Integration from zero gives the sup and spatial-seminorm bounds `K_ref T`; time increments satisfy `|F(t,x)−F(s,x)|≤K_ref|t−s|`, hence temporal `α/2` seminorm at most `K_ref T^(1−α/2)`. Splitting mixed increments yields the required `C_ref(T+T^(1−α/2))`.

Smoothness of `g₀` supplies enough derivatives, but the quantitative N5 premise must actually be proved. In particular `DQ(g*)q₀` contains `D²q₀`; since `q₀` already contains second derivatives of `g₀`, controlling only the second jet of `g₀` is insufficient. Choose a fixed small positive reference interval on which `g*` stays coercive, establish the needed higher spatial derivative bounds there, and then restrict to smaller `T`. This avoids constants secretly depending on the same `T` one is trying to shorten.

Take a prior radius range on which these constants are uniform. Choose `r>0` so that `C_S^glob C_NL r≤1/4`, then `T>0` so that

\[
 C_S^{glob} C_{NL}T^\theta\le1/4,\qquad
 C_S^{glob} C_{ref}(T+T^{1-\alpha/2})\le r/2,
\]

and the positivity/reference restrictions hold. This makes the ball invariant and the map one-half contracting. The reference ansatz removes the initial-rate obstruction: `S Q(g₀)` need not be small in the full graph norm, since `ut(0)=Q(g₀)`.

### 4.3 Invalid shortcuts and remaining regularity

The following are C: deducing small forcing Hölder norm merely from zero trace; asserting bounded inversion from compact coercivity without estimates; substituting a nonlinear `lowerTerm(h,Dh)` for the linearization; asserting covariance of independently solved chart equations; and applying `principalIdentity` directly to a graph-regular metric as if it were already a `ClosedSmoothRiemannianMetric`.

The existing `principalIdentity` quantifies over smooth metrics. The contraction produces a chartwise `C^{2,α}` metric with the stated time derivative. Define `Q` by its jet formula and prove covariance and agreement with the geometric expression at that regularity, using pointwise jet algebra or a justified jet-realization argument. Positive-time smoothness and the joint higher regularity needed by downstream smooth-family consumers require a subsequent bootstrap. The existing `closedSmoothRiemannianMetricOfChartwiseSelf` is an assembly definition with a supplied smoothness premise; it does not remove this gap. Short-time DeTurck existence also leaves the inverse-gauge flow, long-time continuation and Hamilton estimates outside this task.

## 5. First three gated Lean tasks

### Shared dispatch contract

Task 1 can be frozen at the base above. For tasks 2 and 3, freeze an actual commit containing the accepted dependencies before dispatch; no future hashes are invented. A worker owns only its named new Lean file and its job evidence. Existing Lean sources, root imports, frozen contracts, other workers' files and infrastructure remain forbidden. Do not merge or mark acceptance from a worker. The names below are **proposed**, not landed declarations.

Each target named below is a proposition-valued definition in Appendix A. The eventual theorem must have exactly that proposition, with the same quantifier order and actual definitions. The source definitions and constructor checks do not prove any existence target. Use `autoImplicit false`. Each task gate includes the focused command, a no-match scan for the prohibited tokens, `git diff --check`, exact target-type assignment probes and foundational-dependency inspection of all new declarations. The orchestrator independently reruns the gate from its frozen base. A root build/audit is an integration checkpoint, not an extra worker full build.

### 1. `Poincare/Global/FiniteAtlasParabolicTensorSpace.lean`

Objective: define the actual compatible forcing and zero-trace solution carriers and prove they are complete normed real vector spaces, with the record and submodule presentations equivalent.

Base: `6a69ba044e45ae9bfc534c2a5b0c43f8adc641a5`.

Imports: `ParabolicSolutionGraph`, `ClosedLaplacianStokesGlobalCoefficients`; use the existing manifold and finite-product imports transitively or add the direct Mathlib projection import. Additional geometry such as cutoff-one refinement is a consumer condition, not needed for closedness.

Definitions: Appendix A through `carrierFieldsGoal`, retaining the genuine chart/partition structure. Main targets are `carrierClosedGoal A ev`, `carrierCompleteGoal A α T`, and `carrierFieldsGoal A ev`. Also expose membership characterizations for support, symmetry and weighted overlap, and bounded entry evaluation. Install the inherited instances rather than replacing `Y_M` or `X_M` by the ambient product.

Proof route: intersections of continuous-functional kernels, finite-product completeness, inherited submodule norm. Support compactness uses the supplied subordinate partition and compact coordinate closure. The target is mathematically substantive because it selects actual weighted compatible tensors, rather than accepting an unspecified closed submodule as an input.

Stop: the targets and instances pass, with no change to the overlap law. A blocked report must show the exact kernel/membership/instance goal. Reconstruction as `TensorField` is the next geometric consumer; `reconstructionGoal` is probed to fix its meaning, but full chart-transport estimates are not hidden inside this first gate.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
git diff --check
```

### 2. `Poincare/Global/ParabolicCutoffCommutator.lean`

Objective: prove the full lower-derivative time interpolation and the bounded scalar cutoff commutator of an actual second-order operator.

Base: freeze the exact accepted head at dispatch; the scalar analytic proof can be developed without task 1's geometry. Imports: `ParabolicHolderMultiplier`, `DuhamelSolutionOperatorBound`, plus Mathlib mean-value/Taylor tools actually used.

Targets: `interpolationGoal`, then `commutatorGoal`, `cutoffGraphGoal D`, and `cutoffIdentityGoal D potential`. The finite-difference estimate in section 2.5 is the first named intermediate lemma. `CutoffData.b_eq` and `.c_eq` tie the coefficient estimate to the actual cutoff derivatives and principal/drift coefficients. The estimate must include the complete `Y` norm, not just pointwise bounds. For nonsymmetric principal coefficients the probed `b_eq` correctly uses `aⱼₖ+aₖⱼ`.

For a real smooth cutoff, also construct its cylinder-restricted value/first/second derivative `Y` carriers, then build the product graph with

`u'=ψu`, `ut'=ψut`, `du'=Dψ·u+ψdu`, and `ddu'=D²ψ·u+Dψ⊗du+du⊗Dψ+ψddu`.

The cutoff is compactly supported. Its smooth derivative bounds give the `Y` witnesses. Time is fixed during spatial product rules and the cutoff is constant during the within-time rule. For the commutator coefficient constructors, multiply these derivative carriers by the supplied coefficient carriers. Their sizes are measured by the explicit `K_b,K_c`; no independent smallness assumption is smuggled into the task.

Stop: all named targets pass, or record the exact first failing finite-difference, increment or product-jet goal and the strongest proved intermediate result. A bound `C‖G‖` without a positive time power does not meet this gate. No sharp exponent beyond the probed sufficient exponents is required.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/ParabolicCutoffCommutator.lean
git diff --check
```

### 3. `Poincare/Global/BufferedFrozenParabolicSolver.lean`

Objective: construct the genuinely extended coefficient errors from smooth chart data and transport the frozen solution operator to that chart, with the exact oscillation bound before global assembly.

Base: freeze a head containing the accepted frozen analytic result and any CLM transport adapter it needs. Imports: the eventual frozen module, `ParabolicHolderMultiplier`, `ClosedLaplacianStokesGlobalCoefficients`, `ClosedLaplacianStokesProducer`, and task 2 for cutoff transport. Inspect the in-flight result's actual signature before freezing this task.

Targets: `oscillationExtensionGoal`, `frozenErrorGoal S b`, and the actual chart/cutoff agreement supplied by `OscillationData` and `CutoffData`. `FrozenSolver` is the precise input interface. If the in-flight module only proves its currently written existential graph statement, first close `frozenCLMGoal` by the explicit conjugated-Duhamel construction in a separately scoped prerequisite or an explicitly enlarged gate. Do not accept arbitrary chosen solutions as a CLM, and do not duplicate the frozen worker's matrix-square-root proof here.

The nontrivial new part is `oscillationExtensionGoal`: construct every `bᵢⱼ` via `ofFunction` from the smooth supported product and prove a single `Λ` works for all short `T`. Specialize `a` to the genuine inverse metric in the host chart, use a freezing point in the patch, and retain equality on `supp ψ`. Then compose the supplied frozen CLM with the localized forcing projection. `frozenErrorGoal` is already directly supported by landed `norm_error_le`; proving only that wrapper is not completion of this task. It is the acceptance consequence of the new extension/transport work.

On `supp ψ`, verify the variable-principal residual by expanding the frozen equation and the actual entry equality. Apply the cutoff product map from task 2 for compact pushforward. Record every forcing/graph norm change in the fixed linear coordinate conjugation. The output is a supported local tensor contribution after componentwise solving; it does not falsely claim that one independently solved patch already lies in the global compatible carrier.

Stop: actual extended coefficient construction, transported equation and uniform scalar error bound pass. A blocked report must name whether the missing gate is frozen CLM linearity, chart coefficient smoothness/extension, transformed norm comparison or cutoff agreement. Global reconstruction, covariance, controlled-refinement constants and the final Neumann correction remain subsequent tasks with separate files.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/BufferedFrozenParabolicSolver.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/BufferedFrozenParabolicSolver.lean
git diff --check
```

First orchestrator action: extract and rerun Appendix A at the recorded base, then freeze task 1's concrete weighted-overlap definitions. Before scheduling global parametrix assembly, explicitly lease a controlled-refinement/chart-transport task that establishes the radius-independent leading constant in (5).


## Appendix A. Complete successful definition and target probe

The block below is the complete final source, not pseudocode. It contains definitions and structure constructors only; every `...Goal` is a proposition-valued definition, not a theorem asserting that proposition. The cutoff goals explicitly restrict `0<α<1` and `0<T≤1`. Their initial unrestricted versions were corrected during statement review. The current coefficient sum in `firstOrderValue` has parentheses so that the potential term occurs once, not three times.

Run the extracted source with:

```sh
PATH=/Library/Developer/CommandLineTools/usr/bin:$PATH LEAN_NUM_THREADS=1 lake env lean /tmp/finite-atlas-parametrix-survey/ReportProbe.lean
```

The PATH prefix selects the already installed Git executable that works in this environment. It does not modify system settings, accept a license or change repository configuration.

<!-- BEGIN FINAL LEAN PROBE -->
```lean
import Poincare.Global.NearIdentityParabolicRightInverse
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
import Poincare.Global.DeTurckPrincipalIdentity
import Poincare.Global.CompactCoefficientEllipticity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace FiniteAtlasSurvey
open Poincare
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold I ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set E :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : E) : E :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) (e a)) c

def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : E // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

-- Statement definitions, not proofs of closedness, completeness or equivalence.
def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

-- Positive-time candidate strengthened norm functional; no norm instance claimed.
def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=
  T ^ (-(1 - α / 2)) * ‖G.u‖ +
  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖

def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,
    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖

-- Coefficients are the resulting commutator coefficients, already zero-extended.
def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)
    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=
  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p

def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),
  ∃ K : Jet α T →L[ℝ] Scalar α T,
    (∀ G p, K G p = firstOrderValue b c G p) ∧
    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)

structure CutoffData (α T : ℝ) where
  psi : E → ℝ
  smooth : ContDiff ℝ ∞ psi
  compact : HasCompactSupport psi
  a : Fin 3 → Fin 3 → Scalar α T
  drift : Fin 3 → Scalar α T
  b : Fin 3 → Scalar α T
  c : Scalar α T
  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,
    b k (t,x) = -(∑ j : Fin 3,
      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))
  c_eq : ∀ t ∈ Icc 0 T, ∀ x,
    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,
      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -
      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)

def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=
  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
    ∀ G p, (C G).u p = D.psi p.2 * G.u p

structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where
  S : Scalar α T →L[ℝ] Jet α T
  bound : ‖S‖ ≤ C_S
  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,
      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)

def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}
    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=
  0 < α → 0 < T →
  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →
  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →
  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖

-- Actual chart coefficient agreement is separate from the frozen analytic data.
structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where
  cutoff : E → ℝ
  smooth : ContDiff ℝ ∞ cutoff
  compact : HasCompactSupport cutoff
  one_on : ∀ z ∈ U, cutoff z = 1
  b : Fin 3 → Fin 3 → Scalar α T
  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,
    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))

def nonlinearGoal (α T r C_NL C_ref θ : ℝ)
    (N : X_M A α T → Y_M A α T) : Prop :=
  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →
    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧
  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))
def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)
    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)
    (G : Jet α T) (p : ℝ × E) : ℝ :=
  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,
    a i j p * G.ddu p (e i) (e j)) -
    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p

def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)
    (potential : Scalar α T) : Prop :=
  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧
    (∀ G t, t ∈ Icc 0 T → ∀ x,
      localLinearValue D.a D.drift potential (C G) (t,x) -
        D.psi x * localLinearValue D.a D.drift potential G (t,x) =
          firstOrderValue D.b D.c G (t,x))

def oscillationExtensionGoal : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →
  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →
  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →
  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∃ b : Fin 3 → Fin 3 → Scalar α T,
      (∀ t ∈ Icc 0 T, ∀ x i j,
        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧
      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧
      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)

def frozenCLMGoal : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →
  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)

abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →
  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=
  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)

def localizedValue {T : ℝ} (F : TensorField (M := M) T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by
  classical
  exact if ht : p.1 ∈ Icc 0 T then
    if p.2 ∈ (chart A i).target then
      let x := (chart A i).symm p.2
      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))
    else 0
  else 0

def reconstructionGoal (α T : ℝ) : Prop :=
  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,
    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p

abbrev Jet1 := E →L[ℝ] Bilin
abbrev Jet2 := E →L[ℝ] Jet1

def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +
    DeTurckPrincipalIdentity.lowerTerm B DB G J

set_option synthInstance.maxHeartbeats 400000 in
def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (z h : Bilin × Jet1 × Jet2) : Bilin :=
  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +
    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +
    (∑ i : Fin 3, ∑ j : Fin 3,
      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))
end FiniteAtlasSurvey
```
<!-- END FINAL LEAN PROBE -->

