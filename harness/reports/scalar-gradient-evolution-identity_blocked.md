# Scalar-gradient evolution: verified partial results, intrinsic assembly blocked

Date: 2026-09-15. Worker result awaiting independent orchestrator review.

- Branch: `worker/scalar-gradient-evolution-identity`.
- Base: `9f0374b62860f98dffceca5e3596184198f42453`, initially clean.
- Verified proof head: `d72764f979d20c57ab50eda155e15fdaeec17190`.
- New Lean module: `Poincare/Global/ScalarGradientEvolution.lean`.
- Seven named theorems are proved. The complete emitted module has 45 declarations; every declaration has exactly `[propext, Classical.choice, Quot.sound]`.
- The full intrinsic Bochner identity and `SatisfiesScalarGradientEvolutionAt` are not proved or declared. The time derivative theorem has additional explicit scalar regularity hypotheses. This is a blocked result for the original task, not completion with a changed target.

## 1. Survey and probed inventory

Here A means landed or proved by composition in this attempt, B means a remaining calculus or regularity bridge, and C means a later analytic estimate outside the evolution identity. Full Lean signatures are reproduced in the inventory and module-audit outputs below. All names were searched in source. The first inventory mistakenly qualified the root-level `extDerivFun_apply_chart` with `Poincare`; the corrected probe passes.

| Object | Actual repository interface and probed content | Class |
| --- | --- | --- |
| Scalar differential | `extDerivFun f x : TangentSpace I x →L[ℝ] ℝ`; `extDerivFun_apply_chart` identifies it with the derivative of `f ∘ (extChartAt I x).symm` under `MDifferentiableAt`. | A |
| Gradient | `ClosedSmoothRiemannianMetric.gradientAt g f x : TangentSpace I x`; `gradient g f` is the resulting section. `inner_gradientAt` says `g(grad f,w)=df(w)`. | A |
| Scalar-gradient norm | `g.scalarGradNormSqAt x` is `g.inner x (g.gradientAt g.scalarAt x) (g.gradientAt g.scalarAt x)`. `scalarGradNormSqAt_le_three_covRicciNormSqAt g (hn : n=3) x` supplies the factor-three contraction bound. | A |
| Hessian and Laplacian | `g.hessianAt f x v w` is the metric pairing of `∇_v grad f` with `w`; `hessianContinuousAt` packages it as a continuous bilinear map. `laplacianAt` is its raised trace. `hessianAt_eq_chart_derivatives` requires global C² and support inside one chart. The new `laplacianAt_eq_anchor_derivatives` contracts that formula at the anchor. | A; localization needed for application to the unrestricted gradient norm is B |
| Curved Bochner | `RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional` requires globally C³ coordinate metric and function, metric symmetry and invertibility. It gives `Δ|grad f|² = 2|Hess f|² + 2<grad f,grad Δf> + 2Ric(grad f,grad f)`. This was already a proved coordinate theorem. The new anchor version derives its metric hypotheses and identifies its Ricci tensor with the intrinsic one. | A in coordinates; the full intrinsic scalar-gradient formula is B |
| Moving metric and inverse | `hasDerivAt_inner_of_timeDifferentiableAt` differentiates the bilinear metric; `hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt` differentiates the inverse. `metricRaiseDerivAt_inner_apply` lowers that derivative to minus the metric variation. The new covector and gradient norm rules use these actual derivatives. | A |
| Mixed scalar partial | `hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two` is a scalar Euclidean Schwarz interchange. The new manifold version upgrades all evaluations to a derivative in the continuous-dual space. | A under its explicit joint scalar C² and differentiability hypotheses |
| Normalized scalar equation | `SatisfiesNormalizedHamiltonScalarEvolutionAt` lives in `NormalizedFlowScalarLowerProfile`, not directly in `ScalarEvolution`. Its expansion is `HasDerivAt R (ΔR + 2N - (2/3)rR)`. Its producer uses the actual normalized flow and `GlobalLichnerowiczAssemblyRegularity`; the latter follows from all-time joint C³ metric entries. | A |
| Higher scalar regularity | `scalarAt_mdifferentiableAt` and `ricciNormSqAt_mdifferentiableAt` are unconditional slice results. `scalarAt_contMDiffAt_two_of_normalizedRicciFlow` consumes C² metric variation. `anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries` supplies joint C¹ coordinate scalar trace from joint C³ metric entries. It does not supply the joint C² scalar field required below. | B for the requested C⁴-to-scalar upgrade |
| Scalar minimum | `scalarMinimumAt g : ℝ` is available. Neither it nor the compact normalized additive gradient bound proves the historical scale-effective gradient estimate. | A for the definition; C for the later estimate |

The actual imports of the two worker imports were inspected. The normalized quotient assembly supplies spatial C² curvature quantities from metric variation and uses the landed Lichnerowicz producer. Its success does not supply a third spatial scalar derivative or a mixed derivative of the scalar differential.

## 2. Verified results and normalization

The commits are:

| Commit | Result |
| --- | --- |
| `efedfa5b` | Moving covector norm variation with the inverse metric. |
| `30d67a1b` | Moving gradient norm and manifold mixed-partial differentiation. |
| `85e5a1b1` | `hasDerivAt_scalarGradNormSq_normalizedFlow`, with explicit extra scalar regularity. |
| `0bbf6b60` | Coordinate Ricci at the blended chart anchor equals intrinsic Ricci. |
| `282a5a56` | Bochner for the actual blended chart metric, using intrinsic Ricci. |
| `7a6b3f56` | Intrinsic Laplacian expansion for a chart-supported C² scalar. |
| `d72764f9` | Expanded local notation so compiler-generated notation declarations do not violate the exact dependency gate. |

Write `R=scalarAt`, `N=ricciNormSqAt`, `r=meanScalar`, and `S=scalarGradNormSqAt`. The strongest compiled time result is

```text
∂t S = 2<grad R,grad ΔR> + 4<grad R,grad N>
       + 2 Ric(grad R,grad R) - 2 r S.
```

It assumes all-time joint C³ metric entries and the normalized metric equation on the selected slice. Additionally it explicitly assumes

```lean
ContDiffAt ℝ 2
  (fun p : ℝ × ClosedSmoothModel 3 ↦
    (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
  (t₀, extChartAt (closedSmoothModelWithCorners 3) x x)
```

and

```lean
MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
  (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x
```

These are regularity assumptions on the actual scalar and Laplacian. They are not replacement definitions or supplied evolution identities. They have **not** been discharged from joint C⁴ metric entries. The theorem works at any slice satisfying its assumptions; a forward flow can supply its flow premise at `t₀ ≥ 0` without requiring the flow equation at negative times.

The sign calculation is fixed by the proved inverse-metric rule. Differentiating `-(2/3)rR` contributes `-(4/3)rS`. Inverse-metric differentiation contributes `2Ric(grad R,grad R)-(2/3)rS`. Thus the total normalization is `-2rS`. Subtracting the positive-Ricci Bochner identity cancels the Ricci terms, leaving the intended formula

```text
(∂t - Δ) S = -2|Hess R|² + 4<grad R,grad N> - 2rS.
```

There is no further metric correction after these terms are combined. This displayed assembled identity is a mathematical consequence of the two formulas; its **intrinsic Lean producer remains unproved**.

## 3. Exact remaining identities and attempted routes

### 3.1 Intrinsic Bochner transport

The remaining spatial identity is literally

```lean
let R : M → ℝ := fun y ↦ g.scalarAt y
let b := Module.finBasis ℝ (ClosedSmoothModel 3)
g.laplacianAt (fun y ↦ g.scalarGradNormSqAt y) x =
  2 * (∑ i, g.inner x (g.leviCivita (g.gradient R) x (b i))
    (g.leviCivita (g.gradient R) x (metricDualVectorAt g x (b.coord i)))) +
  2 * g.inner x (g.gradientAt R x)
    (g.gradientAt (fun y ↦ g.laplacianAt R y) x) +
  2 * g.ricciAt x (g.gradientAt R x) (g.gradientAt R x)
```

The finite sum is the metric trace of the squared covariant derivative of the gradient, hence the squared Hessian norm. It is not a new norm definition. Probe 27 supplies spatial C³ scalar regularity and even a globally C³ chart representative, then attempts to use the proved anchor Bochner theorem. Lean still reports the exact operator mismatch reproduced below: coordinate `curvedLaplacian`, `coordGradNormSq`, `coordCovariantHessNormSq`, and the coordinate gradient of the coordinate Laplacian do not reduce to the intrinsic expressions.

The work did resolve the Ricci sign/trace bridge and the chart-supported intrinsic Laplacian contraction. The latter initially resisted rewriting because its Hessian is indexed by the inverse-chart base point; an explicit equality of the base points and `congrArg` finished the proof. The remaining task is to localize `R` and its gradient norm inside a chart, transport the squared Hessian trace, and transport the Laplacian as a germ before differentiating it in the gradient direction. An equality only at the anchor is insufficient for the last step. The existing support-restricted Hessian formula cannot be applied to an unrestricted global scalar-gradient norm without that localization proof.

The failed diagnostic is evidence of the remaining Lean interface, not a claim that intrinsic Bochner is false or impossible. The coordinate Bochner theorem was already present; it was not replaced by an assumption.

### 3.2 Joint C⁴ regularity producers

The proposed next regularity contract should assume explicitly

```lean
hJoint4 : ∀ t y, MetricEntriesJointContDiffAt gt t y 4
```

and produce both extra hypotheses of the time theorem above. Joint C⁴ metric entries normally give joint C² scalar curvature through the curvature trace. The normalized metric equation on the slice can additionally express Ricci, and then scalar, through a spatially C³ metric time derivative; that is the expected route to differentiability of `ΔR`. This derivative count is a proposed proof route, not a verified producer. Pure fourth-order metric regularity alone should not be described as automatically giving third-order scalar curvature, since curvature already uses two metric derivatives.

No predicate packaging of the full evolution was added with a Bochner premise. Probe 32 confirms that `Poincare.ScalarGradientEvolution.SatisfiesScalarGradientEvolutionAt` is absent.

First action for a proof continuation: reproduce probe 27 from the appendix, then prove the germ equality between the intrinsic Laplacian and the blended coordinate Laplacian for a localized scalar. Use the committed `laplacianAt_eq_anchor_derivatives` for the contraction and the landed gradient transport for the first derivative. Independent worker acceptance should begin with the focused source command in section 5.

## 4. Hamilton's next auxiliary quantity

Hamilton §11 uses the unnormalized flow and, in Lemma 11.10,

```text
F = |grad R|²/R - ηR² + 168(N - R²/3),    0 < η < 1/3.
```

Lemmas 11.3 and 11.7–11.9 combine the quotient evolution with the traceless-Ricci evolution. The needed bounds are

```text
(∂t-Δ)(|grad R|²/R - ηR²) ≤ 16|∇Ric|² - (4/3)ηR³,
(∂t-Δ)(N-R²/3) ≤ -(2/21)|∇Ric|² + 4R(N-R²/3).
```

Their combination cancels the derivative energy. Improved pinching controls the remaining `672R(N-R²/3) - (4/3)ηR³`, yielding a time-independent upper bound for `(∂t-Δ)F`. This needs quotient/Hessian-square calculus, the sharper contracted-Bianchi bound `|∇R|² ≤ (20/7)|∇Ric|²`, mixed-gradient estimates, improved pinching, and the maximum principle on a finite unnormalized lifespan. The landed factor-three bound alone does not give `2/21`. [Hamilton, §11, pp. 287–290](https://projecteuclid.org/journals/journal-of-differential-geometry/volume-17/issue-2/Three-manifolds-with-positive-Ricci-curvature/10.4310/jdg/1214436922.pdf).

The publisher's full PDF request was blocked by its security page, and the alternate publisher mirror timed out. The original-paper search excerpts did expose Lemmas 11.2, 11.3, and 11.7–11.10, including the coefficient 168. The displayed inequalities also follow by the indicated combination of the derivative-energy and pinching terms; none is claimed as a new Lean theorem here.

The normalized additive bound from compact third jets does not replace this scale-effective unnormalized estimate. Blow-up/rescaling transfer, scalar oscillation control, and the all-time uniform gap `2(2−δ)N/R + η ≤ (4/3)r` remain separate obligations. No progress on that gap is claimed by these calculus lemmas.

## 5. Verification and evidence

Final focused source compilation: exit 0, no output. Emission of the final module: exit 0. Exact module audit: exit 0, 45 declarations, every dependency set exactly the required three. Token search: empty output, ripgrep exit 1 for no matches. `git diff --check`: exit 0.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ScalarGradientEvolution.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ScalarGradientEvolution.lean
git diff --check
```

Use `DEVELOPER_DIR=/Library/Developer/CommandLineTools` with Git in this environment. No full build or root integration audit was run by this worker. Existing Lean files, `Poincare.lean`, and frozen contracts were not edited. `HANDOFF.md` receives the required dated handoff.

The first emitted-module audit failed because an overlay containing only the new module shadowed the other `Poincare` modules. Linking the base-cache modules into that temporary overlay fixed lookup. Its next run found zero-dependency generated notation macros. Expanding the local notation removed those declarations; the final audit checks all remaining declarations, including generated instance proofs and auxiliary definitions.

The following appendix preserves every Lean probe's actual output, including unsuccessful attempts. Error-bearing dependency printouts are diagnostic output and are not accepted verification. Initial `inventory.log` used a shell command that did not retain the Lean exit status separately; its compiler error is preserved and the corrected inventory was observed to exit 0. Subsequent numbered checks explicitly captured their Lean exit statuses in the tool transcript; logs that lack a trailing `exit=` line preserve compiler stdout/stderr, with trailing spaces on blank lines omitted for the repository whitespace gate. Named source snapshots, the final diff, inventory probes, and audit program make the final and resisting statements reproducible.

## Appendix A. Actual probe and search output

<details>
<summary>01-norm.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:36:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormedAddCommGroup (TangentSpace I x)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ScalarGradientEvolution.lean:35:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormedAddCommGroup (TangentSpace I x)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ScalarGradientEvolution.lean:36:80: error: Application type mismatch: The argument
  hα
has type
  @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField (TangentSpace I x →L[ℝ] ℝ) ContinuousLinearMap.addCommGroup
    ContinuousLinearMap.module ContinuousLinearMap.topologicalSpace ⋯ α α' t₀
but is expected to have type
  @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ?m.151 NormedAddCommGroup.toAddCommGroup
    NormedSpace.toModule PseudoMetricSpace.toUniformSpace.toTopologicalSpace ⋯ ?m.160 ?m.161 t₀
in the application
  HasDerivAt.clm_apply ?m.162 hα

```

</details>

<details>
<summary>02-norm.log</summary>

```text

```

</details>

<details>
<summary>03-norm-audit.log</summary>

```text
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq' depends on axioms: [propext, Classical.choice, Quot.sound]

```

</details>

<details>
<summary>04-gradient-mixed.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:74:0: warning: automatically included section variable(s) unused in theorem `Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

```

</details>

<details>
<summary>05-mixed-audit.log</summary>

```text
'Poincare.ScalarGradientEvolution.hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

</details>

<details>
<summary>06-normalized.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:146:4: error: Type mismatch
  MDifferentiableAt.add (MDifferentiableAt.add hL (MDifferentiableAt.smul mdifferentiableAt_const hA))
    (MDifferentiableAt.smul mdifferentiableAt_const hR)
has type
  MDiffAt ((L + fun p => ?m.688 • A p) + fun p => ?m.744 • R p) x
but is expected to have type
  MDiffAt (L + 2 • A + c • R) x
Poincare/Global/ScalarGradientEvolution.lean:153:11: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  g.gradientAt ((L + fun p => ?m.862 • A p) + fun p => ?m.901 • R p) x
in the target expression
  HasDerivAt
    (fun t =>
      (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
        ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
    (2 *
        (((gt t₀).inner x) ((gt t₀).gradientAt (L + 2 • A + c • R) x))
          ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
      timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
        ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
    t₀

N : Type u
inst✝⁸ : TopologicalSpace N
inst✝⁷ : T2Space N
inst✝⁶ : SecondCountableTopology N
inst✝⁵ : CompactSpace N
inst✝⁴ : ConnectedSpace N
inst✝³ : MeasurableSpace N
inst✝² : BorelSpace N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
gt : ℝ → ClosedSmoothRiemannianMetric 3 N
t₀ : ℝ
x : N
hJoint : ∀ (t : ℝ) (y : N), MetricEntriesJointContDiffAt gt t y 3
hFlow : ∀ (y : N), IsClosedNormalizedRicciFlowSolutionAt gt t₀ y
hScalarJoint : ContDiffAt ℝ 2 (fun p => (gt p.1).scalarAt (↑(extChartAt I₃ x).symm p.2)) (t₀, ↑(extChartAt I₃ x) x)
hLap : (MDiffAt fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x
this : Nonempty N := Nonempty.intro x
g : ClosedSmoothRiemannianMetric 3 N := gt t₀
R : N → ℝ := fun y => g.scalarAt y
A : N → ℝ := fun y => g.ricciNormSqAt y
L : N → ℝ := fun y => g.laplacianAt R y
c : ℝ := -(2 / 3) * meanScalar g
hR : MDiffAt R x
hA : MDiffAt A x
hL : MDiffAt L x
heq : (fun y => deriv (fun t => (gt t).scalarAt y) t₀) = L + 2 • A + c • R
hft : (MDiffAt fun y => deriv (fun t => (gt t).scalarAt y) t₀) x
hd :
  HasDerivAt
    (fun t =>
      (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
        ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
    (2 *
        (((gt t₀).inner x) ((gt t₀).gradientAt (L + 2 • A + c • R) x))
          ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
      timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
        ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
    t₀
⊢ HasDerivAt (fun t => (gt t).scalarGradNormSqAt x)
    (2 *
            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
              ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
          4 *
            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
              ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
        2 *
          (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
      2 * meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x)
    t₀

```

</details>

<details>
<summary>07-normalized.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:158:28: error: Application type mismatch: The argument
  hA
has type
  MDiffAt A x
of sort `Prop` but is expected to have type
  ℝ
of sort `Type` in the application
  ClosedSmoothRiemannianMetric.gradientAt_const_smul g hA
Poincare/Global/ScalarGradientEvolution.lean:124:69: error: unsolved goals
N : Type u
inst✝⁸ : TopologicalSpace N
inst✝⁷ : T2Space N
inst✝⁶ : SecondCountableTopology N
inst✝⁵ : CompactSpace N
inst✝⁴ : ConnectedSpace N
inst✝³ : MeasurableSpace N
inst✝² : BorelSpace N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
gt : ℝ → ClosedSmoothRiemannianMetric 3 N
t₀ : ℝ
x : N
hJoint : ∀ (t : ℝ) (y : N), MetricEntriesJointContDiffAt gt t y 3
hFlow : ∀ (y : N), IsClosedNormalizedRicciFlowSolutionAt gt t₀ y
hScalarJoint : ContDiffAt ℝ 2 (fun p => (gt p.1).scalarAt (↑(extChartAt I₃ x).symm p.2)) (t₀, ↑(extChartAt I₃ x) x)
hLap : (MDiffAt fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x
this : Nonempty N := Nonempty.intro x
g : ClosedSmoothRiemannianMetric 3 N := gt t₀
R : N → ℝ := fun y => g.scalarAt y
A : N → ℝ := fun y => g.ricciNormSqAt y
L : N → ℝ := fun y => g.laplacianAt R y
c : ℝ := -(2 / 3) * meanScalar g
hR : MDiffAt R x
hA : MDiffAt A x
hL : MDiffAt L x
heq : (fun y => deriv (fun t => (gt t).scalarAt y) t₀) = L + 2 • A + c • R
h2A : MDiffAt (2 • A) x
hcR : MDiffAt (c • R) x
hft : (MDiffAt fun y => deriv (fun t => (gt t).scalarAt y) t₀) x
hd :
  HasDerivAt
    (fun t =>
      (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
        ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
    (2 *
        (((gt t₀).inner x) (g.gradientAt L x + g.gradientAt (2 • A) x + g.gradientAt (c • R) x))
          ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
      timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
        ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
    t₀
⊢ HasDerivAt (fun t => (gt t).scalarGradNormSqAt x)
    (2 *
            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
              ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
          4 *
            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
              ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
        2 *
          (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
      2 * meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x)
    t₀

```

</details>

<details>
<summary>08-normalized.log</summary>

```text

```

</details>

<details>
<summary>09-normalized-audit.log</summary>

```text
'Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow.{u} : ∀ {N : Type u}
  [inst : TopologicalSpace N] [inst_1 : T2Space N] [SecondCountableTopology N] [inst_3 : CompactSpace N]
  [inst_4 : ConnectedSpace N] [inst_5 : MeasurableSpace N] [inst_6 : BorelSpace N]
  [inst_7 : ChartedSpace (Poincare.ClosedSmoothModel 3) N]
  [inst_8 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ N]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 N} {t₀ : ℝ} {x : N},
  (∀ (t : ℝ) (y : N), Poincare.MetricEntriesJointContDiffAt gt t y 3) →
    (∀ (y : N), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ y) →
      ContDiffAt ℝ 2 (fun p => (gt p.1).scalarAt (↑(extChartAt (Poincare.closedSmoothModelWithCorners 3) x).symm p.2))
          (t₀, ↑(extChartAt (Poincare.closedSmoothModelWithCorners 3) x) x) →
        (MDiffAt fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x →
          HasDerivAt (fun t => (gt t).scalarGradNormSqAt x)
            (2 *
                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                      ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
                  4 *
                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                      ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
                2 *
                  (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
              2 * Poincare.meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x)
            t₀ :=
fun {N} [⋯] [⋯] [⋯] [⋯] [⋯] [⋯] [⋯] [⋯] [⋯] {gt} {t₀} {x} hJoint hFlow hScalarJoint hLap =>
  let g := gt t₀;
  let R := fun y => g.scalarAt y;
  let A := fun y => g.ricciNormSqAt y;
  let L := fun y => g.laplacianAt R y;
  let c := -(2 / 3) * Poincare.meanScalar g;
  have hR := Poincare.scalarAt_mdifferentiableAt g x;
  have hA := Poincare.ricciNormSqAt_mdifferentiableAt g x;
  have hL := hLap;
  have heq :=
    funext fun y =>
      have hs :=
        Poincare.satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz hFlow
          (Poincare.globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint);
      Eq.mpr (id (congrArg (fun _a => _a = (L + 2 • A + c • R) y) (HasDerivAt.deriv hs)))
        (id
          (Mathlib.Tactic.Ring.of_eq
            (Mathlib.Tactic.Ring.Common.sub_congr
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.atom_pf ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y) rfl
                  (Eq.mpr
                    (id
                      (congrArg
                        (fun _a =>
                          (gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1 =
                            (gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                  (Mathlib.Tactic.Ring.Common.atom_pf ((gt t₀).ricciNormSqAt y) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            (gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              (gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ((gt t₀).ricciNormSqAt y) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                  ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.div_congr
                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 3)))
                    (Mathlib.Tactic.Ring.Common.div_pf
                      (Mathlib.Tactic.Ring.Common.inv_single
                        (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNNRat_inv_pos
                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                              (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                  (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                              (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))
                          (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 2 3 + 0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul (NNRat.rawCast 1 3 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 2 3 + 0)))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.meanScalar (gt t₀)) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                            (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                              (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                  (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                    (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                  (Eq.refl (Nat.mul 2 1)) (Eq.refl 3))))
                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Nat.mul 2 1)) (Eq.refl 3))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (NNRat.rawCast 2 3))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * NNRat.rawCast 2 3 + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * NNRat.rawCast 2 3 + 0))))
                (Mathlib.Tactic.Ring.Common.atom_pf ((gt t₀).scalarAt y) rfl
                  (Eq.mpr
                    (id
                      (congrArg
                        (fun _a =>
                          (gt t₀).scalarAt y ^ Nat.rawCast 1 * Nat.rawCast 1 = (gt t₀).scalarAt y ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_left (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ((gt t₀).scalarAt y) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                            (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                              (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                    (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                      (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                        (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                          (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                            (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                        (Eq.refl (Nat.mul 2 1)) (Eq.refl 3))))
                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Nat.mul 2 1)) (Eq.refl 3))))
                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                    (Mathlib.Tactic.Ring.Common.mul_zero
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * NNRat.rawCast 2 3))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                          ((gt t₀).scalarAt y ^ Nat.rawCast 1 * NNRat.rawCast 2 3) +
                        0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                        ((gt t₀).scalarAt y ^ Nat.rawCast 1 * NNRat.rawCast 2 3) +
                      0))))
              (Mathlib.Tactic.Ring.Common.sub_pf
                (Mathlib.Tactic.Ring.Common.neg_add
                  (Mathlib.Tactic.Ring.Common.neg_mul (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.neg_mul ((gt t₀).scalarAt y) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                        (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                            (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                              (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                    (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                      (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                          (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                              (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                                (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                  (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                              (Eq.refl (Nat.mul 2 1)) (Eq.refl 3))))
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Eq.refl (Nat.mul 2 1)) (Eq.refl 3))))
                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                          (Eq.refl (Int.negOfNat 2))))))
                  Mathlib.Tactic.Ring.Common.neg_zero)
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                  ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2)
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                          ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3) +
                        0))))))
            (Mathlib.Tactic.Ring.Common.add_congr
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.atom_pf ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y) rfl
                  (Eq.mpr
                    (id
                      (congrArg
                        (fun _a =>
                          (gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1 =
                            (gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                  (Mathlib.Tactic.Ring.Common.atom_pf ((gt t₀).ricciNormSqAt y) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            (gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              (gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ((gt t₀).ricciNormSqAt y) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                  ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.neg_congr
                    (Mathlib.Tactic.Ring.Common.div_congr
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 3)))
                      (Mathlib.Tactic.Ring.Common.div_pf
                        (Mathlib.Tactic.Ring.Common.inv_single
                          (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNNRat_inv_pos
                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                  (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))
                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 2 3 + 0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul (NNRat.rawCast 1 3 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 2 3 + 0)))))
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                        (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                            (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                              (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                  (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                    (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                  (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                          (Eq.refl (Int.negOfNat 2))))
                      Mathlib.Tactic.Ring.Common.neg_zero))
                  (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.meanScalar (gt t₀)) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                          (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                            (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                              (Mathlib.Meta.NormNum.IsRat.den_nz
                                (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                    (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                      (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                        (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                          (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                            (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                          (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                                  (Eq.refl (Int.negOfNat 2)))))
                            (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                            (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (Rat.rawCast (Int.negOfNat 2) 3))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3 + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3 + 0))))
                (Mathlib.Tactic.Ring.Common.atom_pf ((gt t₀).scalarAt y) rfl
                  (Eq.mpr
                    (id
                      (congrArg
                        (fun _a =>
                          (gt t₀).scalarAt y ^ Nat.rawCast 1 * Nat.rawCast 1 = (gt t₀).scalarAt y ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_left (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ((gt t₀).scalarAt y) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                          (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                            (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                              (Mathlib.Meta.NormNum.IsRat.den_nz
                                (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                                    (Mathlib.Meta.NormNum.IsRat.den_nz
                                      (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                                        (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                          (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                            (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                              (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                                (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                                  (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                                (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                                        (Eq.refl (Int.negOfNat 2)))))
                                  (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                                  (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3))))
                            (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                            (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3)))))
                    (Mathlib.Tactic.Ring.Common.mul_zero
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                          ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3) +
                        0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                        ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3) +
                      0))))
              (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) y ^ Nat.rawCast 1 * Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt ((gt t₀).ricciNormSqAt y ^ Nat.rawCast 1 * Nat.rawCast 2)
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                        ((gt t₀).scalarAt y ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3) +
                      0)))))));
  have h2A := MDifferentiableAt.smul mdifferentiableAt_const hA;
  have hcR := MDifferentiableAt.smul mdifferentiableAt_const hR;
  have hft :=
    Eq.mpr (id (congrArg (fun _a => MDiffAt _a x) heq)) (MDifferentiableAt.add (MDifferentiableAt.add hL h2A) hcR);
  have hd :=
    Poincare.ScalarGradientEvolution.hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
      (Poincare.timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
        (Poincare.MetricEntriesJointContDiffAt.of_le (hJoint t₀ x)
          (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℕ∞ω Nat.cast_one)
            (Mathlib.Meta.NormNum.isNat_ofNat ℕ∞ω (Eq.refl 3)) (Eq.refl true))))
      (Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two
        (fun t => Poincare.scalarAt_mdifferentiableAt (gt t) x) hft hScalarJoint);
  HasDerivAt.congr_deriv
    (Eq.mp
      (congrArg
        (fun _a =>
          HasDerivAt
            (fun t =>
              (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
            (2 *
                (((gt t₀).inner x) (g.gradientAt L x + 2 • g.gradientAt A x + _a))
                  ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
              Poincare.timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
            t₀)
        (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const_smul g c hR))
      (Eq.mp
        (congrArg
          (fun _a =>
            HasDerivAt
              (fun t =>
                (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                  ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
              (2 *
                  (((gt t₀).inner x) (g.gradientAt L x + _a + g.gradientAt (c • R) x))
                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                Poincare.timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                  ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
              t₀)
          (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const_smul g 2 hA))
        (Eq.mp
          (congrArg
            (fun _a =>
              HasDerivAt
                (fun t =>
                  (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                    ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                (2 *
                    (((gt t₀).inner x) (_a + g.gradientAt (c • R) x))
                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                  Poincare.timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                t₀)
            (Poincare.ClosedSmoothRiemannianMetric.gradientAt_add g hL h2A))
          (Eq.mp
            (congrArg
              (fun _a =>
                HasDerivAt
                  (fun t =>
                    (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                      ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                  (2 * (((gt t₀).inner x) _a) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                    Poincare.timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                  t₀)
              (Poincare.ClosedSmoothRiemannianMetric.gradientAt_add g (MDifferentiableAt.add hL h2A) hcR))
            (Eq.mp
              (congrArg
                (fun _a =>
                  HasDerivAt
                    (fun t =>
                      (((gt t).inner x) ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                        ((gt t).gradientAt (fun y => (gt t).scalarAt y) x))
                    (2 *
                        (((gt t₀).inner x) ((gt t₀).gradientAt _a x))
                          ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                      Poincare.timeDerivAt gt t₀ x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                        ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                    t₀)
                heq)
              hd)))))
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            2 *
                  (((gt t₀).inner x) (g.gradientAt L x + 2 • g.gradientAt A x + c • g.gradientAt R x))
                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                _a =
              2 *
                      (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                        ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
                    4 *
                      (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                        ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
                  2 *
                    (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                2 * Poincare.meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x)
          (Poincare.isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt (hFlow x)
            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))))
      (Eq.mpr
        (id
          (congrFun'
            (congrArg Eq
              (congrFun'
                (congrArg HSub.hSub
                  (congrArg (HMul.hMul 2)
                    (congrFun'
                      (congrArg DFunLike.coe
                        (Eq.trans
                          (map_add ((gt t₀).inner x) (g.gradientAt L x + 2 • g.gradientAt A x) (c • g.gradientAt R x))
                          (congr
                            (congrArg HAdd.hAdd
                              (Eq.trans (map_add ((gt t₀).inner x) (g.gradientAt L x) (2 • g.gradientAt A x))
                                (congrArg (HAdd.hAdd (((gt t₀).inner x) (g.gradientAt L x)))
                                  (map_smul ((gt t₀).inner x) 2 (g.gradientAt A x)))))
                            (map_smul ((gt t₀).inner x) c (g.gradientAt R x)))))
                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))))
                (-2 *
                    (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) +
                  2 / ↑3 * Poincare.meanScalar (gt t₀) *
                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))))
            (2 *
                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                      ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
                  4 *
                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                      ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
                2 *
                  (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
              2 * Poincare.meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x)))
        (id
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  2 *
                        (_a +
                            2 *
                              (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) +
                          -(2 / 3) * Poincare.meanScalar (gt t₀) *
                            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                              ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)) -
                      (-2 *
                          (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) +
                        2 / ↑3 * Poincare.meanScalar (gt t₀) *
                          (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)) =
                    2 *
                            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                              ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
                          4 *
                            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                              ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
                        2 *
                          (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                      2 * Poincare.meanScalar (gt t₀) *
                        (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                          ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                (Poincare.ClosedSmoothRiemannianMetric.inner_symm (gt t₀) x
                  ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x)
                  ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))))
            (Eq.mpr
              (id
                (congrArg
                  (fun _a =>
                    2 *
                          ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
                              2 * _a +
                            -(2 / 3) * Poincare.meanScalar (gt t₀) *
                              (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)) -
                        (-2 *
                            (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                              ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) +
                          2 / ↑3 * Poincare.meanScalar (gt t₀) *
                            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                              ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)) =
                      2 *
                              (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
                            4 *
                              (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
                          2 *
                            (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
                              ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
                        2 * Poincare.meanScalar (gt t₀) *
                          (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                  (Poincare.ClosedSmoothRiemannianMetric.inner_symm (gt t₀) x
                    ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x)
                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))))
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.mul_congr
                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf
                          ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                            ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x))
                          rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                          ((gt t₀).gradientAt
                                            (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1 =
                                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                          ((gt t₀).gradientAt
                                            (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) ^
                                        Nat.rawCast 1 *
                                      _a)
                                (Eq.symm rfl)))
                            (Eq.refl
                              ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                    ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y)
                                      x) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                              ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x))
                            rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                            ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                            ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                      ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                  ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 2))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                        ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 2 +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                      ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                      ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 2 +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) ^
                              Nat.rawCast 1 *
                            Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                    ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 2 +
                              0))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.neg_congr
                            (Mathlib.Tactic.Ring.Common.div_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 3)))
                              (Mathlib.Tactic.Ring.Common.div_pf
                                (Mathlib.Tactic.Ring.Common.inv_single
                                  (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                        (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                          (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                            (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                        (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 2 3 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (NNRat.rawCast 1 3 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 2 3 + 0)))))
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                                (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                    (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                      (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                        (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                          (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                            (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                          (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                                  (Eq.refl (Int.negOfNat 2))))
                              Mathlib.Tactic.Ring.Common.neg_zero))
                          (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.meanScalar (gt t₀)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                      Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                                      (Mathlib.Meta.NormNum.IsRat.den_nz
                                        (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                            (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                              (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                                  (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                                    (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                                  (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                                          (Eq.refl (Int.negOfNat 2)))))
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                                    (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Rat.rawCast (Int.negOfNat 2) 3))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3 + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf
                          ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                          rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                          ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1 =
                                    (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                          ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                        Nat.rawCast 1 *
                                      _a)
                                (Eq.symm rfl)))
                            (Eq.refl
                              ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                  ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                                      (Mathlib.Meta.NormNum.IsRat.den_nz
                                        (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                                            (Mathlib.Meta.NormNum.IsRat.den_nz
                                              (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                                                (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                                  (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                                    (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                      (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                                        (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                                          (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                            (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                                        (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                                                (Eq.refl (Int.negOfNat 2)))))
                                          (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                                          (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3))))
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                                    (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3)))))
                            (Mathlib.Tactic.Ring.Common.mul_zero
                              (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 2) 3))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                                  ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                        ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                      Nat.rawCast 1 *
                                    Rat.rawCast (Int.negOfNat 2) 3) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                    ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1 +
                              0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                                ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                    Nat.rawCast 1 *
                                  Rat.rawCast (Int.negOfNat 2) 3) +
                              0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                              ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                              Nat.rawCast 1 *
                            Nat.rawCast 2)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                                ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                      ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                    Nat.rawCast 1 *
                                  Rat.rawCast (Int.negOfNat 2) 3) +
                              0)))))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_right
                          ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                            ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x))
                          (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_right
                            ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                              ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x))
                            (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                (Eq.refl 4))))
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.meanScalar (gt t₀)) (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                  ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsRat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))
                                    (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                                      (Mathlib.Meta.NormNum.IsRat.den_nz
                                        (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                                            (Mathlib.Meta.NormNum.IsRat.den_nz
                                              (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
                                                (Mathlib.Meta.NormNum.IsRat.of_raw ℝ (Int.negOfNat 2) 3
                                                  (Mathlib.Meta.NormNum.IsRat.den_nz
                                                    (Mathlib.Meta.NormNum.isRat_neg (Eq.refl Neg.neg)
                                                      (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                                        (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 2 3
                                                          (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                                              (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 3
                                                                (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                                  (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)))))
                                                              (Eq.refl (Nat.mul 2 1)) (Eq.refl 3)))))
                                                      (Eq.refl (Int.negOfNat 2)))))
                                                (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                                                (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3))))
                                          (Mathlib.Meta.NormNum.IsNNRat.to_isRat
                                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))
                                          (Eq.refl ((Int.negOfNat 2).mul (Int.ofNat 1))) (Eq.refl 3))))
                                    (Eq.refl ((Int.ofNat 2).mul (Int.negOfNat 2))) (Eq.refl 3)))))
                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                                  ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                        ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                      Nat.rawCast 1 *
                                    Rat.rawCast (Int.negOfNat 4) 3) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                  ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 4)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (Poincare.meanScalar (gt t₀) ^ Nat.rawCast 1 *
                                  ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                        ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) ^
                                      Nat.rawCast 1 *
                                    Rat.rawCast (Int.negOfNat 4) 3) +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          ((((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
                                ((gt t₀).gradientAt (fun y => (gt ⋯).laplacianAt ⋯ ⋯) ⋯) ^
                              ⋯ *
                            ⋯)
                          ⋯))
                      ⋯ ⋯))
                  ⋯ ⋯)
                ⋯))))))

```

</details>

<details>
<summary>10-bochner-signatures.log</summary>

```text
Poincare.chartChristoffelField_symm.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (z u v : Poincare.ClosedSmoothModel 3) :
  ((Poincare.GeodesicTransport.chartChristoffelField g x₀ z) u) v =
    ((Poincare.GeodesicTransport.chartChristoffelField g x₀ z) v) u
Poincare.GeodesicTransport.chartChristoffelField_contDiff_top.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (x₀ : M) :
  ContDiff ℝ (↑⊤) (Poincare.GeodesicTransport.chartChristoffelField g x₀)
RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt.{u_2} {E : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E} (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
  (hbg : ∀ (v w : E), (b v) w = ((G x) v) w) (u v : E) :
  (RicciFlow.RicciFlow.christoffelClosedOp G x u) v = CovariantDerivative.christoffelAt G x b hb u v
Poincare.ChartCurvatureBridge.fderiv_clm_family_apply.{u_1, u_2, u_3} {E : Type u_1} {F : Type u_2} {V : Type u_3}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {Φ : E → F →L[ℝ] V} {x : E} (hΦ : DifferentiableAt ℝ Φ x) (v : E) (c : F) :
  ((fderiv ℝ Φ x) v) c = (fderiv ℝ (fun y => (Φ y) c) x) v
Poincare.anchorChartRicciEntryFlow_eq_ricciAt_anchor.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (x : M) (t : ℝ) (v w : Poincare.ClosedSmoothModel n) :
  Poincare.anchorChartRicciEntryFlow gt x t (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x) x) v w =
    (gt t).ricciAt x v w
CovariantDerivative.contDiff_blendedChartMetric.{u_1, u_2, u_3} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type u_2} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u_3}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (↑⊤) M] [I.Boundaryless] (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
  (g : (y : M) → TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (x₀ : M) {m : WithTop ℕ∞} (hm : m + 1 ≤ ↑⊤)
  (hχ : ContDiff ℝ (↑⊤) χ) (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
  (hg : ContMDiff I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) m fun y => ⟨y, g y⟩) :
  ContDiff ℝ m (CovariantDerivative.blendedChartMetric χ G₀ g x₀)
Poincare.anchorBlendedMetricFlow_isInvertible.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (x : M) (t : ℝ) (z : Poincare.ClosedSmoothModel n) :
  (Poincare.anchorBlendedMetricFlow gt x t z).IsInvertible

```

</details>

<details>
<summary>11-ricci-bridge.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:187:71: error: don't know how to synthesize placeholder for argument `hb`
context:
N : Type u
inst✝³ : TopologicalSpace N
inst✝² : T2Space N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
g : ClosedSmoothRiemannianMetric 3 N
x : N
v w : E₃
G : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := ⋯
Γ : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] E₃ := ⋯
q : E₃ := ⋯
hΓ : DifferentiableAt ℝ Γ q
z a b : E₃
⊢ (CovariantDerivative.chartBilin (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric g.inner x
      z).Nondegenerate
Poincare/Global/ScalarGradientEvolution.lean:192:4: error: Type mismatch
  heq z a b
has type
  (RicciFlow.RicciFlow.christoffelClosedOp G z a) b = ((Γ z) a) b
but is expected to have type
  ((RicciFlow.RicciFlow.christoffelClosedOp G z a) b).ofLp i✝ = (((Γ z) a) b).ofLp i✝

```

</details>

<details>
<summary>12-ricci-bridge.log</summary>

```text

```

</details>

<details>
<summary>13-ricci-audit.log</summary>

```text
'Poincare.ScalarGradientEvolution.coordRicci_anchorBlendedMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

</details>

<details>
<summary>14-bochner.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:237:57: error: Application type mismatch: The argument
  G
has type
  E₃ →
    E₃ →L[ℝ]
      @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) E₃ (PiLp.topologicalSpace 2 fun x => ℝ)
        (WithLp.instAddCommGroup 2 ((i : Fin 3) → (fun x => ℝ) i)).toAddCommMonoid ℝ
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace Real.instAddCommMonoid
        (WithLp.instModule 2 ℝ ((i : Fin 3) → (fun x => ℝ) i)) RCLike.toInnerProductSpaceReal.toModule
but is expected to have type
  TangentSpace I₃ x →
    TangentSpace I₃ x →L[ℝ]
      @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (TangentSpace I₃ x)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace NormedAddCommGroup.toAddCommGroup.toAddCommMonoid ℝ
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace Real.instAddCommMonoid NormedSpace.toModule
        RCLike.toInnerProductSpaceReal.toModule
in the application
  RicciFlow.RicciFlow.coordGradient G
Poincare/Global/ScalarGradientEvolution.lean:237:23: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormedAddCommGroup (TangentSpace I₃ x)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ScalarGradientEvolution.lean:238:43: error: Application type mismatch: The argument
  G
has type
  E₃ →
    E₃ →L[ℝ]
      @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) E₃ (PiLp.topologicalSpace 2 fun x => ℝ)
        (WithLp.instAddCommGroup 2 ((i : Fin 3) → (fun x => ℝ) i)).toAddCommMonoid ℝ
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace Real.instAddCommMonoid
        (WithLp.instModule 2 ℝ ((i : Fin 3) → (fun x => ℝ) i)) RCLike.toInnerProductSpaceReal.toModule
but is expected to have type
  TangentSpace I₃ x →
    TangentSpace I₃ x →L[ℝ]
      @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (TangentSpace I₃ x)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace NormedAddCommGroup.toAddCommGroup.toAddCommMonoid ℝ
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace Real.instAddCommMonoid NormedSpace.toModule
        RCLike.toInnerProductSpaceReal.toModule
in the application
  RicciFlow.RicciFlow.coordGradient G
Poincare/Global/ScalarGradientEvolution.lean:238:9: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormedAddCommGroup (TangentSpace I₃ x)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ScalarGradientEvolution.lean:245:43: error: unsolved goals
N : Type u
inst✝³ : TopologicalSpace N
inst✝² : T2Space N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
g : ClosedSmoothRiemannianMetric 3 N
x : N
f : E₃ → ℝ
hf : ContDiff ℝ 3 f
G : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := anchorBlendedMetricFlow (fun x => g) x 0
hsymm : ∀ (z v w : E₃),
  ((CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric g.inner x z)
        v)
      w =
    ((CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric g.inner x
          z)
        w)
      v :=
  CovariantDerivative.blendedChartMetric_symm (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric
    GeodesicTransport.backgroundMetric_symm g.inner (fun y a b => ClosedSmoothRiemannianMetric.inner_symm g y a b) x
hb : ∀ (z : E₃),
  (RicciFlow.RicciFlow.metricBilin
      (CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric g.inner x
        z)).Nondegenerate :=
  fun z => RicciFlow.RicciFlow.metricBilin_nondeg (hsymm z) (anchorBlendedMetricFlow_isInvertible (fun x => g) x 0 z)
Δ : (E₃ → ℝ) → E₃ → ℝ := CovariantDerivative.curvedLaplacian G (fun z => RicciFlow.RicciFlow.metricBilin (G z)) hb
q : E₃ := ↑(extChartAt I₃ x) x
hGtop : ContDiff ℝ ∞ G
⊢ 3 ≤ ∞
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/ScalarGradientEvolution.lean:238:53: error: unsolved goals
N : Type u
inst✝³ : TopologicalSpace N
inst✝² : T2Space N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
g : ClosedSmoothRiemannianMetric 3 N
x : N
f : E₃ → ℝ
hf : ContDiff ℝ 3 f
G : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := anchorBlendedMetricFlow (fun x => g) x 0
hsymm : ∀ (z v w : E₃),
  ((CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric g.inner x z)
        v)
      w =
    ((CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric g.inner x
          z)
        w)
      v :=
  CovariantDerivative.blendedChartMetric_symm (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric
    GeodesicTransport.backgroundMetric_symm g.inner (fun y a b => ClosedSmoothRiemannianMetric.inner_symm g y a b) x
hb : ∀ (z : E₃),
  (RicciFlow.RicciFlow.metricBilin
      (CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff x) GeodesicTransport.backgroundMetric g.inner x
        z)).Nondegenerate :=
  fun z => RicciFlow.RicciFlow.metricBilin_nondeg (hsymm z) (anchorBlendedMetricFlow_isInvertible (fun x => g) x 0 z)
Δ : (E₃ → ℝ) → E₃ → ℝ := CovariantDerivative.curvedLaplacian G (fun z => RicciFlow.RicciFlow.metricBilin (G z)) hb
q : E₃ := ↑(extChartAt I₃ x) x
hGtop : ContDiff ℝ ∞ G
hG : ContDiff ℝ 3 G
h :
  Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
    2 *
        (((G q) (RicciFlow.RicciFlow.coordGradient G f q))
            (RicciFlow.RicciFlow.coordGradient G
              (CovariantDerivative.curvedLaplacian G (fun y => RicciFlow.RicciFlow.metricBilin (G y)) ⋯ f) q) +
          g.ricciAt x (RicciFlow.RicciFlow.coordGradient G f q) (RicciFlow.RicciFlow.coordGradient G f q)) +
      2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q
⊢ ((G q) (RicciFlow.RicciFlow.coordGradient G f q))
            (RicciFlow.RicciFlow.coordGradient G
              (CovariantDerivative.curvedLaplacian G (fun y => RicciFlow.RicciFlow.metricBilin (G y)) ⋯ f) q) *
          2 +
        g.ricciAt x (RicciFlow.RicciFlow.coordGradient G f q) (RicciFlow.RicciFlow.coordGradient G f q) * 2 +
      RicciFlow.RicciFlow.coordCovariantHessNormSq G f q * 2 =
    RicciFlow.RicciFlow.coordCovariantHessNormSq G f q * 2 +
        ((G q) (RicciFlow.RicciFlow.coordGradient G f q)) (RicciFlow.RicciFlow.coordGradient G (Δ f) q) * 2 +
      g.ricciAt x sorry sorry * 2

```

</details>

<details>
<summary>15-bochner.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:235:51: error: unexpected token ':='; expected ')', ',' or ':'

```

</details>

<details>
<summary>16-bochner.log</summary>

```text

```

</details>

<details>
<summary>17-laplacian.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:274:31: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/ScalarGradientEvolution.lean:267:41: error(lean.unknownIdentifier): Unknown identifier `i`

Note: It is not possible to treat `i` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
Poincare/Global/ScalarGradientEvolution.lean:267:48: error(lean.unknownIdentifier): Unknown identifier `i`

Note: It is not possible to treat `i` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
Poincare/Global/ScalarGradientEvolution.lean:274:30: error: unknown free variable `_fvar.79718`
Poincare/Global/ScalarGradientEvolution.lean:267:55: error: unsolved goals
N : Type u
inst✝⁷ : TopologicalSpace N
inst✝⁶ : T2Space N
inst✝⁵ : CompactSpace N
inst✝⁴ : ConnectedSpace N
inst✝³ : MeasurableSpace N
inst✝² : BorelSpace N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
g : ClosedSmoothRiemannianMetric 3 N
x : N
f : N → ℝ
hs : tsupport f ⊆ (extChartAt I₃ x).source
hf : ContMDiff I₃ 𝓘(ℝ, ℝ) 2 f
u : E₃ → ℝ := ClosedLaplacianStokesProducer.coordinateScalar x f
q : E₃ := ↑(extChartAt I₃ x) x
b : Module.Basis (Fin (Module.finrank ℝ E₃)) ℝ E₃ := Module.finBasis ℝ E₃
this : FiniteDimensional ℝ (TangentSpace I₃ x) := laplacianAt_eq_anchor_derivatives._proof_1_1 x
hD : mfderivWithin 𝓘(ℝ, E₃) I₃ (↑(extChartAt I₃ x).symm) (range ↑I₃) q = ContinuousLinearMap.id ℝ E₃
⊢ g.laplacianAt f x =
    ∑ i, ((fderiv ℝ (fderiv ℝ u) q) (metricDualVectorAt g x (b.coord i))) (b i) -
      (fderiv ℝ u q)
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) q
            (metricDualVectorAt g x (b.coord sorry)))
          (b sorry))

```

</details>

<details>
<summary>18-bochner-audit.log</summary>

```text
'Poincare.ScalarGradientEvolution.bochner_anchorBlendedMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

</details>

<details>
<summary>19-laplacian.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:285:2: error: Type mismatch: After simplification, term
  h
 has type
  g.hessianAt f (↑(extChartAt I₃ x).symm (↑(extChartAt I₃ x) x))
      ((mfderivWithin 𝓘(ℝ, E₃) I₃ (↑(extChartAt I₃ x).symm) (range ↑I₃) (↑(extChartAt I₃ x) x))
        (metricDualVectorAt g x (b.coord i)))
      ((mfderivWithin 𝓘(ℝ, E₃) I₃ (↑(extChartAt I₃ x).symm) (range ↑I₃) (↑(extChartAt I₃ x) x)) (b i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(extChartAt I₃ x) x))
          (metricDualVectorAt g x (b.coord i)))
        (b i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(extChartAt I₃ x) x))
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) (↑(extChartAt I₃ x) x)
            (metricDualVectorAt g x (b.coord i)))
          (b i))
but is expected to have type
  g.hessianAt f x (metricDualVectorAt g x ((Module.finBasis ℝ (TangentSpace I₃ x)).coord i))
      ((Module.finBasis ℝ (TangentSpace I₃ x)) i) =
    ((fderiv ℝ (fderiv ℝ u) q) (metricDualVectorAt g x (b.coord i))) (b i) -
      (fderiv ℝ u q)
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) q
            (metricDualVectorAt g x (b.coord i)))
          (b i))

```

</details>

<details>
<summary>20-laplacian.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:287:2: error: Type mismatch: After simplification, term
  h
 has type
  g.hessianAt f (↑(chartAt E₃ x).symm (↑(chartAt E₃ x) x))
      ((ContinuousLinearMap.id ℝ E₃) (metricDualVectorAt g x ((Module.finBasis ℝ E₃).coord i)))
      ((ContinuousLinearMap.id ℝ E₃) ((Module.finBasis ℝ E₃) i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(chartAt E₃ x) x))
          (metricDualVectorAt g x ((Module.finBasis ℝ E₃).coord i)))
        ((Module.finBasis ℝ E₃) i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(chartAt E₃ x) x))
        ((CovariantDerivative.chartMetric g.inner x (↑(chartAt E₃ x) x)).inverse
          (LinearMap.toContinuousLinearMap
            (CovariantDerivative.christoffelFunctional (CovariantDerivative.chartMetric g.inner x) (↑(chartAt E₃ x) x)
              (metricDualVectorAt g x ((Module.finBasis ℝ E₃).coord i)) ((Module.finBasis ℝ E₃) i))))
but is expected to have type
  g.hessianAt f x (metricDualVectorAt g x ((Module.finBasis ℝ (TangentSpace I₃ x)).coord i))
      ((Module.finBasis ℝ (TangentSpace I₃ x)) i) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(chartAt E₃ x) x))
          (metricDualVectorAt g x ((Module.finBasis ℝ E₃).coord i)))
        ((Module.finBasis ℝ E₃) i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(chartAt E₃ x) x))
        ((CovariantDerivative.chartMetric g.inner x (↑(chartAt E₃ x) x)).inverse
          (LinearMap.toContinuousLinearMap
            (CovariantDerivative.christoffelFunctional (CovariantDerivative.chartMetric g.inner x) (↑(chartAt E₃ x) x)
              (metricDualVectorAt g x ((Module.finBasis ℝ E₃).coord i)) ((Module.finBasis ℝ E₃) i))))

```

</details>

<details>
<summary>21-laplacian.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:286:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (ContinuousLinearMap.id ?m.469 ?m.471) ?x
in the target expression
  g.hessianAt f (↑(extChartAt I₃ x).symm (↑(extChartAt I₃ x) x))
      ((ContinuousLinearMap.id ℝ E₃) (metricDualVectorAt g x (b.coord i))) ((ContinuousLinearMap.id ℝ E₃) (b i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(extChartAt I₃ x) x))
          (metricDualVectorAt g x (b.coord i)))
        (b i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(extChartAt I₃ x) x))
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) (↑(extChartAt I₃ x) x)
            (metricDualVectorAt g x (b.coord i)))
          (b i))

N : Type u
inst✝⁷ : TopologicalSpace N
inst✝⁶ : T2Space N
inst✝⁵ : CompactSpace N
inst✝⁴ : ConnectedSpace N
inst✝³ : MeasurableSpace N
inst✝² : BorelSpace N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
g : ClosedSmoothRiemannianMetric 3 N
x : N
f : N → ℝ
hs : tsupport f ⊆ (extChartAt I₃ x).source
hf : ContMDiff I₃ 𝓘(ℝ, ℝ) 2 f
u : E₃ → ℝ := ClosedLaplacianStokesProducer.coordinateScalar x f
q : E₃ := ↑(extChartAt I₃ x) x
b : Module.Basis (Fin (Module.finrank ℝ E₃)) ℝ E₃ := Module.finBasis ℝ E₃
this : FiniteDimensional ℝ (TangentSpace I₃ x) := laplacianAt_eq_anchor_derivatives._proof_1_1 x
hD :
  mfderivWithin 𝓘(ℝ, E₃) I₃ (↑(extChartAt I₃ x).symm) (range ↑I₃) (↑(extChartAt I₃ x) x) = ContinuousLinearMap.id ℝ E₃
i : Fin (Module.finrank ℝ (TangentSpace I₃ x))
a✝ : i ∈ Finset.univ
h :
  g.hessianAt f (↑(extChartAt I₃ x).symm (↑(extChartAt I₃ x) x))
      ((ContinuousLinearMap.id ℝ E₃) (metricDualVectorAt g x (b.coord i))) ((ContinuousLinearMap.id ℝ E₃) (b i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(extChartAt I₃ x) x))
          (metricDualVectorAt g x (b.coord i)))
        (b i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(extChartAt I₃ x) x))
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) (↑(extChartAt I₃ x) x)
            (metricDualVectorAt g x (b.coord i)))
          (b i))
⊢ g.hessianAt f x (metricDualVectorAt g x ((Module.finBasis ℝ (TangentSpace I₃ x)).coord i))
      ((Module.finBasis ℝ (TangentSpace I₃ x)) i) =
    ((fderiv ℝ (fderiv ℝ u) q) (metricDualVectorAt g x (b.coord i))) (b i) -
      (fderiv ℝ u q)
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) q
            (metricDualVectorAt g x (b.coord i)))
          (b i))

```

</details>

<details>
<summary>22-laplacian-audit.log</summary>

```text
/tmp/scalar-gradient-evolution-evidence/22-laplacian-audit.lean:286:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (ContinuousLinearMap.id ?m.469 ?m.471) ?x
in the target expression
  g.hessianAt f (↑(extChartAt I₃ x).symm (↑(extChartAt I₃ x) x))
      ((ContinuousLinearMap.id ℝ E₃) (metricDualVectorAt g x (b.coord i))) ((ContinuousLinearMap.id ℝ E₃) (b i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(extChartAt I₃ x) x))
          (metricDualVectorAt g x (b.coord i)))
        (b i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(extChartAt I₃ x) x))
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) (↑(extChartAt I₃ x) x)
            (metricDualVectorAt g x (b.coord i)))
          (b i))

N : Type u
inst✝⁷ : TopologicalSpace N
inst✝⁶ : T2Space N
inst✝⁵ : CompactSpace N
inst✝⁴ : ConnectedSpace N
inst✝³ : MeasurableSpace N
inst✝² : BorelSpace N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
g : ClosedSmoothRiemannianMetric 3 N
x : N
f : N → ℝ
hs : tsupport f ⊆ (extChartAt I₃ x).source
hf : ContMDiff I₃ 𝓘(ℝ, ℝ) 2 f
u : E₃ → ℝ := ClosedLaplacianStokesProducer.coordinateScalar x f
q : E₃ := ↑(extChartAt I₃ x) x
b : Module.Basis (Fin (Module.finrank ℝ E₃)) ℝ E₃ := Module.finBasis ℝ E₃
this : FiniteDimensional ℝ (TangentSpace I₃ x) := laplacianAt_eq_anchor_derivatives._proof_1_1 x
hD :
  mfderivWithin 𝓘(ℝ, E₃) I₃ (↑(extChartAt I₃ x).symm) (range ↑I₃) (↑(extChartAt I₃ x) x) = ContinuousLinearMap.id ℝ E₃
i : Fin (Module.finrank ℝ (TangentSpace I₃ x))
a✝ : i ∈ Finset.univ
h :
  g.hessianAt f (↑(extChartAt I₃ x).symm (↑(extChartAt I₃ x) x))
      ((ContinuousLinearMap.id ℝ E₃) (metricDualVectorAt g x (b.coord i))) ((ContinuousLinearMap.id ℝ E₃) (b i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(extChartAt I₃ x) x))
          (metricDualVectorAt g x (b.coord i)))
        (b i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(extChartAt I₃ x) x))
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) (↑(extChartAt I₃ x) x)
            (metricDualVectorAt g x (b.coord i)))
          (b i))
⊢ g.hessianAt f x (metricDualVectorAt g x ((Module.finBasis ℝ (TangentSpace I₃ x)).coord i))
      ((Module.finBasis ℝ (TangentSpace I₃ x)) i) =
    ((fderiv ℝ (fderiv ℝ u) q) (metricDualVectorAt g x (b.coord i))) (b i) -
      (fderiv ℝ u q)
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) q
            (metricDualVectorAt g x (b.coord i)))
          (b i))
'Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

```

</details>

<details>
<summary>23-laplacian.log</summary>

```text
Poincare/Global/ScalarGradientEvolution.lean:287:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (ContinuousLinearMap.id ?m.469 ?m.471) ?x
in the target expression
  g.hessianAt f (↑(extChartAt I₃ x).symm (↑(extChartAt I₃ x) x))
      ((ContinuousLinearMap.id ℝ E₃) (metricDualVectorAt g x (b.coord i))) ((ContinuousLinearMap.id ℝ E₃) (b i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(extChartAt I₃ x) x))
          (metricDualVectorAt g x (b.coord i)))
        (b i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(extChartAt I₃ x) x))
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) (↑(extChartAt I₃ x) x)
            (metricDualVectorAt g x (b.coord i)))
          (b i))

N : Type u
inst✝⁷ : TopologicalSpace N
inst✝⁶ : T2Space N
inst✝⁵ : CompactSpace N
inst✝⁴ : ConnectedSpace N
inst✝³ : MeasurableSpace N
inst✝² : BorelSpace N
inst✝¹ : ChartedSpace E₃ N
inst✝ : IsManifold I₃ ∞ N
g : ClosedSmoothRiemannianMetric 3 N
x : N
f : N → ℝ
hs : tsupport f ⊆ (extChartAt I₃ x).source
hf : ContMDiff I₃ 𝓘(ℝ, ℝ) 2 f
u : E₃ → ℝ := ClosedLaplacianStokesProducer.coordinateScalar x f
q : E₃ := ↑(extChartAt I₃ x) x
b : Module.Basis (Fin (Module.finrank ℝ E₃)) ℝ E₃ := Module.finBasis ℝ E₃
this : FiniteDimensional ℝ (TangentSpace I₃ x) := laplacianAt_eq_anchor_derivatives._proof_1_1 x
hD :
  mfderivWithin 𝓘(ℝ, E₃) I₃ (↑(extChartAt I₃ x).symm) (range ↑I₃) (↑(extChartAt I₃ x) x) = ContinuousLinearMap.id ℝ E₃
i : Fin (Module.finrank ℝ (TangentSpace I₃ x))
a✝ : i ∈ Finset.univ
h :
  g.hessianAt f (↑(extChartAt I₃ x).symm (↑(extChartAt I₃ x) x))
      ((ContinuousLinearMap.id ℝ E₃) (metricDualVectorAt g x (b.coord i))) ((ContinuousLinearMap.id ℝ E₃) (b i)) =
    ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f)) (↑(extChartAt I₃ x) x))
          (metricDualVectorAt g x (b.coord i)))
        (b i) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar x f) (↑(extChartAt I₃ x) x))
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) (↑(extChartAt I₃ x) x)
            (metricDualVectorAt g x (b.coord i)))
          (b i))
⊢ g.hessianAt f x (metricDualVectorAt g x ((Module.finBasis ℝ (TangentSpace I₃ x)).coord i))
      ((Module.finBasis ℝ (TangentSpace I₃ x)) i) =
    ((fderiv ℝ (fderiv ℝ u) q) (metricDualVectorAt g x (b.coord i))) (b i) -
      (fderiv ℝ u q)
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) q
            (metricDualVectorAt g x (b.coord i)))
          (b i))

```

</details>

<details>
<summary>24-laplacian.log</summary>

```text

```

</details>

<details>
<summary>25-laplacian-audit.log</summary>

```text
'Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

</details>

<details>
<summary>26-emit.log</summary>

```text

exit=0

```

</details>

<details>
<summary>26-module-audit.log</summary>

```text
/tmp/scalar-gradient-evolution-evidence/26-module-audit.lean:1:0: error: object file '/tmp/scalar-gradient-evolution-evidence/overlay/Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.olean' of module Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic does not exist

exit=1

```

</details>

<details>
<summary>27-intrinsic-bochner-residual.log</summary>

```text
/tmp/scalar-gradient-evolution-evidence/27-intrinsic-bochner-residual.lean:324:2: error: Type mismatch: After simplification, term
  h
 has type
  CovariantDerivative.curvedLaplacian (anchorBlendedMetricFlow (fun x => g) x 0)
      (fun z => RicciFlow.RicciFlow.metricBilin (anchorBlendedMetricFlow (fun x => g) x 0 z)) ⋯
      (RicciFlow.RicciFlow.coordGradNormSq (anchorBlendedMetricFlow (fun x => g) x 0) fun z =>
        g.scalarAt (↑(extChartAt I₃ x).symm z))
      (↑(extChartAt I₃ x) x) =
    2 *
          RicciFlow.RicciFlow.coordCovariantHessNormSq (anchorBlendedMetricFlow (fun x => g) x 0)
            (fun z => g.scalarAt (↑(extChartAt I₃ x).symm z)) (↑(extChartAt I₃ x) x) +
        2 *
          ((anchorBlendedMetricFlow (fun x => g) x 0 (↑(extChartAt I₃ x) x))
              (RicciFlow.RicciFlow.coordGradient (anchorBlendedMetricFlow (fun x => g) x 0)
                (fun z => g.scalarAt (↑(extChartAt I₃ x).symm z)) (↑(extChartAt I₃ x) x)))
            (RicciFlow.RicciFlow.coordGradient (anchorBlendedMetricFlow (fun x => g) x 0)
              (CovariantDerivative.curvedLaplacian (anchorBlendedMetricFlow (fun x => g) x 0)
                (fun z => RicciFlow.RicciFlow.metricBilin (anchorBlendedMetricFlow (fun x => g) x 0 z)) ⋯ fun z =>
                g.scalarAt (↑(extChartAt I₃ x).symm z))
              (↑(extChartAt I₃ x) x)) +
      2 *
        g.ricciAt x
          (RicciFlow.RicciFlow.coordGradient (anchorBlendedMetricFlow (fun x => g) x 0)
            (fun z => g.scalarAt (↑(extChartAt I₃ x).symm z)) (↑(extChartAt I₃ x) x))
          (RicciFlow.RicciFlow.coordGradient (anchorBlendedMetricFlow (fun x => g) x 0)
            (fun z => g.scalarAt (↑(extChartAt I₃ x).symm z)) (↑(extChartAt I₃ x) x))
but is expected to have type
  g.laplacianAt
      (fun y => ((g.inner y) (g.gradientAt (fun y => g.scalarAt y) y)) (g.gradientAt (fun y => g.scalarAt y) y)) x =
    2 *
          ∑ i,
            ((g.inner x) ((↑g.leviCivita (g.gradient R) x) (b i)))
              ((↑g.leviCivita (g.gradient R) x) (metricDualVectorAt g x (b.coord i))) +
        2 * ((g.inner x) (g.gradientAt R x)) (g.gradientAt (fun y => g.laplacianAt R y) x) +
      2 * g.ricciAt x (g.gradientAt R x) (g.gradientAt R x)

```

</details>

<details>
<summary>28-module-audit.log</summary>

```text
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} (hgt : Poincare.TimeDifferentiableAt gt t₀ x)
  {α : ℝ → TangentSpace (Poincare.closedSmoothModelWithCorners n) x →L[ℝ] ℝ}
  {α' : TangentSpace (Poincare.closedSmoothModelWithCorners n) x →L[ℝ] ℝ} (hα : HasDerivAt α α' t₀) :
  HasDerivAt (fun t => (α t) (((gt t).metricRaiseContinuousAt x) (α t)))
    (2 * α' (((gt t₀).metricRaiseContinuousAt x) (α t₀)) -
      Poincare.timeDerivAt gt t₀ x (((gt t₀).metricRaiseContinuousAt x) (α t₀))
        (((gt t₀).metricRaiseContinuousAt x) (α t₀)))
    t₀
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_23.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} (a : ℝ)
  (b : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : ‖a • b‖ ≤ ‖a‖ * ‖b‖
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_23' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_8.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x →
    TangentSpace (Poincare.closedSmoothModelWithCorners n) x → ENNReal
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_14.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  (Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11.lift' fun s => SetRel.comp s s) ≤
    Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {f : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
  (hf : ∀ (t : ℝ), MDiffAt (f t) x) (hft : (MDiffAt fun y => deriv (fun t => f t y) t₀) x)
  (hJoint :
    ContDiffAt ℝ 2 (fun p => f p.1 (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x).symm p.2))
      (t₀, ↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x) x)) :
  HasDerivAt (fun t => extDerivFun (f t) x) (extDerivFun (fun y => deriv (fun t => f t y) t₀) x) t₀
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_17.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Filter (TangentSpace (Poincare.closedSmoothModelWithCorners n) x)
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_17' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution._aux_Poincare_Global_ScalarGradientEvolution___macroRules__private_Poincare_Global_ScalarGradientEvolution_0_Poincare_ScalarGradientEvolution_termTM_1✝ :
  Macro
'_private.Poincare.Global.ScalarGradientEvolution.0.Poincare.ScalarGradientEvolution._aux_Poincare_Global_ScalarGradientEvolution___macroRules__private_Poincare_Global_ScalarGradientEvolution_0_Poincare_ScalarGradientEvolution_termTM_1' does not depend on any axioms
/tmp/scalar-gradient-evolution-evidence/26-module-audit.lean:4:0: error: Unexpected foundational dependencies for _private.Poincare.Global.ScalarGradientEvolution.0.Poincare.ScalarGradientEvolution._aux_Poincare_Global_ScalarGradientEvolution___macroRules__private_Poincare_Global_ScalarGradientEvolution_0_Poincare_ScalarGradientEvolution_termTM_1: []

exit=1

```

</details>

<details>
<summary>29-no-notation.log</summary>

```text

```

</details>

<details>
<summary>30-emit.log</summary>

```text

exit=0

```

</details>

<details>
<summary>30-module-audit.log</summary>

```text
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} (hgt : Poincare.TimeDifferentiableAt gt t₀ x)
  {α : ℝ → TangentSpace (Poincare.closedSmoothModelWithCorners n) x →L[ℝ] ℝ}
  {α' : TangentSpace (Poincare.closedSmoothModelWithCorners n) x →L[ℝ] ℝ} (hα : HasDerivAt α α' t₀) :
  HasDerivAt (fun t => (α t) (((gt t).metricRaiseContinuousAt x) (α t)))
    (2 * α' (((gt t₀).metricRaiseContinuousAt x) (α t₀)) -
      Poincare.timeDerivAt gt t₀ x (((gt t₀).metricRaiseContinuousAt x) (α t₀))
        (((gt t₀).metricRaiseContinuousAt x) (α t₀)))
    t₀
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_23.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} (a : ℝ)
  (b : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : ‖a • b‖ ≤ ‖a‖ * ‖b‖
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_23' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_8.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x →
    TangentSpace (Poincare.closedSmoothModelWithCorners n) x → ENNReal
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_14.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  (Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11.lift' fun s => SetRel.comp s s) ≤
    Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {f : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
  (hf : ∀ (t : ℝ), MDiffAt (f t) x) (hft : (MDiffAt fun y => deriv (fun t => f t y) t₀) x)
  (hJoint :
    ContDiffAt ℝ 2 (fun p => f p.1 (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x).symm p.2))
      (t₀, ↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x) x)) :
  HasDerivAt (fun t => extDerivFun (f t) x) (extDerivFun (fun y => deriv (fun t => f t y) t₀) x) t₀
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_17.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Filter (TangentSpace (Poincare.closedSmoothModelWithCorners n) x)
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_17' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_3.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x →
    TangentSpace (Poincare.closedSmoothModelWithCorners n) x → ℝ
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_7.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ y z : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : dist x✝ z ≤ dist x✝ y + dist y z
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.coordRicci_anchorBlendedMetric.{u} {N : Type u} [TopologicalSpace N] [T2Space N]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) N] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) N]
  (g : Poincare.ClosedSmoothRiemannianMetric 3 N) (x : N) (v w : Poincare.ClosedSmoothModel 3) :
  RicciFlow.RicciFlow.coordRicci (Poincare.anchorBlendedMetricFlow (fun x => g) x 0)
      (↑(extChartAt (Poincare.closedSmoothModelWithCorners 3) x) x) v w =
    g.ricciAt x v w
'Poincare.ScalarGradientEvolution.coordRicci_anchorBlendedMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_6.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : dist x✝ y = dist y x✝
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_13.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Filter.Tendsto Prod.swap Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_11
    Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_11
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_11.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Filter
    (TangentSpace (Poincare.closedSmoothModelWithCorners n) x ×
      TangentSpace (Poincare.closedSmoothModelWithCorners n) x)
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Filter
    (TangentSpace (Poincare.closedSmoothModelWithCorners n) x ×
      TangentSpace (Poincare.closedSmoothModelWithCorners n) x)
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_1.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} : TangentSpace (Poincare.closedSmoothModelWithCorners n) x → ℝ
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_23.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} (a : ℝ)
  (b : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : ‖a • b‖ ≤ ‖a‖ * ‖b‖
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_23' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hgt : Poincare.TimeDifferentiableAt gt t₀ x) {f : ℝ → M → ℝ} {f' : M → ℝ}
  (hdf : HasDerivAt (fun t => extDerivFun (f t) x) (extDerivFun f' x) t₀) :
  HasDerivAt (fun t => (((gt t).inner x) ((gt t).gradientAt (f t) x)) ((gt t).gradientAt (f t) x))
    (2 * (((gt t₀).inner x) ((gt t₀).gradientAt f' x)) ((gt t₀).gradientAt (f t₀) x) -
      Poincare.timeDerivAt gt t₀ x ((gt t₀).gradientAt (f t₀) x) ((gt t₀).gradientAt (f t₀) x))
    t₀
'Poincare.ScalarGradientEvolution.hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_5.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : dist x✝ x✝ = 0
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_10.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam
    (∀ (x_1 y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
      Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_8 x_1 y =
        ENNReal.ofReal (dist x_1 y))
    PseudoMetricSpace.edist_dist._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_14.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  (Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_11.lift' fun s =>
      SetRel.comp s s) ≤
    Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_11
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_16.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam
    (uniformity (TangentSpace (Poincare.closedSmoothModelWithCorners n) x) =
      ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | dist p.1 p.2 < ε})
    PseudoMetricSpace.uniformity_dist._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_21.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  {x✝ y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x} : dist x✝ y = 0 → x✝ = y
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_21' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_13.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Filter.Tendsto Prod.swap Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11
    Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_3.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x →
    TangentSpace (Poincare.closedSmoothModelWithCorners n) x → ℝ
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_15.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) :
  nhds x✝ =
    Filter.comap (Prod.mk x✝) Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_11
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_19.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_17 ≤ Filter.cofinite
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_19' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_22.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam (∀ (x_1 y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x), dist x_1 y = ‖-x_1 + y‖)
    NormedAddCommGroup.dist_eq._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_22' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow.{u} {N : Type u} [TopologicalSpace N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) N] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) N]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 N} {t₀ : ℝ} {x : N}
  (hJoint : ∀ (t : ℝ) (y : N), Poincare.MetricEntriesJointContDiffAt gt t y 3)
  (hFlow : ∀ (y : N), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
  (hScalarJoint :
    ContDiffAt ℝ 2 (fun p => (gt p.1).scalarAt (↑(extChartAt (Poincare.closedSmoothModelWithCorners 3) x).symm p.2))
      (t₀, ↑(extChartAt (Poincare.closedSmoothModelWithCorners 3) x) x))
  (hLap : (MDiffAt fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) :
  HasDerivAt (fun t => (gt t).scalarGradNormSqAt x)
    (2 *
            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
              ((gt t₀).gradientAt (fun y => (gt t₀).laplacianAt (fun z => (gt t₀).scalarAt z) y) x) +
          4 *
            (((gt t₀).inner x) ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x))
              ((gt t₀).gradientAt (fun y => (gt t₀).ricciNormSqAt y) x) +
        2 *
          (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x)
            ((gt t₀).gradientAt (fun y => (gt t₀).scalarAt y) x) -
      2 * Poincare.meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x)
    t₀
'Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_20.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam
    ((Bornology.cobounded (TangentSpace (Poincare.closedSmoothModelWithCorners n) x)).sets =
      {s | ∃ C, ∀ x_1 ∈ sᶜ, ∀ y ∈ sᶜ, dist x_1 y ≤ C})
    PseudoMetricSpace.cobounded_sets._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_20' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_6.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : dist x✝ y = dist y x✝
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_8.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x →
    TangentSpace (Poincare.closedSmoothModelWithCorners n) x → ENNReal
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives._proof_1_1.{u_1} {N : Type u_1} [TopologicalSpace N]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) N] (x : N) :
  FiniteDimensional ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x)
'Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives._proof_1_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_21.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  {x✝ y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x} : dist x✝ y = 0 → x✝ = y
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_21' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_17.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Filter (TangentSpace (Poincare.closedSmoothModelWithCorners n) x)
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_17' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_24.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  FiniteDimensional ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners n) x)
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_24' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_10.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam
    (∀ (x_1 y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
      Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_8 x_1 y = ENNReal.ofReal (dist x_1 y))
    PseudoMetricSpace.edist_dist._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_1.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x → ℝ
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_22.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam (∀ (x_1 y : TangentSpace (Poincare.closedSmoothModelWithCorners n) x), dist x_1 y = ‖-x_1 + y‖)
    NormedAddCommGroup.dist_eq._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_22' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.bochner_anchorBlendedMetric.{u} {N : Type u} [TopologicalSpace N] [T2Space N]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) N] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) N]
  (g : Poincare.ClosedSmoothRiemannianMetric 3 N) (x : N) (f : Poincare.ClosedSmoothModel 3 → ℝ) (hf : ContDiff ℝ 3 f) :
  let G := Poincare.anchorBlendedMetricFlow (fun x => g) x 0;
  have hsymm := ⋯;
  have hb := ⋯;
  have Δ := CovariantDerivative.curvedLaplacian G (fun z => RicciFlow.RicciFlow.metricBilin (G z)) hb;
  have q := ↑(extChartAt (Poincare.closedSmoothModelWithCorners 3) x) x;
  Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
    2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q +
        2 * ((G q) (RicciFlow.RicciFlow.coordGradient G f q)) (RicciFlow.RicciFlow.coordGradient G (Δ f) q) +
      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient G f q) (RicciFlow.RicciFlow.coordGradient G f q)
'Poincare.ScalarGradientEvolution.bochner_anchorBlendedMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_7.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ y z : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : dist x✝ z ≤ dist x✝ y + dist y z
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_5.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : dist x✝ x✝ = 0
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_15.{u_1} {n : ℕ} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M}
  (x✝ : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) :
  nhds x✝ = Filter.comap (Prod.mk x✝) Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._aux_1_11
'Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq._proof_1_15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_19.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._aux_1_17 ≤ Filter.cofinite
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_19' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_20.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam
    ((Bornology.cobounded (TangentSpace (Poincare.closedSmoothModelWithCorners n) x)).sets =
      {s | ∃ C, ∀ x_1 ∈ sᶜ, ∀ y ∈ sᶜ, dist x_1 y ≤ C})
    PseudoMetricSpace.cobounded_sets._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_20' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives.{u} {N : Type u} [TopologicalSpace N] [T2Space N]
  [CompactSpace N] [ConnectedSpace N] [MeasurableSpace N] [BorelSpace N] [ChartedSpace (Poincare.ClosedSmoothModel 3) N]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) N] (g : Poincare.ClosedSmoothRiemannianMetric 3 N) (x : N)
  (f : N → ℝ) (hs : tsupport f ⊆ (extChartAt (Poincare.closedSmoothModelWithCorners 3) x).source)
  (hf : ContMDiff (Poincare.closedSmoothModelWithCorners 3) (modelWithCornersSelf ℝ ℝ) 2 f) :
  have u := Poincare.ClosedLaplacianStokesProducer.coordinateScalar x f;
  have q := ↑(extChartAt (Poincare.closedSmoothModelWithCorners 3) x) x;
  have b := Module.finBasis ℝ (Poincare.ClosedSmoothModel 3);
  g.laplacianAt f x =
    ∑ i,
      (((fderiv ℝ (fderiv ℝ u) q) (Poincare.metricDualVectorAt g x (b.coord i))) (b i) -
        (fderiv ℝ u q)
          ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner x) q
              (Poincare.metricDualVectorAt g x (b.coord i)))
            (b i)))
'Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_16.{u_1} {n : ℕ} {M : Type u_1}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] {x : M} :
  autoParam
    (uniformity (TangentSpace (Poincare.closedSmoothModelWithCorners n) x) =
      ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | dist p.1 p.2 < ε})
    PseudoMetricSpace.uniformity_dist._autoParam
'Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two._proof_1_16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_MODULE_AUDIT declarations=45; every declaration has exactly the required three dependencies

exit=0

```

</details>

<details>
<summary>31-final-token-whitespace-names.log</summary>

```text
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/ScalarGradientEvolution.lean
exit=1
$ git diff --check
exit=0
$ rg -n ^theorem  Poincare/Global/ScalarGradientEvolution.lean
22:theorem hasDerivAt_covectorNormSq
50:theorem hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
72:theorem hasDerivAt_extDerivFun_of_joint_contDiffAt_two
102:theorem hasDerivAt_scalarGradNormSq_normalizedFlow
169:theorem coordRicci_anchorBlendedMetric
215:theorem bochner_anchorBlendedMetric
252:theorem laplacianAt_eq_anchor_derivatives
exit=0

```

</details>

<details>
<summary>32-regularity-and-absence.log</summary>

```text
Poincare.anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
  (hJoint : Poincare.MetricEntriesJointContDiffAt gt t₀ x 3) :
  ContDiffAt ℝ 1 (Function.uncurry (Poincare.anchorChartScalarTraceFlow gt x))
    (t₀, ↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x) x)
Poincare.scalarAt_contMDiffAt_two_of_normalizedRicciFlow.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} (hFlow : ∀ (y : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
  (hEntries : ∀ (y : M), Poincare.TimeVariationExtContMDiffAt gt t₀ y 2) (x : M) :
  ContMDiffAt (Poincare.closedSmoothModelWithCorners n) 𝓘(ℝ, ℝ) 2 (fun y => (gt t₀).scalarAt y) x
Poincare.ricciNormSqAt_mdifferentiableAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (x : M) : (MDiffAt fun y => g.ricciNormSqAt y) x
Poincare.scalarAt_mdifferentiableAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (x : M) : (MDiffAt fun y => g.scalarAt y) x
Poincare.SatisfiesHamiltonScalarEvolutionAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
  [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1] : Prop
Poincare.ClosedSmoothRiemannianMetric.gradient.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x
Poincare.ClosedSmoothRiemannianMetric.hessianContinuousAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x →L[ℝ]
    TangentSpace (Poincare.closedSmoothModelWithCorners n) x →L[ℝ] ℝ
Poincare.covRicciNormSqAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) [g.leviCivita.ContMDiffCovariantDerivative 1] (x : M) : ℝ
/tmp/scalar-gradient-evolution-evidence/32-regularity-and-absence.lean:12:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.ScalarGradientEvolution.SatisfiesScalarGradientEvolutionAt`

exit=1

```

</details>

<details>
<summary>33-source-name-search.log</summary>

```text
$ rg declaration bochner_anchorBlendedMetric Poincare
Poincare/Global/ScalarGradientEvolution.lean:215:theorem bochner_anchorBlendedMetric
exit=0
$ rg declaration coordRicci_anchorBlendedMetric Poincare
Poincare/Global/ScalarGradientEvolution.lean:169:theorem coordRicci_anchorBlendedMetric
exit=0
$ rg declaration hasDerivAt_covectorNormSq Poincare
Poincare/Global/ScalarGradientEvolution.lean:22:theorem hasDerivAt_covectorNormSq
exit=0
$ rg declaration hasDerivAt_extDerivFun_of_joint_contDiffAt_two Poincare
Poincare/Global/ScalarGradientEvolution.lean:72:theorem hasDerivAt_extDerivFun_of_joint_contDiffAt_two
exit=0
$ rg declaration hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun Poincare
Poincare/Global/ScalarGradientEvolution.lean:50:theorem hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
exit=0
$ rg declaration hasDerivAt_scalarGradNormSq_normalizedFlow Poincare
Poincare/Global/ScalarGradientEvolution.lean:102:theorem hasDerivAt_scalarGradNormSq_normalizedFlow
exit=0
$ rg declaration laplacianAt_eq_anchor_derivatives Poincare
Poincare/Global/ScalarGradientEvolution.lean:252:theorem laplacianAt_eq_anchor_derivatives
exit=0

```

</details>

<details>
<summary>34-source-name-search.log</summary>

```text
$ rg declaration contDiff_blendedChartMetric Poincare
exit=1
$ rg declaration fderiv_clm_family_apply Poincare
exit=1
$ rg declaration gradient Poincare
Poincare/Global/Laplacian.lean:76:noncomputable def gradient (g : ClosedSmoothRiemannianMetric n M)
exit=0
$ rg declaration gradientAt Poincare
Poincare/Global/Laplacian.lean:66:noncomputable def gradientAt (g : ClosedSmoothRiemannianMetric n M)
exit=0
$ rg declaration hessianAt Poincare
Poincare/Global/Laplacian.lean:399:noncomputable def hessianAt (g : ClosedSmoothRiemannianMetric n M)
exit=0
$ rg declaration hessianContinuousAt Poincare
Poincare/Global/Laplacian.lean:451:noncomputable def hessianContinuousAt (g : ClosedSmoothRiemannianMetric n M)
exit=0
$ rg declaration laplacianAt Poincare
Poincare/Global/Laplacian.lean:482:noncomputable def laplacianAt (g : ClosedSmoothRiemannianMetric n M)
exit=0
$ rg declaration scalarGradNormSqAt Poincare
Poincare/Global/Laplacian.lean:198:noncomputable def scalarGradNormSqAt (g : ClosedSmoothRiemannianMetric n M)
exit=0
$ rg declaration scalarGradNormSqAt_le_three_covRicciNormSqAt Poincare
exit=1
$ rg declaration chartChristoffelField_contDiff_top Poincare
exit=1
$ rg declaration hessianAt_eq_chart_derivatives Poincare
exit=1
$ rg declaration IsClosedNormalizedRicciFlowSolutionAt Poincare
exit=1
$ rg declaration SatisfiesHamiltonScalarEvolutionAt Poincare
exit=1
$ rg declaration SatisfiesNormalizedHamiltonScalarEvolutionAt Poincare
exit=1
$ rg declaration SatisfiesScalarGradientEvolutionAt Poincare
exit=1
$ rg declaration anchorBlendedMetricFlow_isInvertible Poincare
exit=1
$ rg declaration anchorChartRicciEntryFlow_eq_ricciAt_anchor Poincare
exit=1
$ rg declaration anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries Poincare
exit=1
$ rg declaration chartChristoffelField_symm Poincare
exit=1
$ rg declaration covRicciNormSqAt Poincare
exit=1
$ rg declaration globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree Poincare
exit=1
$ rg declaration hasDerivAt_inner_of_timeDifferentiableAt Poincare
exit=1
$ rg declaration hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt Poincare
exit=1
$ rg declaration hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two Poincare
exit=1
$ rg declaration isClosedNormalizedRicciFlowSolutionAt_timeDerivAt Poincare
exit=1
$ rg declaration isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt Poincare
exit=1
$ rg declaration ricciNormSqAt_mdifferentiableAt Poincare
exit=1
$ rg declaration scalarAt_contMDiffAt_two_of_normalizedRicciFlow Poincare
exit=1
$ rg declaration scalarAt_mdifferentiableAt Poincare
exit=1
$ rg declaration scalarMinimumAt Poincare
Poincare/Global/ScalarEvolution.lean:4047:noncomputable def scalarMinimumAt (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
exit=0
$ rg declaration christoffelClosedOp_eq_christoffelAt Poincare
exit=1
$ rg declaration curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional Poincare
exit=1
$ rg declaration hasDerivAt_clm_of_forall_apply' Poincare
exit=1
$ rg declaration bochner_anchorBlendedMetric Poincare
exit=1
$ rg declaration coordRicci_anchorBlendedMetric Poincare
exit=1
$ rg declaration extDerivFun_apply_chart Poincare
Poincare/ChartIdentification.lean:86:theorem extDerivFun_apply_chart {f : M → 𝕜} {x : M} (hf : MDiffAt f x)
exit=0
$ rg declaration hasDerivAt_covectorNormSq Poincare
exit=1
$ rg declaration hasDerivAt_extDerivFun_of_joint_contDiffAt_two Poincare
exit=1
$ rg declaration hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun Poincare
exit=1
$ rg declaration hasDerivAt_scalarGradNormSq_normalizedFlow Poincare
exit=1
$ rg declaration laplacianAt_eq_anchor_derivatives Poincare
exit=1

```

</details>

<details>
<summary>inventory-corrected.log</summary>

```text
Poincare.ClosedSmoothRiemannianMetric.gradientAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x
Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) [g.leviCivita.ContMDiffCovariantDerivative 1] (x : M) : ℝ
Poincare.ClosedSmoothRiemannianMetric.hessianAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M)
  (v w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : ℝ
Poincare.ClosedSmoothRiemannianMetric.laplacianAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) : ℝ
RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional.{u_2} {E : Type u_2}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
  (hG : ContDiff ℝ 3 G) (hGsymm : ∀ (y p q : E), ((G y) p) q = ((G y) q) p) (hinv : ∀ (y : E), (G y).IsInvertible)
  {f : E → ℝ} (hf : ContDiff ℝ 3 f) :
  CovariantDerivative.curvedLaplacian G (fun y => RicciFlow.RicciFlow.metricBilin (G y)) ⋯
      (RicciFlow.RicciFlow.coordGradNormSq G f) x =
    2 *
        (((G x) (RicciFlow.RicciFlow.coordGradient G f x))
            (RicciFlow.RicciFlow.coordGradient G
              (CovariantDerivative.curvedLaplacian G (fun y => RicciFlow.RicciFlow.metricBilin (G y)) ⋯ f) x) +
          RicciFlow.RicciFlow.coordRicci G x (RicciFlow.RicciFlow.coordGradient G f x)
            (RicciFlow.RicciFlow.coordGradient G f x)) +
      2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f x
Poincare.hasDerivAt_inner_of_timeDifferentiableAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} (hgt : Poincare.TimeDifferentiableAt gt t₀ x) :
  HasDerivAt (fun t => (gt t).inner x) (Poincare.timeDerivContinuousAt gt t₀ x hgt) t₀
Poincare.hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hgt : Poincare.TimeDifferentiableAt gt t₀ x) :
  HasDerivAt (fun t => (gt t).metricRaiseContinuousAt x) (Poincare.metricRaiseDerivAt gt t₀ x hgt) t₀
Poincare.hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two.{u_1} {V : Type u_1} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (F : ℝ → V → ℝ) (t₀ : ℝ) (x a : V) (hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, x)) :
  HasDerivAt (fun t => (fderiv ℝ (F t) x) a) ((fderiv ℝ (fun z => deriv (fun t => F t z) t₀) x) a) t₀
Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt.{u} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (t : ℝ) (x : M) [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1] : Prop
Poincare.IsClosedNormalizedRicciFlowSolutionAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (t₀ : ℝ) (x : M) : Prop
Poincare.isClosedNormalizedRicciFlowSolutionAt_timeDerivAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hflow : Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
  {Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y} (hZ : Poincare.ClosedC2TangentField Z)
  (hreg : (gt t₀).leviCivita.DerivRegularAt Z x) (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) :
  Poincare.timeDerivAt gt t₀ x (Z x) w =
    -2 * (gt t₀).leviCivita.ricciTraceAt hreg w + 2 / ↑n * Poincare.meanScalar (gt t₀) * (((gt t₀).inner x) (Z x)) w
Poincare.globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  (hJoint : ∀ (t : ℝ) (y : M), Poincare.MetricEntriesJointContDiffAt gt t y 3) :
  Poincare.GlobalLichnerowiczAssemblyRegularity gt
Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt_le_three_covRicciNormSqAt.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  [g.leviCivita.ContMDiffCovariantDerivative 1] (hn : n = 3) (x : M) :
  g.scalarGradNormSqAt x ≤ 3 * Poincare.covRicciNormSqAt g x
Poincare.scalarMinimumAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) : ℝ
Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] (g : Poincare.ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
  (hs : tsupport f ⊆ (extChartAt (Poincare.closedSmoothModelWithCorners n) p).source)
  (hf : ContMDiff (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 f)
  {z : Poincare.ClosedSmoothModel n} (hz : z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners n) p).target)
  (v w : Poincare.ClosedSmoothModel n) :
  have u := Poincare.ClosedLaplacianStokesProducer.coordinateScalar p f;
  have D :=
    mfderivWithin (modelWithCornersSelf ℝ (Poincare.ClosedSmoothModel n)) (Poincare.closedSmoothModelWithCorners n)
      (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) p).symm)
      (Set.range ↑(Poincare.closedSmoothModelWithCorners n)) z;
  g.hessianAt f (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) p).symm z) (D v) (D w) =
    ((fderiv ℝ (fderiv ℝ u) z) v) w -
      (fderiv ℝ u z) ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner p) z v) w)
extDerivFun_apply_chart.{u_1, u_2, u_3, u_4} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless] {f : M → 𝕜} {x : M} (hf : MDiffAt f x)
  (v : TangentSpace I x) : (extDerivFun f x) v = (fderiv 𝕜 (f ∘ ↑(extChartAt I x).symm) (↑(extChartAt I x) x)) v
def Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [inst_1 : T2Space M] →
      [CompactSpace M] →
        [ConnectedSpace M] →
          [inst_4 : MeasurableSpace M] →
            [BorelSpace M] →
              [inst_6 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
                [inst_7 : IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] →
                  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) →
                    ℝ → M → [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1] → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] gt t x
    [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1] =>
  HasDerivAt (fun s => (gt s).scalarAt x)
    ((gt t).laplacianAt (fun y => (gt t).scalarAt y) x + 2 * (gt t).ricciNormSqAt x -
      2 / 3 * Poincare.meanScalar (gt t) * (gt t).scalarAt x)
    t
structure Poincare.IsClosedNormalizedRicciFlowSolutionAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (t₀ : ℝ) (x : M) : Prop
number of parameters: 13
fields:
  Poincare.IsClosedNormalizedRicciFlowSolutionAt.leviCivita : ∀ (t : ℝ),
      CovariantDerivative.IsLeviCivitaAt (fun y => (gt t).inner y) (gt t).leviCivita x
  Poincare.IsClosedNormalizedRicciFlowSolutionAt.flow : ∀
      {Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y},
      Poincare.ClosedC2TangentField Z →
        ∀ (hreg : (gt t₀).leviCivita.DerivRegularAt Z x) (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
          deriv (fun t => (((gt t).inner x) (Z x)) w) t₀ =
            -2 * (gt t₀).leviCivita.ricciTraceAt hreg w +
              2 / ↑n * Poincare.meanScalar (gt t₀) * (((gt t₀).inner x) (Z x)) w
constructor:
  Poincare.IsClosedNormalizedRicciFlowSolutionAt.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
    {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (leviCivita : ∀ (t : ℝ), CovariantDerivative.IsLeviCivitaAt (fun y => (gt t).inner y) (gt t).leviCivita x)
    (flow :
      ∀ {Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y},
        Poincare.ClosedC2TangentField Z →
          ∀ (hreg : (gt t₀).leviCivita.DerivRegularAt Z x)
            (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
            deriv (fun t => (((gt t).inner x) (Z x)) w) t₀ =
              -2 * (gt t₀).leviCivita.ricciTraceAt hreg w +
                2 / ↑n * Poincare.meanScalar (gt t₀) * (((gt t₀).inner x) (Z x)) w) :
    Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x
RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'.{u_2, u_3} {E : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type u_3} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : ℝ → E →L[ℝ] F} {ψ : E →L[ℝ] F}
  {t₀ : ℝ} (h : ∀ (w : E), HasDerivAt (fun t => (φ t) w) (ψ w) t₀) : HasDerivAt φ ψ t₀
Poincare.isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
  (hflow : Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
  (v w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) :
  Poincare.timeDerivAt gt t₀ x v w = Poincare.normalizedRicciFlowRHSAt (gt t₀) x v w

```

</details>

<details>
<summary>inventory-names.log</summary>

```text
$ rg -n gradientAt Poincare
Poincare/Global/DeTurckBUCQuasilinearDifferenceEnergy.lean:385:      g.inner x (g.gradientAt f x) (g.gradientAt f x) :=
Poincare/Global/DeTurckBUCQuasilinearDifferenceEnergy.lean:386:    g.inner_nonneg x (g.gradientAt f x)
Poincare/Global/ScalarEvolution.lean:432:    g.gradientAt (fun y : M ↦ f y ^ p) x =
Poincare/Global/ScalarEvolution.lean:433:      (p * f x ^ (p - 1)) • g.gradientAt f x := by
Poincare/Global/ScalarEvolution.lean:445:    g.gradientAt (fun y : M ↦ (g.scalarAt y) ^ p) x =
Poincare/Global/ScalarEvolution.lean:447:        g.gradientAt (fun y : M ↦ g.scalarAt y) x :=
Poincare/Global/ScalarEvolution.lean:538:      g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:544:  have hrepr : (∑ i, g.inner x (g.gradientAt f x) (b i) • sharp i) =
Poincare/Global/ScalarEvolution.lean:545:      g.gradientAt f x := by
Poincare/Global/ScalarEvolution.lean:548:        (v := g.gradientAt f x)
Poincare/Global/ScalarEvolution.lean:551:        (∑ i, g.inner x (g.gradientAt f x) (b i) • sharp i) =
Poincare/Global/ScalarEvolution.lean:552:      ∑ i, g.inner x (g.gradientAt f x) (b i) * extDerivFun f x (sharp i) := by
Poincare/Global/ScalarEvolution.lean:554:      (fun i ↦ g.inner x (g.gradientAt f x) (b i) • sharp i) Finset.univ
Poincare/Global/ScalarEvolution.lean:561:        ∑ i, g.inner x (g.gradientAt f x) (b i) * extDerivFun f x (sharp i) := by
Poincare/Global/ScalarEvolution.lean:564:          (∑ i, g.inner x (g.gradientAt f x) (b i) • sharp i) := hleft.symm
Poincare/Global/ScalarEvolution.lean:565:    _ = extDerivFun f x (g.gradientAt f x) := hdf
Poincare/Global/ScalarEvolution.lean:566:    _ = g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:578:          g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:587:        g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:595:        g.inner x (g.gradientAt f x) (g.gradientAt f x)
Poincare/Global/ScalarEvolution.lean:604:          g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:616:          g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:855:    g.gradientAt f x =
Poincare/Global/ScalarEvolution.lean:872:      b.coord i (g.gradientAt f x) =
Poincare/Global/ScalarEvolution.lean:876:      b.coord i (g.gradientAt f x) =
Poincare/Global/ScalarEvolution.lean:877:          g.inner x (g.gradientAt f x)
Poincare/Global/ScalarEvolution.lean:881:      _ = g.inner x (g.gradientAt f x) ((diag i)⁻¹ • b i) := by
Poincare/Global/ScalarEvolution.lean:887:    g.gradientAt f x = ∑ i, b.coord i (g.gradientAt f x) • b i :=
Poincare/Global/ScalarEvolution.lean:888:      (b.sum_repr (g.gradientAt f x)).symm
Poincare/Global/ScalarEvolution.lean:916:    g.inner x (g.gradientAt f x) (g.gradientAt f x) =
Poincare/Global/ScalarEvolution.lean:922:          (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:927:            g.inner x (b i) (g.gradientAt f x) := by
Poincare/Global/ScalarEvolution.lean:931:          rw [g.inner_symm x (b i) (g.gradientAt f x),
Poincare/Global/ScalarEvolution.lean:1144:        (g.gradientAt (fun y : M ↦ g.scalarAt y) x) := by
Poincare/Global/ScalarEvolution.lean:1155:      (g.gradientAt f x)
Poincare/Global/ScalarEvolution.lean:1194:      covRicciRicciPairingAt g x (g.gradientAt f x) =
Poincare/Global/ScalarEvolution.lean:1370:        (g.gradientAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x)
Poincare/Global/ScalarEvolution.lean:1371:        (g.gradientAt (fun y : M ↦ g.scalarAt y) x) =
Poincare/Global/ScalarEvolution.lean:1388:      g.gradientAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x =
Poincare/Global/ScalarEvolution.lean:1389:        g.gradientAt Nf x
Poincare/Global/ScalarEvolution.lean:1391:            g.gradientAt (fun y : M ↦ Rf y ^ 2) x := by
Poincare/Global/ScalarEvolution.lean:1400:      g.gradientAt (fun y : M ↦ Rf y ^ 2) x =
Poincare/Global/ScalarEvolution.lean:1401:        (2 * Rf x) • g.gradientAt Rf x := by
Poincare/Global/ScalarEvolution.lean:1412:      g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x) = 2 * B := by
Poincare/Global/ScalarEvolution.lean:1414:      g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x) =
Poincare/Global/ScalarEvolution.lean:1415:          extDerivFun Nf x (g.gradientAt Rf x) := by
Poincare/Global/ScalarEvolution.lean:1416:            simpa [Nf] using g.inner_gradientAt Nf x (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1417:      _ = 2 * covRicciRicciPairingAt g x (g.gradientAt Rf x) := by
Poincare/Global/ScalarEvolution.lean:1420:                (g := g) x (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1425:        (g.gradientAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x)
Poincare/Global/ScalarEvolution.lean:1426:        (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:1428:            (g.gradientAt Nf x
Poincare/Global/ScalarEvolution.lean:1430:                g.gradientAt (fun y : M ↦ Rf y ^ 2) x)
Poincare/Global/ScalarEvolution.lean:1431:            (g.gradientAt Rf x) := by
Poincare/Global/ScalarEvolution.lean:1526:    v x • g.gradientAt q x =
Poincare/Global/ScalarEvolution.lean:1527:      g.gradientAt u x - q x • g.gradientAt v x := by
Poincare/Global/ScalarEvolution.lean:1530:      g.gradientAt (q * v) x = g.gradientAt u x :=
Poincare/Global/ScalarEvolution.lean:1554:          - 2 * g.inner x (g.gradientAt q x) (g.gradientAt v x)) / v x := by
Poincare/Global/ScalarEvolution.lean:1563:          + 2 * g.inner x (g.gradientAt q x) (g.gradientAt v x) := by
Poincare/Global/ScalarEvolution.lean:1615:        + (p / Rf x) * g.inner x (g.gradientAt q x) (g.gradientAt Rf x) =
Poincare/Global/ScalarEvolution.lean:1618:        - p * g.inner x (g.gradientAt u x) (g.gradientAt Rf x) /
Poincare/Global/ScalarEvolution.lean:1621:            g.inner x (g.gradientAt Rf x) (g.gradientAt Rf x) / (Rf x) ^ 2 := by
Poincare/Global/ScalarEvolution.lean:1629:  let S : ℝ := g.inner x (g.gradientAt Rf x) (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1630:  let C : ℝ := g.inner x (g.gradientAt u x) (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1631:  let IQ : ℝ := g.inner x (g.gradientAt q x) (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1654:      g.gradientAt Vf x = (p * R ^ (p - 1)) • g.gradientAt Rf x := by
Poincare/Global/ScalarEvolution.lean:1668:            - 2 * g.inner x (g.gradientAt q x) (g.gradientAt Vf x)) /
Poincare/Global/ScalarEvolution.lean:1678:      Vf x • g.gradientAt q x =
Poincare/Global/ScalarEvolution.lean:1679:        g.gradientAt u x - q x • g.gradientAt Vf x :=
Poincare/Global/ScalarEvolution.lean:1684:      g.inner x (g.gradientAt q x) (g.gradientAt Vf x) =
Poincare/Global/ScalarEvolution.lean:1691:      (fun v : TM x ↦ g.inner x v (g.gradientAt Rf x)) hGradQuot
Poincare/Global/ScalarEvolution.lean:1750:              (g.gradientAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x)
Poincare/Global/ScalarEvolution.lean:1751:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x) /
Poincare/Global/ScalarEvolution.lean:1783:          g.inner x (g.gradientAt Qf x) (g.gradientAt Rf x) := by
Poincare/Global/ScalarEvolution.lean:1786:      (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:1787:      (g.gradientAt (fun y : M ↦ g.tracelessPinchingAt y δ) x)]
Poincare/Global/ScalarEvolution.lean:1814:                (g.gradientAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x)
Poincare/Global/ScalarEvolution.lean:1815:                (g.gradientAt (fun y : M ↦ g.scalarAt y) x) /
Poincare/Global/ScalarEvolution.lean:1905:  let IQ : ℝ := g.inner x (g.gradientAt Qf x) (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1937:            - 2 * g.inner x (g.gradientAt Qf x) (g.gradientAt Vf x)) / Vf x :=
Poincare/Global/ScalarEvolution.lean:1941:      Vf x • g.gradientAt Qf x =
Poincare/Global/ScalarEvolution.lean:1942:        g.gradientAt Nf x - Qf x • g.gradientAt Vf x :=
Poincare/Global/ScalarEvolution.lean:1946:      g.gradientAt Vf x = (2 * R) • g.gradientAt Rf x := by
Poincare/Global/ScalarEvolution.lean:1949:    change g.gradientAt (Rf * Rf) x = (2 * R) • g.gradientAt Rf x
Poincare/Global/ScalarEvolution.lean:1951:      g.gradientAt (Rf * Rf) x =
Poincare/Global/ScalarEvolution.lean:1952:          Rf x • g.gradientAt Rf x + Rf x • g.gradientAt Rf x := h
Poincare/Global/ScalarEvolution.lean:1953:      _ = (2 * R) • g.gradientAt Rf x := by
Poincare/Global/ScalarEvolution.lean:1970:      g.inner x (g.gradientAt Qf x) (g.gradientAt Vf x) = (2 * R) * IQ := by
Poincare/Global/ScalarEvolution.lean:1974:      g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x) = 2 * B := by
Poincare/Global/ScalarEvolution.lean:1976:      g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x) =
Poincare/Global/ScalarEvolution.lean:1977:          extDerivFun Nf x (g.gradientAt Rf x) := by
Poincare/Global/ScalarEvolution.lean:1979:              g.inner_gradientAt Nf x (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1980:      _ = 2 * covRicciRicciPairingAt g x (g.gradientAt Rf x) := by
Poincare/Global/ScalarEvolution.lean:1983:                (g := g) x (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1987:      g.inner x (g.gradientAt Vf x) (g.gradientAt Rf x) = (2 * R) * S := by
Poincare/Global/ScalarEvolution.lean:1994:        g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x)
Poincare/Global/ScalarEvolution.lean:1995:          - Qf x * g.inner x (g.gradientAt Vf x) (g.gradientAt Rf x) := by
Poincare/Global/ScalarEvolution.lean:1997:      (fun v : TM x ↦ g.inner x v (g.gradientAt Rf x)) hGradQuot
Poincare/Global/ScalarEvolution.lean:2010:    rw [g.inner_symm x (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:2011:      (g.gradientAt (fun y : M ↦ g.pinchingQuotientAt y) x)]
Poincare/Global/ScalarEvolution.lean:2019:            - 2 * g.inner x (g.gradientAt Qf x) (g.gradientAt Vf x)) / Vf x
Poincare/Global/ScalarEvolution.lean:3959:    g.gradientAt f x = 0 := by
Poincare/Global/ScalarEvolution.lean:3960:  refine LeviCivitaExistence.metric_nondegenerate g x (g.gradientAt f x) ?_
Poincare/Global/ScalarEvolution.lean:3989:    g.gradientAt f x = 0 := by
Poincare/Global/ScalarEvolution.lean:4000:      (-1 : ℝ) • g.gradientAt f x = 0 := by
Poincare/Global/ScalarEvolution.lean:4281:      g.gradientAt Qf x = 0 :=
Poincare/Global/ScalarEvolution.lean:4835:          (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:4836:          (g.gradientAt f x)
Poincare/Global/ScalarEvolution.lean:4887:        g.gradientAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/ScalarEvolution.lean:4888:          g.gradientAt (u τ) x := by
Poincare/Global/ScalarEvolution.lean:4889:      change g.gradientAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/ScalarEvolution.lean:4890:        g.gradientAt (u τ) x
Poincare/Global/ScalarEvolution.lean:4899:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:4900:              (g.gradientAt (fun y : M ↦ u τ y + k) x) =
Poincare/Global/ScalarEvolution.lean:4904:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:4905:              (g.gradientAt (u τ) x)
Poincare/Global/ScalarEvolution.lean:4963:        g.gradientAt (u τ) x = -g.gradientAt (Q τ) x := by
Poincare/Global/ScalarEvolution.lean:4976:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:4977:              (g.gradientAt (u τ) x) =
Poincare/Global/ScalarEvolution.lean:4992:                (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:4993:                (g.gradientAt (u τ) x) =
Poincare/Global/ScalarEvolution.lean:5013:        g.gradientAt (u τ) x = 0 :=
Poincare/Global/ScalarEvolution.lean:5020:            (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:5021:            (g.gradientAt (u τ) x)
Poincare/Global/ScalarEvolution.lean:5166:          (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:5167:          (g.gradientAt f x)
Poincare/Global/ScalarEvolution.lean:5219:        g.gradientAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/ScalarEvolution.lean:5220:          g.gradientAt (u τ) x := by
Poincare/Global/ScalarEvolution.lean:5221:      change g.gradientAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/ScalarEvolution.lean:5222:        g.gradientAt (u τ) x
Poincare/Global/ScalarEvolution.lean:5231:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:5232:              (g.gradientAt (fun y : M ↦ u τ y + k) x) =
Poincare/Global/ScalarEvolution.lean:5236:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:5237:              (g.gradientAt (u τ) x)
Poincare/Global/ScalarEvolution.lean:5282:        g.gradientAt (u τ) x = -g.gradientAt (Q τ) x := by
Poincare/Global/ScalarEvolution.lean:5295:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:5296:              (g.gradientAt (u τ) x) =
Poincare/Global/ScalarEvolution.lean:5311:                (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:5312:                (g.gradientAt (u τ) x) =
Poincare/Global/ScalarEvolution.lean:5332:        g.gradientAt (u τ) x = 0 :=
Poincare/Global/ScalarEvolution.lean:5339:            (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:5340:            (g.gradientAt (u τ) x)
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:79:    (g.gradientAt f ((extChartAt I p).symm z)) (D w) = _
Poincare/Global/Laplacian.lean:66:noncomputable def gradientAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:78:  fun x ↦ g.gradientAt f x
Poincare/Global/Laplacian.lean:80:/-- The defining property of `gradientAt`: pairing with the metric recovers `df`. -/
Poincare/Global/Laplacian.lean:83:    g.inner x (g.gradientAt f x) w = extDerivFun f x w := by
Poincare/Global/Laplacian.lean:86:  unfold gradientAt
Poincare/Global/Laplacian.lean:105:    g.gradientAt f x = g.gradientAt h x := by
Poincare/Global/Laplacian.lean:112:  unfold gradientAt
Poincare/Global/Laplacian.lean:119:    g.gradientAt (f + h) x = g.gradientAt f x + g.gradientAt h x := by
Poincare/Global/Laplacian.lean:127:  unfold gradientAt
Poincare/Global/Laplacian.lean:143:    g.gradientAt (f * h) x =
Poincare/Global/Laplacian.lean:144:      f x • g.gradientAt h x + h x • g.gradientAt f x := by
Poincare/Global/Laplacian.lean:164:    g.gradientAt (c • f) x = c • g.gradientAt f x := by
Poincare/Global/Laplacian.lean:171:  unfold gradientAt
Poincare/Global/Laplacian.lean:184:    g.gradientAt (fun _ : M ↦ c) x = 0 := by
Poincare/Global/Laplacian.lean:187:  unfold gradientAt
Poincare/Global/Laplacian.lean:201:  g.inner x (g.gradientAt (fun y ↦ g.scalarAt y) x)
Poincare/Global/Laplacian.lean:202:    (g.gradientAt (fun y ↦ g.scalarAt y) x)
Poincare/Global/Laplacian.lean:794:        + 2 * g.inner x (g.gradientAt f x) (g.gradientAt h x) := by
Poincare/Global/Laplacian.lean:835:        g.gradientAt h x := by
Poincare/Global/Laplacian.lean:836:    unfold gradientAt
Poincare/Global/Laplacian.lean:842:        g.gradientAt f x := by
Poincare/Global/Laplacian.lean:843:    unfold gradientAt
Poincare/Global/Laplacian.lean:846:  rw [← g.inner_gradientAt f x (g.gradientAt h x),
Poincare/Global/Laplacian.lean:847:    ← g.inner_gradientAt h x (g.gradientAt f x)]
Poincare/Global/Laplacian.lean:848:  rw [g.inner_symm x (g.gradientAt h x) (g.gradientAt f x)]
Poincare/Global/Laplacian.lean:857:        + 2 * g.inner x (g.gradientAt f x) (g.gradientAt h x) :=
Poincare/Global/Laplacian.lean:869:        2 * g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
Poincare/Global/ScalarVariation.lean:566:      (g.gradientAt (fun y ↦ g.scalarAt y) x)
Poincare/Global/ScalarVariation.lean:567:      (g.gradientAt (fun y ↦ g.pinchingQuotientAt y) x)
Poincare/Global/ScalarVariation.lean:576:      (g.gradientAt (fun y ↦ g.scalarAt y) x)
Poincare/Global/ScalarVariation.lean:577:      (g.gradientAt (fun y ↦ g.tracelessPinchingAt y δ) x)
Poincare/Global/ScalarVariation.lean:25294:    v x • g.gradientAt q x =
Poincare/Global/ScalarVariation.lean:25295:      g.gradientAt u x - q x • g.gradientAt v x := by
Poincare/Global/ScalarVariation.lean:25300:  change v x • g.gradientAt q x =
Poincare/Global/ScalarVariation.lean:25301:    g.gradientAt (q * v) x - q x • g.gradientAt v x
Poincare/Global/ScalarVariation.lean:25319:          - 2 * g.inner x (g.gradientAt q x) (g.gradientAt v x)) / v x := by
Poincare/Global/ScalarVariation.lean:25326:          + 2 * g.inner x (g.gradientAt q x) (g.gradientAt v x) := by
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:794:  let gradR : TM x := g.gradientAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1521:  have hgrad : g.gradientAt Qf x = 0 :=
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1527:      g.inner x (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1528:        (g.gradientAt Qf x) = 0
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1585:          (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1586:          (g.gradientAt f x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1637:        g.gradientAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1638:          g.gradientAt (u τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1639:      change g.gradientAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1640:        g.gradientAt (u τ) x
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1649:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1650:              (g.gradientAt (fun y : M ↦ u τ y + k) x) =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1654:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1655:              (g.gradientAt (u τ) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1713:        g.gradientAt (u τ) x = -g.gradientAt (Q τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1726:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1727:              (g.gradientAt (u τ) x) =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1742:                (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1743:                (g.gradientAt (u τ) x) =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1763:        g.gradientAt (u τ) x = 0 :=
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1770:            (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1771:            (g.gradientAt (u τ) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1892:          (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1893:          (g.gradientAt f x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1945:        g.gradientAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1946:          g.gradientAt (u τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1947:      change g.gradientAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1948:        g.gradientAt (u τ) x
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1957:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1958:              (g.gradientAt (fun y : M ↦ u τ y + k) x) =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1962:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1963:              (g.gradientAt (u τ) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2008:        g.gradientAt (u τ) x = -g.gradientAt (Q τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2021:              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2022:              (g.gradientAt (u τ) x) =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2037:                (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2038:                (g.gradientAt (u τ) x) =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2058:        g.gradientAt (u τ) x = 0 :=
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2065:            (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2066:            (g.gradientAt (u τ) x)
exit=0
$ rg -n scalarGradNormSqAt Poincare
Poincare/Global/ScalarEvolution.lean:92:        - 2 * (gt t₀).scalarGradNormSqAt x
Poincare/Global/ScalarEvolution.lean:108:          - 2 * (gt t₀).scalarGradNormSqAt x
Poincare/Global/ScalarEvolution.lean:116:    simp [ClosedSmoothRiemannianMetric.scalarGradNormSqAt]
Poincare/Global/ScalarEvolution.lean:632:          g.scalarGradNormSqAt x := by
Poincare/Global/ScalarEvolution.lean:633:  simpa [scalarGradNormSqAt] using
Poincare/Global/ScalarEvolution.lean:901:    g.scalarGradNormSqAt x =
Poincare/Global/ScalarEvolution.lean:914:  unfold scalarGradNormSqAt
Poincare/Global/ScalarEvolution.lean:1046:    g.scalarGradNormSqAt x ≤ 3 * covRicciNormSqAt g x := by
Poincare/Global/ScalarEvolution.lean:1230:      g.scalarGradNormSqAt x * g.ricciNormSqAt x := by
Poincare/Global/ScalarEvolution.lean:1298:        + g.scalarGradNormSqAt x * g.ricciNormSqAt x := by
Poincare/Global/ScalarEvolution.lean:1309:        g.scalarGradNormSqAt x * g.ricciNormSqAt x :=
Poincare/Global/ScalarEvolution.lean:1324:      (g.pinchingMixedGradientPairingAt x) (g.scalarGradNormSqAt x) δ ≤ 0 := by
Poincare/Global/ScalarEvolution.lean:1373:        - (2 / (n : ℝ)) * g.scalarAt x * g.scalarGradNormSqAt x := by
Poincare/Global/ScalarEvolution.lean:1376:  let S : ℝ := g.scalarGradNormSqAt x
Poincare/Global/ScalarEvolution.lean:1437:      simp [S, Rf, scalarGradNormSqAt, smul_eq_mul]
Poincare/Global/ScalarEvolution.lean:1459:        - (2 / (n : ℝ)) * g.scalarGradNormSqAt x := by
Poincare/Global/ScalarEvolution.lean:1505:        2 * Rf x * g.laplacianAt Rf x + 2 * g.scalarGradNormSqAt x := by
Poincare/Global/ScalarEvolution.lean:1506:    simpa [Sqf, Rf, scalarGradNormSqAt] using
Poincare/Global/ScalarEvolution.lean:1754:            g.scalarGradNormSqAt x / (g.scalarAt x) ^ 2 := by
Poincare/Global/ScalarEvolution.lean:1789:  simpa [Qf, Uf, Rf, p, ClosedSmoothRiemannianMetric.scalarGradNormSqAt] using
Poincare/Global/ScalarEvolution.lean:1818:              g.scalarGradNormSqAt x / (g.scalarAt x) ^ 2) :
Poincare/Global/ScalarEvolution.lean:1827:              - (2 / (n : ℝ)) * g.scalarAt x * g.scalarGradNormSqAt x) /
Poincare/Global/ScalarEvolution.lean:1830:            g.scalarGradNormSqAt x / (g.scalarAt x) ^ 2 := by
Poincare/Global/ScalarEvolution.lean:1902:  let S : ℝ := g.scalarGradNormSqAt x
Poincare/Global/ScalarEvolution.lean:1967:    simp [Rf, R, S, scalarGradNormSqAt, mul_comm, mul_left_comm]
Poincare/Global/ScalarEvolution.lean:1989:    simp [S, Rf, scalarGradNormSqAt, smul_eq_mul]
Poincare/Global/ScalarEvolution.lean:2212:        + (2 / 3 : ℝ) * g.scalarGradNormSqAt x
Poincare/Global/ScalarEvolution.lean:2234:      + (2 / 3 : ℝ) * g.scalarGradNormSqAt x
Poincare/Global/ScalarEvolution.lean:2243:  let S : ℝ := g.scalarGradNormSqAt x
Poincare/Global/ScalarEvolution.lean:2279:      ClosedSmoothRiemannianMetric.scalarGradNormSqAt] using
Poincare/Global/ScalarEvolution.lean:2676:  let S : ℝ := g.scalarGradNormSqAt x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:217:        - 2 * (gt t₀).scalarGradNormSqAt x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:239:          - 2 * (gt t₀).scalarGradNormSqAt x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:253:    simp [ClosedSmoothRiemannianMetric.scalarGradNormSqAt]
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:263:    + (2 / 3 : ℝ) * g.scalarGradNormSqAt x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:389:  let S : ℝ := g.scalarGradNormSqAt x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:443:      ClosedSmoothRiemannianMetric.scalarGradNormSqAt] using
Poincare/Global/Laplacian.lean:198:noncomputable def scalarGradNormSqAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:63:  covRicciNormSqAt g x - g.scalarGradNormSqAt x / (n : ℝ)
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:607:      g.scalarGradNormSqAt x = ∑ a, (S a) ^ 2 / diag a := by
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:761:  have hGradNonneg : 0 ≤ (g i).scalarGradNormSqAt x := by
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:762:    unfold ClosedSmoothRiemannianMetric.scalarGradNormSqAt
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:795:  have hGradNormSq : g.scalarGradNormSqAt x = ‖gradR‖ ^ 2 := by
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:796:    unfold ClosedSmoothRiemannianMetric.scalarGradNormSqAt
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:799:  have hGradSq : g.scalarGradNormSqAt x ≤ 3 * D ^ 2 :=
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:227:  let S : ℝ := g.scalarGradNormSqAt x
exit=0
$ rg -n hessianAt Poincare
Poincare/Global/ScalarEvolution.lean:500:    g.hessianAt (fun y : M ↦ f y ^ p) x v w =
Poincare/Global/ScalarEvolution.lean:501:      (p * f x ^ (p - 1)) * g.hessianAt f x v w
Poincare/Global/ScalarEvolution.lean:528:  unfold hessianAt
Poincare/Global/ScalarEvolution.lean:592:  change (∑ i, g.hessianAt (fun y : M ↦ f y ^ p) x (b i) (sharp i)) =
Poincare/Global/ScalarEvolution.lean:593:    (p * f x ^ (p - 1)) * (∑ i, g.hessianAt f x (b i) (sharp i)) +
Poincare/Global/ScalarEvolution.lean:3937:        g.hessianAt f x v v =
Poincare/Global/ScalarEvolution.lean:3940:          g.hessianAt f x v v +
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:24:      (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:41:        g.hessianAt f ((extChartAt I p).symm z)
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:131:    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:200:  rw [ClosedSmoothRiemannianMetric.hessianAt]
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:222:    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:316:    g.hessianAt f ((extChartAt I₃ p).symm z)
Poincare/Global/Laplacian.lean:399:noncomputable def hessianAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:412:    g.hessianAt f x v w = g.hessianAt h x v w := by
Poincare/Global/Laplacian.lean:421:  unfold hessianAt
Poincare/Global/Laplacian.lean:428:    { toFun := fun w ↦ g.hessianAt f x v w
Poincare/Global/Laplacian.lean:431:        simp [hessianAt]
Poincare/Global/Laplacian.lean:434:        simp [hessianAt, smul_eq_mul] }
Poincare/Global/Laplacian.lean:438:    simp [hessianAt]
Poincare/Global/Laplacian.lean:442:    simp [hessianAt, smul_eq_mul]
Poincare/Global/Laplacian.lean:447:    g.hessianDualAt f x v w = g.hessianAt f x v w :=
Poincare/Global/Laplacian.lean:463:    g.hessianContinuousAt f x v w = g.hessianAt f x v w := by
Poincare/Global/Laplacian.lean:548:    g.hessianAt (f + h) x v w =
Poincare/Global/Laplacian.lean:549:      g.hessianAt f x v w + g.hessianAt h x v w := by
Poincare/Global/Laplacian.lean:552:  unfold hessianAt
Poincare/Global/Laplacian.lean:568:    g.hessianAt (c • f) x v w = c * g.hessianAt f x v w := by
Poincare/Global/Laplacian.lean:571:  unfold hessianAt
Poincare/Global/Laplacian.lean:582:    g.hessianAt (f * h) x v w =
Poincare/Global/Laplacian.lean:583:      f x * g.hessianAt h x v w + h x * g.hessianAt f x v w
Poincare/Global/Laplacian.lean:594:  unfold hessianAt
Poincare/Global/Laplacian.lean:619:    g.hessianAt (fun _ : M ↦ c) x v w = 0 := by
Poincare/Global/Laplacian.lean:621:  unfold hessianAt
Poincare/Global/Laplacian.lean:634:    g.hessianAt f x v w = g.hessianAt f x w v := by
Poincare/Global/Laplacian.lean:664:        g.hessianAt f x v w + extDerivFun f x (g.leviCivita Y x v) := by
Poincare/Global/Laplacian.lean:667:    simpa [hessianAt] using h
Poincare/Global/Laplacian.lean:670:        g.hessianAt f x w v + extDerivFun f x (g.leviCivita X x w) := by
Poincare/Global/Laplacian.lean:673:    simpa [hessianAt] using h
Poincare/Global/Laplacian.lean:699:    g.hessianAt f x v w = g.hessianAt f x w v :=
Poincare/Global/ScalarVariation.lean:2112:        ∑ i, g.hessianAt f x ((Module.finBasis ℝ (TM x)) i)
Poincare/Global/ScalarVariation.lean:2120:    ∑ i, g.hessianAt f x (b i) (metricDualVectorAt g x (b.coord i))
Poincare/Global/ScalarVariation.lean:2131:      ∑ i, g.hessianAt f x (b i)
Poincare/Global/ScalarVariation.lean:2137:    ∑ i, g.hessianAt f x (b i) (metricDualVectorAt g x (b.coord i))
Poincare/Global/ScalarVariation.lean:5502:        (1 / 2 : ℝ) * g.hessianAt f x u w
Poincare/Global/ScalarVariation.lean:11246:      - (1 / 2 : ℝ) * g.hessianAt f x w u
Poincare/Global/ScalarVariation.lean:16423:      g.hessianAt f x u w +
Poincare/Global/ScalarVariation.lean:16442:  simpa [ClosedSmoothRiemannianMetric.hessianAt, Y] using h
Poincare/Global/ScalarVariation.lean:16459:    g.hessianAt (fun y : M ↦ g.ricciNormSqAt y) x u w =
Poincare/Global/ScalarVariation.lean:16559:      g.hessianAt f x u w) := by
Poincare/Global/ScalarVariation.lean:16683:        g.hessianAt f x u w + extDerivFun f x Γw := by
Poincare/Global/ScalarVariation.lean:16691:        g.hessianAt f x u w + extDerivFun f x Γw := by
Poincare/Global/ScalarVariation.lean:16726:      g.hessianAt f x u w) := by
Poincare/Global/ScalarVariation.lean:16860:        g.hessianAt f x u w + extDerivFun f x Γw := by
Poincare/Global/ScalarVariation.lean:16868:        g.hessianAt f x u w + extDerivFun f x Γw := by
Poincare/Global/ScalarVariation.lean:16900:      ∑ j, g.hessianAt f x (b j) (sharp j)) := by
Poincare/Global/ScalarVariation.lean:16913:      ∑ j, g.hessianAt f x (b j) (sharp j)
Poincare/Global/ScalarVariation.lean:18904:        g.hessianAt f x u w +
Poincare/Global/ScalarVariation.lean:18917:        (1 / 2 : ℝ) * g.hessianAt f x u w
Poincare/Global/ScalarVariation.lean:19339:        (1 / 2 : ℝ) * g.hessianAt f x (sharp j) (b j) := by
Poincare/Global/ScalarVariation.lean:19370:          g.hessianAt f x (sharp j) (b j) +
Poincare/Global/ScalarVariation.lean:19394:        = ∑ j, (1 / 2 : ℝ) * g.hessianAt f x (sharp j) (b j) := by
Poincare/Global/ScalarVariation.lean:19396:    _ = (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (sharp j) (b j) := by
Poincare/Global/ScalarVariation.lean:19398:    _ = (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (b j) (sharp j) := by
Poincare/Global/ScalarVariation.lean:19567:          g.hessianAt (fun y : M ↦ g.scalarAt y) x u w := by
Poincare/Global/ScalarVariation.lean:19600:        g.hessianAt f x u w + extDerivFun f x Γw := by
Poincare/Global/ScalarVariation.lean:19629:          g.hessianAt (fun y : M ↦ g.scalarAt y) x u w :=
Poincare/Global/ScalarVariation.lean:19657:          g.hessianAt (fun y : M ↦ g.scalarAt y) x u w := by
Poincare/Global/ScalarVariation.lean:19679:      g.hessianAt (fun y : M ↦ g.scalarAt y) x u w := by
Poincare/Global/ScalarVariation.lean:19703:        g.hessianAt f x u w := by
Poincare/Global/ScalarVariation.lean:19721:      g.hessianAt f x u w =
Poincare/Global/ScalarVariation.lean:19722:        g.hessianAt (fun y : M ↦ g.scalarAt y) x u w :=
Poincare/Global/ScalarVariation.lean:23641:  let Hu : ℝ := g.hessianAt (fun y : M ↦ g.scalarAt y) x u w
Poincare/Global/ScalarVariation.lean:23642:  let Hw : ℝ := g.hessianAt (fun y : M ↦ g.scalarAt y) x w u
Poincare/Global/ScalarVariation.lean:24189:        g.hessianAt f x (b i) (sharp i) := by
Poincare/Global/ScalarVariation.lean:24207:        ∑ i, g.hessianAt f x (b i) (sharp i) := by
Poincare/Global/ScalarVariation.lean:24212:        ∑ i, g.hessianAt f x (b i) (sharp i)
Poincare/Global/ScalarVariation.lean:24217:        ∑ i, g.hessianAt f x (b i) (sharp i) := by
Poincare/Global/ScalarVariation.lean:25541:          ∑ j, (gt t₀).hessianAt
Poincare/Global/ScalarVariation.lean:25563:        ∑ j, (gt t₀).hessianAt
Poincare/Global/ScalarVariation.lean:25581:      (1 / 2 : ℝ) * (gt t₀).hessianAt
Poincare/Global/ScalarVariation.lean:25616:        ∑ j, (gt t₀).hessianAt
Poincare/Global/ScalarVariation.lean:25645:        (1 / 2 : ℝ) * g.hessianAt f x u w := by
Poincare/Global/ScalarVariation.lean:25893:    g.hessianAt f x (b j) (sharp j)
Poincare/Global/ScalarVariation.lean:25921:      g.hessianAt
Poincare/Global/ScalarVariation.lean:26223:        ∑ j, g.hessianAt f x (b j) (sharp j))) :
Poincare/Global/ScalarVariation.lean:26239:        ∑ j, g.hessianAt f x (b j) (sharp j) := by
Poincare/Global/ScalarVariation.lean:26243:      - (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (b j) (sharp j)
Poincare/Global/ScalarVariation.lean:26371:            (∑ j, g.hessianAt f x (b j) (sharp j)) := by
Poincare/Global/ScalarVariation.lean:26376:      - (1 / 2 : ℝ) * (∑ j, g.hessianAt f x (b j) (sharp j))
Poincare/Global/ScalarVariation.lean:26393:    (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (b j) (sharp j)
Poincare/Global/ScalarVariation.lean:26413:        ∑ j, g.hessianAt f x (b j) (sharp j) := by
Poincare/Global/ScalarVariation.lean:26420:            (∑ j, g.hessianAt f x (b j) (sharp j)) := by
Poincare/Global/ScalarVariation.lean:26440:        ∑ j, g.hessianAt f x (b j) (sharp j) := by
Poincare/Global/ScalarVariation.lean:26446:          (∑ j, g.hessianAt f x (b j) (sharp j)) := by
exit=0
$ rg -n laplacianAt Poincare
Poincare/Global/NormalizedFlowEnergyCriticality.lean:75:        (fun x : M ↦ g.laplacianAt (fun _ : M ↦ meanScalar g) x) =
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:44:      (gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:47:        (gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:71:        ((gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:84:        (gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:115:        ((gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:125:        (gt t).laplacianAt
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:46:    ((gt t).laplacianAt (fun y ↦ (gt t).scalarAt y) x +
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:119:    (gt (t0 + tau)).laplacianAt (R tau) x +
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:134:    (lap := fun tau f x ↦ (gt (t0 + tau)).laplacianAt f x)
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:158:          (gt (t0 + tau)).laplacianAt
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:160:            (gt (t0 + tau)).laplacianAt (R tau) x := by
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:172:        (gt (t0 + tau)).laplacianAt
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:77:      (gt t).laplacianAt (fun y ↦ (gt t).scalarAt y) x +
Poincare/Global/HamiltonScalarNegativeBarrier.lean:58:    (gt (t₀ + τ)).laplacianAt (R τ) x +
Poincare/Global/HamiltonScalarNegativeBarrier.lean:72:      (gt (t₀ + τ)).laplacianAt (R τ) x + a * (R τ x) ^ 2 ≤
Poincare/Global/HamiltonScalarNegativeBarrier.lean:146:    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
Poincare/Global/HamiltonScalarNegativeBarrier.lean:182:      change (gt (t₀ + τ)).laplacianAt
Poincare/Global/HamiltonScalarNegativeBarrier.lean:184:        (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x
Poincare/Global/HamiltonScalarNegativeBarrier.lean:200:          (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x =
Poincare/Global/HamiltonScalarNegativeBarrier.lean:201:            (gt (t₀ + τ)).laplacianAt (R τ) x := by
Poincare/Global/HamiltonScalarNegativeBarrier.lean:211:      change (gt (t₀ + τ)).laplacianAt
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:439:    g.laplacianAt
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:447:        g.laplacianAt (fun y : M ↦ partition i y * f y) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:487:    g.laplacianAt (A.localizedScalar i) x = 0 := by
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:492:    g.laplacianAt (A.localizedScalar i) x =
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:493:        g.laplacianAt (fun _ : M ↦ (0 : ℝ)) x :=
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:549:        g.laplacianAt (A.localizedScalar i) (A.inverseChart i z) =
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:563:        g.laplacianAt (A.localizedScalar i) (A.inverseChart i z) =
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:591:          g.laplacianAt (A.localizedScalar i) (A.inverseChart i z))
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:620:        g.laplacianAt (A.localizedScalar i) (A.inverseChart i z))
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:651:    IntegrableOn (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:656:      (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:662:      (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:677:    Integrable (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:693:    (∫ x : M, g.laplacianAt (A.localizedScalar i) x
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:696:          g.laplacianAt (A.localizedScalar i) x
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:703:            g.laplacianAt (A.localizedScalar i) (A.inverseChart i z)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:708:            (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:739:    g.laplacianAt (∑ i ∈ s, F i) x =
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:740:      ∑ i ∈ s, g.laplacianAt (F i) x := by
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:785:    g.laplacianAt f x =
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:787:        g.laplacianAt (A.localizedScalar i) x := by
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:789:    g.laplacianAt f x =
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:790:        g.laplacianAt
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:792:      congrArg (fun q : M → ℝ ↦ g.laplacianAt q x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:795:          g.laplacianAt (A.localizedScalar i) x :=
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:807:      Integrable (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:812:        g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:815:  have hLapInt : Integrable (fun x : M ↦ g.laplacianAt f x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:822:    (∫ x : M, g.laplacianAt f x ∂(volumeMeasure g)) =
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:824:          g.laplacianAt (A.localizedScalar i) x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:829:          ∫ x : M, g.laplacianAt (A.localizedScalar i) x
Poincare/Global/ScalarEvolution.lean:16:`scalarAt`, `laplacianAt`, `ricciNormSqAt`, and
Poincare/Global/ScalarEvolution.lean:64:    ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
Poincare/Global/ScalarEvolution.lean:74:        ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
Poincare/Global/ScalarEvolution.lean:91:      ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
Poincare/Global/ScalarEvolution.lean:100:        (((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/ScalarEvolution.lean:103:            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/ScalarEvolution.lean:107:      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
Poincare/Global/ScalarEvolution.lean:110:        (((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/ScalarEvolution.lean:113:            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/ScalarEvolution.lean:375:    g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / R ^ 2
Poincare/Global/ScalarEvolution.lean:376:      - 2 * N * g.laplacianAt (fun y : M ↦ g.scalarAt y) x / R ^ 3
Poincare/Global/ScalarEvolution.lean:378:    g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:575:    g.laplacianAt (fun y : M ↦ f y ^ p) x =
Poincare/Global/ScalarEvolution.lean:576:      (p * f x ^ (p - 1)) * g.laplacianAt f x
Poincare/Global/ScalarEvolution.lean:628:    g.laplacianAt (fun y : M ↦ (g.scalarAt y) ^ p) x =
Poincare/Global/ScalarEvolution.lean:630:        g.laplacianAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/ScalarEvolution.lean:1455:    g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x =
Poincare/Global/ScalarEvolution.lean:1456:      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:1458:            g.laplacianAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/ScalarEvolution.lean:1488:      g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x =
Poincare/Global/ScalarEvolution.lean:1489:        g.laplacianAt Nf x + g.laplacianAt ((-((1 : ℝ) / (n : ℝ))) • Sqf) x := by
Poincare/Global/ScalarEvolution.lean:1498:      g.laplacianAt ((-((1 : ℝ) / (n : ℝ))) • Sqf) x =
Poincare/Global/ScalarEvolution.lean:1499:        -((1 : ℝ) / (n : ℝ)) * g.laplacianAt Sqf x := by
Poincare/Global/ScalarEvolution.lean:1504:      g.laplacianAt Sqf x =
Poincare/Global/ScalarEvolution.lean:1505:        2 * Rf x * g.laplacianAt Rf x + 2 * g.scalarGradNormSqAt x := by
Poincare/Global/ScalarEvolution.lean:1552:    g.laplacianAt q x =
Poincare/Global/ScalarEvolution.lean:1553:      (g.laplacianAt u x - q x * g.laplacianAt v x
Poincare/Global/ScalarEvolution.lean:1558:      g.laplacianAt (q * v) x = g.laplacianAt u x :=
Poincare/Global/ScalarEvolution.lean:1561:      g.laplacianAt u x =
Poincare/Global/ScalarEvolution.lean:1562:        q x * g.laplacianAt v x + v x * g.laplacianAt q x
Poincare/Global/ScalarEvolution.lean:1614:    g.laplacianAt q x
Poincare/Global/ScalarEvolution.lean:1616:      g.laplacianAt u x / (Rf x) ^ p
Poincare/Global/ScalarEvolution.lean:1617:        - p * q x * g.laplacianAt Rf x / Rf x
Poincare/Global/ScalarEvolution.lean:1627:  let LU : ℝ := g.laplacianAt u x
Poincare/Global/ScalarEvolution.lean:1628:  let LR : ℝ := g.laplacianAt Rf x
Poincare/Global/ScalarEvolution.lean:1632:  let LQ : ℝ := g.laplacianAt q x
Poincare/Global/ScalarEvolution.lean:1659:      g.laplacianAt Vf x =
Poincare/Global/ScalarEvolution.lean:1667:        (LU - Q * g.laplacianAt Vf x
Poincare/Global/ScalarEvolution.lean:1742:    g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/ScalarEvolution.lean:1744:      g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x /
Poincare/Global/ScalarEvolution.lean:1747:            g.laplacianAt (fun y : M ↦ g.scalarAt y) x / g.scalarAt x
Poincare/Global/ScalarEvolution.lean:1806:      g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/ScalarEvolution.lean:1808:        g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x /
Poincare/Global/ScalarEvolution.lean:1811:              g.laplacianAt (fun y : M ↦ g.scalarAt y) x / g.scalarAt x
Poincare/Global/ScalarEvolution.lean:1819:    g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/ScalarEvolution.lean:1821:      g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x /
Poincare/Global/ScalarEvolution.lean:1824:            g.laplacianAt (fun y : M ↦ g.scalarAt y) x / g.scalarAt x
Poincare/Global/ScalarEvolution.lean:1888:    g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:1890:      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / (g.scalarAt x) ^ 2
Poincare/Global/ScalarEvolution.lean:1892:            g.laplacianAt (fun y : M ↦ g.scalarAt y) x / (g.scalarAt x) ^ 3
Poincare/Global/ScalarEvolution.lean:1935:      g.laplacianAt Qf x =
Poincare/Global/ScalarEvolution.lean:1936:        (g.laplacianAt Nf x - Qf x * g.laplacianAt Vf x
Poincare/Global/ScalarEvolution.lean:1958:      g.laplacianAt Vf x =
Poincare/Global/ScalarEvolution.lean:1959:        2 * R * g.laplacianAt Rf x + 2 * S := by
Poincare/Global/ScalarEvolution.lean:1964:    change g.laplacianAt (Rf * Rf) x =
Poincare/Global/ScalarEvolution.lean:1965:      2 * R * g.laplacianAt Rf x + 2 * S
Poincare/Global/ScalarEvolution.lean:2016:    g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:2018:        (g.laplacianAt Nf x - Qf x * g.laplacianAt Vf x
Poincare/Global/ScalarEvolution.lean:2023:      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / (g.scalarAt x) ^ 2
Poincare/Global/ScalarEvolution.lean:2025:            g.laplacianAt (fun y : M ↦ g.scalarAt y) x / (g.scalarAt x) ^ 3
Poincare/Global/ScalarEvolution.lean:2054:      g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:2056:        g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / (g.scalarAt x) ^ 2
Poincare/Global/ScalarEvolution.lean:2058:              g.laplacianAt (fun y : M ↦ g.scalarAt y) x / (g.scalarAt x) ^ 3
Poincare/Global/ScalarEvolution.lean:2074:    (lapN := g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x)
Poincare/Global/ScalarEvolution.lean:2075:    (lapR := g.laplacianAt (fun y : M ↦ g.scalarAt y) x)
Poincare/Global/ScalarEvolution.lean:2077:    (lapQ := g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x)
Poincare/Global/ScalarEvolution.lean:2122:      (g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2142:    (g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2152:      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x =
Poincare/Global/ScalarEvolution.lean:2210:      (g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2232:    (g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2238:  let lapN : ℝ := g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2239:  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/ScalarEvolution.lean:2240:  let lapR2 : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y ^ 2) x
Poincare/Global/ScalarEvolution.lean:2241:  let lapU : ℝ := g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2358:  let lapN : ℝ := g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2359:  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/ScalarEvolution.lean:2389:        g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:2418:        g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:2428:      _ = (g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:2433:      _ = g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:2465:      (gt t₀).laplacianAt (fun y : M ↦ (gt t₀).pinchingQuotientAt y) x
Poincare/Global/ScalarEvolution.lean:2467:        (gt t₀).laplacianAt (fun y : M ↦ (gt t₀).ricciNormSqAt y) x /
Poincare/Global/ScalarEvolution.lean:2470:              (gt t₀).laplacianAt (fun y : M ↦ (gt t₀).scalarAt y) x /
Poincare/Global/ScalarEvolution.lean:2672:  let lapU : ℝ := g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
Poincare/Global/ScalarEvolution.lean:2673:  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/ScalarEvolution.lean:2710:      g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/ScalarEvolution.lean:2776:        = (g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/ScalarEvolution.lean:2782:    _ ≤ (g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/ScalarEvolution.lean:2787:        g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/ScalarEvolution.lean:2829:    g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 := by
Poincare/Global/ScalarEvolution.lean:2865:  have hlap : g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 :=
Poincare/Global/ScalarEvolution.lean:2869:  have hrhs : g.laplacianAt (fun y ↦ g.scalarAt y) x + 2 * g.ricciNormSqAt x = 0 := by
Poincare/Global/ScalarEvolution.lean:3017:        -(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x :=
Poincare/Global/ScalarEvolution.lean:3022:        -(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x := by
Poincare/Global/ScalarEvolution.lean:3026:          - (gt t₀).laplacianAt
Poincare/Global/ScalarEvolution.lean:3029:        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
Poincare/Global/ScalarEvolution.lean:3842:        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/ScalarEvolution.lean:3844:  refine ⟨(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/ScalarEvolution.lean:3864:      0 ≤ (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x) :
Poincare/Global/ScalarEvolution.lean:3889:    0 ≤ g.laplacianAt f x := by
Poincare/Global/ScalarEvolution.lean:4014:    g.laplacianAt f x ≤ 0 := by
Poincare/Global/ScalarEvolution.lean:4020:      0 ≤ g.laplacianAt nf x :=
Poincare/Global/ScalarEvolution.lean:4028:      g.laplacianAt nf x = -g.laplacianAt f x := by
Poincare/Global/ScalarEvolution.lean:4277:      g.laplacianAt Qf x ≤ 0 := by
Poincare/Global/ScalarEvolution.lean:4306:      g.laplacianAt Qf x + g.pinchingQuotientGradientDrift3At x
Poincare/Global/ScalarEvolution.lean:4516:    (gt (t₀ + τ)).laplacianAt (R τ) x +
Poincare/Global/ScalarEvolution.lean:4531:      (gt (t₀ + τ)).laplacianAt (R τ) x + a * (R τ x) ^ 2 ≤ R' τ x := by
Poincare/Global/ScalarEvolution.lean:4607:    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
Poincare/Global/ScalarEvolution.lean:4642:      change (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ + k) x =
Poincare/Global/ScalarEvolution.lean:4643:        (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x
Poincare/Global/ScalarEvolution.lean:4661:      have hlap : (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x =
Poincare/Global/ScalarEvolution.lean:4662:          (gt (t₀ + τ)).laplacianAt (R τ) x := by
Poincare/Global/ScalarEvolution.lean:4672:      change (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x
Poincare/Global/ScalarEvolution.lean:4725:    (gt (t₀ + τ)).laplacianAt (R τ) x +
Poincare/Global/ScalarEvolution.lean:4737:      (gt (t₀ + τ)).laplacianAt (R τ) x ≤ R' τ x := by
Poincare/Global/ScalarEvolution.lean:4759:    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
Poincare/Global/ScalarEvolution.lean:4772:      change (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y + k) x =
Poincare/Global/ScalarEvolution.lean:4773:        (gt (t₀ + τ)).laplacianAt (R τ) x
Poincare/Global/ScalarEvolution.lean:4832:    g.laplacianAt f x +
Poincare/Global/ScalarEvolution.lean:4879:        g.laplacianAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/ScalarEvolution.lean:4880:          g.laplacianAt (u τ) x := by
Poincare/Global/ScalarEvolution.lean:4881:      change g.laplacianAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/ScalarEvolution.lean:4882:        g.laplacianAt (u τ) x
Poincare/Global/ScalarEvolution.lean:4896:      g.laplacianAt (fun y : M ↦ u τ y + k) x +
Poincare/Global/ScalarEvolution.lean:4901:        g.laplacianAt (u τ) x +
Poincare/Global/ScalarEvolution.lean:4922:          g.laplacianAt (Q τ) x
Poincare/Global/ScalarEvolution.lean:4946:        Q' τ x ≤ g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x := by
Poincare/Global/ScalarEvolution.lean:4953:        g.laplacianAt (u τ) x = -g.laplacianAt (Q τ) x := by
Poincare/Global/ScalarEvolution.lean:4987:          -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x) := by
Poincare/Global/ScalarEvolution.lean:4989:        g.laplacianAt (u τ) x +
Poincare/Global/ScalarEvolution.lean:4994:          -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x)
Poincare/Global/ScalarEvolution.lean:5008:        0 ≤ g.laplacianAt (u τ) x :=
Poincare/Global/ScalarEvolution.lean:5017:      0 ≤ g.laplacianAt (u τ) x +
Poincare/Global/ScalarEvolution.lean:5163:    g.laplacianAt f x +
Poincare/Global/ScalarEvolution.lean:5211:        g.laplacianAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/ScalarEvolution.lean:5212:          g.laplacianAt (u τ) x := by
Poincare/Global/ScalarEvolution.lean:5213:      change g.laplacianAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/ScalarEvolution.lean:5214:        g.laplacianAt (u τ) x
Poincare/Global/ScalarEvolution.lean:5228:      g.laplacianAt (fun y : M ↦ u τ y + k) x +
Poincare/Global/ScalarEvolution.lean:5233:        g.laplacianAt (u τ) x +
Poincare/Global/ScalarEvolution.lean:5252:          g.laplacianAt (Q τ) x
Poincare/Global/ScalarEvolution.lean:5265:        Q' τ x ≤ g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ := by
Poincare/Global/ScalarEvolution.lean:5272:        g.laplacianAt (u τ) x = -g.laplacianAt (Q τ) x := by
Poincare/Global/ScalarEvolution.lean:5306:          -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ) := by
Poincare/Global/ScalarEvolution.lean:5308:        g.laplacianAt (u τ) x +
Poincare/Global/ScalarEvolution.lean:5313:          -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ)
Poincare/Global/ScalarEvolution.lean:5327:        0 ≤ g.laplacianAt (u τ) x :=
Poincare/Global/ScalarEvolution.lean:5336:      0 ≤ g.laplacianAt (u τ) x +
Poincare/Global/ScalarEvolution.lean:5383:      0 ≤ (gt (t₀ + τ)).laplacianAt
Poincare/Global/ScalarEvolution.lean:5389:    (gt (t₀ + τ)).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary.lean:158:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary.lean:259:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary.lean:347:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary.lean:460:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundary.lean:171:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundary.lean:272:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundary.lean:362:            (reactionData.metric p.1).laplacianAt
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:23:    g.laplacianAt f x = ∑ i, ∑ j,
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:39:    g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:54:  change g.laplacianAt f ((extChartAt I p).symm z) = _
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:380:    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:498:      w z * g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) = D z) :
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:499:    Continuous (fun x ↦ g.laplacianAt f x) := by
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:501:      g.laplacianAt f x = D (extChartAt I p x) / w (extChartAt I p x) := by
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:522:      g.laplacianAt f y = g.laplacianAt (fun _ : M ↦ (0 : ℝ)) y :=
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:551:      g.laplacianAt (fun x ↦ ρ i x * f x)
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:594:  have hcontinuous (i) : Continuous (fun x ↦ g.laplacianAt (fun y ↦ ρ i y * f y) x) := by
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:698:    change g.laplacianAt (fun x ↦ ρ i x * f x)
Poincare/Global/HausdorffScalarDensityDomination.lean:162:      (gt t).laplacianAt (fun y ↦ (gt t).scalarAt y) x +
Poincare/Global/DeTurckBUCQuasilinearDifferenceEnergy.lean:381:    2 * f x * g.laplacianAt f x ≤
Poincare/Global/DeTurckBUCQuasilinearDifferenceEnergy.lean:382:      g.laplacianAt (fun y ↦ f y ^ 2) x := by
Poincare/Global/DeTurckBUCQuasilinearDifferenceEnergy.lean:399:        g.laplacianAt
Poincare/Global/DeTurckBUCQuasilinearDifferenceEnergy.lean:401:      g.laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:216:      ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:227:        ((((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:232:            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:238:      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:243:        (((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:248:            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:318:      ((gt t₀).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:330:    (g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:383:  let lapN : ℝ := g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:384:  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:385:  let lapR2 : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y ^ 2) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:387:    g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:472:      ((gt t₀).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:496:      ((gt t₀).laplacianAt
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:232:    (gt (t₀ + τ)).laplacianAt (R τ) x +
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:245:      (gt (t₀ + τ)).laplacianAt (R τ) x + a * (R τ x) ^ 2 ≤
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:318:    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:356:      change (gt (t₀ + τ)).laplacianAt
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:358:        (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:375:          (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x =
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:376:            (gt (t₀ + τ)).laplacianAt (R τ) x := by
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:386:      change (gt (t₀ + τ)).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary.lean:123:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary.lean:222:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary.lean:308:            (reactionData.metric p.1).laplacianAt
Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary.lean:433:            (reactionData.metric p.1).laplacianAt
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:9:integral of this intrinsic `laplacianAt` with zero.  The available Euclidean
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:47:  Integrable (fun x : M ↦ g.laplacianAt f x) (volumeMeasure g) ∧
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:48:    (∫ x, g.laplacianAt f x ∂(volumeMeasure g)) = 0
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:66:      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x := by
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:110:  change g.laplacianAt
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:112:    -2 * g.laplacianAt R x
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:377:      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x := by
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:429:      fun x ↦ (gt t₀).laplacianAt
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:541:      fun x ↦ (gt t₀).laplacianAt
Poincare/Global/Laplacian.lean:482:noncomputable def laplacianAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:497:    g.laplacianAt f x =
Poincare/Global/Laplacian.lean:507:  unfold laplacianAt hessianContinuousAt
Poincare/Global/Laplacian.lean:518:    g.laplacianAt f x = g.laplacianAt h x := by
Poincare/Global/Laplacian.lean:519:  unfold laplacianAt
Poincare/Global/Laplacian.lean:739:    g.laplacianAt (f + h) x = g.laplacianAt f x + g.laplacianAt h x := by
Poincare/Global/Laplacian.lean:740:  unfold laplacianAt
Poincare/Global/Laplacian.lean:752:    g.laplacianAt (f + h) x = g.laplacianAt f x + g.laplacianAt h x :=
Poincare/Global/Laplacian.lean:769:    g.laplacianAt (c • f) x = c * g.laplacianAt f x := by
Poincare/Global/Laplacian.lean:770:  unfold laplacianAt
Poincare/Global/Laplacian.lean:781:    g.laplacianAt (c • f) x = c * g.laplacianAt f x :=
Poincare/Global/Laplacian.lean:792:    g.laplacianAt (f * h) x =
Poincare/Global/Laplacian.lean:793:      f x * g.laplacianAt h x + h x * g.laplacianAt f x
Poincare/Global/Laplacian.lean:855:    g.laplacianAt (f * h) x =
Poincare/Global/Laplacian.lean:856:      f x * g.laplacianAt h x + h x * g.laplacianAt f x
Poincare/Global/Laplacian.lean:867:    g.laplacianAt (fun y ↦ f y ^ 2) x =
Poincare/Global/Laplacian.lean:868:      2 * f x * g.laplacianAt f x +
Poincare/Global/Laplacian.lean:878:    g.laplacianAt (fun _ : M ↦ c) x = 0 := by
Poincare/Global/Laplacian.lean:879:  unfold laplacianAt
Poincare/Global/ClosedLaplacianStokesProducer.lean:136:      w z * g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) = D z) :
Poincare/Global/ClosedLaplacianStokesProducer.lean:137:    Continuous (fun x ↦ g.laplacianAt f x) := by
Poincare/Global/ClosedLaplacianStokesProducer.lean:139:      g.laplacianAt f x = D (extChartAt I p x) / w (extChartAt I p x) := by
Poincare/Global/ClosedLaplacianStokesProducer.lean:159:      g.laplacianAt f y = g.laplacianAt (fun _ : M ↦ (0 : ℝ)) y :=
Poincare/Global/ClosedLaplacianStokesProducer.lean:181:      g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
Poincare/Global/ClosedLaplacianStokesProducer.lean:183:    Continuous (fun x ↦ g.laplacianAt f x) := by
Poincare/Global/ClosedLaplacianStokesProducer.lean:234:      g.laplacianAt (fun x ↦ ρ i x * f x)
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:44:    R' = (gt t).laplacianAt (fun y : M => (gt t).scalarAt y) x +
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:48:        ((gt t).laplacianAt (fun y : M => (gt t).scalarAt y) x +
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:506:        (g k t).laplacianAt (fun y : M => (g k t).scalarAt y) (xmin k t) +
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:525:        0 ≤ (g k t).laplacianAt
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:137:    AEStronglyMeasurable (fun x : M ↦ (gt t).laplacianAt f x)
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:149:          (gt t).laplacianAt f (D.inverseChart i z) =
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:163:          (gt t).laplacianAt f (D.inverseChart i z))
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:193:        (gt t).laplacianAt f (D.inverseChart i z))
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:227:    Integrable (fun x : M ↦ (gt t).laplacianAt f x)
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:235:      (fun x : M ↦ (gt t).laplacianAt f x)
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:240:  have hMap : Integrable (fun x : M ↦ (gt t).laplacianAt f x)
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:266:          (gt t).laplacianAt f (D.inverseChart i z)
Poincare/Global/DeTurckBUCOverlapParabolicUniqueness.lean:1069:  lap := fun t f x ↦ (gt t).laplacianAt f x
Poincare/Global/DeTurckBUCOverlapParabolicUniqueness.lean:1079:    change (gt t).laplacianAt (fun y : M ↦ -energy y) x =
Poincare/Global/DeTurckBUCOverlapParabolicUniqueness.lean:1080:      -(gt t).laplacianAt energy x
Poincare/Global/DeTurckBUCOverlapParabolicUniqueness.lean:1097:    change (gt t).laplacianAt (fun y : M ↦ negEnergy y + k) x =
Poincare/Global/DeTurckBUCOverlapParabolicUniqueness.lean:1098:      (gt t).laplacianAt negEnergy x
Poincare/Global/ScalarVariation.lean:597:          (gt t₀).laplacianAt (fun y ↦ (gt t₀).pinchingQuotientAt y) x
Poincare/Global/ScalarVariation.lean:2110:    g.laplacianAt f x =
Poincare/Global/ScalarVariation.lean:2119:  change g.laplacianAt f x =
Poincare/Global/ScalarVariation.lean:2121:  simpa [ClosedSmoothRiemannianMetric.laplacianAt, metricTraceEndomorphismAt,
Poincare/Global/ScalarVariation.lean:2130:    g.laplacianAt f x =
Poincare/Global/ScalarVariation.lean:2136:  change g.laplacianAt f x =
Poincare/Global/ScalarVariation.lean:2138:  simpa [ClosedSmoothRiemannianMetric.laplacianAt, metricTraceEndomorphismAt,
Poincare/Global/ScalarVariation.lean:16509:    g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x =
Poincare/Global/ScalarVariation.lean:19239:    (1 / 2 : ℝ) * g.laplacianAt (fun y ↦ g.scalarAt y) x
Poincare/Global/ScalarVariation.lean:19331:      (1 / 2 : ℝ) * g.laplacianAt f x
Poincare/Global/ScalarVariation.lean:19402:    _ = (1 / 2 : ℝ) * g.laplacianAt f x := by
Poincare/Global/ScalarVariation.lean:19801:      -g.laplacianAt (fun y ↦ g.scalarAt y) x := by
Poincare/Global/ScalarVariation.lean:19867:  (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:19869:    -2 * (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
Poincare/Global/ScalarVariation.lean:19903:      g.laplacianAt fTrace x = g.laplacianAt fNegScalar x :=
Poincare/Global/ScalarVariation.lean:19906:      g.laplacianAt fNegScalar x =
Poincare/Global/ScalarVariation.lean:19907:        -2 * g.laplacianAt fScalar x := by
Poincare/Global/ScalarVariation.lean:19912:  change g.laplacianAt fTrace x =
Poincare/Global/ScalarVariation.lean:19913:    -2 * g.laplacianAt fScalar x
Poincare/Global/ScalarVariation.lean:20697:    g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x =
Poincare/Global/ScalarVariation.lean:20705:      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x =
Poincare/Global/ScalarVariation.lean:20741:    g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x =
Poincare/Global/ScalarVariation.lean:23873:    = g.laplacianAt (fun y ↦ g.scalarAt y) x
Poincare/Global/ScalarVariation.lean:24216:      g.laplacianAt f x =
Poincare/Global/ScalarVariation.lean:24226:      g.laplacianAt (fun y ↦ g.scalarAt y) x
Poincare/Global/ScalarVariation.lean:24261:        g.laplacianAt (fun y ↦ g.scalarAt y) x +
Poincare/Global/ScalarVariation.lean:24272:        g.laplacianAt (fun y ↦ g.scalarAt y) x := by
Poincare/Global/ScalarVariation.lean:24306:      g.laplacianAt (fun y ↦ g.scalarAt y) x +
Poincare/Global/ScalarVariation.lean:24326:        g.laplacianAt (fun y ↦ g.scalarAt y) x +
Poincare/Global/ScalarVariation.lean:24349:        g.laplacianAt (fun y ↦ g.scalarAt y) x := by
Poincare/Global/ScalarVariation.lean:24359:        g.laplacianAt (fun y ↦ g.scalarAt y) x := by
Poincare/Global/ScalarVariation.lean:24385:      g.laplacianAt (fun y ↦ g.scalarAt y) x
Poincare/Global/ScalarVariation.lean:24401:        g.laplacianAt (fun y ↦ g.scalarAt y) x :=
Poincare/Global/ScalarVariation.lean:24429:        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
Poincare/Global/ScalarVariation.lean:24439:        g.laplacianAt (fun y ↦ g.scalarAt y) x := by
Poincare/Global/ScalarVariation.lean:24452:        g.laplacianAt (fun y ↦ g.scalarAt y) x +
Poincare/Global/ScalarVariation.lean:24472:        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
Poincare/Global/ScalarVariation.lean:24652:      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarVariation.lean:24671:    g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarVariation.lean:24680:      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x =
Poincare/Global/ScalarVariation.lean:24689:        g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x := by
Poincare/Global/ScalarVariation.lean:24694:    _ ≤ g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
Poincare/Global/ScalarVariation.lean:25234:          (gt t₀).laplacianAt (fun y ↦ (gt t₀).pinchingQuotientAt y) x
Poincare/Global/ScalarVariation.lean:25268:              (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:25317:    g.laplacianAt q x =
Poincare/Global/ScalarVariation.lean:25318:      (g.laplacianAt u x - q x * g.laplacianAt v x
Poincare/Global/ScalarVariation.lean:25324:      g.laplacianAt u x =
Poincare/Global/ScalarVariation.lean:25325:        q x * g.laplacianAt v x + v x * g.laplacianAt q x
Poincare/Global/ScalarVariation.lean:25507:        - (1 / 2 : ℝ) * (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:25521:      (1 / 2 : ℝ) * (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:25550:`δΓ` contraction; the conversion from Hessian trace to `laplacianAt` is
Poincare/Global/ScalarVariation.lean:26412:      g.laplacianAt f x =
Poincare/Global/ScalarVariation.lean:26424:      - (1 / 2 : ℝ) * g.laplacianAt f x
Poincare/Global/ScalarVariation.lean:26439:      g.laplacianAt f x =
Poincare/Global/ScalarVariation.lean:26449:    (1 / 2 : ℝ) * g.laplacianAt f x
Poincare/Global/ScalarVariation.lean:26461:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26467:  let L : ℝ := (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26497:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26521:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26552:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26596:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26600:        - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26631:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26644:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26673:          - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26677:        - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26703:        - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26723:        - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26744:        - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26766:        - (gt t₀).laplacianAt
Poincare/Global/ScalarVariation.lean:26792:          - (gt t₀).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay.lean:62:        (gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay.lean:107:        (gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay.lean:139:        (gt t).laplacianAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay.lean:194:        (gt t).laplacianAt
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:43:theorem continuous_joint_covRicciNormSqAt_of_bochner_fields {n : ℕ} {N : Type u} {K : Type v} [TopologicalSpace N] [T2Space N] [ChartedSpace (ClosedSmoothModel n) N] [IsManifold (closedSmoothModelWithCorners n) ∞ N] [TopologicalSpace K] (metric : K → ClosedSmoothRiemannianMetric n N) (hRicNorm₂ : ∀ k : K, ∀ x : N, ContMDiffAt (closedSmoothModelWithCorners n) 𝓘(ℝ) 2 (fun y : N ↦ (metric k).ricciNormSqAt y) x) (hPairDiff : ∀ k : K, ∀ x : N, ∀ w : TangentSpace (closedSmoothModelWithCorners n) x, MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (fun y : N ↦ covRicciRicciPairingAt (metric k) y (extend (ClosedSmoothModel n) w y)) x) (hRicSecond : ∀ k : K, ∀ x : N, CovTensor2DerivExtDifferentiableAt (metric k) (ricciVariationField (metric k)) x) (hLaplacian : Continuous (fun p : K × N ↦ (metric p.1).laplacianAt (fun y : N ↦ (metric p.1).ricciNormSqAt y) p.2)) (hRough : Continuous (fun p : K × N ↦ roughRicciLaplacianPairingAt (metric p.1) p.2)) : Continuous (fun p : K × N ↦ covRicciNormSqAt (metric p.1) p.2) := by
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:44:  have hformula : (fun p : K × N ↦ covRicciNormSqAt (metric p.1) p.2) = fun p : K × N ↦ ((metric p.1).laplacianAt (fun y : N ↦ (metric p.1).ricciNormSqAt y) p.2 - 2 * roughRicciLaplacianPairingAt (metric p.1) p.2) / 2 := by
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:67:      (metric p.1).laplacianAt
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:93:      (metric p.1).laplacianAt
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:116:      (metric p.1).laplacianAt
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:298:        (reaction.metric p.1).laplacianAt (fun y : M ↦ (reaction.metric p.1).ricciNormSqAt y) p.2))
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:320:        (reaction.metric p.1).laplacianAt (fun y : M ↦ (reaction.metric p.1).ricciNormSqAt y) p.2))
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:340:        (reaction.metric p.1).laplacianAt (fun y : M ↦ (reaction.metric p.1).ricciNormSqAt y) p.2))
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:369:        (reaction.metric p.1).laplacianAt (fun y : M ↦ (reaction.metric p.1).ricciNormSqAt y) p.2))
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1518:  have hlap : g.laplacianAt Qf x ≤ 0 :=
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1537:  have hFineq' : F' ≤ g.laplacianAt Qf x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1582:    g.laplacianAt f x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1629:        g.laplacianAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1630:          g.laplacianAt (u τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1631:      change g.laplacianAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1632:        g.laplacianAt (u τ) x
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1646:      g.laplacianAt (fun y : M ↦ u τ y + k) x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1651:        g.laplacianAt (u τ) x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1672:          g.laplacianAt (Q τ) x
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1696:        Q' τ x ≤ g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1703:        g.laplacianAt (u τ) x = -g.laplacianAt (Q τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1737:          -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x) := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1739:        g.laplacianAt (u τ) x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1744:          -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1758:        0 ≤ g.laplacianAt (u τ) x :=
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1767:      0 ≤ g.laplacianAt (u τ) x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1889:    g.laplacianAt f x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1937:        g.laplacianAt (fun y : M ↦ u τ y + k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1938:          g.laplacianAt (u τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1939:      change g.laplacianAt ((u τ) + fun _ : M ↦ k) x =
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1940:        g.laplacianAt (u τ) x
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1954:      g.laplacianAt (fun y : M ↦ u τ y + k) x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1959:        g.laplacianAt (u τ) x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1978:          g.laplacianAt (Q τ) x
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1991:        Q' τ x ≤ g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1998:        g.laplacianAt (u τ) x = -g.laplacianAt (Q τ) x := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2032:          -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ) := by
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2034:        g.laplacianAt (u τ) x +
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2039:          -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ)
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2053:        0 ≤ g.laplacianAt (u τ) x :=
Poincare/Global/MetricFlowJointPinchingEvolution.lean:2062:      0 ≤ g.laplacianAt (u τ) x +
Poincare/Global/ClosedRiemannianParabolicExponentialMaximum.lean:46:      Q' t x ≤ (gt t).laplacianAt (Q t) x - rate * Q t x)
Poincare/Global/ClosedRiemannianParabolicExponentialMaximum.lean:51:    (M := M) (lap := fun t f x ↦ (gt t).laplacianAt f x)
Poincare/Global/ClosedRiemannianParabolicExponentialMaximum.lean:92:      Q' t x ≤ (gt t).laplacianAt (Q t) x - rate * Q t x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:156:    (gt t₀).laplacianAt
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:120:  let lapN := g.laplacianAt (fun y ↦ g.ricciNormSqAt y) x
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:121:  let lapR := g.laplacianAt (fun y ↦ g.scalarAt y) x
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:223:  let lapU : ℝ := g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:224:  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:264:      g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:332:  change _ ≤ g.laplacianAt (fun y ↦ g.tracelessPinchingAt y δ) x +
exit=0
$ rg -n curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional Poincare
Poincare/ModelLaplacianRootAliases.lean:686:    curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
Poincare/ModelLaplacian.lean:29337:theorem curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
Poincare/ModelLaplacian.lean:30118:(`curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional`), replacing `|∇²f|²` by its lower bound
Poincare/ModelLaplacian.lean:30135:  rw [curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional G hG hGsymm hinv hf]
Poincare/ModelLaplacian.lean:35792:/-- Theorem contract for `curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional`. -/
Poincare/ModelLaplacian.lean:35794:    @RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional = @RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional :=
exit=0
$ rg -n hasDerivAt_inner_of_timeDifferentiableAt Poincare
Poincare/Global/ScalarVariation.lean:635:theorem hasDerivAt_inner_of_timeDifferentiableAt
Poincare/Global/ScalarVariation.lean:3674:    hasDerivAt_inner_of_timeDifferentiableAt (gt := gt) (t₀ := t₀) (x := x) hgt
Poincare/Global/ScalarVariation.lean:10358:  have hinner := hasDerivAt_inner_of_timeDifferentiableAt (hgt x)
exit=0
$ rg -n hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt Poincare
Poincare/Global/NormalizedFlowHausdorffLichnerowiczEndpoint.lean:52:from `timeDifferentiable` by `hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt`.
Poincare/Global/NormalizedFlowHausdorffLichnerowiczEndpoint.lean:192:    (hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
Poincare/Global/ScalarEvolution.lean:3402:    (hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt (hgt x))
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:334:    hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
Poincare/Global/MetricFlowJointPinchingEvolution.lean:671:    exact hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
Poincare/Global/MetricFlowJointPinchingEvolution.lean:834:    hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
Poincare/Global/MetricRaiseTimeDerivative.lean:236:theorem hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:45:    hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
exit=0
$ rg -n hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two Poincare
Poincare/Global/MetricFlowJointRegularity.lean:34:theorem hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
Poincare/Global/MetricFlowJointRegularity.lean:358:  have hmix := hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
exit=0
$ rg -n SatisfiesNormalizedHamiltonScalarEvolutionAt Poincare
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:40:def SatisfiesNormalizedHamiltonScalarEvolutionAt
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:59:    SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x := by
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:69:  unfold SatisfiesNormalizedHamiltonScalarEvolutionAt
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:102:      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:128:      simpa [SatisfiesNormalizedHamiltonScalarEvolutionAt, a, R, r, R'] using
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:222:      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:267:      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:303:      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:346:      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:211:    (hHam : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:236:    simpa [SatisfiesNormalizedHamiltonScalarEvolutionAt] using hHam.mul hHam
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:316:    (hScalar : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ x) :
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:80:  have hScalar : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ x :=
exit=0
$ rg -n IsClosedNormalizedRicciFlowSolutionAt Poincare
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinScalarProfile.lean:51:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinScalarProfile.lean:129:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinScalarProfile.lean:205:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/ProofBearingPartitionEndToEndCompletion.lean:52:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:38:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:58:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:88:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:106:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:110:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:158:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:197:  IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradientSphere.lean:45:  IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:131:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:214:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) :
Poincare/Global/NormalizedFlowVolumeVariation.lean:243:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:261:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:275:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:333:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:356:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:376:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:391:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowVolumeVariation.lean:407:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:33:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:63:    (hflow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:79:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:126:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowEnergyCriticality.lean:210:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowEnergyCriticality.lean:260:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowEnergyCriticality.lean:292:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowEnergyCriticality.lean:564:      IsClosedNormalizedRicciFlowSolutionAt gt (sample i) x)
Poincare/Global/NormalizedFlowEnergyCriticality.lean:905:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:65:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay.lean:102:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:58:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:100:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:125:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) :
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:143:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:228:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:306:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:346:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:391:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:438:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:485:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:532:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:594:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:636:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:693:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay.lean:60:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/HausdorffTotalScalarFirstVariation.lean:291:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/HausdorffTotalScalarFirstVariation.lean:344:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HausdorffTotalScalarFirstVariation.lean:379:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:187:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:212:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:238:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:268:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:294:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffLichnerowiczEndpoint.lean:252:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:57:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t y)
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:379:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimeCurvatureCompactness.lean:211:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimeCurvatureCompactness.lean:260:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimeCurvatureCompactness.lean:305:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusSelectedSmoothAtlasPoincare.lean:60:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean:314:      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:42:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:92:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:138:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient.lean:154:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient.lean:208:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient.lean:264:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient.lean:319:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient.lean:382:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient.lean:470:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowChartFramePartitionCompactOrbitEndpoint.lean:68:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowChartFramePartitionCompactOrbitEndpoint.lean:103:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowChartFramePartitionCompactOrbitEndpoint.lean:124:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowChartFramePartitionCompactOrbitEndpoint.lean:141:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowChartFramePartitionCompactOrbitEndpoint.lean:175:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowChartFramePartitionCompactOrbitEndpoint.lean:212:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination.lean:92:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination.lean:147:  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowTopologicalSphereBridge.lean:71:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowTopologicalSphereBridge.lean:160:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay.lean:54:    (hFlow : IsClosedNormalizedRicciFlowSolutionAt gt (T + s) x) :
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay.lean:55:    IsClosedNormalizedRicciFlowSolutionAt (fun r ↦ gt (T + r)) s x := by
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay.lean:115:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay.lean:233:      IsClosedNormalizedRicciFlowSolutionAt data.shiftedFlow s x := by
Poincare/Global/NormalizedFlowForwardAbsoluteDissipation.lean:88:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardAbsoluteDissipation.lean:226:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardAbsoluteDissipation.lean:265:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardAbsoluteDissipation.lean:301:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantCompactness.lean:51:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantCompactness.lean:109:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantCompactness.lean:152:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantCompactness.lean:191:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantCompactness.lean:227:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:887:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:911:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:935:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteAtlasAutomaticAreaEndpoint.lean:61:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteAtlasAutomaticAreaEndpoint.lean:87:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteAtlasAutomaticAreaEndpoint.lean:123:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteAtlasAutomaticAreaEndpoint.lean:168:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteAtlasAutomaticAreaEndpoint.lean:213:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowEnergyConcentrationLipschitzBridge.lean:422:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowEnergyConcentrationLipschitzBridge.lean:456:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalar.lean:78:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalar.lean:169:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:51:    (hFlow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) :
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:127:    (hFlow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:314:      IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:468:      IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:492:      IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:517:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:548:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:575:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:611:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:62:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:125:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:192:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:223:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:289:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:338:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:356:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x :=
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:469:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:507:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:560:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:638:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare.lean:80:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/HausdorffScalarDensityDomination.lean:140:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HausdorffScalarDensityDomination.lean:184:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HausdorffScalarDensityDomination.lean:217:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:81:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:273:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:371:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:423:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:443:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:467:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:499:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:577:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:613:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:711:    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M₃, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimeMeanScalarPinching.lean:50:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimeMeanScalarPinching.lean:159:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:32:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:54:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:78:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:115:      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/NormalizedFlowLowerSemicontinuousCompactness.lean:62:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowLowerSemicontinuousCompactness.lean:116:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowQuantitativeNearRoundTailFromDecay.lean:353:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalar.lean:56:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalar.lean:144:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalar.lean:247:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarSphere.lean:50:  IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarSphere.lean:125:  IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:207:      IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:222:  change IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:254:      IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:328:      IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:357:      IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:182:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:352:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowPointwiseConvergence.lean:43:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowPointwiseConvergence.lean:110:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowPointwiseConvergence.lean:136:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowPointwiseConvergence.lean:172:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowPointwiseConvergence.lean:196:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/ProofBearingEndToEndCompletion.lean:65:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/ProofBearingEndToEndCompletion.lean:115:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowDissipationDifferentialDecay.lean:105:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:34:      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/HamiltonEtaCoreReduction.lean:67:      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/NormalizedFlowImprovedPinchingSubsequenceDecay.lean:157:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/ClosedRicciFlowNormalization.lean:32:      IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowScalarVarianceConcentration.lean:126:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowScalarVarianceConcentration.lean:237:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowImprovedPinchingSampleScalarFloorDecay.lean:182:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonReactionCoreFinal.lean:40:      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/HausdorffVolumeFirstVariation.lean:206:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/HausdorffVolumeFirstVariation.lean:253:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusSelectedSmoothAtlasPoincare.lean:48:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowCompactFixedTargetFiniteTimePositiveEinstein.lean:67:    IsClosedNormalizedRicciFlowSolutionAt gt t.1 x
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyMaximumDifferentialDecay.lean:76:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowRescaling.lean:73:    IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/NormalizedFlowRescaling.lean:148:    IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/NormalizedFlowRescaling.lean:174:      IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/ForwardRescalingChartFramePartitionEndToEnd.lean:101:      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
Poincare/Global/ForwardRescalingChartFramePartitionEndToEnd.lean:174:      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
Poincare/Global/ForwardRescalingChartFramePartitionEndToEnd.lean:250:      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
Poincare/Global/ForwardRescalingChartFramePartitionEndToEnd.lean:321:      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
Poincare/Global/ForwardRescalingChartFramePartitionEndToEnd.lean:392:      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
Poincare/Global/ForwardRescalingChartFramePartitionEndToEnd.lean:460:      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
Poincare/Global/ForwardRescalingChartFramePartitionEndToEnd.lean:526:      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:62:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:124:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:164:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:267:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:294:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:340:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:364:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:388:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:244:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:287:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyDecay.lean:66:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyDecay.lean:97:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowMeanScalarTopologicalSphereBridge.lean:83:    IsClosedNormalizedRicciFlowSolutionAt gt t.1 x
Poincare/Global/NormalizedFlowPartitionFullyAssembledEnergyEndpoint.lean:50:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay.lean:85:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay.lean:130:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay.lean:178:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffDissipationEndpoint.lean:35:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlow.lean:91:structure IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/NormalizedFlow.lean:107:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlow.lean:123:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlow.lean:138:    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlow.lean:244:    IsClosedNormalizedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t₀ x := by
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:379:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:418:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:454:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonReactionCoreReduction.lean:145:      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/NormalizedFlowAbsoluteDissipationDecay.lean:113:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffClosedRangeEndpoint.lean:41:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffClosedRangeEndpoint.lean:61:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffClosedRangeEndpoint.lean:78:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffClosedRangeEndpoint.lean:105:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowHausdorffClosedRangeEndpoint.lean:135:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteDissipationLimit.lean:61:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteDissipationLimit.lean:103:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteDissipationLimit.lean:132:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureQuantitativeNearRoundTail.lean:99:    IsClosedNormalizedRicciFlowSolutionAt gt t x
Poincare/Global/NormalizedFlowScalarRegularity.lean:46:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowScalarRegularity.lean:93:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowScalarRegularity.lean:138:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient.lean:54:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 y)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient.lean:86:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient.lean:108:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient.lean:140:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient.lean:239:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient.lean:296:  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient.lean:367:  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:45:      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:102:      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:365:    IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:391:      IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:459:    IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:484:      IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/HamiltonChartDensityLocalDomination.lean:210:      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:182:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:267:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:372:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:473:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:538:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:601:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:664:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:732:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergy.lean:59:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergy.lean:114:  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowCompactFixedTargetEventualCoerciveGapPositiveEinstein.lean:62:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowCompactFixedTargetEventualCoerciveGapPositiveEinstein.lean:136:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowCompactFixedTargetEventualCoerciveGapPositiveEinstein.lean:205:    IsClosedNormalizedRicciFlowSolutionAt gt t.1 x
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarJointContinuity.lean:52:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarJointContinuity.lean:106:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:30:    (hFlow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:163:    (hFlow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowHausdorffScalarDominationJointC1Reduction.lean:260:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/HausdorffChartFrameFirstVariation.lean:120:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/HausdorffChartFrameFirstVariation.lean:181:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HausdorffChartFrameFirstVariation.lean:281:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/HausdorffChartFrameFirstVariation.lean:332:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorReduction.lean:33:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorReduction.lean:57:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorReduction.lean:68:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorReduction.lean:89:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorReduction.lean:122:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/HamiltonMeanFloorReduction.lean:170:    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowEnergyConcentration.lean:318:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowEnergyConcentration.lean:367:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantRangeClosure.lean:40:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantRangeClosure.lean:86:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantRangeClosure.lean:109:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantRangeClosure.lean:144:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowInvariantRangeClosure.lean:175:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowPartitionCompactOrbitEndpoint.lean:52:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowPartitionCompactOrbitEndpoint.lean:96:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowRicciTensorEvolution.lean:165:    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
Poincare/Global/NormalizedFlowCompactFixedTargetCoerciveGapPositiveEinstein.lean:65:    IsClosedNormalizedRicciFlowSolutionAt gt t.1 x
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:47:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:92:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:147:  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowCompactFiniteDissipationBoundedVariation.lean:50:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowCompactFiniteDissipationBoundedVariation.lean:204:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowCompactFiniteDissipationBoundedVariation.lean:283:      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
Poincare/Global/NormalizedFlowMeanScalarLimit.lean:77:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowMeanScalarLimit.lean:189:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowMeanScalarLimit.lean:236:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:308:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:329:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:395:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:432:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:477:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:536:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:572:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:605:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:661:    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:731:    (hFlow : ∀ x : N, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
Poincare/Global/HamiltonStokesFreeReactionCore.lean:47:      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
Poincare/Global/NormalizedFlowCompactFixedTargetFiniteTracelessEnergyPositiveEinstein.lean:65:    IsClosedNormalizedRicciFlowSolutionAt gt t.1 x
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:253:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:312:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
exit=0
$ rg -n isClosedNormalizedRicciFlowSolutionAt_timeDerivAt Poincare
Poincare/Global/NormalizedFlowPointwiseConvergence.lean:59:    isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
Poincare/Global/NormalizedFlow.lean:105:theorem isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
Poincare/Global/NormalizedFlow.lean:131:  rw [isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
exit=0
$ rg -n globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree Poincare
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:63:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:114:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:158:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:41:  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:413:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:462:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:556:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:657:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:714:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:153:def globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:283:      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:309:      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
Poincare/Global/NormalizedFlowChartFramePartitionCompactOrbitEndpoint.lean:232:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowInvariantCompactness.lean:208:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowFiniteAtlasAutomaticAreaEndpoint.lean:70:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowFiniteAtlasAutomaticAreaEndpoint.lean:236:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffPositiveEinstein.lean:100:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:47:      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:502:      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:561:      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:628:      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/ProofBearingEndToEndCompletion.lean:209:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/NormalizedFlowPartitionFullyAssembledEnergyEndpoint.lean:72:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:416:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:498:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/HamiltonMeanFloorReduction.lean:101:  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
Poincare/Global/HamiltonMeanFloorReduction.lean:180:  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
Poincare/Global/NormalizedFlowPartitionCompactOrbitEndpoint.lean:116:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowInvariantRangeClosure.lean:158:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowHausdorffScalarVariationJointContinuityReduction.lean:77:    (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:82:      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:243:      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
exit=0
$ rg -n scalarGradNormSqAt_le_three_covRicciNormSqAt Poincare
Poincare/Global/ScalarEvolution.lean:1044:theorem scalarGradNormSqAt_le_three_covRicciNormSqAt
Poincare/Global/ScalarEvolution.lean:1328:      (g.scalarGradNormSqAt_le_three_covRicciNormSqAt hn x)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:280:  have hGradient := g.scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:177:  have hTrace := g.scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x
Poincare/Global/NormalizedFlowEnergyConcentrationCurvatureDerivative.lean:800:    (g.scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x).trans
exit=0
$ rg -n scalarMinimumAt Poincare
Poincare/Global/NormalizedFlowPinchingLimit.lean:46:  (scalarMinimumAt g, tracelessPinchingMaximumAt g 0)
Poincare/Global/NormalizedFlowPinchingLimit.lean:57:  (scalarMinimumAt g, tracelessRicciMaximumAt g)
Poincare/Global/NormalizedFlowPinchingLimit.lean:65:    c ≤ scalarMinimumAt g := by
Poincare/Global/NormalizedFlowPinchingLimit.lean:67:  rw [scalarMinimumAt]
Poincare/Global/NormalizedFlowPinchingLimit.lean:80:    scalarMinimumAt g ≤ g.scalarAt x := by
Poincare/Global/NormalizedFlowPinchingLimit.lean:246:  have hLimitMinimumLower : c ≤ scalarMinimumAt gLimit := by
Poincare/Global/NormalizedFlowPinchingLimit.lean:252:      _ = scalarMinimumAt gLimit := rfl
Poincare/Global/NormalizedFlowPinchingLimit.lean:436:  have hLimitMinimumLower : c ≤ scalarMinimumAt gLimit := by
Poincare/Global/NormalizedFlowPinchingLimit.lean:441:      _ = scalarMinimumAt gLimit := rfl
Poincare/Global/NormalizedFlowPinchingLimit.lean:560:  have hLimitMinimumLower : c ≤ scalarMinimumAt gLimit := by
Poincare/Global/NormalizedFlowPinchingLimit.lean:565:      _ = scalarMinimumAt gLimit := rfl
Poincare/Global/HamiltonScalarNegativeBarrier.lean:88:      (by simpa [scalarMinimumTrack, scalarMinimumAt, R] using hminle)
Poincare/Global/HamiltonScalarNegativeBarrier.lean:320:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarNegativeBarrier.lean:321:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarNegativeBarrier.lean:322:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/HamiltonScalarNegativeBarrier.lean:337:  have hfloor : ∀ k, cseg k ≤ scalarMinimumAt (g k (start k)) := by
Poincare/Global/HamiltonScalarNegativeBarrier.lean:372:            cseg (k + 1) ≤ scalarMinimumAt (g k (start (k + 1))) := by
Poincare/Global/HamiltonScalarNegativeBarrier.lean:416:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarNegativeBarrier.lean:417:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarNegativeBarrier.lean:418:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/HamiltonScalarNegativeBarrier.lean:474:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarNegativeBarrier.lean:475:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarNegativeBarrier.lean:476:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/HamiltonScalarNegativeBarrier.lean:491:  have hfloor : ∀ k, cseg k ≤ scalarMinimumAt (g k (start k)) := by
Poincare/Global/HamiltonScalarNegativeBarrier.lean:526:            cseg (k + 1) ≤ scalarMinimumAt (g k (start (k + 1))) := by
Poincare/Global/HamiltonScalarNegativeBarrier.lean:573:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarNegativeBarrier.lean:574:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarNegativeBarrier.lean:575:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/ScalarEvolution.lean:4047:noncomputable def scalarMinimumAt (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/ScalarEvolution.lean:4053:  fun τ ↦ scalarMinimumAt (gt (t₀ + τ))
Poincare/Global/ScalarEvolution.lean:4059:    scalarMinimumAt g = g.scalarAt x := by
Poincare/Global/ScalarEvolution.lean:4075:    scalarMinimumAt g ≤ g.scalarAt x := by
Poincare/Global/ScalarEvolution.lean:4548:    exact le_trans h0 (by simpa [scalarMinimumTrack, scalarMinimumAt, R] using hminle)
Poincare/Global/ScalarEvolution.lean:4757:    exact le_trans h0 (by simpa [scalarMinimumTrack, scalarMinimumAt, R] using hminle)
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:50:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:51:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:53:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:63:        scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:91:        -(3 / (2 * (C + t))) ≤ scalarMinimumAt (g k t) := by
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:134:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:135:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:137:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:149:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:200:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:201:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:203:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInterior.lean:215:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:260:      (by simpa [scalarMinimumTrack, scalarMinimumAt, R] using hminle)
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:475:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:476:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:477:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:492:  have hfloor : ∀ k, cseg k ≤ scalarMinimumAt (g k (start k)) := by
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:527:            cseg (k + 1) ≤ scalarMinimumAt (g k (start (k + 1))) := by
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:578:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:579:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:580:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:616:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:617:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:618:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:669:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:670:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:671:    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInterior.lean:78:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInterior.lean:79:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInterior.lean:81:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInterior.lean:93:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:85:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:86:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:88:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:98:        scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:124:        -(3 / (2 * (C + t))) ≤ scalarMinimumAt (g k t) := by
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:170:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:171:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:173:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:183:        scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:209:        -(3 / (2 * (C + t))) ≤ scalarMinimumAt (g k t) := by
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:251:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:252:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:254:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:264:        scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:319:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:320:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:322:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:334:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:388:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:389:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:391:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:403:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:454:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:455:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:457:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidth.lean:469:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:70:    Continuous (fun k ↦ scalarMinimumAt (metric k)) := by
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:71:  simpa only [scalarMinimumAt, Set.image_univ] using
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:55:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:56:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:58:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:70:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:157:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:158:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:170:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:175:      (scalarMinimumAt (g 0 (start 0))) with ⟨C, hC, hScalarInitial⟩
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:51:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:52:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:54:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:64:        scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:92:        -(3 / (2 * (C + t))) ≤ scalarMinimumAt (g k t) := by
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:138:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:139:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:141:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:153:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:207:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:208:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:210:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionGeometricScalarWidthInteriorContinuousOn.lean:222:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionPerelmanWidth.lean:55:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionPerelmanWidth.lean:56:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionPerelmanWidth.lean:68:          scalarMinimumAt (g k t) * W k t)
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInteriorContinuousOn.lean:75:      scalarMinimumAt (g k (start (k + 1))) ≤
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInteriorContinuousOn.lean:76:        scalarMinimumAt (g (k + 1) (start (k + 1))))
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInteriorContinuousOn.lean:78:      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInteriorContinuousOn.lean:90:          scalarMinimumAt (g k t) * W k t)
exit=0
$ rg -n hessianAt_eq_chart_derivatives Poincare
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:214:theorem hessianAt_eq_chart_derivatives
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:361:  rw [hessianAt_eq_chart_derivatives g p f hs hf hz]
exit=0
$ rg -n extDerivFun_apply_chart Poincare
Poincare/ChartIdentification.lean:86:theorem extDerivFun_apply_chart {f : M → 𝕜} {x : M} (hf : MDiffAt f x)
Poincare/ChartIdentification.lean:307:  rw [extDerivFun_apply_chart (hf.mdifferentiableAt two_ne_zero),
Poincare/ChartIdentification.lean:445:  rw [extDerivFun_apply_chart hgd v]
Poincare/ChartIdentification.lean:531:    rw [extDerivFun_apply_chart hgd (V₀ x)]
Poincare/ChartIdentification.lean:571:/-- Theorem contract for `extDerivFun_apply_chart`. -/
Poincare/ChartIdentification.lean:573:    @extDerivFun_apply_chart = @extDerivFun_apply_chart :=
Poincare/ModelLaplacianRootAliases.lean:26:    extDerivFun_apply_chart
Poincare/Global/MetricFlowJointRegularity.lean:369:      extDerivFun_apply_chart (hm.mdifferentiableAt two_ne_zero) a
Poincare/Global/MetricFlowJointRegularity.lean:372:  have hright := extDerivFun_apply_chart
Poincare/Global/ScalarEvolution.lean:3915:      extDerivFun_apply_chart
Poincare/Global/ScalarEvolution.lean:3975:    extDerivFun_apply_chart
exit=0

```

</details>

<details>
<summary>inventory.log</summary>

```text
Poincare.ClosedSmoothRiemannianMetric.gradientAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) :
  TangentSpace (Poincare.closedSmoothModelWithCorners n) x
Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) [g.leviCivita.ContMDiffCovariantDerivative 1] (x : M) : ℝ
Poincare.ClosedSmoothRiemannianMetric.hessianAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M)
  (v w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) : ℝ
Poincare.ClosedSmoothRiemannianMetric.laplacianAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) : ℝ
RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional.{u_2} {E : Type u_2}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (G : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
  (hG : ContDiff ℝ 3 G) (hGsymm : ∀ (y p q : E), ((G y) p) q = ((G y) q) p) (hinv : ∀ (y : E), (G y).IsInvertible)
  {f : E → ℝ} (hf : ContDiff ℝ 3 f) :
  CovariantDerivative.curvedLaplacian G (fun y => RicciFlow.RicciFlow.metricBilin (G y)) ⋯
      (RicciFlow.RicciFlow.coordGradNormSq G f) x =
    2 *
        (((G x) (RicciFlow.RicciFlow.coordGradient G f x))
            (RicciFlow.RicciFlow.coordGradient G
              (CovariantDerivative.curvedLaplacian G (fun y => RicciFlow.RicciFlow.metricBilin (G y)) ⋯ f) x) +
          RicciFlow.RicciFlow.coordRicci G x (RicciFlow.RicciFlow.coordGradient G f x)
            (RicciFlow.RicciFlow.coordGradient G f x)) +
      2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f x
Poincare.hasDerivAt_inner_of_timeDifferentiableAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} (hgt : Poincare.TimeDifferentiableAt gt t₀ x) :
  HasDerivAt (fun t => (gt t).inner x) (Poincare.timeDerivContinuousAt gt t₀ x hgt) t₀
Poincare.hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hgt : Poincare.TimeDifferentiableAt gt t₀ x) :
  HasDerivAt (fun t => (gt t).metricRaiseContinuousAt x) (Poincare.metricRaiseDerivAt gt t₀ x hgt) t₀
Poincare.hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two.{u_1} {V : Type u_1} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (F : ℝ → V → ℝ) (t₀ : ℝ) (x a : V) (hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, x)) :
  HasDerivAt (fun t => (fderiv ℝ (F t) x) a) ((fderiv ℝ (fun z => deriv (fun t => F t z) t₀) x) a) t₀
Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt.{u} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (t : ℝ) (x : M) [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1] : Prop
Poincare.IsClosedNormalizedRicciFlowSolutionAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (t₀ : ℝ) (x : M) : Prop
Poincare.isClosedNormalizedRicciFlowSolutionAt_timeDerivAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hflow : Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
  {Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y} (hZ : Poincare.ClosedC2TangentField Z)
  (hreg : (gt t₀).leviCivita.DerivRegularAt Z x) (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x) :
  Poincare.timeDerivAt gt t₀ x (Z x) w =
    -2 * (gt t₀).leviCivita.ricciTraceAt hreg w + 2 / ↑n * Poincare.meanScalar (gt t₀) * (((gt t₀).inner x) (Z x)) w
Poincare.globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  (hJoint : ∀ (t : ℝ) (y : M), Poincare.MetricEntriesJointContDiffAt gt t y 3) :
  Poincare.GlobalLichnerowiczAssemblyRegularity gt
Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt_le_three_covRicciNormSqAt.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  [g.leviCivita.ContMDiffCovariantDerivative 1] (hn : n = 3) (x : M) :
  g.scalarGradNormSqAt x ≤ 3 * Poincare.covRicciNormSqAt g x
Poincare.scalarMinimumAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) : ℝ
Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] (g : Poincare.ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
  (hs : tsupport f ⊆ (extChartAt (Poincare.closedSmoothModelWithCorners n) p).source)
  (hf : ContMDiff (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 f)
  {z : Poincare.ClosedSmoothModel n} (hz : z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners n) p).target)
  (v w : Poincare.ClosedSmoothModel n) :
  have u := Poincare.ClosedLaplacianStokesProducer.coordinateScalar p f;
  have D :=
    mfderivWithin (modelWithCornersSelf ℝ (Poincare.ClosedSmoothModel n)) (Poincare.closedSmoothModelWithCorners n)
      (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) p).symm)
      (Set.range ↑(Poincare.closedSmoothModelWithCorners n)) z;
  g.hessianAt f (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) p).symm z) (D v) (D w) =
    ((fderiv ℝ (fderiv ℝ u) z) v) w -
      (fderiv ℝ u z) ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner p) z v) w)
/tmp/scalar-gradient-evolution-evidence/inventory.lean:18:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.extDerivFun_apply_chart`
def Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [inst_1 : T2Space M] →
      [CompactSpace M] →
        [ConnectedSpace M] →
          [inst_4 : MeasurableSpace M] →
            [BorelSpace M] →
              [inst_6 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
                [inst_7 : IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] →
                  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) →
                    ℝ → M → [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1] → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] gt t x
    [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1] =>
  HasDerivAt (fun s => (gt s).scalarAt x)
    ((gt t).laplacianAt (fun y => (gt t).scalarAt y) x + 2 * (gt t).ricciNormSqAt x -
      2 / 3 * Poincare.meanScalar (gt t) * (gt t).scalarAt x)
    t
structure Poincare.IsClosedNormalizedRicciFlowSolutionAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (t₀ : ℝ) (x : M) : Prop
number of parameters: 13
fields:
  Poincare.IsClosedNormalizedRicciFlowSolutionAt.leviCivita : ∀ (t : ℝ),
      CovariantDerivative.IsLeviCivitaAt (fun y => (gt t).inner y) (gt t).leviCivita x
  Poincare.IsClosedNormalizedRicciFlowSolutionAt.flow : ∀
      {Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y},
      Poincare.ClosedC2TangentField Z →
        ∀ (hreg : (gt t₀).leviCivita.DerivRegularAt Z x) (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
          deriv (fun t => (((gt t).inner x) (Z x)) w) t₀ =
            -2 * (gt t₀).leviCivita.ricciTraceAt hreg w +
              2 / ↑n * Poincare.meanScalar (gt t₀) * (((gt t₀).inner x) (Z x)) w
constructor:
  Poincare.IsClosedNormalizedRicciFlowSolutionAt.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
    {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (leviCivita : ∀ (t : ℝ), CovariantDerivative.IsLeviCivitaAt (fun y => (gt t).inner y) (gt t).leviCivita x)
    (flow :
      ∀ {Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y},
        Poincare.ClosedC2TangentField Z →
          ∀ (hreg : (gt t₀).leviCivita.DerivRegularAt Z x)
            (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
            deriv (fun t => (((gt t).inner x) (Z x)) w) t₀ =
              -2 * (gt t₀).leviCivita.ricciTraceAt hreg w +
                2 / ↑n * Poincare.meanScalar (gt t₀) * (((gt t₀).inner x) (Z x)) w) :
    Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x

```

</details>

## Appendix B. Probe sources

<details>
<summary>inventory.lean</summary>

```lean
import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.IntrinsicLaplacianCoordinateForm
#check Poincare.ClosedSmoothRiemannianMetric.gradientAt
#check Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt
#check Poincare.ClosedSmoothRiemannianMetric.hessianAt
#check Poincare.ClosedSmoothRiemannianMetric.laplacianAt
#check RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
#check Poincare.hasDerivAt_inner_of_timeDifferentiableAt
#check Poincare.hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
#check Poincare.hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
#check Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt
#check Poincare.IsClosedNormalizedRicciFlowSolutionAt
#check Poincare.isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
#check Poincare.globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
#check Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt_le_three_covRicciNormSqAt
#check Poincare.scalarMinimumAt
#check Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#check Poincare.extDerivFun_apply_chart
#print Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt
#print Poincare.IsClosedNormalizedRicciFlowSolutionAt

```

</details>

<details>
<summary>inventory-corrected.lean</summary>

```lean
import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.IntrinsicLaplacianCoordinateForm
#check Poincare.ClosedSmoothRiemannianMetric.gradientAt
#check Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt
#check Poincare.ClosedSmoothRiemannianMetric.hessianAt
#check Poincare.ClosedSmoothRiemannianMetric.laplacianAt
#check RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
#check Poincare.hasDerivAt_inner_of_timeDifferentiableAt
#check Poincare.hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
#check Poincare.hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
#check Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt
#check Poincare.IsClosedNormalizedRicciFlowSolutionAt
#check Poincare.isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
#check Poincare.globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
#check Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt_le_three_covRicciNormSqAt
#check Poincare.scalarMinimumAt
#check Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#check extDerivFun_apply_chart
#print Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt
#print Poincare.IsClosedNormalizedRicciFlowSolutionAt
#check RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
#check Poincare.isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt

```

</details>

<details>
<summary>10-bochner-signatures.lean</summary>

```lean
import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.IntrinsicLaplacianCoordinateForm
#check Poincare.chartChristoffelField_symm
#check Poincare.GeodesicTransport.chartChristoffelField_contDiff_top
#check RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt
#check Poincare.ChartCurvatureBridge.fderiv_clm_family_apply
#check Poincare.anchorChartRicciEntryFlow_eq_ricciAt_anchor
#check CovariantDerivative.contDiff_blendedChartMetric
#check Poincare.anchorBlendedMetricFlow_isInvertible

```

</details>

<details>
<summary>26-module-audit.lean</summary>

```lean
import Poincare.Global.ScalarGradientEvolution
set_option pp.proofs false
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.ScalarGradientEvolution
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #check $(mkIdent n)))
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"

```

</details>

<details>
<summary>27-intrinsic-bochner-residual.lean</summary>

```lean
import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.IntrinsicLaplacianCoordinateForm

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false

universe u

namespace Poincare.ScalarGradientEvolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Differentiate the squared norm of a moving covector with the moving
inverse metric. The metric variation has a negative sign. -/
theorem hasDerivAt_covectorNormSq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    {α : ℝ → TM x →L[ℝ] ℝ} {α' : TM x →L[ℝ] ℝ}
    (hα : HasDerivAt α α' t₀) :
    HasDerivAt (fun t ↦ α t ((gt t).metricRaiseContinuousAt x (α t)))
      (2 * α' ((gt t₀).metricRaiseContinuousAt x (α t₀)) -
        timeDerivAt gt t₀ x
          ((gt t₀).metricRaiseContinuousAt x (α t₀))
          ((gt t₀).metricRaiseContinuousAt x (α t₀))) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  have hd := hα.clm_apply
    ((hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt hgt).clm_apply hα)
  apply hd.congr_deriv
  simp only [map_add]
  have hswap (v : TM x) :
      α t₀ v = (gt t₀).inner x v
        ((gt t₀).metricRaiseContinuousAt x (α t₀)) := by
    rw [(gt t₀).inner_symm]
    exact ((gt t₀).metricRaiseContinuousAt_inner_apply x (α t₀) v).symm
  rw [hswap (metricRaiseDerivAt gt t₀ x hgt (α t₀)),
    metricRaiseDerivAt_inner_apply hgt,
    hswap ((gt t₀).metricRaiseContinuousAt x α'),
    ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  ring

/-- The moving-gradient norm rule, expressed using the derivative of `df`. -/
theorem hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    {f : ℝ → M → ℝ} {f' : M → ℝ}
    (hdf : HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
      (extDerivFun f' x) t₀) :
    HasDerivAt
      (fun t ↦ (gt t).inner x ((gt t).gradientAt (f t) x)
        ((gt t).gradientAt (f t) x))
      (2 * (gt t₀).inner x ((gt t₀).gradientAt f' x)
          ((gt t₀).gradientAt (f t₀) x) -
        timeDerivAt gt t₀ x ((gt t₀).gradientAt (f t₀) x)
          ((gt t₀).gradientAt (f t₀) x)) t₀ := by
  have h := hasDerivAt_covectorNormSq hgt hdf
  have heq (g : ClosedSmoothRiemannianMetric n M) (u : M → ℝ) :
      g.metricRaiseContinuousAt x (extDerivFun u x) = g.gradientAt u x := rfl
  simp_rw [heq] at h
  simpa only [ClosedSmoothRiemannianMetric.inner_gradientAt] using h

omit [T2Space M] [IsManifold I ∞ M] in
/-- Joint second-order scalar regularity commutes the time derivative and
the manifold differential in a fixed tangent fiber. -/
theorem hasDerivAt_extDerivFun_of_joint_contDiffAt_two
    {f : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
    (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) (f t) x)
    (hft : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ deriv (fun t ↦ f t y) t₀) x)
    (hJoint : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ f p.1 ((extChartAt I x).symm p.2))
      (t₀, extChartAt I x x)) :
    HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
      (extDerivFun (fun y ↦ deriv (fun t ↦ f t y) t₀) x) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
  intro v
  simp_rw [extDerivFun_apply_chart (hf _), extDerivFun_apply_chart hft]
  exact hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
    (fun t z ↦ f t ((extChartAt I x).symm z)) t₀ (extChartAt I x x) v hJoint

section Normalized

variable {N : Type u} [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (ClosedSmoothModel 3) N]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]

local notation "I₃" => closedSmoothModelWithCorners 3
local notation "E₃" => ClosedSmoothModel 3

/-- Pointwise time variation of the scalar-gradient norm along normalized
flow. The joint scalar and Laplacian hypotheses are explicit regularity
requirements beyond the supplied joint metric entries. -/
theorem hasDerivAt_scalarGradNormSq_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 N} {t₀ : ℝ} {x : N}
    (hJoint : ∀ t y, MetricEntriesJointContDiffAt gt t y 3)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hScalarJoint : ContDiffAt ℝ 2
      (fun p : ℝ × E₃ ↦ (gt p.1).scalarAt ((extChartAt I₃ x).symm p.2))
      (t₀, extChartAt I₃ x x))
    (hLap : MDifferentiableAt I₃ 𝓘(ℝ)
      (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) :
    HasDerivAt (fun t ↦ (gt t).scalarGradNormSqAt x)
      (2 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
          ((gt t₀).gradientAt
            (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) +
        4 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
          ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x) +
        2 * (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
          ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x) -
        2 * meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x) t₀ := by
  letI : Nonempty N := ⟨x⟩
  let g := gt t₀
  let R : N → ℝ := fun y ↦ g.scalarAt y
  let A : N → ℝ := fun y ↦ g.ricciNormSqAt y
  let L : N → ℝ := fun y ↦ g.laplacianAt R y
  let c : ℝ := -(2 / 3 : ℝ) * meanScalar g
  have hR : MDifferentiableAt I₃ 𝓘(ℝ) R x := scalarAt_mdifferentiableAt g x
  have hA : MDifferentiableAt I₃ 𝓘(ℝ) A x := ricciNormSqAt_mdifferentiableAt g x
  have hL : MDifferentiableAt I₃ 𝓘(ℝ) L x := hLap
  have heq : (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) =
      L + (2 : ℝ) • A + c • R := by
    funext y
    have hs : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ y :=
      satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
        hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
    rw [hs.deriv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, L, A, R, c, g]
    ring
  have h2A : MDifferentiableAt I₃ 𝓘(ℝ) ((2 : ℝ) • A) x := by
    exact mdifferentiableAt_const.smul hA
  have hcR : MDifferentiableAt I₃ 𝓘(ℝ) (c • R) x := by
    exact mdifferentiableAt_const.smul hR
  have hft : MDifferentiableAt I₃ 𝓘(ℝ)
      (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) x := by
    rw [heq]
    exact (hL.add h2A).add hcR
  have hd := hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
    (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint t₀ x).of_le (by norm_num)))
    (hasDerivAt_extDerivFun_of_joint_contDiffAt_two
      (fun t ↦ scalarAt_mdifferentiableAt (gt t) x) hft hScalarJoint)
  rw [heq, g.gradientAt_add (hL.add h2A) hcR,
    g.gradientAt_add hL h2A,
    g.gradientAt_const_smul 2 hA, g.gradientAt_const_smul c hR] at hd
  apply hd.congr_deriv
  rw [isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
    (hFlow x)]
  simp only [normalizedRicciFlowRHSAt, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [ClosedSmoothRiemannianMetric.scalarGradNormSqAt, R, A, L, c, g]
  rw [(gt t₀).inner_symm x ((gt t₀).gradientAt
    (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x),
    (gt t₀).inner_symm x ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x)]
  ring

omit [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N] in
/-- The Ricci term in the coordinate Bochner formula is the intrinsic Ricci
tensor at the chart anchor, with the same curvature sign. -/
theorem coordRicci_anchorBlendedMetric
    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (v w : E₃) :
    RicciFlow.RicciFlow.coordRicci (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
      (extChartAt I₃ x x) v w = g.ricciAt x v w := by
  let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
  let Γ := GeodesicTransport.chartChristoffelField g x
  let q := extChartAt I₃ x x
  have hΓ : DifferentiableAt ℝ Γ q :=
    (GeodesicTransport.chartChristoffelField_contDiff_top g x).differentiable
      (by simp) q
  have heq (z a b : E₃) :
      RicciFlow.RicciFlow.christoffelClosedOp G z a b = Γ z a b := by
    rw [show Γ z a b = Γ z b a from chartChristoffelField_symm g x z a b]
    exact RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt G _
      (CovariantDerivative.chartBilin_nondegenerate
        (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
        GeodesicTransport.backgroundMetric_pos g.inner
        (fun y u hu ↦ g.inner_pos y hu) x
        (GeodesicTransport.cutoff_nonneg x) (GeodesicTransport.cutoff_le_one x)
        (GeodesicTransport.cutoff_support_invertible x) z)
      (fun _ _ ↦ rfl) a b
  have heqCLM (z a : E₃) :
      RicciFlow.RicciFlow.christoffelClosedOp G z a = Γ z a := by
    apply ContinuousLinearMap.ext
    intro b
    exact heq z a b
  have hcurv (a b c : E₃) :
      RicciFlow.RicciFlow.coordCurvatureOp G q a b c =
        chartCurvatureOf Γ q a b c := by
    unfold RicciFlow.RicciFlow.coordCurvatureOp chartCurvatureOf
    simp_rw [heqCLM]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply]
    rw [ChartCurvatureBridge.fderiv_clm_family_apply hΓ a b,
      ChartCurvatureBridge.fderiv_clm_family_apply hΓ b a]
  rw [← anchorChartRicciEntryFlow_eq_ricciAt_anchor (fun _ ↦ g) x 0 v w]
  unfold RicciFlow.RicciFlow.coordRicci anchorChartRicciEntryFlow
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg ((Module.finBasis ℝ E₃).coord i)
    (hcurv ((Module.finBasis ℝ E₃) i) v w)

omit [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N] in
/-- Bochner's formula for the actual blended metric, with its curvature
term identified with the intrinsic Ricci tensor at the anchor. -/
theorem bochner_anchorBlendedMetric
    (g : ClosedSmoothRiemannianMetric 3 N) (x : N)
    (f : E₃ → ℝ) (hf : ContDiff ℝ 3 f) :
    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
    let hsymm := CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      GeodesicTransport.backgroundMetric_symm g.inner
      (fun y a b ↦ g.inner_symm y a b) x
    let hb := fun z ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm z)
      (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 z)
    let Δ := CovariantDerivative.curvedLaplacian G
      (fun z ↦ RicciFlow.RicciFlow.metricBilin (G z)) hb
    let q := extChartAt I₃ x x
    Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
      2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q +
      2 * G q (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q)
        (RicciFlow.RicciFlow.coordGradient («E» := E₃) G (Δ f) q) +
      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q)
        (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q) := by
  intro G hsymm hb Δ q
  have hGtop : ContDiff ℝ ∞ G :=
    CovariantDerivative.contDiff_blendedChartMetric
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
      (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
  have hG : ContDiff ℝ 3 G := hGtop.of_le (WithTop.coe_le_coe.mpr le_top)
  have h := RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
    G (x := q) hG hsymm (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0) hf
  rw [coordRicci_anchorBlendedMetric g x] at h
  change Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q = _ at h
  rw [h]
  ring

set_option backward.isDefEq.respectTransparency false in
omit [SecondCountableTopology N] in
/-- Contract the intrinsic Hessian into ordinary chart derivatives at the
anchor. This version uses a scalar supported inside that chart. -/
theorem laplacianAt_eq_anchor_derivatives
    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (f : N → ℝ)
    (hs : tsupport f ⊆ (extChartAt I₃ x).source)
    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f) :
    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
    let q := extChartAt I₃ x x
    let b := Module.finBasis ℝ E₃
    g.laplacianAt f x = ∑ i,
      (fderiv ℝ (fderiv ℝ u) q (metricDualVectorAt g x (b.coord i)) (b i) -
      fderiv ℝ u q (RicciFlow.RicciFlow.christoffelClosedOp
        (CovariantDerivative.chartMetric g.inner x) q
        (metricDualVectorAt g x (b.coord i)) (b i))) := by
  intro u q b
  letI : FiniteDimensional ℝ (TangentSpace I₃ x) :=
    inferInstanceAs (FiniteDimensional ℝ E₃)
  have hD : mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ x).symm (range I₃) q =
      ContinuousLinearMap.id ℝ E₃ := by
    have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (mem_extChartAt_source («I» := I₃) x)
    rw [mfderiv_extChartAt_self] at h
    simpa [q] using h
  rw [laplacianAt_eq_sum_hessianAt g f x]
  apply Finset.sum_congr rfl
  intro i _
  rw [g.hessianAt_symm' hf.contMDiffAt]
  have h := IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
    g x f hs hf (mem_extChartAt_target x)
    (metricDualVectorAt g x (b.coord i)) (b i)
  dsimp only at h
  dsimp only [q] at hD
  rw [hD] at h
  change g.hessianAt f ((extChartAt I₃ x).symm (extChartAt I₃ x x))
    (metricDualVectorAt g x (b.coord i)) (b i) = _ at h
  have hp : (extChartAt I₃ x).symm (extChartAt I₃ x x) = x :=
    (extChartAt I₃ x).left_inv (mem_extChartAt_source x)
  have he := congrArg (fun y : N ↦ g.hessianAt f y
    (metricDualVectorAt g x (b.coord i)) (b i)) hp
  exact he.symm.trans h

end Normalized

end Poincare.ScalarGradientEvolution

namespace Poincare.ScalarGradientEvolution
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology
variable {N : Type u} [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (ClosedSmoothModel 3) N]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
local notation "I₃" => closedSmoothModelWithCorners 3
local notation "E₃" => ClosedSmoothModel 3
example (g : ClosedSmoothRiemannianMetric 3 N) (x : N)
    (hR : ContMDiff I₃ 𝓘(ℝ) 3 (fun y ↦ g.scalarAt y))
    (hcoord : ContDiff ℝ 3 (fun z : E₃ ↦ g.scalarAt ((extChartAt I₃ x).symm z))) :
    let R : N → ℝ := fun y ↦ g.scalarAt y
    let b := Module.finBasis ℝ E₃
    g.laplacianAt (fun y ↦ g.scalarGradNormSqAt y) x =
      2 * (∑ i, g.inner x (g.leviCivita (g.gradient R) x (b i))
        (g.leviCivita (g.gradient R) x (metricDualVectorAt g x (b.coord i)))) +
      2 * g.inner x (g.gradientAt R x)
        (g.gradientAt (fun y ↦ g.laplacianAt R y) x) +
      2 * g.ricciAt x (g.gradientAt R x) (g.gradientAt R x) := by
  intro R b
  have h := bochner_anchorBlendedMetric g x
    (fun z : E₃ ↦ g.scalarAt ((extChartAt I₃ x).symm z)) hcoord
  simpa only [ClosedSmoothRiemannianMetric.scalarGradNormSqAt] using h
end Poincare.ScalarGradientEvolution

```

</details>

<details>
<summary>32-regularity-and-absence.lean</summary>

```lean
import Poincare.Global.ScalarGradientEvolution
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology
#check Poincare.anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries
#check Poincare.scalarAt_contMDiffAt_two_of_normalizedRicciFlow
#check Poincare.ricciNormSqAt_mdifferentiableAt
#check Poincare.scalarAt_mdifferentiableAt
#check Poincare.SatisfiesHamiltonScalarEvolutionAt
#check Poincare.ClosedSmoothRiemannianMetric.gradient
#check Poincare.ClosedSmoothRiemannianMetric.hessianContinuousAt
#check Poincare.covRicciNormSqAt
#check Poincare.ScalarGradientEvolution.SatisfiesScalarGradientEvolutionAt

```

</details>

## Appendix C. Numbered source snapshots

The first snapshot is complete. Each later diff applies to the immediately preceding listed snapshot, preserving the actual probe sources without repeating the whole module. Blank context lines in displayed diffs omit their single space marker to pass the repository whitespace gate; restore that marker when applying a diff.

<details>
<summary>03-norm-audit.lean; SHA-256 f502395c256d2d66091f54254bd6ab9e931b4a806386fcd556d801ec1d848dbc</summary>

```lean
import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.IntrinsicLaplacianCoordinateForm

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false

universe u

namespace Poincare.ScalarGradientEvolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Differentiate the squared norm of a moving covector with the moving
inverse metric. The metric variation has a negative sign. -/
theorem hasDerivAt_covectorNormSq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    {α : ℝ → TM x →L[ℝ] ℝ} {α' : TM x →L[ℝ] ℝ}
    (hα : HasDerivAt α α' t₀) :
    HasDerivAt (fun t ↦ α t ((gt t).metricRaiseContinuousAt x (α t)))
      (2 * α' ((gt t₀).metricRaiseContinuousAt x (α t₀)) -
        timeDerivAt gt t₀ x
          ((gt t₀).metricRaiseContinuousAt x (α t₀))
          ((gt t₀).metricRaiseContinuousAt x (α t₀))) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  have hd := hα.clm_apply
    ((hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt hgt).clm_apply hα)
  apply hd.congr_deriv
  simp only [map_add]
  have hswap (v : TM x) :
      α t₀ v = (gt t₀).inner x v
        ((gt t₀).metricRaiseContinuousAt x (α t₀)) := by
    rw [(gt t₀).inner_symm]
    exact ((gt t₀).metricRaiseContinuousAt_inner_apply x (α t₀) v).symm
  rw [hswap (metricRaiseDerivAt gt t₀ x hgt (α t₀)),
    metricRaiseDerivAt_inner_apply hgt,
    hswap ((gt t₀).metricRaiseContinuousAt x α'),
    ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  ring

end Poincare.ScalarGradientEvolution

#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq

```

</details>

<details>
<summary>05-mixed-audit.lean; SHA-256 cb169add7ea89719d894e375d339e23ee0380f7bbe1b1877ff1a478e0f7b5267</summary>

```diff
--- previous-snapshot
+++ 05-mixed-audit.lean
@@ -49,6 +49,48 @@
     ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
   ring

+/-- The moving-gradient norm rule, expressed using the derivative of `df`. -/
+theorem hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
+    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
+    (hgt : TimeDifferentiableAt gt t₀ x)
+    {f : ℝ → M → ℝ} {f' : M → ℝ}
+    (hdf : HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
+      (extDerivFun f' x) t₀) :
+    HasDerivAt
+      (fun t ↦ (gt t).inner x ((gt t).gradientAt (f t) x)
+        ((gt t).gradientAt (f t) x))
+      (2 * (gt t₀).inner x ((gt t₀).gradientAt f' x)
+          ((gt t₀).gradientAt (f t₀) x) -
+        timeDerivAt gt t₀ x ((gt t₀).gradientAt (f t₀) x)
+          ((gt t₀).gradientAt (f t₀) x)) t₀ := by
+  have h := hasDerivAt_covectorNormSq hgt hdf
+  have heq (g : ClosedSmoothRiemannianMetric n M) (u : M → ℝ) :
+      g.metricRaiseContinuousAt x (extDerivFun u x) = g.gradientAt u x := rfl
+  simp_rw [heq] at h
+  simpa only [ClosedSmoothRiemannianMetric.inner_gradientAt] using h
+
+omit [T2Space M] [IsManifold I ∞ M] in
+/-- Joint second-order scalar regularity commutes the time derivative and
+the manifold differential in a fixed tangent fiber. -/
+theorem hasDerivAt_extDerivFun_of_joint_contDiffAt_two
+    {f : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
+    (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) (f t) x)
+    (hft : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ deriv (fun t ↦ f t y) t₀) x)
+    (hJoint : ContDiffAt ℝ 2
+      (fun p : ℝ × E ↦ f p.1 ((extChartAt I x).symm p.2))
+      (t₀, extChartAt I x x)) :
+    HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
+      (extDerivFun (fun y ↦ deriv (fun t ↦ f t y) t₀) x) t₀ := by
+  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
+  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
+  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
+  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
+  intro v
+  simp_rw [extDerivFun_apply_chart (hf _), extDerivFun_apply_chart hft]
+  exact hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
+    (fun t z ↦ f t ((extChartAt I x).symm z)) t₀ (extChartAt I x x) v hJoint
+
 end Poincare.ScalarGradientEvolution

-#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_covectorNormSq
+#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
+#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two

```

</details>

<details>
<summary>09-normalized-audit.lean; SHA-256 9f53e6b21d7764859d8f67f0c580ea6126236a8c8263f295efa57371ca2ac32f</summary>

```diff
--- previous-snapshot
+++ 09-normalized-audit.lean
@@ -90,7 +90,86 @@
   exact hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
     (fun t z ↦ f t ((extChartAt I x).symm z)) t₀ (extChartAt I x x) v hJoint

+section Normalized
+
+variable {N : Type u} [TopologicalSpace N] [T2Space N]
+  [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
+  [MeasurableSpace N] [BorelSpace N]
+  [ChartedSpace (ClosedSmoothModel 3) N]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
+
+local notation "I₃" => closedSmoothModelWithCorners 3
+local notation "E₃" => ClosedSmoothModel 3
+
+/-- Pointwise time variation of the scalar-gradient norm along normalized
+flow. The joint scalar and Laplacian hypotheses are explicit regularity
+requirements beyond the supplied joint metric entries. -/
+theorem hasDerivAt_scalarGradNormSq_normalizedFlow
+    {gt : ℝ → ClosedSmoothRiemannianMetric 3 N} {t₀ : ℝ} {x : N}
+    (hJoint : ∀ t y, MetricEntriesJointContDiffAt gt t y 3)
+    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
+    (hScalarJoint : ContDiffAt ℝ 2
+      (fun p : ℝ × E₃ ↦ (gt p.1).scalarAt ((extChartAt I₃ x).symm p.2))
+      (t₀, extChartAt I₃ x x))
+    (hLap : MDifferentiableAt I₃ 𝓘(ℝ)
+      (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) :
+    HasDerivAt (fun t ↦ (gt t).scalarGradNormSqAt x)
+      (2 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
+          ((gt t₀).gradientAt
+            (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) +
+        4 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
+          ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x) +
+        2 * (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
+          ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x) -
+        2 * meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x) t₀ := by
+  letI : Nonempty N := ⟨x⟩
+  let g := gt t₀
+  let R : N → ℝ := fun y ↦ g.scalarAt y
+  let A : N → ℝ := fun y ↦ g.ricciNormSqAt y
+  let L : N → ℝ := fun y ↦ g.laplacianAt R y
+  let c : ℝ := -(2 / 3 : ℝ) * meanScalar g
+  have hR : MDifferentiableAt I₃ 𝓘(ℝ) R x := scalarAt_mdifferentiableAt g x
+  have hA : MDifferentiableAt I₃ 𝓘(ℝ) A x := ricciNormSqAt_mdifferentiableAt g x
+  have hL : MDifferentiableAt I₃ 𝓘(ℝ) L x := hLap
+  have heq : (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) =
+      L + (2 : ℝ) • A + c • R := by
+    funext y
+    have hs : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ y :=
+      satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
+        hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
+    rw [hs.deriv]
+    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, L, A, R, c, g]
+    ring
+  have h2A : MDifferentiableAt I₃ 𝓘(ℝ) ((2 : ℝ) • A) x := by
+    exact mdifferentiableAt_const.smul hA
+  have hcR : MDifferentiableAt I₃ 𝓘(ℝ) (c • R) x := by
+    exact mdifferentiableAt_const.smul hR
+  have hft : MDifferentiableAt I₃ 𝓘(ℝ)
+      (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) x := by
+    rw [heq]
+    exact (hL.add h2A).add hcR
+  have hd := hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
+    (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
+      ((hJoint t₀ x).of_le (by norm_num)))
+    (hasDerivAt_extDerivFun_of_joint_contDiffAt_two
+      (fun t ↦ scalarAt_mdifferentiableAt (gt t) x) hft hScalarJoint)
+  rw [heq, g.gradientAt_add (hL.add h2A) hcR,
+    g.gradientAt_add hL h2A,
+    g.gradientAt_const_smul 2 hA, g.gradientAt_const_smul c hR] at hd
+  apply hd.congr_deriv
+  rw [isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
+    (hFlow x)]
+  simp only [normalizedRicciFlowRHSAt, map_add, map_smul,
+    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
+  simp only [ClosedSmoothRiemannianMetric.scalarGradNormSqAt, R, A, L, c, g]
+  rw [(gt t₀).inner_symm x ((gt t₀).gradientAt
+    (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x),
+    (gt t₀).inner_symm x ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x)]
+  ring
+
+end Normalized
+
 end Poincare.ScalarGradientEvolution

-#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
-#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_extDerivFun_of_joint_contDiffAt_two
+#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow
+#print Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow

```

</details>

<details>
<summary>11-ricci-bridge.lean; SHA-256 96a7d27d37d481a5b3d3eb061506e1b8ed445719239a4cec5b6791f9da86e924</summary>

```diff
--- previous-snapshot
+++ 11-ricci-bridge.lean
@@ -167,9 +167,45 @@
     (gt t₀).inner_symm x ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x)]
   ring

+omit [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
+  [MeasurableSpace N] [BorelSpace N] in
+/-- The Ricci term in the coordinate Bochner formula is the intrinsic Ricci
+tensor at the chart anchor, with the same curvature sign. -/
+theorem coordRicci_anchorBlendedMetric
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (v w : E₃) :
+    RicciFlow.RicciFlow.coordRicci (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
+      (extChartAt I₃ x x) v w = g.ricciAt x v w := by
+  let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
+  let Γ := GeodesicTransport.chartChristoffelField g x
+  let q := extChartAt I₃ x x
+  have hΓ : DifferentiableAt ℝ Γ q :=
+    (GeodesicTransport.chartChristoffelField_contDiff_top g x).differentiable
+      (by simp) q
+  have heq (z a b : E₃) :
+      RicciFlow.RicciFlow.christoffelClosedOp G z a b = Γ z a b := by
+    rw [show Γ z a b = Γ z b a from chartChristoffelField_symm g x z a b]
+    exact RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt G _ _
+      (fun _ _ ↦ rfl) a b
+  have heqCLM (z a : E₃) :
+      RicciFlow.RicciFlow.christoffelClosedOp G z a = Γ z a := by
+    ext b
+    exact heq z a b
+  have hcurv (a b c : E₃) :
+      RicciFlow.RicciFlow.coordCurvatureOp G q a b c =
+        chartCurvatureOf Γ q a b c := by
+    unfold RicciFlow.RicciFlow.coordCurvatureOp chartCurvatureOf
+    simp_rw [heqCLM]
+    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
+      ContinuousLinearMap.comp_apply]
+    rw [ChartCurvatureBridge.fderiv_clm_family_apply hΓ a b,
+      ChartCurvatureBridge.fderiv_clm_family_apply hΓ b a]
+  rw [← anchorChartRicciEntryFlow_eq_ricciAt_anchor (fun _ ↦ g) x 0 v w]
+  unfold RicciFlow.RicciFlow.coordRicci anchorChartRicciEntryFlow
+  apply Finset.sum_congr rfl
+  intro i _
+  exact congrArg ((Module.finBasis ℝ E₃).coord i)
+    (hcurv ((Module.finBasis ℝ E₃) i) v w)
+
 end Normalized

 end Poincare.ScalarGradientEvolution
-
-#print axioms Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow
-#print Poincare.ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow

```

</details>

<details>
<summary>12-ricci-bridge.lean; SHA-256 513910f57d26d9bf05ec1e540fce5d48100c4601789ed1c1182f5fdada186e93</summary>

```diff
--- previous-snapshot
+++ 12-ricci-bridge.lean
@@ -184,11 +184,18 @@
   have heq (z a b : E₃) :
       RicciFlow.RicciFlow.christoffelClosedOp G z a b = Γ z a b := by
     rw [show Γ z a b = Γ z b a from chartChristoffelField_symm g x z a b]
-    exact RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt G _ _
+    exact RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt G _
+      (CovariantDerivative.chartBilin_nondegenerate
+        (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
+        GeodesicTransport.backgroundMetric_pos g.inner
+        (fun y u hu ↦ g.inner_pos y hu) x
+        (GeodesicTransport.cutoff_nonneg x) (GeodesicTransport.cutoff_le_one x)
+        (GeodesicTransport.cutoff_support_invertible x) z)
       (fun _ _ ↦ rfl) a b
   have heqCLM (z a : E₃) :
       RicciFlow.RicciFlow.christoffelClosedOp G z a = Γ z a := by
-    ext b
+    apply ContinuousLinearMap.ext
+    intro b
     exact heq z a b
   have hcurv (a b c : E₃) :
       RicciFlow.RicciFlow.coordCurvatureOp G q a b c =

```

</details>

<details>
<summary>13-ricci-audit.lean; SHA-256 39e3b174ef5f724d63f5322ae5e61901451b8edca36c07e1de5f78df9b57b937</summary>

```diff
--- previous-snapshot
+++ 13-ricci-audit.lean
@@ -216,3 +216,5 @@
 end Normalized

 end Poincare.ScalarGradientEvolution
+
+#print axioms Poincare.ScalarGradientEvolution.coordRicci_anchorBlendedMetric

```

</details>

<details>
<summary>14-bochner.lean; SHA-256 841fbcd34cc9448730315894f1f2892d0eb0754a552ed1948f97953b724ff006</summary>

```diff
--- previous-snapshot
+++ 14-bochner.lean
@@ -213,8 +213,43 @@
   exact congrArg ((Module.finBasis ℝ E₃).coord i)
     (hcurv ((Module.finBasis ℝ E₃) i) v w)

+omit [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
+  [MeasurableSpace N] [BorelSpace N] in
+/-- Bochner's formula for the actual blended metric, with its curvature
+term identified with the intrinsic Ricci tensor at the anchor. -/
+theorem bochner_anchorBlendedMetric
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N)
+    (f : E₃ → ℝ) (hf : ContDiff ℝ 3 f) :
+    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
+    let hsymm := CovariantDerivative.blendedChartMetric_symm
+      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
+      GeodesicTransport.backgroundMetric_symm g.inner
+      (fun y a b ↦ g.inner_symm y a b) x
+    let hb := fun z ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm z)
+      (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 z)
+    let Δ := CovariantDerivative.curvedLaplacian G
+      (fun z ↦ RicciFlow.RicciFlow.metricBilin (G z)) hb
+    let q := extChartAt I₃ x x
+    Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
+      2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q +
+      2 * G q (RicciFlow.RicciFlow.coordGradient G f q)
+        (RicciFlow.RicciFlow.coordGradient G (Δ f) q) +
+      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient G f q)
+        (RicciFlow.RicciFlow.coordGradient G f q) := by
+  intro G hsymm hb Δ q
+  have hGtop : ContDiff ℝ ∞ G :=
+    CovariantDerivative.contDiff_blendedChartMetric
+      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
+      g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
+      (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
+  have hG : ContDiff ℝ 3 G := hGtop.of_le (by norm_num)
+  have h := RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
+    G (x := q) hG hsymm (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0) hf
+  rw [coordRicci_anchorBlendedMetric g x] at h
+  change Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q = _ at h
+  rw [h]
+  ring
+
 end Normalized

 end Poincare.ScalarGradientEvolution
-
-#print axioms Poincare.ScalarGradientEvolution.coordRicci_anchorBlendedMetric

```

</details>

<details>
<summary>15-bochner.lean; SHA-256 7d5c42741a1d877e44c8f59a02c2884375aa370dfb93e012c1bd57ec8de79359</summary>

```diff
--- previous-snapshot
+++ 15-bochner.lean
@@ -232,17 +232,17 @@
     let q := extChartAt I₃ x x
     Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
       2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q +
-      2 * G q (RicciFlow.RicciFlow.coordGradient G f q)
-        (RicciFlow.RicciFlow.coordGradient G (Δ f) q) +
-      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient G f q)
-        (RicciFlow.RicciFlow.coordGradient G f q) := by
+      2 * G q (RicciFlow.RicciFlow.coordGradient (E := E₃) G f q)
+        (RicciFlow.RicciFlow.coordGradient (E := E₃) G (Δ f) q) +
+      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient (E := E₃) G f q)
+        (RicciFlow.RicciFlow.coordGradient (E := E₃) G f q) := by
   intro G hsymm hb Δ q
   have hGtop : ContDiff ℝ ∞ G :=
     CovariantDerivative.contDiff_blendedChartMetric
       (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
       g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
       (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
-  have hG : ContDiff ℝ 3 G := hGtop.of_le (by norm_num)
+  have hG : ContDiff ℝ 3 G := hGtop.of_le (WithTop.coe_le_coe.mpr le_top)
   have h := RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
     G (x := q) hG hsymm (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0) hf
   rw [coordRicci_anchorBlendedMetric g x] at h

```

</details>

<details>
<summary>16-bochner.lean; SHA-256 a6c9621384d649c6f31577a51fde82be10bffc2b56e21df3acf154d6c0ae8e2b</summary>

```diff
--- previous-snapshot
+++ 16-bochner.lean
@@ -232,10 +232,10 @@
     let q := extChartAt I₃ x x
     Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
       2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q +
-      2 * G q (RicciFlow.RicciFlow.coordGradient (E := E₃) G f q)
-        (RicciFlow.RicciFlow.coordGradient (E := E₃) G (Δ f) q) +
-      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient (E := E₃) G f q)
-        (RicciFlow.RicciFlow.coordGradient (E := E₃) G f q) := by
+      2 * G q (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q)
+        (RicciFlow.RicciFlow.coordGradient («E» := E₃) G (Δ f) q) +
+      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q)
+        (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q) := by
   intro G hsymm hb Δ q
   have hGtop : ContDiff ℝ ∞ G :=
     CovariantDerivative.contDiff_blendedChartMetric

```

</details>

<details>
<summary>17-laplacian.lean; SHA-256 f2865d0ac5847be577b8c884ef008e74030e451c7e152bb1bcbbdb662b58cdc1</summary>

```diff
--- previous-snapshot
+++ 17-laplacian.lean
@@ -250,6 +250,41 @@
   rw [h]
   ring

+omit [SecondCountableTopology N] in
+/-- Contract the intrinsic Hessian into ordinary chart derivatives at the
+anchor. This version uses a scalar supported inside that chart. -/
+theorem laplacianAt_eq_anchor_derivatives
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (f : N → ℝ)
+    (hs : tsupport f ⊆ (extChartAt I₃ x).source)
+    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f) :
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
+    let q := extChartAt I₃ x x
+    let b := Module.finBasis ℝ E₃
+    g.laplacianAt f x = ∑ i,
+      fderiv ℝ (fderiv ℝ u) q (metricDualVectorAt g x (b.coord i)) (b i) -
+      fderiv ℝ u q (RicciFlow.RicciFlow.christoffelClosedOp
+        (CovariantDerivative.chartMetric g.inner x) q
+        (metricDualVectorAt g x (b.coord i)) (b i)) := by
+  intro u q b
+  letI : FiniteDimensional ℝ (TangentSpace I₃ x) :=
+    inferInstanceAs (FiniteDimensional ℝ E₃)
+  have hD : mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ x).symm (range I₃) q =
+      ContinuousLinearMap.id ℝ E₃ := by
+    have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
+      (mem_extChartAt_source (I := I₃) x)
+    rw [mfderiv_extChartAt_self] at h
+    simpa [q] using h
+  rw [laplacianAt_eq_sum_hessianAt g f x]
+  apply Finset.sum_congr rfl
+  intro i _
+  rw [g.hessianAt_symm' hf.contMDiffAt]
+  have h := IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
+    g x f hs hf (mem_extChartAt_target x)
+    (metricDualVectorAt g x (b.coord i)) (b i)
+  dsimp only at h
+  simpa only [hD, ContinuousLinearMap.id_apply,
+    (extChartAt I₃ x).left_inv (mem_extChartAt_source x)] using h
+
 end Normalized

 end Poincare.ScalarGradientEvolution

```

</details>

<details>
<summary>18-bochner-audit.lean; SHA-256 d1ef7b571f142fca47a13da0737c869e5b62188850d3e57cd5dc83a2d34f8d30</summary>

```diff
--- previous-snapshot
+++ 18-bochner-audit.lean
@@ -250,41 +250,8 @@
   rw [h]
   ring

-omit [SecondCountableTopology N] in
-/-- Contract the intrinsic Hessian into ordinary chart derivatives at the
-anchor. This version uses a scalar supported inside that chart. -/
-theorem laplacianAt_eq_anchor_derivatives
-    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (f : N → ℝ)
-    (hs : tsupport f ⊆ (extChartAt I₃ x).source)
-    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f) :
-    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
-    let q := extChartAt I₃ x x
-    let b := Module.finBasis ℝ E₃
-    g.laplacianAt f x = ∑ i,
-      fderiv ℝ (fderiv ℝ u) q (metricDualVectorAt g x (b.coord i)) (b i) -
-      fderiv ℝ u q (RicciFlow.RicciFlow.christoffelClosedOp
-        (CovariantDerivative.chartMetric g.inner x) q
-        (metricDualVectorAt g x (b.coord i)) (b i)) := by
-  intro u q b
-  letI : FiniteDimensional ℝ (TangentSpace I₃ x) :=
-    inferInstanceAs (FiniteDimensional ℝ E₃)
-  have hD : mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ x).symm (range I₃) q =
-      ContinuousLinearMap.id ℝ E₃ := by
-    have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
-      (mem_extChartAt_source (I := I₃) x)
-    rw [mfderiv_extChartAt_self] at h
-    simpa [q] using h
-  rw [laplacianAt_eq_sum_hessianAt g f x]
-  apply Finset.sum_congr rfl
-  intro i _
-  rw [g.hessianAt_symm' hf.contMDiffAt]
-  have h := IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
-    g x f hs hf (mem_extChartAt_target x)
-    (metricDualVectorAt g x (b.coord i)) (b i)
-  dsimp only at h
-  simpa only [hD, ContinuousLinearMap.id_apply,
-    (extChartAt I₃ x).left_inv (mem_extChartAt_source x)] using h
-
 end Normalized

 end Poincare.ScalarGradientEvolution
+
+#print axioms Poincare.ScalarGradientEvolution.bochner_anchorBlendedMetric

```

</details>

<details>
<summary>19-laplacian.lean; SHA-256 e157bee8a713a3dd853ea95bc73076eada58f940d05df9f1d3a9430d5942fb35</summary>

```diff
--- previous-snapshot
+++ 19-laplacian.lean
@@ -250,8 +250,41 @@
   rw [h]
   ring

+omit [SecondCountableTopology N] in
+/-- Contract the intrinsic Hessian into ordinary chart derivatives at the
+anchor. This version uses a scalar supported inside that chart. -/
+theorem laplacianAt_eq_anchor_derivatives
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (f : N → ℝ)
+    (hs : tsupport f ⊆ (extChartAt I₃ x).source)
+    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f) :
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
+    let q := extChartAt I₃ x x
+    let b := Module.finBasis ℝ E₃
+    g.laplacianAt f x = ∑ i,
+      (fderiv ℝ (fderiv ℝ u) q (metricDualVectorAt g x (b.coord i)) (b i) -
+      fderiv ℝ u q (RicciFlow.RicciFlow.christoffelClosedOp
+        (CovariantDerivative.chartMetric g.inner x) q
+        (metricDualVectorAt g x (b.coord i)) (b i))) := by
+  intro u q b
+  letI : FiniteDimensional ℝ (TangentSpace I₃ x) :=
+    inferInstanceAs (FiniteDimensional ℝ E₃)
+  have hD : mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ x).symm (range I₃) q =
+      ContinuousLinearMap.id ℝ E₃ := by
+    have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
+      (mem_extChartAt_source («I» := I₃) x)
+    rw [mfderiv_extChartAt_self] at h
+    simpa [q] using h
+  rw [laplacianAt_eq_sum_hessianAt g f x]
+  apply Finset.sum_congr rfl
+  intro i _
+  rw [g.hessianAt_symm' hf.contMDiffAt]
+  have h := IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
+    g x f hs hf (mem_extChartAt_target x)
+    (metricDualVectorAt g x (b.coord i)) (b i)
+  dsimp only at h
+  simpa only [hD, ContinuousLinearMap.id_apply,
+    (extChartAt I₃ x).left_inv (mem_extChartAt_source x)] using h
+
 end Normalized

 end Poincare.ScalarGradientEvolution
-
-#print axioms Poincare.ScalarGradientEvolution.bochner_anchorBlendedMetric

```

</details>

<details>
<summary>20-laplacian.lean; SHA-256 17da34e7f40872d3520c80758e76fdba01fb0104cb89a587326ba4ad4fd705cc</summary>

```diff
--- previous-snapshot
+++ 20-laplacian.lean
@@ -282,8 +282,9 @@
     g x f hs hf (mem_extChartAt_target x)
     (metricDualVectorAt g x (b.coord i)) (b i)
   dsimp only at h
-  simpa only [hD, ContinuousLinearMap.id_apply,
-    (extChartAt I₃ x).left_inv (mem_extChartAt_source x)] using h
+  dsimp only [q] at hD
+  rw [hD] at h
+  simpa [u, q, b, (extChartAt I₃ x).left_inv (mem_extChartAt_source x)] using h

 end Normalized


```

</details>

<details>
<summary>21-laplacian.lean; SHA-256 1d6f3b5e647186fa62003a5493a6a76db55497fb7b28043ae050d85a0b8a9522</summary>

```diff
--- previous-snapshot
+++ 21-laplacian.lean
@@ -283,8 +283,9 @@
     (metricDualVectorAt g x (b.coord i)) (b i)
   dsimp only at h
   dsimp only [q] at hD
-  rw [hD] at h
-  simpa [u, q, b, (extChartAt I₃ x).left_inv (mem_extChartAt_source x)] using h
+  rw [hD, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply] at h
+  rw [(extChartAt I₃ x).left_inv (mem_extChartAt_source x)] at h
+  exact h

 end Normalized


```

</details>

<details>
<summary>22-laplacian-audit.lean; SHA-256 5f1ef1351e338d959a4750f23ef13f0e5587044ccfe4bd54a57256aea58c0ae1</summary>

```diff
--- previous-snapshot
+++ 22-laplacian-audit.lean
@@ -290,3 +290,5 @@
 end Normalized

 end Poincare.ScalarGradientEvolution
+
+#print axioms Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives

```

</details>

<details>
<summary>23-laplacian.lean; SHA-256 eac90ca1db237cb0ab6ec5a3cf2574312479220991abb351b05c0a21f251f0dd</summary>

```diff
--- previous-snapshot
+++ 23-laplacian.lean
@@ -250,6 +250,7 @@
   rw [h]
   ring

+set_option backward.isDefEq.respectTransparency false in
 omit [SecondCountableTopology N] in
 /-- Contract the intrinsic Hessian into ordinary chart derivatives at the
 anchor. This version uses a scalar supported inside that chart. -/
@@ -290,5 +291,3 @@
 end Normalized

 end Poincare.ScalarGradientEvolution
-
-#print axioms Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives

```

</details>

<details>
<summary>24-laplacian.lean; SHA-256 4d4a3e1bea342d52d00dd2069cb6a5d2617e3764eccad7c873bcd64e962420c3</summary>

```diff
--- previous-snapshot
+++ 24-laplacian.lean
@@ -284,9 +284,14 @@
     (metricDualVectorAt g x (b.coord i)) (b i)
   dsimp only at h
   dsimp only [q] at hD
-  rw [hD, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply] at h
-  rw [(extChartAt I₃ x).left_inv (mem_extChartAt_source x)] at h
-  exact h
+  rw [hD] at h
+  change g.hessianAt f ((extChartAt I₃ x).symm (extChartAt I₃ x x))
+    (metricDualVectorAt g x (b.coord i)) (b i) = _ at h
+  have hp : (extChartAt I₃ x).symm (extChartAt I₃ x x) = x :=
+    (extChartAt I₃ x).left_inv (mem_extChartAt_source x)
+  have he := congrArg (fun y : N ↦ g.hessianAt f y
+    (metricDualVectorAt g x (b.coord i)) (b i)) hp
+  exact he.symm.trans h

 end Normalized


```

</details>

<details>
<summary>25-laplacian-audit.lean; SHA-256 2843ca48439e8ee2232477e967a14a4713224047d7cda8a3edc0ab7fd931ac2a</summary>

```diff
--- previous-snapshot
+++ 25-laplacian-audit.lean
@@ -296,3 +296,5 @@
 end Normalized

 end Poincare.ScalarGradientEvolution
+
+#print axioms Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives

```

</details>

<details>
<summary>29-no-notation.lean; SHA-256 5ea8370a46466b36b1047fcad32fd7658e43c65b04b3fa22226c5b52dd1d3558</summary>

```diff
--- previous-snapshot
+++ 29-no-notation.lean
@@ -16,29 +16,26 @@
   [ChartedSpace (ClosedSmoothModel n) M]
   [IsManifold (closedSmoothModelWithCorners n) ∞ M]

-local notation "I" => closedSmoothModelWithCorners n
-local notation "E" => ClosedSmoothModel n
-local notation "TM" => (TangentSpace I : M → Type _)

 /-- Differentiate the squared norm of a moving covector with the moving
 inverse metric. The metric variation has a negative sign. -/
 theorem hasDerivAt_covectorNormSq
     {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
     (hgt : TimeDifferentiableAt gt t₀ x)
-    {α : ℝ → TM x →L[ℝ] ℝ} {α' : TM x →L[ℝ] ℝ}
+    {α : ℝ → (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ} {α' : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ}
     (hα : HasDerivAt α α' t₀) :
     HasDerivAt (fun t ↦ α t ((gt t).metricRaiseContinuousAt x (α t)))
       (2 * α' ((gt t₀).metricRaiseContinuousAt x (α t₀)) -
         timeDerivAt gt t₀ x
           ((gt t₀).metricRaiseContinuousAt x (α t₀))
           ((gt t₀).metricRaiseContinuousAt x (α t₀))) t₀ := by
-  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
-  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
+  letI : NormedAddCommGroup ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedAddCommGroup (ClosedSmoothModel n))
+  letI : NormedSpace ℝ ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedSpace ℝ (ClosedSmoothModel n))
   have hd := hα.clm_apply
     ((hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt hgt).clm_apply hα)
   apply hd.congr_deriv
   simp only [map_add]
-  have hswap (v : TM x) :
+  have hswap (v : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) :
       α t₀ v = (gt t₀).inner x v
         ((gt t₀).metricRaiseContinuousAt x (α t₀)) := by
     rw [(gt t₀).inner_symm]
@@ -54,7 +51,7 @@
     {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
     (hgt : TimeDifferentiableAt gt t₀ x)
     {f : ℝ → M → ℝ} {f' : M → ℝ}
-    (hdf : HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
+    (hdf : HasDerivAt (fun t ↦ (extDerivFun (f t) x : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ))
       (extDerivFun f' x) t₀) :
     HasDerivAt
       (fun t ↦ (gt t).inner x ((gt t).gradientAt (f t) x)
@@ -69,26 +66,26 @@
   simp_rw [heq] at h
   simpa only [ClosedSmoothRiemannianMetric.inner_gradientAt] using h

-omit [T2Space M] [IsManifold I ∞ M] in
+omit [T2Space M] [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
 /-- Joint second-order scalar regularity commutes the time derivative and
 the manifold differential in a fixed tangent fiber. -/
 theorem hasDerivAt_extDerivFun_of_joint_contDiffAt_two
     {f : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
-    (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) (f t) x)
-    (hft : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ deriv (fun t ↦ f t y) t₀) x)
+    (hf : ∀ t, MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (f t) x)
+    (hft : MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (fun y ↦ deriv (fun t ↦ f t y) t₀) x)
     (hJoint : ContDiffAt ℝ 2
-      (fun p : ℝ × E ↦ f p.1 ((extChartAt I x).symm p.2))
-      (t₀, extChartAt I x x)) :
-    HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
+      (fun p : ℝ × (ClosedSmoothModel n) ↦ f p.1 ((extChartAt (closedSmoothModelWithCorners n) x).symm p.2))
+      (t₀, extChartAt (closedSmoothModelWithCorners n) x x)) :
+    HasDerivAt (fun t ↦ (extDerivFun (f t) x : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ))
       (extDerivFun (fun y ↦ deriv (fun t ↦ f t y) t₀) x) t₀ := by
-  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
-  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
-  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
+  letI : NormedAddCommGroup ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedAddCommGroup (ClosedSmoothModel n))
+  letI : NormedSpace ℝ ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedSpace ℝ (ClosedSmoothModel n))
+  letI : FiniteDimensional ℝ ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel n))
   apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
   intro v
   simp_rw [extDerivFun_apply_chart (hf _), extDerivFun_apply_chart hft]
   exact hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
-    (fun t z ↦ f t ((extChartAt I x).symm z)) t₀ (extChartAt I x x) v hJoint
+    (fun t z ↦ f t ((extChartAt (closedSmoothModelWithCorners n) x).symm z)) t₀ (extChartAt (closedSmoothModelWithCorners n) x x) v hJoint

 section Normalized

@@ -98,8 +95,6 @@
   [ChartedSpace (ClosedSmoothModel 3) N]
   [IsManifold (closedSmoothModelWithCorners 3) ∞ N]

-local notation "I₃" => closedSmoothModelWithCorners 3
-local notation "E₃" => ClosedSmoothModel 3

 /-- Pointwise time variation of the scalar-gradient norm along normalized
 flow. The joint scalar and Laplacian hypotheses are explicit regularity
@@ -109,9 +104,9 @@
     (hJoint : ∀ t y, MetricEntriesJointContDiffAt gt t y 3)
     (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
     (hScalarJoint : ContDiffAt ℝ 2
-      (fun p : ℝ × E₃ ↦ (gt p.1).scalarAt ((extChartAt I₃ x).symm p.2))
-      (t₀, extChartAt I₃ x x))
-    (hLap : MDifferentiableAt I₃ 𝓘(ℝ)
+      (fun p : ℝ × (ClosedSmoothModel 3) ↦ (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
+      (t₀, extChartAt (closedSmoothModelWithCorners 3) x x))
+    (hLap : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
       (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) :
     HasDerivAt (fun t ↦ (gt t).scalarGradNormSqAt x)
       (2 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
@@ -128,9 +123,9 @@
   let A : N → ℝ := fun y ↦ g.ricciNormSqAt y
   let L : N → ℝ := fun y ↦ g.laplacianAt R y
   let c : ℝ := -(2 / 3 : ℝ) * meanScalar g
-  have hR : MDifferentiableAt I₃ 𝓘(ℝ) R x := scalarAt_mdifferentiableAt g x
-  have hA : MDifferentiableAt I₃ 𝓘(ℝ) A x := ricciNormSqAt_mdifferentiableAt g x
-  have hL : MDifferentiableAt I₃ 𝓘(ℝ) L x := hLap
+  have hR : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) R x := scalarAt_mdifferentiableAt g x
+  have hA : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) A x := ricciNormSqAt_mdifferentiableAt g x
+  have hL : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) L x := hLap
   have heq : (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) =
       L + (2 : ℝ) • A + c • R := by
     funext y
@@ -140,11 +135,11 @@
     rw [hs.deriv]
     simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, L, A, R, c, g]
     ring
-  have h2A : MDifferentiableAt I₃ 𝓘(ℝ) ((2 : ℝ) • A) x := by
+  have h2A : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) ((2 : ℝ) • A) x := by
     exact mdifferentiableAt_const.smul hA
-  have hcR : MDifferentiableAt I₃ 𝓘(ℝ) (c • R) x := by
+  have hcR : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) (c • R) x := by
     exact mdifferentiableAt_const.smul hR
-  have hft : MDifferentiableAt I₃ 𝓘(ℝ)
+  have hft : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
       (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) x := by
     rw [heq]
     exact (hL.add h2A).add hcR
@@ -172,16 +167,16 @@
 /-- The Ricci term in the coordinate Bochner formula is the intrinsic Ricci
 tensor at the chart anchor, with the same curvature sign. -/
 theorem coordRicci_anchorBlendedMetric
-    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (v w : E₃) :
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (v w : (ClosedSmoothModel 3)) :
     RicciFlow.RicciFlow.coordRicci (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
-      (extChartAt I₃ x x) v w = g.ricciAt x v w := by
+      (extChartAt (closedSmoothModelWithCorners 3) x x) v w = g.ricciAt x v w := by
   let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
   let Γ := GeodesicTransport.chartChristoffelField g x
-  let q := extChartAt I₃ x x
+  let q := extChartAt (closedSmoothModelWithCorners 3) x x
   have hΓ : DifferentiableAt ℝ Γ q :=
     (GeodesicTransport.chartChristoffelField_contDiff_top g x).differentiable
       (by simp) q
-  have heq (z a b : E₃) :
+  have heq (z a b : (ClosedSmoothModel 3)) :
       RicciFlow.RicciFlow.christoffelClosedOp G z a b = Γ z a b := by
     rw [show Γ z a b = Γ z b a from chartChristoffelField_symm g x z a b]
     exact RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt G _
@@ -192,12 +187,12 @@
         (GeodesicTransport.cutoff_nonneg x) (GeodesicTransport.cutoff_le_one x)
         (GeodesicTransport.cutoff_support_invertible x) z)
       (fun _ _ ↦ rfl) a b
-  have heqCLM (z a : E₃) :
+  have heqCLM (z a : (ClosedSmoothModel 3)) :
       RicciFlow.RicciFlow.christoffelClosedOp G z a = Γ z a := by
     apply ContinuousLinearMap.ext
     intro b
     exact heq z a b
-  have hcurv (a b c : E₃) :
+  have hcurv (a b c : (ClosedSmoothModel 3)) :
       RicciFlow.RicciFlow.coordCurvatureOp G q a b c =
         chartCurvatureOf Γ q a b c := by
     unfold RicciFlow.RicciFlow.coordCurvatureOp chartCurvatureOf
@@ -210,8 +205,8 @@
   unfold RicciFlow.RicciFlow.coordRicci anchorChartRicciEntryFlow
   apply Finset.sum_congr rfl
   intro i _
-  exact congrArg ((Module.finBasis ℝ E₃).coord i)
-    (hcurv ((Module.finBasis ℝ E₃) i) v w)
+  exact congrArg ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)
+    (hcurv ((Module.finBasis ℝ (ClosedSmoothModel 3)) i) v w)

 omit [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
   [MeasurableSpace N] [BorelSpace N] in
@@ -219,7 +214,7 @@
 term identified with the intrinsic Ricci tensor at the anchor. -/
 theorem bochner_anchorBlendedMetric
     (g : ClosedSmoothRiemannianMetric 3 N) (x : N)
-    (f : E₃ → ℝ) (hf : ContDiff ℝ 3 f) :
+    (f : (ClosedSmoothModel 3) → ℝ) (hf : ContDiff ℝ 3 f) :
     let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
     let hsymm := CovariantDerivative.blendedChartMetric_symm
       (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
@@ -229,13 +224,13 @@
       (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 z)
     let Δ := CovariantDerivative.curvedLaplacian G
       (fun z ↦ RicciFlow.RicciFlow.metricBilin (G z)) hb
-    let q := extChartAt I₃ x x
+    let q := extChartAt (closedSmoothModelWithCorners 3) x x
     Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
       2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q +
-      2 * G q (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q)
-        (RicciFlow.RicciFlow.coordGradient («E» := E₃) G (Δ f) q) +
-      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q)
-        (RicciFlow.RicciFlow.coordGradient («E» := E₃) G f q) := by
+      2 * G q (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G f q)
+        (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G (Δ f) q) +
+      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G f q)
+        (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G f q) := by
   intro G hsymm hb Δ q
   have hGtop : ContDiff ℝ ∞ G :=
     CovariantDerivative.contDiff_blendedChartMetric
@@ -256,23 +251,23 @@
 anchor. This version uses a scalar supported inside that chart. -/
 theorem laplacianAt_eq_anchor_derivatives
     (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (f : N → ℝ)
-    (hs : tsupport f ⊆ (extChartAt I₃ x).source)
-    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f) :
+    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
+    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
     let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
-    let q := extChartAt I₃ x x
-    let b := Module.finBasis ℝ E₃
+    let q := extChartAt (closedSmoothModelWithCorners 3) x x
+    let b := Module.finBasis ℝ (ClosedSmoothModel 3)
     g.laplacianAt f x = ∑ i,
       (fderiv ℝ (fderiv ℝ u) q (metricDualVectorAt g x (b.coord i)) (b i) -
       fderiv ℝ u q (RicciFlow.RicciFlow.christoffelClosedOp
         (CovariantDerivative.chartMetric g.inner x) q
         (metricDualVectorAt g x (b.coord i)) (b i))) := by
   intro u q b
-  letI : FiniteDimensional ℝ (TangentSpace I₃ x) :=
-    inferInstanceAs (FiniteDimensional ℝ E₃)
-  have hD : mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ x).symm (range I₃) q =
-      ContinuousLinearMap.id ℝ E₃ := by
+  letI : FiniteDimensional ℝ (TangentSpace (closedSmoothModelWithCorners 3) x) :=
+    inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel 3))
+  have hD : mfderivWithin 𝓘(ℝ, (ClosedSmoothModel 3)) (closedSmoothModelWithCorners 3) (extChartAt (closedSmoothModelWithCorners 3) x).symm (range (closedSmoothModelWithCorners 3)) q =
+      ContinuousLinearMap.id ℝ (ClosedSmoothModel 3) := by
     have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
-      (mem_extChartAt_source («I» := I₃) x)
+      (mem_extChartAt_source («I» := (closedSmoothModelWithCorners 3)) x)
     rw [mfderiv_extChartAt_self] at h
     simpa [q] using h
   rw [laplacianAt_eq_sum_hessianAt g f x]
@@ -285,10 +280,10 @@
   dsimp only at h
   dsimp only [q] at hD
   rw [hD] at h
-  change g.hessianAt f ((extChartAt I₃ x).symm (extChartAt I₃ x x))
+  change g.hessianAt f ((extChartAt (closedSmoothModelWithCorners 3) x).symm (extChartAt (closedSmoothModelWithCorners 3) x x))
     (metricDualVectorAt g x (b.coord i)) (b i) = _ at h
-  have hp : (extChartAt I₃ x).symm (extChartAt I₃ x x) = x :=
-    (extChartAt I₃ x).left_inv (mem_extChartAt_source x)
+  have hp : (extChartAt (closedSmoothModelWithCorners 3) x).symm (extChartAt (closedSmoothModelWithCorners 3) x x) = x :=
+    (extChartAt (closedSmoothModelWithCorners 3) x).left_inv (mem_extChartAt_source x)
   have he := congrArg (fun y : N ↦ g.hessianAt f y
     (metricDualVectorAt g x (b.coord i)) (b i)) hp
   exact he.symm.trans h
@@ -296,5 +291,3 @@
 end Normalized

 end Poincare.ScalarGradientEvolution
-
-#print axioms Poincare.ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives

```

</details>

## Appendix D. Final proof diff against the base

```diff
diff --git a/Poincare/Global/ScalarGradientEvolution.lean b/Poincare/Global/ScalarGradientEvolution.lean
new file mode 100644
index 00000000..0648989d
--- /dev/null
+++ b/Poincare/Global/ScalarGradientEvolution.lean
@@ -0,0 +1,293 @@
+import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
+import Poincare.Global.IntrinsicLaplacianCoordinateForm
+
+noncomputable section
+
+open Bundle FiberBundle Filter Set
+open scoped Manifold ContDiff Topology
+
+set_option autoImplicit false
+
+universe u
+
+namespace Poincare.ScalarGradientEvolution
+
+variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
+  [ChartedSpace (ClosedSmoothModel n) M]
+  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
+
+
+/-- Differentiate the squared norm of a moving covector with the moving
+inverse metric. The metric variation has a negative sign. -/
+theorem hasDerivAt_covectorNormSq
+    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
+    (hgt : TimeDifferentiableAt gt t₀ x)
+    {α : ℝ → (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ} {α' : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ}
+    (hα : HasDerivAt α α' t₀) :
+    HasDerivAt (fun t ↦ α t ((gt t).metricRaiseContinuousAt x (α t)))
+      (2 * α' ((gt t₀).metricRaiseContinuousAt x (α t₀)) -
+        timeDerivAt gt t₀ x
+          ((gt t₀).metricRaiseContinuousAt x (α t₀))
+          ((gt t₀).metricRaiseContinuousAt x (α t₀))) t₀ := by
+  letI : NormedAddCommGroup ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedAddCommGroup (ClosedSmoothModel n))
+  letI : NormedSpace ℝ ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedSpace ℝ (ClosedSmoothModel n))
+  have hd := hα.clm_apply
+    ((hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt hgt).clm_apply hα)
+  apply hd.congr_deriv
+  simp only [map_add]
+  have hswap (v : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) :
+      α t₀ v = (gt t₀).inner x v
+        ((gt t₀).metricRaiseContinuousAt x (α t₀)) := by
+    rw [(gt t₀).inner_symm]
+    exact ((gt t₀).metricRaiseContinuousAt_inner_apply x (α t₀) v).symm
+  rw [hswap (metricRaiseDerivAt gt t₀ x hgt (α t₀)),
+    metricRaiseDerivAt_inner_apply hgt,
+    hswap ((gt t₀).metricRaiseContinuousAt x α'),
+    ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
+  ring
+
+/-- The moving-gradient norm rule, expressed using the derivative of `df`. -/
+theorem hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
+    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
+    (hgt : TimeDifferentiableAt gt t₀ x)
+    {f : ℝ → M → ℝ} {f' : M → ℝ}
+    (hdf : HasDerivAt (fun t ↦ (extDerivFun (f t) x : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ))
+      (extDerivFun f' x) t₀) :
+    HasDerivAt
+      (fun t ↦ (gt t).inner x ((gt t).gradientAt (f t) x)
+        ((gt t).gradientAt (f t) x))
+      (2 * (gt t₀).inner x ((gt t₀).gradientAt f' x)
+          ((gt t₀).gradientAt (f t₀) x) -
+        timeDerivAt gt t₀ x ((gt t₀).gradientAt (f t₀) x)
+          ((gt t₀).gradientAt (f t₀) x)) t₀ := by
+  have h := hasDerivAt_covectorNormSq hgt hdf
+  have heq (g : ClosedSmoothRiemannianMetric n M) (u : M → ℝ) :
+      g.metricRaiseContinuousAt x (extDerivFun u x) = g.gradientAt u x := rfl
+  simp_rw [heq] at h
+  simpa only [ClosedSmoothRiemannianMetric.inner_gradientAt] using h
+
+omit [T2Space M] [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
+/-- Joint second-order scalar regularity commutes the time derivative and
+the manifold differential in a fixed tangent fiber. -/
+theorem hasDerivAt_extDerivFun_of_joint_contDiffAt_two
+    {f : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
+    (hf : ∀ t, MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (f t) x)
+    (hft : MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (fun y ↦ deriv (fun t ↦ f t y) t₀) x)
+    (hJoint : ContDiffAt ℝ 2
+      (fun p : ℝ × (ClosedSmoothModel n) ↦ f p.1 ((extChartAt (closedSmoothModelWithCorners n) x).symm p.2))
+      (t₀, extChartAt (closedSmoothModelWithCorners n) x x)) :
+    HasDerivAt (fun t ↦ (extDerivFun (f t) x : (TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x →L[ℝ] ℝ))
+      (extDerivFun (fun y ↦ deriv (fun t ↦ f t y) t₀) x) t₀ := by
+  letI : NormedAddCommGroup ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedAddCommGroup (ClosedSmoothModel n))
+  letI : NormedSpace ℝ ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (NormedSpace ℝ (ClosedSmoothModel n))
+  letI : FiniteDimensional ℝ ((TangentSpace (closedSmoothModelWithCorners n) : M → Type _) x) := inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel n))
+  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
+  intro v
+  simp_rw [extDerivFun_apply_chart (hf _), extDerivFun_apply_chart hft]
+  exact hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
+    (fun t z ↦ f t ((extChartAt (closedSmoothModelWithCorners n) x).symm z)) t₀ (extChartAt (closedSmoothModelWithCorners n) x x) v hJoint
+
+section Normalized
+
+variable {N : Type u} [TopologicalSpace N] [T2Space N]
+  [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
+  [MeasurableSpace N] [BorelSpace N]
+  [ChartedSpace (ClosedSmoothModel 3) N]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
+
+
+/-- Pointwise time variation of the scalar-gradient norm along normalized
+flow. The joint scalar and Laplacian hypotheses are explicit regularity
+requirements beyond the supplied joint metric entries. -/
+theorem hasDerivAt_scalarGradNormSq_normalizedFlow
+    {gt : ℝ → ClosedSmoothRiemannianMetric 3 N} {t₀ : ℝ} {x : N}
+    (hJoint : ∀ t y, MetricEntriesJointContDiffAt gt t y 3)
+    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
+    (hScalarJoint : ContDiffAt ℝ 2
+      (fun p : ℝ × (ClosedSmoothModel 3) ↦ (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
+      (t₀, extChartAt (closedSmoothModelWithCorners 3) x x))
+    (hLap : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
+      (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) :
+    HasDerivAt (fun t ↦ (gt t).scalarGradNormSqAt x)
+      (2 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
+          ((gt t₀).gradientAt
+            (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) +
+        4 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
+          ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x) +
+        2 * (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
+          ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x) -
+        2 * meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x) t₀ := by
+  letI : Nonempty N := ⟨x⟩
+  let g := gt t₀
+  let R : N → ℝ := fun y ↦ g.scalarAt y
+  let A : N → ℝ := fun y ↦ g.ricciNormSqAt y
+  let L : N → ℝ := fun y ↦ g.laplacianAt R y
+  let c : ℝ := -(2 / 3 : ℝ) * meanScalar g
+  have hR : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) R x := scalarAt_mdifferentiableAt g x
+  have hA : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) A x := ricciNormSqAt_mdifferentiableAt g x
+  have hL : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) L x := hLap
+  have heq : (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) =
+      L + (2 : ℝ) • A + c • R := by
+    funext y
+    have hs : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ y :=
+      satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
+        hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
+    rw [hs.deriv]
+    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, L, A, R, c, g]
+    ring
+  have h2A : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) ((2 : ℝ) • A) x := by
+    exact mdifferentiableAt_const.smul hA
+  have hcR : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) (c • R) x := by
+    exact mdifferentiableAt_const.smul hR
+  have hft : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
+      (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) x := by
+    rw [heq]
+    exact (hL.add h2A).add hcR
+  have hd := hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
+    (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
+      ((hJoint t₀ x).of_le (by norm_num)))
+    (hasDerivAt_extDerivFun_of_joint_contDiffAt_two
+      (fun t ↦ scalarAt_mdifferentiableAt (gt t) x) hft hScalarJoint)
+  rw [heq, g.gradientAt_add (hL.add h2A) hcR,
+    g.gradientAt_add hL h2A,
+    g.gradientAt_const_smul 2 hA, g.gradientAt_const_smul c hR] at hd
+  apply hd.congr_deriv
+  rw [isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
+    (hFlow x)]
+  simp only [normalizedRicciFlowRHSAt, map_add, map_smul,
+    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
+  simp only [ClosedSmoothRiemannianMetric.scalarGradNormSqAt, R, A, L, c, g]
+  rw [(gt t₀).inner_symm x ((gt t₀).gradientAt
+    (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x),
+    (gt t₀).inner_symm x ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x)]
+  ring
+
+omit [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
+  [MeasurableSpace N] [BorelSpace N] in
+/-- The Ricci term in the coordinate Bochner formula is the intrinsic Ricci
+tensor at the chart anchor, with the same curvature sign. -/
+theorem coordRicci_anchorBlendedMetric
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (v w : (ClosedSmoothModel 3)) :
+    RicciFlow.RicciFlow.coordRicci (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
+      (extChartAt (closedSmoothModelWithCorners 3) x x) v w = g.ricciAt x v w := by
+  let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
+  let Γ := GeodesicTransport.chartChristoffelField g x
+  let q := extChartAt (closedSmoothModelWithCorners 3) x x
+  have hΓ : DifferentiableAt ℝ Γ q :=
+    (GeodesicTransport.chartChristoffelField_contDiff_top g x).differentiable
+      (by simp) q
+  have heq (z a b : (ClosedSmoothModel 3)) :
+      RicciFlow.RicciFlow.christoffelClosedOp G z a b = Γ z a b := by
+    rw [show Γ z a b = Γ z b a from chartChristoffelField_symm g x z a b]
+    exact RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt G _
+      (CovariantDerivative.chartBilin_nondegenerate
+        (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
+        GeodesicTransport.backgroundMetric_pos g.inner
+        (fun y u hu ↦ g.inner_pos y hu) x
+        (GeodesicTransport.cutoff_nonneg x) (GeodesicTransport.cutoff_le_one x)
+        (GeodesicTransport.cutoff_support_invertible x) z)
+      (fun _ _ ↦ rfl) a b
+  have heqCLM (z a : (ClosedSmoothModel 3)) :
+      RicciFlow.RicciFlow.christoffelClosedOp G z a = Γ z a := by
+    apply ContinuousLinearMap.ext
+    intro b
+    exact heq z a b
+  have hcurv (a b c : (ClosedSmoothModel 3)) :
+      RicciFlow.RicciFlow.coordCurvatureOp G q a b c =
+        chartCurvatureOf Γ q a b c := by
+    unfold RicciFlow.RicciFlow.coordCurvatureOp chartCurvatureOf
+    simp_rw [heqCLM]
+    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
+      ContinuousLinearMap.comp_apply]
+    rw [ChartCurvatureBridge.fderiv_clm_family_apply hΓ a b,
+      ChartCurvatureBridge.fderiv_clm_family_apply hΓ b a]
+  rw [← anchorChartRicciEntryFlow_eq_ricciAt_anchor (fun _ ↦ g) x 0 v w]
+  unfold RicciFlow.RicciFlow.coordRicci anchorChartRicciEntryFlow
+  apply Finset.sum_congr rfl
+  intro i _
+  exact congrArg ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)
+    (hcurv ((Module.finBasis ℝ (ClosedSmoothModel 3)) i) v w)
+
+omit [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
+  [MeasurableSpace N] [BorelSpace N] in
+/-- Bochner's formula for the actual blended metric, with its curvature
+term identified with the intrinsic Ricci tensor at the anchor. -/
+theorem bochner_anchorBlendedMetric
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N)
+    (f : (ClosedSmoothModel 3) → ℝ) (hf : ContDiff ℝ 3 f) :
+    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
+    let hsymm := CovariantDerivative.blendedChartMetric_symm
+      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
+      GeodesicTransport.backgroundMetric_symm g.inner
+      (fun y a b ↦ g.inner_symm y a b) x
+    let hb := fun z ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm z)
+      (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 z)
+    let Δ := CovariantDerivative.curvedLaplacian G
+      (fun z ↦ RicciFlow.RicciFlow.metricBilin (G z)) hb
+    let q := extChartAt (closedSmoothModelWithCorners 3) x x
+    Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q =
+      2 * RicciFlow.RicciFlow.coordCovariantHessNormSq G f q +
+      2 * G q (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G f q)
+        (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G (Δ f) q) +
+      2 * g.ricciAt x (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G f q)
+        (RicciFlow.RicciFlow.coordGradient («E» := (ClosedSmoothModel 3)) G f q) := by
+  intro G hsymm hb Δ q
+  have hGtop : ContDiff ℝ ∞ G :=
+    CovariantDerivative.contDiff_blendedChartMetric
+      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
+      g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
+      (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
+  have hG : ContDiff ℝ 3 G := hGtop.of_le (WithTop.coe_le_coe.mpr le_top)
+  have h := RicciFlow.RicciFlow.curvedLaplacian_coordGradNormSq_bochner_gradient_unconditional
+    G (x := q) hG hsymm (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0) hf
+  rw [coordRicci_anchorBlendedMetric g x] at h
+  change Δ (RicciFlow.RicciFlow.coordGradNormSq G f) q = _ at h
+  rw [h]
+  ring
+
+set_option backward.isDefEq.respectTransparency false in
+omit [SecondCountableTopology N] in
+/-- Contract the intrinsic Hessian into ordinary chart derivatives at the
+anchor. This version uses a scalar supported inside that chart. -/
+theorem laplacianAt_eq_anchor_derivatives
+    (g : ClosedSmoothRiemannianMetric 3 N) (x : N) (f : N → ℝ)
+    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
+    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
+    let q := extChartAt (closedSmoothModelWithCorners 3) x x
+    let b := Module.finBasis ℝ (ClosedSmoothModel 3)
+    g.laplacianAt f x = ∑ i,
+      (fderiv ℝ (fderiv ℝ u) q (metricDualVectorAt g x (b.coord i)) (b i) -
+      fderiv ℝ u q (RicciFlow.RicciFlow.christoffelClosedOp
+        (CovariantDerivative.chartMetric g.inner x) q
+        (metricDualVectorAt g x (b.coord i)) (b i))) := by
+  intro u q b
+  letI : FiniteDimensional ℝ (TangentSpace (closedSmoothModelWithCorners 3) x) :=
+    inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel 3))
+  have hD : mfderivWithin 𝓘(ℝ, (ClosedSmoothModel 3)) (closedSmoothModelWithCorners 3) (extChartAt (closedSmoothModelWithCorners 3) x).symm (range (closedSmoothModelWithCorners 3)) q =
+      ContinuousLinearMap.id ℝ (ClosedSmoothModel 3) := by
+    have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
+      (mem_extChartAt_source («I» := (closedSmoothModelWithCorners 3)) x)
+    rw [mfderiv_extChartAt_self] at h
+    simpa [q] using h
+  rw [laplacianAt_eq_sum_hessianAt g f x]
+  apply Finset.sum_congr rfl
+  intro i _
+  rw [g.hessianAt_symm' hf.contMDiffAt]
+  have h := IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
+    g x f hs hf (mem_extChartAt_target x)
+    (metricDualVectorAt g x (b.coord i)) (b i)
+  dsimp only at h
+  dsimp only [q] at hD
+  rw [hD] at h
+  change g.hessianAt f ((extChartAt (closedSmoothModelWithCorners 3) x).symm (extChartAt (closedSmoothModelWithCorners 3) x x))
+    (metricDualVectorAt g x (b.coord i)) (b i) = _ at h
+  have hp : (extChartAt (closedSmoothModelWithCorners 3) x).symm (extChartAt (closedSmoothModelWithCorners 3) x x) = x :=
+    (extChartAt (closedSmoothModelWithCorners 3) x).left_inv (mem_extChartAt_source x)
+  have he := congrArg (fun y : N ↦ g.hessianAt f y
+    (metricDualVectorAt g x (b.coord i)) (b i)) hp
+  exact he.symm.trans h
+
+end Normalized
+
+end Poincare.ScalarGradientEvolution

```
