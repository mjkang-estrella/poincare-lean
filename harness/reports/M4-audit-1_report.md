# M4-audit-1 consolidation audit

Scope: M4 goal-4/5/6 theorem chain around Ricci evolution, Hamilton pinching
preservation, improved traceless pinching, and eigenvalue pinching.

## Verification run

- Read `harness/worker_contract.md` first.
- Refreshed stale local artifacts with:
  `lake build Poincare.Global.ScalarEvolution`
- Result: success, warnings only. The build rebuilt the missing
  `Mathlib.Analysis.SpecialFunctions.Pow.Deriv` dependency, rebuilt
  `Poincare.Global.ScalarVariation`, then built
  `Poincare.Global.ScalarEvolution`.
- Re-ran `#check` and `#print axioms` for all five headline theorems against
  the refreshed artifacts.
- Axiom result for all five:
  `[propext, Classical.choice, Quot.sound]`.
- No source Lean files were changed.

## Source predicates that matter

`SatisfiesRicciEvolutionAt` is the pointwise tensor evolution target:

```lean
def SatisfiesRicciEvolutionAt
    (gt : R -> ClosedSmoothRiemannianMetric n M) (t0 : R) (x : M)
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  forall u w : TM x,
    HasDerivAt (fun t => (gt t).ricciAt x u w)
      (ricciEvolutionTensorRHSAt (gt t0) x u w) t0
```

`SatisfiesPinchingQuotientEvolutionAt` is not a tautology: it contains
positive scalar curvature and an existential derivative witness satisfying a
parabolic inequality.

```lean
def SatisfiesPinchingQuotientEvolutionAt
    (gt : R -> ClosedSmoothRiemannianMetric n M) (t0 : R) (x : M)
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (ricciNormReactionMotionTrace : R) :
    Prop :=
  0 < (gt t0).scalarAt x /\
    exists Q' : R,
      HasDerivAt (fun t => (gt t).pinchingQuotientAt x) Q' t0 /\
        Q' <=
          (gt t0).laplacianAt (fun y => (gt t0).pinchingQuotientAt y) x
            + (gt t0).pinchingQuotientGradientDrift3At x
            + (gt t0).pinchingGradientDampingAt x
            + (2 / ((gt t0).scalarAt x) ^ 4) *
              (gt t0).pinchingReactionRemainderAt x
                ricciNormReactionMotionTrace
```

`SatisfiesTracelessPinchingImprovementEvolutionAt` is similarly nontrivial:

```lean
def SatisfiesTracelessPinchingImprovementEvolutionAt
    (gt : R -> ClosedSmoothRiemannianMetric n M) (t0 : R) (x : M)
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (delta ricciNormReactionMotionTrace : R) :
    Prop :=
  0 < delta /\
    delta <= 1 /\
      0 < (gt t0).scalarAt x /\
        exists F' : R,
          HasDerivAt (fun t => (gt t).tracelessPinchingAt x delta) F' t0 /\
            F' <=
              (gt t0).laplacianAt
                (fun y => (gt t0).tracelessPinchingAt y delta) x
                + (gt t0).tracelessPinchingGradientDrift3At x delta
                + (gt t0).tracelessPinchingReactionTermAt x delta
                  ((gt t0).pinchingTracelessRicciReactionTrace3At x
                    ricciNormReactionMotionTrace)
```

The maximum tracks use `sSup (Set.range ...)`, not a max over an empty set.
The maximum-principle theorems assume `[Nonempty M]`, and the source proves
attainment lemmas for both quotient tracks using compactness.

## Headline theorem audit

### 1. `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity`

Full source statement:

```lean
theorem satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity
    {gt : R -> ClosedSmoothRiemannianMetric n M} {t0 : R} {x : M}
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t0 x)
    (hgt : forall y : M, TimeDifferentiableAt gt t0 y)
    (hExt :
      forall a b c : TM x,
        HasDerivAt
          (fun t =>
            extDerivFun
              (fun y : M => (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M => timeDerivAt gt t0 y (extend E b y) (extend E c y))
            x a) t0)
    (hNear :
      forall^f y in nhds x,
        MetricFlowRegularAt gt t0 y /\
        (forall a b c : TM y,
          HasDerivAt
            (fun t =>
              extDerivFun
                (fun z : M => (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M => timeDerivAt gt t0 z (extend E b z) (extend E c z))
              y a) t0))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t0 x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t0) (timeDerivAt gt t0) x)
    (hFlowNear :
      forall^f y in nhds x,
        IsClosedRicciFlowSolutionAt gt t0 y /\
        ClosedRicciFlowExtensionRegularAt gt t0 y)
    (hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t0) (ricciVariationField (gt t0)) x)
    (hRicC2 :
      CovTensor2ExtContMDiffAt (ricciVariationField (gt t0)) x 2)
    (hScalar2 :
      ContMDiffAt I I(R) 2 (fun y : M => (gt t0).scalarAt y) x)
    (hScalarExt2 : forall w : TM x,
      MDifferentiableAt I I(R)
        (fun y : M =>
          extDerivFun (fun z : M => (gt t0).scalarAt z) y
            (extend E w y)) x) :
    SatisfiesRicciEvolutionAt gt t0 x
```

Hypothesis assessment:

- Structural manifold/metric instances are standard for this repo.
- `hreg`, `hgt`, `hExt`, `hNear`, `hBridge`, `hSecond`: genuine regularity and
  commutation hypotheses. They are stronger than the informal "Ricci flow"
  theorem, but not Prop-placeholder certificates.
- `hFlowNear`: most suspicious bundle. It combines the pointwise Ricci-flow PDE
  with `ClosedRicciFlowExtensionRegularAt`, whose definition requires every
  canonical extension `extend E v` to be a global `ClosedC2TangentField`.
  There is a static Ricci-flat PDE theorem, but no named static theorem for the
  full extension-regularity bundle.
- `hRicSecond`, `hRicC2`, `hScalar2`, `hScalarExt2`: trace-second regularity
  assumptions. They are plausible analytic regularity classes, but still
  conditional.

Conclusion assessment:

- The conclusion is exactly `SatisfiesRicciEvolutionAt gt t0 x`, i.e. the
  Ricci tensor derivative equals the named RHS for every pair of tangent
  vectors. This matches the theorem name and is not a hidden identity of the
  same term.

### 2. `hamilton_pinching_preserved`

Full source statement:

```lean
theorem hamilton_pinching_preserved
    [CompactSpace M] [Nonempty M]
    {gt : R -> ClosedSmoothRiemannianMetric n M} {t0 T : R}
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 <= T)
    (hQ_cont :
      Continuous (uncurry (fun tau (x : M) => (gt (t0 + tau)).pinchingQuotientAt x)))
    (hQ2 : forall tau in Icc (0 : R) T, forall x : M,
      ContMDiffAt I I(R) 2
        (fun y : M => (gt (t0 + tau)).pinchingQuotientAt y) x)
    (hEvol : forall tau in Icc (0 : R) T, forall x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t0 + tau) x
          ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x)) :
    forall tau in Icc (0 : R) T,
      pinchingMaximumTrack gt t0 tau <= pinchingMaximumTrack gt t0 0
```

Hypothesis assessment:

- `[CompactSpace M] [Nonempty M]` prevents empty maximum ranges.
- `hn`, `hT0`: expected dimension and time-interval assumptions. `T = 0` is
  allowed, making the statement degenerate but not vacuous.
- `hQ_cont`, `hQ2`: regularity of the quotient track; stronger than a purely
  formal maximum principle statement but standard for the proof used.
- `hEvol`: the real mathematical input. It includes scalar positivity through
  `SatisfiesPinchingQuotientEvolutionAt`.

Conclusion assessment:

- It proves nonincreasing spatial maximum of `|Ric|^2 / R^2` on `[0,T]`.
- The maximum is `sSup (Set.range ...)` over a nonempty type, and the proof
  uses an attained maximum, so this is not an empty-set artifact.

### 3. `satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow`

Full source statement:

```lean
theorem satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow
    {gt : R -> ClosedSmoothRiemannianMetric n M} {t0 : R} {x : M} {delta : R}
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x ->L[R] R) ->L[R] TM x}
    (hRaise : HasDerivAt (fun t => (gt t).metricRaiseContinuousAt x) raise' t0)
    (hRicci : SatisfiesRicciEvolutionAt gt t0 x)
    (hScalar : SatisfiesHamiltonScalarEvolutionAt gt t0 x)
    (hn : n = 3)
    (hdelta_pos : 0 < delta) (hdelta_le : delta <= 1)
    (hRpos : 0 < (gt t0).scalarAt x)
    (hRicNorm2 : forall y : M, ContMDiffAt I I(R) 2
      (fun z : M => (gt t0).ricciNormSqAt z) y)
    (hScalar2 : forall y : M, ContMDiffAt I I(R) 2
      (fun z : M => (gt t0).scalarAt z) y)
    (hScalarSqDiff : forall y : M, MDifferentiableAt I I(R)
      (fun z : M => (gt t0).scalarAt z ^ 2) y)
    (hScalarSqGrad :
      MDifferentiableAt I ((I).prod I(R,E))
        (T% ((gt t0).gradient
          (fun z : M => (gt t0).scalarAt z ^ 2))) x)
    (hPairDiff : forall w : TM x,
      MDifferentiableAt I I(R)
        (fun y : M => covRicciRicciPairingAt (gt t0) y (extend E w y)) x)
    (hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t0) (ricciVariationField (gt t0)) x)
    (hScalarCont : ContinuousAt (fun y : M => (gt t0).scalarAt y) x)
    (hScalarDiff : forall y : M,
      MDifferentiableAt I I(R) (fun z : M => (gt t0).scalarAt z) y)
    (hScalarNe : forall y : M, (gt t0).scalarAt y != 0)
    (hTraceQuotDiff : forall y : M,
      MDifferentiableAt I I(R)
        (fun z : M => (gt t0).tracelessPinchingAt z delta) y)
    (hTraceQuotGrad :
      MDifferentiableAt I ((I).prod I(R,E))
        (T% ((gt t0).gradient
          (fun y : M => (gt t0).tracelessPinchingAt y delta))) x)
    (hScalarGrad :
      MDifferentiableAt I ((I).prod I(R,E))
        (T% ((gt t0).gradient (fun y : M => (gt t0).scalarAt y))) x)
    (hTraceProductGrad :
      MDifferentiableAt I ((I).prod I(R,E))
        (T% ((gt t0).gradient
          ((fun y : M => (gt t0).tracelessPinchingAt y delta) *
            (fun y : M => ((gt t0).scalarAt y) ^ (2 - delta))))) x)
    (hTraceNormGrad :
      MDifferentiableAt I ((I).prod I(R,E))
        (T% ((gt t0).gradient
          (fun y : M => (gt t0).tracelessRicciNormSqAt y))) x) :
    let g : ClosedSmoothRiemannianMetric n M := gt t0
    let deltaRic3 : TM x -> TM x -> R :=
      fun u w => ricciEvolution3ReactionRHSAt g x u w
    let hRic3 : forall u w : TM x,
        HasDerivAt (fun t => (gt t).ricciAt x u w) (deltaRic3 u w) t0 :=
      SatisfiesRicciEvolutionAt.reaction3
        (gt := gt) (t0 := t0) (x := x) hRicci hn
    let fullTrace : R := ...
    ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
      gt t0 x delta (g.pinchingRicciNormReactionMotionTraceAt x fullTrace)
```

Hypothesis assessment:

- `hRaise`, `hRicci`, `hScalar`: depends on earlier Ricci/scalar evolution
  packages. These are meaningful but conditional.
- `0 < delta`, `delta <= 1`, `hRpos`: expected for improved pinching.
- `hScalarNe : forall y, scalarAt y != 0` is stronger than point positivity at
  `x`; it is a global denominator/power-domain assumption for the time slice.
- The many `ContMDiffAt`, `MDifferentiableAt`, and gradient hypotheses are
  stronger than the informal statement. They are not vacuous certificates, but
  they are unbundled analytic regularity obligations.

Conclusion assessment:

- The conclusion is the improved traceless pinching evolution predicate with a
  computed motion trace. It does not assert reaction nonpositivity; that is
  deliberately left for the later eigenvalue pinching/reaction layer.

### 4. `hamilton_pinching_improvement`

Full source statement:

```lean
theorem hamilton_pinching_improvement
    [CompactSpace M] [Nonempty M]
    {gt : R -> ClosedSmoothRiemannianMetric n M} {t0 T epsilon delta : R}
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 <= T)
    (hepsilon_pos : 0 < epsilon) (hepsilon_le : epsilon <= 1 / 3)
    (hdelta_nonneg : 0 <= delta)
    (hdelta_adm : delta <= PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hQ_cont :
      Continuous (uncurry (fun tau (x : M) => (gt (t0 + tau)).tracelessPinchingAt x delta)))
    (hQ2 : forall tau in Icc (0 : R) T, forall x : M,
      ContMDiffAt I I(R) 2
        (fun y : M => (gt (t0 + tau)).tracelessPinchingAt y delta) x)
    (hEvol : forall tau in Icc (0 : R) T, forall x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + tau) x delta
          ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hPin : forall tau in Icc (0 : R) T, forall x : M,
      forall (b : Module.Basis (Fin 3) R (TM x)) (mu : Fin 3 -> R),
        (forall i : Fin 3, (gt (t0 + tau)).ricciEndoAt x (b i) = mu i • b i) ->
          forall i : Fin 3, epsilon * (gt (t0 + tau)).scalarAt x <= mu i) :
    forall tau in Icc (0 : R) T,
      tracelessPinchingMaximumTrack gt t0 delta tau <=
        tracelessPinchingMaximumTrack gt t0 delta 0
```

Hypothesis assessment:

- `[CompactSpace M] [Nonempty M]` prevents empty maximum ranges.
- `epsilon` range is inhabited; source proves
  `pinchedTracelessAdmissibleDelta3 (1 / 10) = 6 / 83`, giving a concrete
  positive admissible delta example.
- The theorem only assumes `0 <= delta`, but `hEvol` itself contains
  `0 < delta`; because `[Nonempty M]`, `hT0`, and `0 in Icc 0 T`, the package
  is not silently allowing `delta = 0` in real uses.
- `hPin` is very strong: it assumes the eigenvalue floor for every time and
  point. The theorem is not deriving that floor; it consumes it.

Conclusion assessment:

- The conclusion is the nonincreasing spatial maximum of
  `|Ric0|^2 / R^(2 - delta)`. It is not an equality-to-self theorem and not an
  empty maximum.

### 5. `hamilton_eigenvalue_pinching_floor_preserved`

Full source statement:

```lean
theorem hamilton_eigenvalue_pinching_floor_preserved
    [CompactSpace M] [Nonempty M]
    {gt : R -> ClosedSmoothRiemannianMetric n M} {t0 T epsilon : R}
    [forall t : R,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hepsilon_le : epsilon <= 1 / 3) (hT0 : 0 <= T)
    (hQ_cont :
      Continuous (uncurry (fun tau (x : M) => (gt (t0 + tau)).pinchingQuotientAt x)))
    (hQ2 : forall tau in Icc (0 : R) T, forall x : M,
      ContMDiffAt I I(R) 2
        (fun y : M => (gt (t0 + tau)).pinchingQuotientAt y) x)
    (hEvol : forall tau in Icc (0 : R) T, forall x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t0 + tau) x
          ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hRpos : forall tau in Icc (0 : R) T, forall x : M,
      0 < (gt (t0 + tau)).scalarAt x)
    (hInitPin : forall x : M,
      forall (b : Module.Basis (Fin 3) R (TM x)) (mu : Fin 3 -> R),
        (forall i : Fin 3, (gt t0).ricciEndoAt x (b i) = mu i • b i) ->
          forall i : Fin 3, epsilon * (gt t0).scalarAt x <= mu i) :
    forall tau in Icc (0 : R) T, forall x : M,
      forall (b : Module.Basis (Fin 3) R (TM x)) (mu : Fin 3 -> R),
        (forall i : Fin 3, (gt (t0 + tau)).ricciEndoAt x (b i) = mu i • b i) ->
          forall i : Fin 3, (2 * epsilon - 1 / 3) * (gt (t0 + tau)).scalarAt x <= mu i
```

Hypothesis assessment:

- Same compact/nonempty/quotient-evolution dependencies as
  `hamilton_pinching_preserved`.
- `hepsilon_le` has no positivity assumption. This is not vacuous, but it means
  the transported floor can be weak or negative. If the intended theorem needs
  positive epsilon, that is a statement-strength gap.
- `hInitPin` is a true eigenbasis/eigenvalue floor assumption at `t0`.

Conclusion assessment:

- The conclusion exactly matches the docstring's transported floor
  `(2 * epsilon - 1 / 3) * R <= mu_i`. It is weaker than the initial floor in
  much of the epsilon range, but it is not hiddenly trivialized by an empty
  eigenbasis: the basis is universally quantified by the caller.

## Inhabitation spot-checks

Scratch Lean examples were run through `lake env lean --stdin`; all examples
below elaborated unless noted.

Confirmed non-vacuous:

- Static metric regularity:
  `MetricFlowRegularAt (fun _ : R => g) t0 x` via
  `metricFlowRegularAt_const`.
- Static pointwise time differentiability:
  `forall y, TimeDifferentiableAt (fun _ : R => g) t0 y` via
  `timeDifferentiableAt_const`.
- Static `DeltaGammaEntryDerivativeBridgeAt` via
  `deltaGammaEntryDerivativeBridgeAt_const`.
- Static `hExt` and neighborhood `hNear` shapes for time-constant metric
  families were constructed directly in scratch Lean.
- Static Ricci-flat PDE witness:
  `IsClosedRicciFlowSolutionAt (fun _ : R => g) t0 x` via
  `isClosedRicciFlowSolutionAt_const_of_ricciFlat`.
- Maximum-track nonemptiness:
  `exists_pinchingQuotientAt_isMaxOn` and
  `exists_tracelessPinchingAt_isMaxOn` elaborate under
  `[CompactSpace M] [Nonempty M]` and `C2` quotient regularity.
- Zero tensor regularity classes are inhabited:
  `covTensor2DerivExtDifferentiableAt_zero` and
  `covTensor2ExtContMDiffAt_zero`.

Vacuity-prone or uninstantiated:

- `ClosedRicciFlowExtensionRegularAt` has no named static witness. A direct
  scratch attempt using `FiberBundle.contMDiffAt_extend'` failed because that
  theorem gives smoothness at the base point of the extension, while
  `ClosedC2TangentField (extend E v)` asks for global `ContMDiff` of the
  canonical extension field. I did not prove this bundle impossible, but it is
  the highest-priority gap for making `hFlowNear` non-vacuous in the current
  global closed-manifold interface.
- `CovTensor2DerivExtDifferentiableAt g (ricciVariationField g) x` and
  `CovTensor2ExtContMDiffAt (ricciVariationField g) x 2` are assumed in the
  trace-second route. The source has a canonical first-order theorem
  `covTensor2ExtDifferentiableAt_ricciVariationField_canonical`, but I did not
  find a named canonical theorem discharging the second-derivative/C2 pair.
- The pinching maximum theorems are intentionally conditional on the pointwise
  evolution predicates and quotient regularity. The source proves the maximum
  principle layer, not a fully instantiated Ricci-flow corollary.

## Honest-strength summary

Genuinely proved in the current source:

- The Ricci-evolution theorem derives `SatisfiesRicciEvolutionAt` from a large
  but meaningful local Ricci-flow/trace-second-regularity bundle.
- The quotient and traceless maximum-principle theorems prove actual
  nonincreasing spatial maximum statements under compactness, nonemptiness,
  regularity, and pointwise evolution predicates.
- The eigenvalue theorem converts preserved quotient pinching plus initial
  eigenvalue pinching into the stated transported floor.
- All five headline theorem constants build and have exactly the expected
  axiom set: `propext`, `Classical.choice`, `Quot.sound`.

Conditional / gap list before these become fully instantiated Ricci-flow
corollaries:

1. Add or prove a usable inhabitance theorem for
   `ClosedRicciFlowExtensionRegularAt`, at least for the intended static
   Ricci-flat/space-form witnesses and preferably under a clean global smooth
   extension hypothesis.
2. Bundle the repeated regularity hypotheses for `hRaise`, scalar/Ricci-norm
   `C2`, quotient differentiability, and gradient differentiability into a
   named flow-regularity package.
3. Prove or expose canonical second-regularity lemmas for
   `ricciVariationField`: the current source has first-order canonical
   differentiability, but the headline Ricci route still assumes
   `CovTensor2DerivExtDifferentiableAt` and `CovTensor2ExtContMDiffAt`.
4. Add instantiated corollaries chaining
   `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity`,
   `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` or its static-flat
   version, and `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow` into the
   `hamilton_pinching_preserved` hypotheses.
5. Add the analogous instantiated corollary for
   `satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow` into
   `hamilton_pinching_improvement`.
6. Decide whether `hamilton_eigenvalue_pinching_floor_preserved` should require
   `0 < epsilon`; the current theorem is correct as stated but can yield a weak
   negative transported floor when epsilon is nonpositive.

Bottom line: no critical impossible-inhabitant finding was proved. The main
audit finding is that the M4 chain is mathematically meaningful but still
conditional on strong, only partially instantiated analytic regularity
bundles. The most suspicious concrete bundle is
`ClosedRicciFlowExtensionRegularAt`, because it asks for global `C2` regularity
of the canonical extension fields and currently lacks a named static witness.
