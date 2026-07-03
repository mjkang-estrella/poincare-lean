# M4-prep-5 report

## Survey first

The closed target starts from
`deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g)`.
M4-prep-1 already supplied the second-derivative contraction and the target
vocabulary:

- `deltaRicciSecondDerivContractionAt`
- `roughTensorLaplacianAt`
- `lichnerowiczCurvatureAt`
- `ricciActionOnTensorAt`
- `lichnerowiczLaplacianAt`
- `ricciQuadraticAt`

The model route has two relevant pieces.

1. `g_covDeltaGammaDeriv_lichnerowicz` rewrites a metric-paired
   `covDeltaGammaDeriv` as the derivative of the `1/2` Koszul sum of
   `covTensor2Deriv` entries, with three Christoffel correction terms.  The
   follow-up `fderiv_lichnerowicz_sum` and
   `g_covDeltaGammaDeriv_sndDeriv_form` turn this into a second-covariant
   derivative form.
2. The scalar/Bianchi lane specializes `H = -2 Ric` through
   `ricciDeriv_neg_two_eq_div_add_covariantHessian`,
   `deltaGammaDivergence_lichnerowicz_form`, and
   `deltaGammaDivergence_lichnerowicz_split`, then uses the twice-contracted
   Bianchi package to collapse the traced divergence terms.

The closed file already contains the native replacement for the first model
piece:

- `covDeltaGamma_koszul`
- `covDeltaGamma_koszul_secondDerivAt`
- `deltaRicciAt_eq_secondDerivContractionAt`
- `deltaRicciAt_eq_negTwoRicci_secondDerivContractionAt_of_isClosedRicciFlowSolutionAt_near`

The closed file also already contains the Bianchi/commutation inputs needed
later:

- `closed_cyclic_second_bianchi_at_of_inner_sum`
- `eventually_closed_cyclic_second_bianchi`
- `closed_first_contracted_bianchi_of_second_bianchi`
- `closed_twice_contracted_bianchi_trace_of_second_bianchi`
- `closedContractedBianchiAt_canonical`
- `closedCurvatureDivergenceAt_contraction_eq_closedRicciDivergenceTraceAt`
- `covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt`

I found no separate Uhlenbeck-free 3D shortcut in the model that bypasses the
untraced Ricci-identity work.  The 3D/scalar shortcut is the Bianchi-free
Hamilton scalar route; it validates traces but does not prove the tensor-level
`deltaRicciSecondDerivContractionAt -> lichnerowiczLaplacianAt +
ricciQuadraticAt` identity.

## Slice plan

1. First slice, landed here:

```lean
theorem covDeltaGamma_koszul_secondDerivAt_negTwoRicci_of_isClosedRicciFlowSolutionAt_near
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hFlowNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (u v w z : TM x) :
    2 * (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u v w) z =
      covTensor2SecondDerivAt (gt t₀)
          (negTwoRicciVariationField (gt t₀)) x u v w z
        + covTensor2SecondDerivAt (gt t₀)
          (negTwoRicciVariationField (gt t₀)) x u w v z
        - covTensor2SecondDerivAt (gt t₀)
          (negTwoRicciVariationField (gt t₀)) x u z v w
```

2. Linear Ricci form:

```lean
theorem covTensor2SecondDerivAt_negTwoRicciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRicSecond : CovTensor2DerivExtDifferentiableAt g (ricciVariationField g) x)
    (u v w z : TM x) :
    covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u v w z =
      -2 * covTensor2SecondDerivAt g (ricciVariationField g) x u v w z
```

3. Raw contraction specialization:

```lean
theorem deltaRicciSecondDerivContractionAt_negTwoRicci_eq_neg_two_ricci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRicSecond : CovTensor2DerivExtDifferentiableAt g (ricciVariationField g) x)
    (u w : TM x) :
    deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
      -2 * deltaRicciSecondDerivContractionAt g (ricciVariationField g) x u w
```

4. Commutation entry:

```lean
def RicciSecondDerivCommutationAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ u w : TM x,
    deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
      lichnerowiczLaplacianAt g (ricciVariationField g) x u w
        + ricciQuadraticAt g x u w
```

5. Bianchi-fed divergence reorderings:

```lean
def RicciSecondDerivCurvatureCommutationAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ u w : TM x,
    deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
      roughTensorLaplacianAt g (ricciVariationField g) x u w
        - 2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
        + ricciActionOnTensorAt g (ricciVariationField g) x u w
        + ricciQuadraticAt g x u w

theorem RicciSecondDerivCommutationAt.of_closed_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : ClosedRicciDerivativeExpansionAt g x)
    (hSecond : ∀ u v w z : TM x,
      closedCurvatureCovDerivAt g x v u w z
        + closedCurvatureCovDerivAt g x u w v z
        + closedCurvatureCovDerivAt g x w v u z = 0)
    (hCurvComm : RicciSecondDerivCurvatureCommutationAt g x) :
    RicciSecondDerivCommutationAt g x
```

6. Assembly into the target equation:

```lean
theorem satisfiesRicciEvolutionAt_of_secondDerivCommutation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hDeltaRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciSecondDerivContractionAt
          (gt t₀) (negTwoRicciVariationField (gt t₀)) x u w) t₀)
    (hComm : RicciSecondDerivCommutationAt (gt t₀) x) :
    SatisfiesRicciEvolutionAt gt t₀ x
```

## Trace sanity

The trace side is already validated by
`ricciEvolution_rhs_trace_eq_hamilton_rhs_of_traceSecondRegularity`.  The new
first slice is pointwise and traces to the already-existing
`deltaRicciAt_eq_negTwoRicci_secondDerivContractionAt_of_isClosedRicciFlowSolutionAt_near`
route before any commutation is attempted.

## Verification

- `lake env lean Poincare/Global/ScalarVariation.lean` succeeded, with
  existing linter warnings only.
- `lake build Poincare.Global.ScalarVariation` succeeded, with existing
  warnings only.
