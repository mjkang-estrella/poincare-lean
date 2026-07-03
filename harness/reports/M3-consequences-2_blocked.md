# M3-consequences-2 blocked report

## Summary

The requested global minimum package is mathematically the right target, but the
current closed-manifold API does not expose enough proved bridges to discharge
`0 ≤ g.laplacianAt f x` from `IsLocalMin f x` without adding substantial new
infrastructure outside this task's safe surface.

I did not add placeholder proofs, primitive assumptions, or a vacuous witness.
The target theorem `hamilton_finite_time_singularity` in
`Poincare.Global.ScalarEvolution` remains unchanged.

## Exact attempted goal state

The intended closed lemmas were:

```lean
theorem exists_scalarAt_isMinOn
    [CompactSpace M] [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hscalar :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x) :
    ∃ x : M, IsMinOn (fun y : M ↦ g.scalarAt y) Set.univ x

theorem laplacianAt_nonneg_of_isLocalMin
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hgrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hmin : IsLocalMin f x) :
    0 ≤ g.laplacianAt f x
```

and then the finite-time corollary:

```lean
theorem hamilton_finite_time_singularity'
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ} {x₀ : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ)) (hT0 : 0 ≤ T)
    (hHam : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x₀)
    (hScalar₂ : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) x₀)
    (hScalarGrad : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((gt (t₀ + τ)).gradient
          (fun y : M ↦ (gt (t₀ + τ)).scalarAt y))) x₀)
    (hMin : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      IsMinOn (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) Set.univ x₀)
    (hRpos : 0 < (gt t₀).scalarAt x₀) :
    T < (n : ℝ) / (2 * (gt t₀).scalarAt x₀)
```

## What is already available

The compactness part is straightforward once a scalar-curvature continuity
hypothesis is supplied:

* `IsCompact.exists_isMinOn`
* `isCompact_univ`
* `ContMDiffAt.continuousAt`

The closed Hessian definition and trace bridge are also available:

* `ClosedSmoothRiemannianMetric.hessianAt`
* `ClosedSmoothRiemannianMetric.laplacianAt`
* `laplacianAt_eq_sum_hessianAt`
* `extDerivFun_extDerivFun_extend_eq_hessianAt_add`

The chart side has the key canonical-extension constancy:

* `extDerivFun_section_eventually_chart`
* `mfderiv_extChartAt_extend_apply`
* `chartTransportedLeviCivitaSection_extend_apply_chart`

The model side has the flat positive-Hessian lemma:

* `RicciFlow.hessian_nonneg_of_isLocalMin`
* `RicciFlow.trace_dual_comp_nonneg`

## Blocking gaps

1. `RicciFlow.hessian_nonneg_of_isLocalMin` requires global
   `ContDiff ℝ 2 f`, but the closed statement naturally has only
   `ContMDiffAt I 𝓘(ℝ) 2 f x`.  A local `ContDiffAt` version of the flat
   second-derivative test is needed before the chart route can be closed
   without strengthening the theorem in an unnatural way.

2. The closed Laplacian stores Hessians as
   `TM x →ₗ[ℝ] Module.Dual ℝ (TM x)`, while the model trace-positivity lemma
   expects a continuous bilinear map
   `TM x →L[ℝ] TM x →L[ℝ] ℝ`.  The missing finite-dimensional conversion must
   identify the trace expression after moving through
   `LinearMap.toContinuousLinearMap`.

3. The chart identification needed for the Hessian diagonal is not exported as
   a standalone lemma.  The proof pattern exists inside
   `ChartIdentification.lean` for the Lie-bracket identity, but this task would
   need a reusable lemma of the shape:

```lean
extDerivFun (fun y : M ↦ extDerivFun f y (extend E v y)) x v =
  fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm))
    (extChartAt I x x) v v
```

for `ContMDiffAt I 𝓘(ℝ) 2 f x`.

## Recommended next slice

Split this into a prerequisite lemma task:

1. Prove a local flat lemma
   `fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt`.
2. Export the chart iterated-`extDerivFun` diagonal identity for canonical
   extensions.
3. Prove the finite-dimensional algebraic-dual/continuous-bilinear trace
   bridge for `hessianDualAt`.
4. Then re-run this M3 consequence task with `laplacianAt_nonneg_of_isLocalMin`
   as a small assembly lemma.
