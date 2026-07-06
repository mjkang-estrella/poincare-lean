# M5-geo-3 done report

## New module

File: `Poincare/Global/GeodesicGerm.lean`

No existing Lean file or root import was edited.

## Final signatures

Namespace: `Poincare.GeodesicTransport`

```lean
theorem geodesicFlowField_chartChristoffelField_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E)
    {γ η : ℝ → E × E}
    (hγ0 : γ 0 = (extChartAt I x₀ x₀, v₀))
    (hη0 : η 0 = (extChartAt I x₀ x₀, v₀))
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η
        (geodesicFlowField (chartChristoffelField g x₀) (η t)) t) :
    γ =ᶠ[𝓝 (0 : ℝ)] η

theorem pulledback_geodesic_eventuallyEq_of_chartChristoffelField
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E)
    {γ η : ℝ → E × E}
    (hγ0 : γ 0 = (extChartAt I x₀ x₀, v₀))
    (hη0 : η 0 = (extChartAt I x₀ x₀, v₀))
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η
        (geodesicFlowField (chartChristoffelField g x₀) (η t)) t) :
    (fun t : ℝ => (extChartAt I x₀).symm (γ t).1)
      =ᶠ[𝓝 (0 : ℝ)]
    (fun t : ℝ => (extChartAt I x₀).symm (η t).1)

noncomputable def geodesicGermRadius
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ

theorem geodesicGermRadius_pos
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    0 < geodesicGermRadius g x₀ v₀

noncomputable def geodesicGermChartSolution
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ → E × E

theorem geodesicGermChartSolution_spec
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    geodesicGermChartSolution g x₀ v₀ 0 =
        (extChartAt I x₀ x₀, v₀) ∧
      (∀ t ∈ Ioo (-(geodesicGermRadius g x₀ v₀)) (geodesicGermRadius g x₀ v₀),
        HasDerivAt (geodesicGermChartSolution g x₀ v₀)
          (geodesicFlowField (chartChristoffelField g x₀)
            (geodesicGermChartSolution g x₀ v₀ t)) t) ∧
      (let c : ℝ → M :=
        fun t => (extChartAt I x₀).symm (geodesicGermChartSolution g x₀ v₀ t).1
       c 0 = x₀ ∧
        ∀ᶠ t in 𝓝 (0 : ℝ),
          (geodesicGermChartSolution g x₀ v₀ t).1 ∈ (extChartAt I x₀).target ∧
            c t ∈ (extChartAt I x₀).source)

noncomputable def geodesicGermAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ → M

@[simp]
theorem geodesicGermAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    geodesicGermAt g x₀ v₀ 0 = x₀

theorem geodesicGermAt_eventually_mem_source
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), geodesicGermAt g x₀ v₀ t ∈ (extChartAt I x₀).source

theorem geodesicGermAt_spec
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = (extChartAt I x₀ x₀, v₀) ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt γ
          (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t) ∧
      (∀ t ∈ Ioo (-ε) ε,
        geodesicGermAt g x₀ v₀ t = (extChartAt I x₀).symm (γ t).1)

theorem geodesicGermChartSolution_position_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    HasDerivAt
      (fun t : ℝ => (geodesicGermChartSolution g x₀ v₀ t).1) v₀ 0

theorem geodesicGermAt_chart_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    HasDerivAt
      (fun t : ℝ => extChartAt I x₀ (geodesicGermAt g x₀ v₀ t)) v₀ 0
```

## Scope completed

- Instantiated `geodesicFlowField_eventuallyEq_of_contDiffAt` with
  `geodesicFlowField_chartChristoffelField_contDiffAt` to prove same-anchor
  chart uniqueness.
- Proved the pulled-back manifold curves agree as germs at `0`.
- Chose the local chart solution from `exists_local_geodesic_chart_solution`
  and packaged the manifold-valued germ `geodesicGermAt`.
- Proved `geodesicGermAt g x₀ v₀ 0 = x₀` and eventual membership in the
  anchor chart source.
- Exposed the chosen chart solution and interval in `geodesicGermAt_spec`.
- Proved both the chart-solution initial velocity statement and the germ-level
  chart derivative spelling.

## Next decomposition

1. Chart-overlap and choice independence: prove two germs chosen through
   overlapping anchor charts agree after applying the chart transition on a
   common neighborhood.
2. Velocity-smoothness of the germ family: package smooth dependence of the
   chosen chart solution on `(x₀, v₀)` once the chart-overlap independence API
   is available.
3. Exponential germ: define the reparametrized germ
   `exp_{x₀}(t * v₀)` and expose zero and chart-velocity lemmas.
4. Gauss lemma prerequisites: formalize the local radial variation and
   metric-compatibility ingredients needed after the exponential germ API.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|axiom|native_decide)\b" Poincare/Global/GeodesicGerm.lean
```

Actual result: no matches.

Required build command:

```text
lake build Poincare.Global.GeodesicGerm
```

Actual result:

```text
Build completed successfully (2825 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/GeodesicGerm.lean`.
