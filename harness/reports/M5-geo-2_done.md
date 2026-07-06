# M5-geo-2 done report

## New module

File: `Poincare/Global/GeodesicTransport.lean`

No existing Lean file or root import was edited.

## Reused transport machinery

I did not find a pre-existing standalone closed-metric chart Christoffel field
definition.  The new field is built from the existing transported-connection
machinery rather than by re-deriving coefficients:

- `CovariantDerivative.exists_blending_cutoff`
- `CovariantDerivative.blendedChartMetric`
- `CovariantDerivative.chartBilin` and
  `CovariantDerivative.chartBilin_nondegenerate`
- `CovariantDerivative.chartLeviCivita`
- `CovariantDerivative.christoffelOneForm`
- `LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed`
- `CovariantDerivative.contDiff_blendedChartMetric`
- `CovariantDerivative.contDiffAt_christoffelAt`
- `exists_geodesicFlowField_solution`

The chosen cutoff is equal to `1` near the anchor and is supported in the
anchor chart target, so the blended chart metric agrees locally with the
closed metric transported through `extChartAt`.

## Final signatures

```lean
def chartLeviCivita :
    CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _)

def chartChristoffelField : E → E →L[ℝ] E →L[ℝ] E

theorem chartLeviCivita_eventuallyEq_closed
    {σ : Π y : M, TM y}
    (hσ : ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) Set.univ) :
    (fun y : M =>
      (⟨y,
        CovariantDerivative.chartTransportedLeviCivitaHom
          (cutoff (n := n) x₀) (backgroundMetric (n := n))
          (backgroundMetric_pos (n := n)) g.inner
          (fun y u hu => g.inner_pos y (v := u) hu) x₀
          (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
          (cutoff_support_invertible (n := n) x₀) σ y⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
      =ᶠ[𝓝 x₀]
    (fun y : M =>
      (⟨y, g.leviCivita σ y⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))

theorem chartChristoffelField_contDiffAt :
    ContDiffAt ℝ 1 (chartChristoffelField g x₀) (extChartAt I x₀ x₀)

theorem geodesicFlowField_chartChristoffelField_contDiffAt (v₀ : E) :
    ContDiffAt ℝ 1
      (geodesicFlowField (chartChristoffelField g x₀))
      (extChartAt I x₀ x₀, v₀)

theorem exists_local_geodesic_chart_solution (v₀ : E) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = (extChartAt I x₀ x₀, v₀) ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt γ
          (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t) ∧
      (let c : ℝ → M := fun t => (extChartAt I x₀).symm (γ t).1
       c 0 = x₀ ∧
        ∀ᶠ t in 𝓝 (0 : ℝ),
          (γ t).1 ∈ (extChartAt I x₀).target ∧
            c t ∈ (extChartAt I x₀).source)
```

## Scope completed

- Defined a chart-side Christoffel field for `g : ClosedSmoothRiemannianMetric n M`.
- Proved that the transported chart connection agrees eventually near the
  anchor with the actual closed Levi-Civita connection `g.leviCivita`.
- Proved `ContDiffAt ℝ 1` regularity for the chart Christoffel field at the
  anchor chart image.
- Instantiated the M5-geo-1 chart ODE existence theorem for every anchor
  `x₀ : M` and every chart velocity `v₀ : ClosedSmoothModel n`.
- Packaged the pulled-back curve
  `c t = (extChartAt I x₀).symm (γ t).1`, with `c 0 = x₀` and eventual chart
  target/source membership near `0`.

## Next decomposition

1. Prove chart-overlap uniqueness: solutions driven by the two anchor chart
   Christoffel fields agree after transition on common domains, using
   `geodesicFlowField_eventuallyEq_of_contDiffAt` plus the existing transport
   uniqueness bridges.
2. Package the solution as a local geodesic germ on `M`, hiding the chart-pair
   state `γ : ℝ → E × E` behind a manifold-level API.
3. Define the exponential germ from the unique local solution and prove
   `exp_x 0 = x` and the chart derivative at `0` is the supplied velocity.

## Verification

Forbidden-token check:

```text
rg -n "sorry|axiom|native_decide" Poincare/Global/GeodesicTransport.lean
```

Actual result: no matches.

Required build command:

```text
lake build Poincare.Global.GeodesicTransport
```

Actual result:

```text
Build completed successfully (2824 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/GeodesicTransport.lean`.
