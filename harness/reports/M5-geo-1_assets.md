# M5-geo-1 assets report

## Mathlib inventory

- `Mathlib/Analysis/ODE/Basic.lean`: first-order vector-space integral-curve predicates:
  `IsIntegralCurveOn`, `IsIntegralCurveAt`, `IsIntegralCurve`.
- `Mathlib/Analysis/ODE/PicardLindelof.lean`: local existence. The useful entry point here is
  `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`, which gives an
  autonomous local solution on an `Ioo` interval from a `ContDiffAt ℝ 1` vector field on a complete
  normed space.
- `Mathlib/Analysis/ODE/Gronwall.lean`: uniqueness and comparison. The useful entry point here is
  `ODE_solution_unique_of_eventually`, fed by an eventually local `LipschitzOnWith` hypothesis.
- `Mathlib/Geometry/Manifold/IntegralCurve/*.lean`: first-order manifold vector-field integral
  curves and existence/uniqueness for `C¹` vector fields. These are not second-order geodesics and
  do not provide exponential maps.
- `Mathlib/Geometry/Manifold/Riemannian/Basic.lean` and `PathELength.lean`: Riemannian bundle
  metrics, induced extended distance/path e-length, and local chart distance estimates.
- Search result: no pinned Mathlib definitions/theorems for Riemannian `geodesic`, exponential map,
  Hopf-Rinow, or Killing-Hopf. Project files contain surgery/reduced-distance `L-geodesic`
  interface fields, but these are not Mathlib Riemannian geodesic foundations.

## New module

File: `Poincare/Global/GeodesicChart.lean`

No existing file or root import was edited.

Main definitions and theorem signatures:

```lean
def geodesicFlowField (Γ : E → E →L[ℝ] E →L[ℝ] E) :
    E × E → E × E :=
  fun p ↦ (p.2, -Γ p.1 p.2 p.2)

theorem contDiffAt_geodesicFlowField
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E}
    (hΓ : ContDiffAt ℝ 1 Γ p₀.1) :
    ContDiffAt ℝ 1 (geodesicFlowField Γ) p₀

theorem contDiff_geodesicFlowField
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiff ℝ 1 Γ) :
    ContDiff ℝ 1 (geodesicFlowField Γ)

theorem exists_geodesicFlowField_solution_of_contDiffAt
    [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E}
    (hΓ : ContDiffAt ℝ 1 (geodesicFlowField Γ) p₀) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = p₀ ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (geodesicFlowField Γ (γ t)) t

theorem exists_geodesicFlowField_solution
    [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E}
    (hΓ : ContDiffAt ℝ 1 Γ p₀.1) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = p₀ ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (geodesicFlowField Γ (γ t)) t

theorem exists_geodesicFlowField_solution_of_contDiff
    [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ 1 Γ) (p₀ : E × E) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = p₀ ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (geodesicFlowField Γ (γ t)) t

theorem geodesicFlowField_eventuallyEq_of_lipschitz
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ η : ℝ → E × E}
    {K : ℝ≥0} {s : ℝ → Set (E × E)}
    (hLip : ∀ᶠ t in 𝓝 (0 : ℝ),
      LipschitzOnWith K (fun p ↦ geodesicFlowField Γ p) (s t))
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ (geodesicFlowField Γ (γ t)) t ∧ γ t ∈ s t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η (geodesicFlowField Γ (η t)) t ∧ η t ∈ s t)
    (h0 : γ 0 = η 0) :
    γ =ᶠ[𝓝 (0 : ℝ)] η

theorem geodesicFlowField_eventuallyEq_of_contDiffAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E} {γ η : ℝ → E × E}
    (hΓ : ContDiffAt ℝ 1 (geodesicFlowField Γ) p₀)
    (hγ0 : γ 0 = p₀) (hη0 : η 0 = p₀)
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ (geodesicFlowField Γ (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η (geodesicFlowField Γ (η t)) t) :
    γ =ᶠ[𝓝 (0 : ℝ)] η

theorem geodesic_position_hasDerivAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E} {t : ℝ}
    (hγ : HasDerivAt γ (geodesicFlowField Γ (γ t)) t) :
    HasDerivAt (fun τ ↦ (γ τ).1) (γ t).2 t

theorem geodesic_velocity_hasDerivAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E} {t : ℝ}
    (hγ : HasDerivAt γ (geodesicFlowField Γ (γ t)) t) :
    HasDerivAt (fun τ ↦ (γ τ).2) (-(Γ (γ t).1) (γ t).2 (γ t).2) t

theorem geodesic_components_hasDerivAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E}
    {I : Set ℝ}
    (hγ : ∀ t ∈ I, HasDerivAt γ (geodesicFlowField Γ (γ t)) t) :
    (∀ t ∈ I, HasDerivAt (fun τ ↦ (γ τ).1) (γ t).2 t) ∧
      ∀ t ∈ I,
        HasDerivAt (fun τ ↦ (γ τ).2)
          (-(Γ (γ t).1) (γ t).2 (γ t).2) t
```

## Adaptations

- The core existence theorem is stated at the `ContDiffAt` level because that is the exact
  hypothesis consumed by Mathlib's autonomous Picard-Lindelof theorem. The file also proves
  `contDiffAt_geodesicFlowField`, `exists_geodesicFlowField_solution`, and
  `exists_geodesicFlowField_solution_of_contDiff`, so a local or global `C¹` Christoffel field
  yields the requested local solution.
- The core uniqueness theorem has an explicit eventually local `LipschitzOnWith` hypothesis because
  this is the exact Gronwall API. The `ContDiffAt` convenience theorem obtains that local
  Lipschitz neighborhood from `ContDiffAt.exists_lipschitzOnWith`.
- Generality is a real normed space `E`; existence requires `[CompleteSpace E]`. No finite
  dimensionality was needed.

## Roadmap

1. Define chart Christoffel fields for `ClosedSmoothRiemannianMetric n M` by transporting
   `g.leviCivita` through `extChartAt`, using the regularity in `Poincare/Global/Curvature.lean`
   and transport machinery in `Poincare/Global/LeviCivitaTransport.lean`.
2. Prove these transported Christoffel fields are `ContDiffAt ℝ 1` on chart targets and instantiate
   `exists_geodesicFlowField_solution` for `ClosedSmoothModel n = EuclideanSpace ℝ (Fin n)`.
3. Package a chart geodesic as a curve in `M` by applying the inverse extended chart to the position
   component, and prove independence/uniqueness on overlapping charts from
   `geodesicFlowField_eventuallyEq_of_contDiffAt`.
4. Define local exponential-map germs from the unique chart solution and prove the basic initial
   properties: `exp_x 0 = x` and derivative at `0` equals the initial velocity.
5. Build the manifold-level Hopf-Rinow/Killing-Hopf prerequisites only after the local geodesic and
   exponential-map API exists; the current pinned Mathlib has no ready-made global geodesic layer.

## Verification

Command run:

```text
lake build Poincare.Global.GeodesicChart
```

Actual result:

```text
Build completed successfully (2665 jobs).
```
