# M5-rigid-55 blocked: sine formula is abstract/covariant, not raw chart harmonic

## Status

Added `Poincare/Global/PositionRoute.lean` and did not edit existing Lean files,
including `Poincare.lean`.

The position-only action consumer is verified, but the full route is still
blocked by one missing geometric statement: an endpoint position bridge from the
hosted chart-linearized state to an abstract covariant harmonic Jacobi state.
The missing statement is not the false raw-coordinate acceleration collapse
refuted by M5-rigid-53 and M5-rigid-54.

## Audit findings

### 1. Where the sine formula lives

`JacobiOscillator.lean`'s sine theorem is not a raw stereographic/chart
linearized theorem.  Its statement is an abstract first-order harmonic
oscillator on `E3 × E3`:

```lean
theorem jacobi_position_eq_sin_smul_on_Icc
    {tmin tmax : ℝ} (w : E3) (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E3 × E3 => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩ ((0 : E3), w) a r L K)
    {Ψ : ℝ → E3 × E3}
    (hΨ : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt Ψ (harmonicJacobiOperator (Ψ t)) (Icc tmin tmax) t)
    (hΨmem : ∀ t ∈ Icc tmin tmax, Ψ t ∈ closedBall ((0 : E3), w) a)
    (hsinmem : ∀ t ∈ Icc tmin tmax, jacobiSinState w t ∈ closedBall ((0 : E3), w) a)
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (Ψ t).1 = Real.sin t • w
```

The operator consumed there is exactly:

```lean
def harmonicJacobiOperator : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod (-(ContinuousLinearMap.fst ℝ E E))
```

So the theorem proves the position formula only after some state has already
been placed in the abstract oscillator chart/frame where the derivative state is
the covariant derivative.

### 2. The geometric cutoff-one theorem is covariant

The geometric theorem in `JacobiOscillator.lean` lives in the anchor
`extChartAt I3 x₀` model coordinates, but only under the cutoff-one germ:

```lean
(htarget : (γ t).1 ∈ (extChartAt I3 x₀).target)
(hχone : ∀ᶠ z' in 𝓝 (γ t).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
(hunit : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 = 1)
(horth : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (Ψ t).1 (γ t).2 = 0)
```

Its conclusion is the covariant oscillator, not raw coordinate acceleration:

```lean
coordinateCovariantJacobiSecond
    (GeodesicTransport.chartChristoffelField g x₀)
    (γ t).1 (γ t).2 (Ψ t).1 (Ψ t).2 = -(Ψ t).1
```

This is exactly the distinction made in `JacobiConstantCurvature.lean`:

```lean
def coordinateJacobiAcceleration
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (base ψ : E × E) : E :=
  -((fderiv ℝ Γ base.1) ψ.1 base.2 base.2) -
    Γ base.1 ψ.2 base.2 - Γ base.1 base.2 ψ.2
```

```lean
def coordinateCovariantJacobiSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (z v J K : E) : E :=
  coordinateJacobiAcceleration Γ (z, v) (J, K)
    + ((fderiv ℝ Γ z) v) v J
    - Γ z (Γ z v v) J
    + Γ z v K
    + Γ z v (K + Γ z v J)
```

Thus `sin(st) • w` should not be expected to solve the hosted raw
`coordinateJacobiAcceleration` equation in the stereographic chart.  That is
precisely what the M5-rigid-53 and M5-rigid-54 counterexamples established.

### 3. What `CartanIsometryTheorem.lean` actually discharged

`CartanIsometryTheorem.lean` discharges the pointwise geometric oscillator only
through `JacobiNormClose.chart_linearized_state_feeds_norm_system_at`, and it
uses the corrected covariant derivative state:

```lean
let D : ℝ → E3 :=
  fun τ => (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1
```

The call site is:

```lean
have hfeed :=
  JacobiNormClose.chart_linearized_state_feeds_norm_system_at
    (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
    (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
    (hunit s hs) (horth s hs) (hGd s hs)
```

Inside `JacobiNormClose.lean`, the same correction is explicit:

```lean
let D : ℝ → E3 :=
  fun τ => (Ψ τ).2 +
    (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1
```

So the object satisfying the geometric Jacobi input is the hosted
chart-linearized position together with the covariant derivative correction,
not the raw hosted coordinate state `(J,K)` as a harmonic first-order ODE.

## Verified formal progress

`Poincare/Global/PositionRoute.lean` exports two theorems:

```text
Poincare.PositionRoute.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_transverse_position
Poincare.PositionRoute.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_covariant_position
```

The first proves the source action equation from:

```lean
(Psi transverse T).1 =
  CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T • transverse
```

The second composes that direct position consumer with
`jacobi_position_eq_sin_smul_on_Icc` for an abstract covariant harmonic state
`Jcov`, using only the endpoint position bridge:

```lean
(Psi transverse T).1 = (Jcov transverse (speed * T)).1
```

This bypasses `hΦderHosted` and `haccCollapse` at the action-equation consumer
level.

## One true missing statement

The remaining theorem should be a vector-level covariant position bridge, not a
raw-coordinate harmonic claim.  In Lean-shaped terms, for the hosted
linearized solution `Psi` and base `γ`, one needs to construct or identify an
abstract covariant harmonic state `Jcov` such that, for each transverse input
`w` on the shared interval:

```lean
HasDerivWithinAt (Jcov w)
  (harmonicJacobiOperator (Jcov w τ)) (Icc tmin tmax) τ
```

with the expected initial state, and with the endpoint position bridge:

```lean
(Psi w T).1 = (Jcov w (speed * T)).1
```

Equivalently, this bridge must formalize that the hosted chart-linearized state
`(J,K)` and the covariant Jacobi state with
`D = K + Γ(γ)(γ',J)` have the same position component, while the covariant
oscillator is expressed in the correct covariant/parallel frame.  No theorem
currently exports that vector-level bridge from the cutoff-one hypotheses.

## Verification

Forbidden-token scan on the new Lean file:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/PositionRoute.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/PositionRoute.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.PositionRoute
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3161/3161] Built Poincare.Global.PositionRoute (13s)
Build completed successfully (3161 jobs).
```
