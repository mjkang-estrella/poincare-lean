# M5-rigid-89 blocked: pinned membership bound landed, actual membership remains circular

## Status

Added `Poincare/Global/MembershipBound.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The new module proves the explicit closed-ball bound for the speed-pinned norm
trajectory:

- `MembershipBound.speedPinnedMembershipRadius`
- `MembershipBound.speedPinned_mem_closedBall`
- `MembershipBound.speedPinned_mem_closedBall_of_radius_ge`
- `MembershipBound.speedPinned_mem_closedBall_on_Icc`
- `MembershipBound.speedPinned_mem_closedBall_on_Icc_of_radius_ge`
- `MembershipBound.actual_state_mem_closedBall_of_eq_speedPinned`
- `MembershipBound.actual_state_mem_closedBall_of_eq_speedPinned_of_radius_ge`

The radius is

```lean
max (max (|(speed ^ 2)⁻¹| * |q|) (|speed⁻¹| * |q|)) (2 * |q|)
```

and the proof uses `|sin| ≤ 1`, `|cos| ≤ 1`, the product norm on
`ℝ × ℝ × ℝ`, and a triangle bound for `|c - q|`.

## Blocker

The requested route says to use the pinned-value theorem to prove the actual
norm trajectory membership.  In the current API that is circular:

`CartanIsometryTheorem.actual_jacobi_norms_eq_speed_pinned_on_cutoff_one_Icc`
requires the actual membership before it proves the actual values are pinned.
The resisting premise is:

```lean
(hmem : ∀ s ∈ Icc tmin tmax,
  (JacobiNormSystem.normA g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ τ).1) s,
    JacobiNormSystem.normB g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ τ).1)
      (fun τ : ℝ =>
        (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s,
    JacobiNormSystem.normC g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ =>
        (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s) ∈
    closedBall ((0 : ℝ), (0 : ℝ), q) radius)
```

The downstream `SolutionsFeed` field is additionally all-direction with one
fixed finite `radius`:

```lean
(hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
  (JacobiNormSystem.normA g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ w τ).1) s,
    JacobiNormSystem.normB g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ w τ).1)
      (fun τ : ℝ =>
        (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
          (γ τ).2 (Ψ w τ).1) s,
    JacobiNormSystem.normC g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ =>
        (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
          (γ τ).2 (Ψ w τ).1) s) ∈
    closedBall ((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) radius)
```

The explicit pinned radius depends on

```lean
q = chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
      (T⁻¹ • w) (T⁻¹ • w)
```

so it cannot directly feed a single fixed-radius `∀ w : E3` membership.  It
can feed either a per-direction radius, a bounded-`w` version with a center
bound, or a fixed-radius version after a genuine side condition
`speedPinnedMembershipRadius speed q ≤ radius`.

## Verification

- `lake build Poincare.Global.MembershipBound`
  - Result: success.
  - Final lines:

```text
✔ [3180/3180] Built Poincare.Global.MembershipBound (1.9s)
Build completed successfully (3180 jobs).
```

- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/MembershipBound.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/MembershipBound.lean`
  - Result: success.
