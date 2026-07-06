# M5-geo-9 blocked report

## New module

File: `Poincare/Global/ExponentialFixedTime.lean`

No existing Lean source file or root import was edited.  In particular,
`Poincare.lean` was not changed.

## Verified progress

### 1. Flow homogeneity on `Icc`

The new theorem

```lean
theorem Poincare.GeodesicTransport.exists_uniform_local_geodesic_chart_flow_with_mem_closedBall_mem_target_homogeneous
```

extends the target-shrunk PL package with the requested closed-interval
homogeneity statement.  It returns common `δ`, `ε`, `a`, and `α`, and for every
`‖v₀‖ < δ`, `s ∈ Icc 0 1`, and `σ ∈ Icc (-ε) ε` proves

```lean
α (extChartAt I x₀ x₀, s • v₀) σ =
  ((α (extChartAt I x₀ x₀, v₀) (s * σ)).1,
    s • (α (extChartAt I x₀ x₀, v₀) (s * σ)).2)
```

The proof reruns the target-shrunk PL construction locally so the
`IsPicardLindelof` witness is still in scope.  The reparametrized curve is
checked as a `HasDerivWithinAt` solution on the closed interval, its image is
kept in the common PL closed ball using `s ∈ [0,1]`, and interval uniqueness is
applied by `IsPicardLindelof.eqOn_Icc_of_mem_closedBall`.

### 2. Fixed-time endpoint map

The new definition is

```lean
noncomputable def Poincare.GeodesicTransport.expAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ClosedSmoothModel n → M
```

It is chosen from a fixed-time endpoint package.  The package uses
`τ = ε / 2` and, inside the honest ball, evaluates
`(extChartAt I x₀).symm (α (z₀, τ⁻¹ • w) τ).1`; outside the honest ball it uses
the documented junk value `x₀`.

Proved endpoint facts:

```lean
theorem Poincare.GeodesicTransport.expAt_zero :
  expAt g x₀ 0 = x₀

theorem Poincare.GeodesicTransport.expAt_eventually_eq_geodesicGermAt :
  ∃ τ > 0, ∃ δ > 0, ∀ v, ‖v‖ < δ →
    ∀ᶠ t in 𝓝[Icc 0 τ] 0,
      expAt g x₀ (t • v) = geodesicGermAt g x₀ v t

theorem Poincare.GeodesicTransport.expAt_mem_source_of_norm_lt :
  ∃ ρ > 0, ∀ v, ‖v‖ < ρ →
    expAt g x₀ v ∈ (extChartAt I x₀).source
```

## Remaining blocker

The full requested honest interval ray law

```lean
expAt g x₀ (t • v) = geodesicGermAt g x₀ v t
```

for every `t ∈ [0, τ)` is not proved in this module.  The available germ
identification is still only an `EventuallyEq` at `0` between the PL flow and
the separately chosen `geodesicGermChartSolution`.  The new homogeneity theorem
turns the fixed endpoint into the PL flow value at time `t`, but identifying
that PL value with the chosen germ for all `t < τ` would require an interval
identification of the chosen germ solution with the PL flow.

Concretely, the missing ingredient is one of:

- a strengthened exported theorem showing the chosen
  `geodesicGermChartSolution g x₀ v` agrees with the target-shrunk PL flow on a
  uniform interval, or
- enough closed-ball control for the chosen `geodesicGermChartSolution` to
  apply `IsPicardLindelof.eqOn_Icc_of_mem_closedBall` against the PL flow, or
- a redefinition/package tying the chosen geodesic germ directly to the same
  target-shrunk PL flow.

## Next decomposition

1. Prove PL-flow/germ interval identification for small `‖v‖`.
   The narrow goal is to upgrade the existing `EventuallyEq` germ identification
   to an `EqOn` statement on a concrete interval, or to expose a uniform germ
   choice from the same PL flow.

2. Upgrade the ray law from `𝓝[Icc 0 τ] 0` to all `t ∈ Ico 0 τ`.
   This should be a short endpoint theorem once item 1 exists.

3. Prove continuity and smoothness in `v`.
   Current Mathlib/local API status: this file only uses fixed-point existence
   and interval uniqueness.  It does not expose smooth dependence of the PL
   flow on initial data, so a genuine smoothness theorem will need either a
   parametric ODE/smooth-flow result or a new local package exporting that
   dependence.

4. Prove the derivative at `0`.
   After the honest ray law and enough continuity are available, the derivative
   should follow by comparing `expAt g x₀ (t • v)` with
   `geodesicGermAt g x₀ v t` and using the existing chart derivative of the
   geodesic germ.

5. Prepare Gauss lemma prerequisites.
   Needed inputs are smoothness of `expAt`, differential at `0`, and a proven
   geodesic/radial variation framework on the honest exponential domain.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ExponentialFixedTime.lean
```

Actual result: no matches.

Whitespace check:

```text
git diff --check -- Poincare/Global/ExponentialFixedTime.lean
```

Actual result: no output.

Required build command:

```text
lake build Poincare.Global.ExponentialFixedTime
```

Actual result:

```text
Build completed successfully (2830 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/ExponentialFixedTime.lean`.
