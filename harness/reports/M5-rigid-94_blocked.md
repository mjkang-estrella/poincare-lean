# M5-rigid-94 blocked: PL packages exported only after interval shrink

## Status

Added `Poincare/Global/PLPackages.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module exports the non-vacuous PL construction that was missing from
`M5-rigid-93`:

- `PLPackages.exists_shrunk_zero_centered_pl_package_of_continuousOn_linearODE`
  bounds the operator norm on a compact time interval and constructs a
  zero-centered `IsPicardLindelof` package on a smaller symmetric interval.
- `PLPackages.exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage`
  specializes this to the linearized geodesic equation along an
  `EnrichedCascade.BaseCurvePackage`.
- `PLPackages.exists_selected_linearized_family_of_zero_centered_pl_package`
  feeds the package to the existing hosted rescaled-family selector, recovering
  initial values, derivative fields, endpoint additivity, and endpoint
  homogeneity.
- `PLPackages.exists_shrunk_pl_package_and_selected_linearized_family` bundles
  the package and selector for every endpoint time inside the shrunk interval.

## First resisting witness

The constructed PL package necessarily has a shrunk interval:

```lean
∃ εlin : ℝ, ∃ hεlin_pos : 0 < εlin, εlin ≤ εs ∧
  ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
    IsPicardLindelof
      (fun s : ℝ => fun ψ : E3 × E3 =>
        linearizedGeodesicFlowOperator
          (chartChristoffelField g x₀)
          (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
      (tmin := -εlin) (tmax := εlin)
      ⟨(0 : ℝ), by constructor <;> linarith [hεlin_pos]⟩
      ((0 : E3), (0 : E3)) aPL r Lip K
```

But `CommonTime.exists_common_time_enriched_source_target_cascade` still
selects the enriched linearized family only from a PL package on the original
exported interval:

```lean
∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
  IsPicardLindelof
    (fun s : ℝ => fun ψ : E3 × E3 =>
      linearizedGeodesicFlowOperator
        (chartChristoffelField g x₀)
        (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
    (tmin := -εs) (tmax := εs)
    ⟨(0 : ℝ), by constructor <;> linarith [hεs_pos]⟩
    ((0 : E3), (0 : E3)) aPL r Lip K →
  ∃ Ψ : E3 → ℝ → E3 × E3, ...
```

The missing alignment is not a theorem about existence of a PL package anymore;
it is a common-time shrink/export problem.  To feed the current common-time
selector, one needs either:

```lean
T ∈ Icc (-εlin) εlin
```

for the already selected common `T`, plus a replayed selector whose
`EnrichedCascade.LinearizedFamilyPackage` and strict derivative fields are
exported at `εlin`; or a strengthened common-time theorem that chooses `T`
after the source and target linearized-operator bounds are known.

The plain ODE family can be selected on the shrunk interval by
`PLPackages.exists_selected_linearized_family_of_zero_centered_pl_package`, but
that does not yet export the full enriched package fields needed downstream:

```lean
EnrichedCascade.LinearizedFamilyPackage g x₀ T εlin αs v PsiS
HasStrictFDerivAt
  (expAtChartOpenPartialHomeomorph (g := g) x₀)
  (linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls) v
```

Consequently the ray fields are still not reachable from public exports:

```lean
hSourceRay : (PsiS v T).1 = T • Vs
hTargetRay : (PsiT (align v) T).1 = T • Vt
```

`RayIdentification.radial_linearized_endpoint_eq_time_smul_velocity_of_uniform_geodesicFlow`
also needs the uniform-flow hypotheses (`δ`, `hα0`, `hαder`, `hαmem`,
`hαtarget`, `hexp`) used inside the common-time construction; those are not
exported by `EnrichedCascade.BaseCurvePackage`.

## Verification

- Forbidden-token scan on `Poincare/Global/PLPackages.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/PLPackages.lean`
  - Result: success.
- `lake build Poincare.Global.PLPackages`
  - Result: success.  The build replayed pre-existing imported-module warnings.
  - Final lines:

```text
✔ [3201/3201] Built Poincare.Global.PLPackages (2.9s)
Build completed successfully (3201 jobs).
```
