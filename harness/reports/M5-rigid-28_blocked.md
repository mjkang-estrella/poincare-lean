# M5-rigid-28 blocked: polarized Jacobi pairing strict partial

## Files

- Added `Poincare/Global/CartanIsometryPackage.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Verified strict partial

The new module contains one isolated non-vacuous statement:

```lean
theorem Poincare.CartanIsometryPackage.actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique
```

This proves the polarization stage after `M5-rigid-27`.

Given three quadratic endpoint norm identities of the exact form supplied by

```lean
CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc
```

for initial transverse directions `w`, `w'`, and `w + w'`, it first proves the
missing state linearity

```lean
(Ψadd t).1 = (Ψw t).1 + (Ψw' t).1
```

from `linearODE_solution_uniqueOn_Icc` applied to the linearized geodesic flow.
It then applies `JacobiNormSystem.polarize_endpoint_pairing_of_quadratic` to
derive the bilinear endpoint pairing:

```lean
chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw' t).1 =
  Real.sin t ^ 2 *
    chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w'
```

No `Jadd` linearity hypothesis is assumed; the theorem derives it from the
linearized-flow PL uniqueness surface.

## Remaining obstruction

The full exp-chart metric coefficient package and local-isometry conclusion are
still blocked by the same public API boundary visible in the earlier Cartan
assembly files.

The repository now has:

- the cutoff-one quadratic scalar identities from `CartanIsometryTheorem`;
- the polarization/linearity strict partial in this module;
- the downstream Cartan local-isometry consumers in `CartanLocalIsometry`,
  `CartanExpansionBridge`, `CartanPunctured`, and `CartanWeightInvariant`.

What is still not exported is the geometric coefficient bridge turning the
polarized Jacobi pairings, radial-radial Gauss input, radial-transverse
integrated Gauss input, and flow-derivative identification into the
source-owned punctured endpoint expansion consumed by:

```lean
CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion
```

The existing `CartanSourceOwned.lean` and `CartanAssembly.lean` files still
record this as theorem-free boundary surface.  I therefore did not add a
wrapper claiming the full coefficient formulas or final local-isometry theorem.

## Verification

Forbidden-placeholder scan on `Poincare/Global/CartanIsometryPackage.lean`
found no matches.

Top-level declaration scan found exactly one declaration:

```text
43:theorem actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique
```

Diff whitespace check:

```bash
git diff --check
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanIsometryPackage
```

Actual result: success. Final output ended with:

```text
✔ [3152/3152] Built Poincare.Global.CartanIsometryPackage (3.0s)
Build completed successfully (3152 jobs).
```

The build replayed existing upstream warnings; after trimming the unused
`T2Space` assumption, it emitted no new warning from
`Poincare/Global/CartanIsometryPackage.lean`.
