# M5-rigid-2 report: tangent alignment exists

## Verification

- `lake build Poincare.Global.TangentAlignmentExists`: **success**.
- The build completed with replayed upstream warnings only; the new module built.
- `rg -n "sorry|axiom|native_decide" Poincare/Global/TangentAlignmentExists.lean`: no matches.

## Added file

- `Poincare/Global/TangentAlignmentExists.lean`

No existing Lean file or import aggregator was edited.

## Verified signatures

```lean
def Poincare.CartanMap.BilinFormSpace
def Poincare.CartanMap.BilinFormSpace.ofModel
def Poincare.CartanMap.BilinFormSpace.toModel
def Poincare.CartanMap.BilinFormSpace.innerProductCore
def Poincare.CartanMap.positiveDefiniteBilinFormIsometryEquiv

theorem Poincare.CartanMap.tangentAlignment_nonempty
theorem Poincare.CartanMap.exists_sourceTargetHomeomorph_cartanMap_anchor
```

## What is proved

The new module constructs a genuine tangent alignment from the two anchor chart
metrics.  The proof turns each positive-definite symmetric bilinear form on the
finite-dimensional model space into an `InnerProductSpace.Core` on a tagged copy
of the model space, chooses the standard orthonormal basis for each induced
inner product, maps one basis to the other by `Orthonormal.equiv`, and packages
the resulting linear isometry as a `LinearMap.BilinForm.IsometryEquiv`.

This instantiates the parameterized Cartan-map opener from rigid-1:

```lean
∃ L : TangentAlignment g x₀ p₀,
  ∃ _ : (openPartialHomeomorph g x₀ p₀ L).source ≃ₜ
      (openPartialHomeomorph g x₀ p₀ L).target,
    cartanMap g x₀ p₀ L x₀ = p₀
```

## Next tasks

The next work remains the Jacobi-comparison roadmap from rigid-1:

1. Identify `D(expAt)` on radial and transverse directions using the existing
   linearized geodesic-flow/Jacobi machinery.
2. In constant curvature `1`, prove the transverse Jacobi factor is
   `sin t / t` on both `M` and `RoundSphere3`; the radial factor is `1`.
3. Combine those formulas with `TangentAlignment.map_app` at the anchor to show
   the pullback metric of `roundSphereMetric3` by `cartanMap` equals `g` on the
   normal source.
4. After metric preservation, promote the local isometry through covering,
   connectedness, and simple-connectedness arguments toward the
   `UnitConstantCurvatureSphereRecognition3` interface.
