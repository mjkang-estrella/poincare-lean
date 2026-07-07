# M5-rigid-1 report: Cartan map opener

## Verification

- `lake build Poincare.Global.CartanMap`: **success**.
- The build completed with replayed upstream warnings only; the new module built.
- No forbidden proof placeholders, new axiomatic declarations, or native decision shortcuts were added.

## Added file

- `Poincare/Global/CartanMap.lean`

No existing Lean module or import aggregator was edited.

## Verified signatures

```lean
def Poincare.CartanMap.sourceAnchorChartMetric
def Poincare.CartanMap.targetAnchorChartMetric
def Poincare.CartanMap.continuousBilinFormToBilinForm
def Poincare.CartanMap.sourceAnchorBilinForm
def Poincare.CartanMap.targetAnchorBilinForm

abbrev Poincare.CartanMap.TangentAlignment
theorem Poincare.CartanMap.sourceAnchorChartMetric_symm
theorem Poincare.CartanMap.targetAnchorChartMetric_symm
theorem Poincare.CartanMap.sourceAnchorChartMetric_pos
theorem Poincare.CartanMap.targetAnchorChartMetric_pos
theorem Poincare.CartanMap.TangentAlignment.map_app

def Poincare.CartanMap.TangentAlignment.toContinuousLinearEquiv
def Poincare.CartanMap.tangentAlignmentOpenPartialHomeomorph

def Poincare.CartanMap.openPartialHomeomorph
def Poincare.CartanMap.cartanMap
theorem Poincare.CartanMap.cartanMap_apply
theorem Poincare.CartanMap.cartanMap_anchor
theorem Poincare.CartanMap.anchor_mem_source
theorem Poincare.CartanMap.anchor_mem_target
theorem Poincare.CartanMap.isOpen_source
theorem Poincare.CartanMap.isOpen_target
def Poincare.CartanMap.sourceTargetHomeomorph
```

## What is proved

The file packages the candidate Cartan map as the composition

```lean
chartAt x₀ ; (expAtChartOpenPartialHomeomorph g x₀).symm ;
L ; expAtChartOpenPartialHomeomorph roundSphereMetric3 p₀ ; (chartAt p₀).symm
```

where `L : TangentAlignment g x₀ p₀` is a bilinear-form isometry between the two anchor chart metrics. The verified facts include:

- the source and target anchor chart metrics are symmetric and positive definite;
- `L` preserves those anchor bilinear forms by `TangentAlignment.map_app`;
- `cartanMap g x₀ p₀ L x₀ = p₀`;
- `x₀` is in the source and `p₀` is in the target of the composed `OpenPartialHomeomorph`;
- the source and target are open, and the source-target restriction is a homeomorphism.

## Blocker

The only missing opener item is an unconditional construction of an inhabitant

```lean
Nonempty (TangentAlignment g x₀ p₀)
```

from the two positive-definite chart bilinear forms. Mathlib exposes `LinearMap.BilinForm.IsometryEquiv` and its `refl`/`symm`/`trans` API, but I did not find a ready classification or Gram-Schmidt constructor for arbitrary positive-definite bilinear forms on the same finite-dimensional real model space. The current file therefore parameterizes the Cartan map by a genuine `L`, not by a vacuous certificate.

The local-homeomorphism statement is also phrased for the open source of the composed `OpenPartialHomeomorph`, not yet for a named metric ball. Since `anchor_mem_source` and `isOpen_source` are proved, a later task can restrict to a smaller explicit normal neighborhood once the desired ball formulation is fixed.

## Jacobi-comparison roadmap

Next tasks should prove metric preservation on the open source:

1. Use the existing linearized geodesic-flow/Jacobi machinery to identify `D(expAt)` on radial and transverse directions.
2. In constant curvature `1`, prove the transverse Jacobi factor is `sin t / t` on both `M` and `RoundSphere3`; the radial factor is `1`.
3. Combine those formulas with `TangentAlignment.map_app` at the anchor to show the pullback metric of `roundSphereMetric3` by `cartanMap` equals `g` on the normal source.
4. After metric preservation, promote the local isometry through covering/connected/simply-connected arguments toward the `UnitConstantCurvatureSphereRecognition3` interface.
