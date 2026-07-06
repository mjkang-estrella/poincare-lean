# M5-model-3 done: stereographic conformal factor

## Completed

- Added `Poincare/Global/RoundSphereChart.lean`.
- Proved the ambient Euclidean stereographic inverse derivative formula for
  Mathlib's `stereoInvFunAux`.
- Proved the orthogonal-complement pullback metric formula:

  ```lean
  theorem inner_fderiv_stereoInvFunAux_comp_subtype (v : E) (hv : ‖v‖ = 1)
      (z u w : (ℝ ∙ v)ᗮ) :
      inner ℝ
          (fderiv ℝ (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) z u)
          (fderiv ℝ (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) z w) =
        stereoInvFunAuxConformalFactor (z : E) * inner ℝ u w
  ```

## Final Signatures

```lean
def stereoInvFunAuxConformalFactor (z : E) : ℝ :=
  16 / (‖z‖ ^ 2 + 4) ^ 2

noncomputable def stereoInvFunAuxFDeriv (v z : E) : E →L[ℝ] E

theorem stereoInvFunAuxFDeriv_apply (v z u : E) :
    stereoInvFunAuxFDeriv v z u =
      (4 * (‖z‖ ^ 2 + 4)⁻¹) • u
        - (8 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 2 * inner ℝ z u) • z
        + (16 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 2 * inner ℝ z u) • v

theorem hasFDerivAt_stereoInvFunAuxFDeriv (v z : E) :
    HasFDerivAt (stereoInvFunAux v) (stereoInvFunAuxFDeriv v z) z

theorem fderiv_stereoInvFunAux (v z : E) :
    fderiv ℝ (stereoInvFunAux v) z = stereoInvFunAuxFDeriv v z

theorem fderiv_stereoInvFunAux_comp_subtype (v : E) (z : (ℝ ∙ v)ᗮ) :
    fderiv ℝ (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) z =
      (stereoInvFunAuxFDeriv v (z : E)).comp (ℝ ∙ v)ᗮ.subtypeL

theorem inner_stereoInvFunAuxFDeriv_of_mem_orthogonal {v z u w : E}
    (hv : ‖v‖ = 1) (hz : z ∈ (ℝ ∙ v)ᗮ)
    (hu : u ∈ (ℝ ∙ v)ᗮ) (hw : w ∈ (ℝ ∙ v)ᗮ) :
    inner ℝ (stereoInvFunAuxFDeriv v z u) (stereoInvFunAuxFDeriv v z w) =
      stereoInvFunAuxConformalFactor z * inner ℝ u w
```

## Constant Derivation

Mathlib defines

```lean
stereoInvFunAux v z =
  (‖z‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • z + (‖z‖ ^ 2 - 4) • v)
```

Writing `r = ‖z‖ ^ 2 + 4` and `p = inner ℝ z u`, differentiation gives

```text
Dψ_z(u) = (4 / r) u - (8 p / r^2) z + (16 p / r^2) v.
```

For `z,u,w : (ℝ ∙ v)ᗮ` and `‖v‖ = 1`, the cross terms involving
`-z + 2v` cancel, leaving

```text
inner (Dψ_z u) (Dψ_z w) = 16 / r^2 * inner u w.
```

Thus the conformal factor is exactly `16 / (‖z‖ ^ 2 + 4) ^ 2` for
Mathlib's normalization.

## Tie-in Roadmap

The bundle-level tie-in to `roundSphereMetric3` was not added in this file.
The next lemma should identify the inverse `stereographic'` chart as

```text
stereoInvFunAux (-x0.val) ∘ Subtype.val ∘ U.symm
```

where `U` is Mathlib's
`OrthonormalBasis.fromOrthogonalSpanSingleton 3 ... .repr`, then combine:

- `roundSphereMetric3_inner_mfderiv_eq`,
- the chain rule for `mfderiv` of the inclusion after `(chartAt _ x0).symm`,
- `fderiv_stereoInvFunAux_comp_subtype`,
- `LinearIsometryEquiv.inner_map_map` for the `U.symm` identification.

That should express the metric in the Euclidean chart as
`stereoInvFunAuxConformalFactor (U.symm z : E) * inner ℝ v w`.

Curvature path after this coefficient formula:

1. Feed the conformal metric coefficients into the local Christoffel formulas.
2. Compute curvature operator coefficients in stereographic coordinates.
3. Package the result as `HasConstantSectionalCurvature3 roundSphereMetric3 1`,
   unless the chart computation forces a different normalization constant.

## Verification

Command run:

```bash
lake build Poincare.Global.RoundSphereChart
```

Actual result: success.

The edited Lean file contains no `sorry`, no new `axiom`, and no
`native_decide`.
