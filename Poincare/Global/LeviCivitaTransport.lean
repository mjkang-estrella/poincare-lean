import Poincare.ChartTransport
import Poincare.ChartIdentification
import Poincare.Global.LeviCivitaExistence

/-!
# Chart transport for Levi-Civita values

This file records the value-level chart transport used by the local
Levi-Civita regularity argument.  It keeps the construction local to one
extended chart: pull a tangent field to the model space, apply the already
constructed chart Levi-Civita connection there, and push the resulting model
tangent vector back through the inverse chart derivative.
-/

noncomputable section

open Bundle Set FiberBundle
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- Pull a manifold tangent field back to the model chart through the inverse extended chart. -/
noncomputable def chartTransportedLeviCivitaSection
    (x₀ : M) (σ : Π y : M, TangentSpace I y) :
    Π z : E, TangentSpace 𝓘(ℝ, E) z :=
  VectorField.mpullbackWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) σ (range I)

omit [IsManifold I 1 M] in
@[simp]
theorem chartTransportedLeviCivitaSection_apply
    (x₀ : M) (σ : Π y : M, TangentSpace I y) (z : E) :
    chartTransportedLeviCivitaSection (I := I) x₀ σ z =
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z).inverse
        (σ ((extChartAt I x₀).symm z)) :=
  rfl

/--
At a point in the chart source, the transported model section is the chart
derivative of the original tangent field.
-/
theorem chartTransportedLeviCivitaSection_apply_chart
    (x₀ : M) (σ : Π y : M, TangentSpace I y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) :
    chartTransportedLeviCivitaSection (I := I) x₀ σ (extChartAt I x₀ y) =
      mfderiv% (extChartAt I x₀) y (σ y) := by
  rw [chartTransportedLeviCivitaSection_apply]
  have htarget : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  have h1 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := I) (x := x₀) htarget
  have h2 := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    (I := I) (x := x₀) htarget
  have hinv :
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I)
        (extChartAt I x₀ y)).inverse =
        mfderiv% (extChartAt I x₀) y := by
    have hinv0 := ContinuousLinearMap.inverse_eq h2 h1
    rw [hleft] at hinv0
    exact hinv0
  rw [hinv, hleft]

/--
On the fixed chart target, the chart metric evaluated on inverse-chart
transported fields recovers the original manifold metric.
-/
theorem chartMetric_chartTransportedLeviCivitaSection
    [FiniteDimensional ℝ E]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) (Y Z : Π y : M, TangentSpace I y) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    chartMetric g x₀ z
        (chartTransportedLeviCivitaSection (I := I) x₀ Y z)
        (chartTransportedLeviCivitaSection (I := I) x₀ Z z) =
      g ((extChartAt I x₀).symm z)
        (Y ((extChartAt I x₀).symm z))
        (Z ((extChartAt I x₀).symm z)) := by
  let D : TangentSpace 𝓘(ℝ, E) z →L[ℝ]
      TangentSpace I ((extChartAt I x₀).symm z) :=
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z
  have hD : D.IsInvertible :=
    isInvertible_mfderivWithin_extChartAt_symm (I := I) hz
  have hY :
      D (D.inverse (Y ((extChartAt I x₀).symm z))) =
        Y ((extChartAt I x₀).symm z) :=
    (hD.inverse_apply_eq.mp rfl).symm
  have hZ :
      D (D.inverse (Z ((extChartAt I x₀).symm z))) =
        Z ((extChartAt I x₀).symm z) :=
    (hD.inverse_apply_eq.mp rfl).symm
  rw [chartMetric_apply, chartTransportedLeviCivitaSection_apply,
    chartTransportedLeviCivitaSection_apply]
  change g ((extChartAt I x₀).symm z)
      (D (D.inverse (Y ((extChartAt I x₀).symm z))))
      (D (D.inverse (Z ((extChartAt I x₀).symm z)))) =
    g ((extChartAt I x₀).symm z)
      (Y ((extChartAt I x₀).symm z))
      (Z ((extChartAt I x₀).symm z))
  rw [hY, hZ]

/--
In the boundaryless case, inverse-chart transport commutes with Lie brackets
at source points where the original fields are differentiable.
-/
theorem chartTransportedLeviCivitaSection_mlieBracket_apply_chart
    [IsManifold I (minSmoothness ℝ 2) M] [I.Boundaryless] [CompleteSpace E]
    (x₀ : M) {X Y : Π y : M, TangentSpace I y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hX : MDiffAt (T% X) y) (hY : MDiffAt (T% Y) y) :
    chartTransportedLeviCivitaSection (I := I) x₀
        (VectorField.mlieBracket I X Y) (extChartAt I x₀ y) =
      VectorField.mlieBracket 𝓘(ℝ, E)
        (chartTransportedLeviCivitaSection (I := I) x₀ X)
        (chartTransportedLeviCivitaSection (I := I) x₀ Y)
        (extChartAt I x₀ y) := by
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  have htarget : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hsmWithin :
      CMDiffAt[range I] 2 ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) :=
    contMDiffWithinAt_extChartAt_symm_range (n := 2) x₀ htarget
  have hsm :
      CMDiffAt 2 ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) := by
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at hsmWithin
  have hX' :
      MDiffAt (T% X) (((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)) := by
    rw [hleft]
    exact hX
  have hY' :
      MDiffAt (T% Y) (((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)) := by
    rw [hleft]
    exact hY
  have hbracket := VectorField.mpullback_mlieBracket
    (I := 𝓘(ℝ, E)) (I' := I)
    (f := ((extChartAt I x₀).symm : E → M))
    (V := X) (W := Y) (x₀ := extChartAt I x₀ y)
    (n := 2)
    hX' hY'
    hsm (by simp)
  simpa [chartTransportedLeviCivitaSection, I.range_eq_univ] using hbracket

/--
The inverse-chart pullback of a differentiable tangent field is
differentiable at source points after applying the chart.
-/
theorem chartTransportedLeviCivitaSection_mdiffAt_apply_chart
    [IsManifold I (minSmoothness ℝ 2) M] [I.Boundaryless] [CompleteSpace E]
    (x₀ : M) {X : Π y : M, TangentSpace I y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source) (hX : MDiffAt (T% X) y) :
    MDiffAt (T% (chartTransportedLeviCivitaSection (I := I) x₀ X))
      (extChartAt I x₀ y) := by
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  have htarget : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hsmWithin :
      CMDiffAt[range I] 2 ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) :=
    contMDiffWithinAt_extChartAt_symm_range (n := 2) x₀ htarget
  have hsm :
      CMDiffAt 2 ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) := by
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at hsmWithin
  have hinv :
      (mfderiv% ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)).IsInvertible := by
    have hinvWithin := isInvertible_mfderivWithin_extChartAt_symm htarget
    rwa [I.range_eq_univ, mfderivWithin_univ] at hinvWithin
  have hX' :
      MDiffAt[univ] (T% X) (((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)) := by
    rw [hleft, mdifferentiableWithinAt_univ]
    exact hX
  have hpull := hX'.mpullback_vectorField_preimage hsm hinv (by norm_num)
  rw [preimage_univ, mdifferentiableWithinAt_univ] at hpull
  simpa [chartTransportedLeviCivitaSection, I.range_eq_univ] using hpull

section ChartConnection

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/--
The model-coordinate value obtained after applying the chart Levi-Civita
connection and pushing the result back through the inverse chart derivative.
-/
noncomputable def chartTransportedLeviCivitaModelValue
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) z).IsInvertible)
    (σ : Π y : M, TangentSpace I y) (z : E)
    (u : TangentSpace 𝓘(ℝ, E) z) :
    TangentSpace I ((extChartAt I x₀).symm z) :=
  mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z
    ((chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
      (chartTransportedLeviCivitaSection (I := I) x₀ σ) z) u)

theorem chartTransportedLeviCivitaModelValue_apply
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) z).IsInvertible)
    (σ : Π y : M, TangentSpace I y) (z : E)
    (u : TangentSpace 𝓘(ℝ, E) z) :
    chartTransportedLeviCivitaModelValue χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
        hsupp σ z u =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z
        ((chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
          (chartTransportedLeviCivitaSection (I := I) x₀ σ) z) u) :=
  rfl

/--
The transported value at a manifold point in the chart source, applied to a
tangent direction at that point.
-/
noncomputable def chartTransportedLeviCivitaValueAt
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) z).IsInvertible)
    (σ : Π y : M, TangentSpace I y) {y : M}
    (_hy : y ∈ (extChartAt I x₀).source) (v : TangentSpace I y) :
    TangentSpace I y :=
  chartTransportedLeviCivitaModelValue χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
    hsupp σ (extChartAt I x₀ y) (mfderiv% (extChartAt I x₀) y v)

theorem chartTransportedLeviCivitaValueAt_apply
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) z).IsInvertible)
    (σ : Π y : M, TangentSpace I y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) (v : TangentSpace I y) :
    chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
        hsupp σ hy v =
      chartTransportedLeviCivitaModelValue χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
        hsupp σ (extChartAt I x₀ y) (mfderiv% (extChartAt I x₀) y v) :=
  rfl

omit [IsManifold I 1 M] [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The source hypothesis puts the chart coordinate in the inverse-chart target. -/
theorem chartTransportedLeviCivita_mem_target
    (x₀ : M) {y : M} (hy : y ∈ (extChartAt I x₀).source) :
    extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
  (extChartAt I x₀).map_source hy

omit [IsManifold I 1 M] [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The inverse chart sends the chart coordinate of a source point back to that point. -/
theorem chartTransportedLeviCivita_left_inv
    (x₀ : M) {y : M} (hy : y ∈ (extChartAt I x₀).source) :
    (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
  (extChartAt I x₀).left_inv hy

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The chart derivative and inverse-chart derivative round-trip tangent directions. -/
theorem chartTransportedLeviCivita_direction_roundtrip
    (x₀ : M) {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (v : TangentSpace I y) :
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I)
        (extChartAt I x₀ y) (mfderiv% (extChartAt I x₀) y v) = v := by
  have h := congrArg (fun L => L v)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (I := I) (x := x₀) hy)
  simpa [ContinuousLinearMap.comp_apply] using h

/--
At a chart-source point, the value-level transported chart Levi-Civita
operator has zero torsion. This is the torsion-free theorem for the
transported values; the remaining bridge obstruction is packaging these
values as a bundled manifold `CovariantDerivative`.
-/
theorem chartTransported_torsionFreeAt
    [IsManifold I (minSmoothness ℝ 2) M] [I.Boundaryless]
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) z).IsInvertible)
    (hbl : Differentiable ℝ (blendedChartMetric χ G₀ g x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    {X Y : Π y : M, TangentSpace I y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hX : MDiffAt (T% X) y) (hY : MDiffAt (T% Y) y) :
    chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
        hsupp Y hy (X y)
      - chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0
        hχ1 hsupp X hy (Y y) =
      VectorField.mlieBracket I X Y y := by
  let z : E := extChartAt I x₀ y
  let D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I y :=
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z
  let Xc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ X
  let Yc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ Y
  let covC := chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  have hXc : MDiffAt (T% Xc) z := by
    simpa [Xc, z] using
      chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        (I := I) x₀ hy hX
  have hYc : MDiffAt (T% Yc) z := by
    simpa [Yc, z] using
      chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        (I := I) x₀ hy hY
  have ht :
      covC Yc z (Xc z) - covC Xc z (Yc z) =
        VectorField.mlieBracket 𝓘(ℝ, E) Xc Yc z :=
    chartLeviCivita_torsionFreeAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
      hsupp hbl hG₀symm hgsymm z hXc hYc
  have hpush :
      D (covC Yc z (Xc z)) - D (covC Xc z (Yc z)) =
        D (VectorField.mlieBracket 𝓘(ℝ, E) Xc Yc z) := by
    simpa [D, map_sub] using congrArg D ht
  have hbr :
      D (VectorField.mlieBracket 𝓘(ℝ, E) Xc Yc z) =
        VectorField.mlieBracket I X Y y := by
    have hbrc :
        chartTransportedLeviCivitaSection (I := I) x₀
            (VectorField.mlieBracket I X Y) z =
          VectorField.mlieBracket 𝓘(ℝ, E) Xc Yc z := by
      simpa [Xc, Yc, z] using
        chartTransportedLeviCivitaSection_mlieBracket_apply_chart
          (I := I) x₀ (X := X) (Y := Y) hy hX hY
    rw [← hbrc, chartTransportedLeviCivitaSection_apply_chart x₀
      (VectorField.mlieBracket I X Y) hy]
    exact chartTransportedLeviCivita_direction_roundtrip (I := I) x₀ hy
      (VectorField.mlieBracket I X Y y)
  have hXcz :
      Xc z = mfderiv% (extChartAt I x₀) y (X y) := by
    simpa [Xc, z] using
      chartTransportedLeviCivitaSection_apply_chart (I := I) x₀ X hy
  have hYcz :
      Yc z = mfderiv% (extChartAt I x₀) y (Y y) := by
    simpa [Yc, z] using
      chartTransportedLeviCivitaSection_apply_chart (I := I) x₀ Y hy
  calc
    chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
        hsupp Y hy (X y)
      - chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0
        hχ1 hsupp X hy (Y y)
        = D (covC Yc z (mfderiv% (extChartAt I x₀) y (X y)))
            - D (covC Xc z (mfderiv% (extChartAt I x₀) y (Y y))) := by
          rfl
    _ = D (covC Yc z (Xc z)) - D (covC Xc z (Yc z)) := by
          rw [hXcz, hYcz]
    _ = D (VectorField.mlieBracket 𝓘(ℝ, E) Xc Yc z) := hpush
    _ = VectorField.mlieBracket I X Y y := hbr

/--
On a chart sub-neighborhood where the blending cutoff is identically `1`,
the value-level transported chart Levi-Civita operator is metric-compatible
with the original manifold metric.
-/
theorem chartTransported_metricCompatibleAt
    [IsManifold I (minSmoothness ℝ 2) M] [I.Boundaryless]
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) z).IsInvertible)
    (hbl : Differentiable ℝ (blendedChartMetric χ G₀ g x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    {Y Z : Π y : M, TangentSpace I y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I x₀ y), χ z' = 1)
    (hY : MDiffAt (T% Y) y) (hZ : MDiffAt (T% Z) y)
    (hYZ : MDiffAt (fun p => g p (Y p) (Z p)) y)
    (v : TangentSpace I y) :
    extDerivFun (fun p => g p (Y p) (Z p)) y v =
      g y
        (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
          hsupp Y hy v)
        (Z y)
      + g y (Y y)
        (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
          hsupp Z hy v) := by
  let z : E := extChartAt I x₀ y
  let D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I y :=
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z
  let vc : TangentSpace 𝓘(ℝ, E) z := mfderiv% (extChartAt I x₀) y v
  let Yc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ Y
  let Zc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ Z
  let covC := chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  have htarget : z ∈ (extChartAt I x₀).target := by
    simpa [z] using (extChartAt I x₀).map_source hy
  have hleft : (extChartAt I x₀).symm z = y := by
    simpa [z] using (extChartAt I x₀).left_inv hy
  have hYc : MDiffAt (T% Yc) z := by
    simpa [Yc, z] using
      chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        (I := I) x₀ hy hY
  have hZc : MDiffAt (T% Zc) z := by
    simpa [Zc, z] using
      chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        (I := I) x₀ hy hZ
  have hcoord :
      (fun q : E =>
        g ((extChartAt I x₀).symm q)
          (Y ((extChartAt I x₀).symm q))
          (Z ((extChartAt I x₀).symm q))) =ᶠ[𝓝 z]
        (fun q : E => chartMetric g x₀ q (Yc q) (Zc q)) := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds htarget] with q hq
    exact (chartMetric_chartTransportedLeviCivitaSection
      (I := I) g x₀ Y Z hq).symm
  have hblend :
      (fun q : E => blendedChartMetric χ G₀ g x₀ q (Yc q) (Zc q)) =ᶠ[𝓝 z]
        (fun q : E => chartMetric g x₀ q (Yc q) (Zc q)) := by
    filter_upwards [hχone] with q hq
    rw [show blendedChartMetric χ G₀ g x₀ q = chartMetric g x₀ q from
      blendedChartMetric_eq_chartMetric_of_eq_one χ G₀ g x₀ hq]
  have hleftDeriv :
      extDerivFun (fun p => g p (Y p) (Z p)) y v =
        extDerivFun
          (fun q : E => blendedChartMetric χ G₀ g x₀ q (Yc q) (Zc q)) z vc := by
    calc
      extDerivFun (fun p => g p (Y p) (Z p)) y v
          = fderiv ℝ
              ((fun p => g p (Y p) (Z p)) ∘ (extChartAt I x₀).symm)
              (extChartAt I x₀ y) (mfderiv% (extChartAt I x₀) y v) := by
            exact extDerivFun_apply_fixed_chart (I := I) hy hYZ v
      _ = fderiv ℝ
              (fun q : E => chartMetric g x₀ q (Yc q) (Zc q)) z vc := by
            exact congrArg (fun L : E →L[ℝ] ℝ => L vc)
              (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hcoord)
      _ = fderiv ℝ
              (fun q : E => blendedChartMetric χ G₀ g x₀ q (Yc q) (Zc q)) z vc := by
            exact congrArg (fun L : E →L[ℝ] ℝ => L vc)
              (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hblend.symm)
      _ = extDerivFun
              (fun q : E => blendedChartMetric χ G₀ g x₀ q (Yc q) (Zc q)) z vc := by
            simp only [extDerivFun, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
            rfl
  have hmc :
      extDerivFun
          (fun q : E => blendedChartMetric χ G₀ g x₀ q (Yc q) (Zc q)) z vc =
        blendedChartMetric χ G₀ g x₀ z (covC Yc z vc) (Zc z)
          + blendedChartMetric χ G₀ g x₀ z (Yc z) (covC Zc z vc) := by
    exact (chartLeviCivita_metricCompatibleAt χ G₀ hG₀pos g hgpos x₀
      hχ0 hχ1 hsupp hbl hG₀symm hgsymm z) hYc hZc vc
  have hχz : χ z = 1 := by
    simpa [z] using hχone.self_of_nhds
  have hblendz : blendedChartMetric χ G₀ g x₀ z = chartMetric g x₀ z :=
    blendedChartMetric_eq_chartMetric_of_eq_one χ G₀ g x₀ hχz
  have hZcz :
      Zc z = mfderiv% (extChartAt I x₀) y (Z y) := by
    simpa [Zc, z] using
      chartTransportedLeviCivitaSection_apply_chart (I := I) x₀ Z hy
  have hYcz :
      Yc z = mfderiv% (extChartAt I x₀) y (Y y) := by
    simpa [Yc, z] using
      chartTransportedLeviCivitaSection_apply_chart (I := I) x₀ Y hy
  have hright₁ :
      blendedChartMetric χ G₀ g x₀ z (covC Yc z vc) (Zc z) =
        g y
          (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
            hsupp Y hy v)
          (Z y) := by
    rw [hblendz, chartMetric_apply]
    change g ((extChartAt I x₀).symm z)
        (D (covC Yc z vc)) (D (Zc z)) =
      g y
        (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
          hsupp Y hy v)
        (Z y)
    rw [hleft]
    have hDY :
        D (covC Yc z vc) =
          chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
            hsupp Y hy v := by
      rfl
    have hDZ : D (Zc z) = Z y := by
      rw [hZcz]
      exact chartTransportedLeviCivita_direction_roundtrip (I := I) x₀ hy
        (Z y)
    rw [hDY, hDZ]
  have hright₂ :
      blendedChartMetric χ G₀ g x₀ z (Yc z) (covC Zc z vc) =
        g y (Y y)
          (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
            hsupp Z hy v) := by
    rw [hblendz, chartMetric_apply]
    change g ((extChartAt I x₀).symm z)
        (D (Yc z)) (D (covC Zc z vc)) =
      g y (Y y)
        (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
          hsupp Z hy v)
    rw [hleft]
    have hDY : D (Yc z) = Y y := by
      rw [hYcz]
      exact chartTransportedLeviCivita_direction_roundtrip (I := I) x₀ hy
        (Y y)
    have hDZ :
        D (covC Zc z vc) =
          chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
            hsupp Z hy v := by
      rfl
    rw [hDY, hDZ]
  calc
    extDerivFun (fun p => g p (Y p) (Z p)) y v
        = extDerivFun
          (fun q : E => blendedChartMetric χ G₀ g x₀ q (Yc q) (Zc q)) z vc :=
          hleftDeriv
    _ = blendedChartMetric χ G₀ g x₀ z (covC Yc z vc) (Zc z)
          + blendedChartMetric χ G₀ g x₀ z (Yc z) (covC Zc z vc) := hmc
    _ = g y
        (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
          hsupp Y hy v)
        (Z y)
      + g y (Y y)
        (chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
          hsupp Z hy v) := by
        rw [hright₁, hright₂]

end ChartConnection

end CovariantDerivative

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

namespace LeviCivitaTransport

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Local uniqueness bridge for the transported chart value.  Once a candidate
local covariant derivative `covT` is shown to have the displayed
chart-transport value and to be torsion-free and metric-compatible at `y`, it
agrees there with the closed smooth Levi-Civita connection.
-/
theorem chartTransportedLeviCivitaValueAt_eq_closed_of_isLeviCivitaAt
    (g : ClosedSmoothRiemannianMetric n M)
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (covT : CovariantDerivative I E TM)
    {σ : Π y : M, TM y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hcT : CovariantDerivative.MetricCompatibleAt g.inner covT y)
    (htT : CovariantDerivative.TorsionFreeAt covT y)
    (hσ : MDiffAtTangentField σ y)
    (htransport : ∀ v : TM y,
      covT σ y v =
        CovariantDerivative.chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g.inner
          (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp σ hy v)
    (v : TM y) :
    CovariantDerivative.chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp σ hy v =
      (LeviCivitaExistence.closedLeviCivitaConnection g) σ y v := by
  have hcClosed :
      CovariantDerivative.MetricCompatibleAt g.inner
        (LeviCivitaExistence.closedLeviCivitaConnection g) y := by
    intro Y Z hY hZ w
    exact LeviCivitaExistence.closedLeviCivitaConnection_metricCompatible g
      (by simpa [MDiffAtTangentField] using hY)
      (by simpa [MDiffAtTangentField] using hZ) w
  have htClosed :
      CovariantDerivative.TorsionFreeAt
        (LeviCivitaExistence.closedLeviCivitaConnection g) y := by
    have ht := LeviCivitaExistence.closedLeviCivitaConnection_torsion g
    rw [CovariantDerivative.torsion_eq_zero_iff] at ht
    intro X Y hX hY
    exact ht hX hY
  have huniq := CovariantDerivative.leviCivita_unique_at (g := g.inner)
    (cov := covT) (cov' := LeviCivitaExistence.closedLeviCivitaConnection g)
    (g.inner_symm y)
    (fun u hu => LeviCivitaExistence.metric_nondegenerate g y u hu)
    hcT hcClosed htT htClosed
    (by simpa [MDiffAtTangentField] using hσ)
  exact (htransport v).symm.trans (congrArg (fun L => L v) huniq)

/--
On a chart sub-neighborhood where the blending cutoff is identically `1`, the
transported chart Levi-Civita value agrees with the closed smooth
Levi-Civita connection.
-/
theorem chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
    (g : ClosedSmoothRiemannianMetric n M)
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hbl : Differentiable ℝ (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    {σ : Π y : M, TM y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I x₀ y), χ z' = 1)
    (hσ : MDiffAtTangentField σ y)
    (v : TM y) :
    CovariantDerivative.chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp σ hy v =
      (LeviCivitaExistence.closedLeviCivitaConnection g) σ y v := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : ModelWithCorners.Boundaryless (closedSmoothModelWithCorners n) := by
    infer_instance
  let z : E := extChartAt I x₀ y
  let D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TM y :=
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (Set.range I) z
  let covC :=
    CovariantDerivative.chartLeviCivita χ G₀ hG₀pos g.inner
      (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp
  let covT : (Π y : M, TM y) → TM y →L[ℝ] TM y :=
    fun X =>
      let Xc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
        CovariantDerivative.chartTransportedLeviCivitaSection x₀ X
      D.comp ((covC Xc z).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y))
  let covClosed : (Π y : M, TM y) → TM y →L[ℝ] TM y :=
    fun X => (LeviCivitaExistence.closedLeviCivitaConnection g) X y
  have hcompatT :
      ∀ {Y Z : Π y : M, TM y},
        MDiffAtTangentField Y y → MDiffAtTangentField Z y →
          ∀ v : TM y,
            extDerivFun (fun p => g.inner p (Y p) (Z p)) y v =
              g.inner y (covT Y v) (Z y) + g.inner y (Y y) (covT Z v) := by
    intro Y Z hY hZ w
    have hYZ :
        MDifferentiableAt I 𝓘(ℝ) (fun p : M => g.inner p (Y p) (Z p)) y := by
      exact LeviCivitaExistence.metric_pairing_mdiffAt g hY hZ
    simpa [covT, covC, D, z, CovariantDerivative.chartTransportedLeviCivitaValueAt,
      CovariantDerivative.chartTransportedLeviCivitaModelValue] using
      (CovariantDerivative.chartTransported_metricCompatibleAt χ G₀ hG₀pos
        g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1
        hsupp hbl hG₀symm (fun y v w => g.inner_symm y v w)
        hy hχone
        (by simpa [MDiffAtTangentField] using hY)
        (by simpa [MDiffAtTangentField] using hZ)
        hYZ w)
  have hcompatClosed :
      ∀ {Y Z : Π y : M, TM y},
        MDiffAtTangentField Y y → MDiffAtTangentField Z y →
          ∀ v : TM y,
            extDerivFun (fun p => g.inner p (Y p) (Z p)) y v =
              g.inner y (covClosed Y v) (Z y) + g.inner y (Y y) (covClosed Z v) := by
    intro Y Z hY hZ w
    simpa [covClosed] using
      LeviCivitaExistence.closedLeviCivitaConnection_metricCompatible g hY hZ w
  have htorsionT :
      ∀ {X Y : Π y : M, TM y},
        MDiffAtTangentField X y → MDiffAtTangentField Y y →
          covT Y (X y) - covT X (Y y) = VectorField.mlieBracket I X Y y := by
    intro X Y hX hY
    simpa [covT, covC, D, z, CovariantDerivative.chartTransportedLeviCivitaValueAt,
      CovariantDerivative.chartTransportedLeviCivitaModelValue] using
      (CovariantDerivative.chartTransported_torsionFreeAt χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp
        hbl hG₀symm (fun y v w => g.inner_symm y v w) hy
        (by simpa [MDiffAtTangentField] using hX)
        (by simpa [MDiffAtTangentField] using hY))
  have htorsionClosed :
      ∀ {X Y : Π y : M, TM y},
        MDiffAtTangentField X y → MDiffAtTangentField Y y →
          covClosed Y (X y) - covClosed X (Y y) = VectorField.mlieBracket I X Y y := by
    have ht := LeviCivitaExistence.closedLeviCivitaConnection_torsion g
    rw [CovariantDerivative.torsion_eq_zero_iff] at ht
    intro X Y hX hY
    simpa [covClosed] using ht
      (by simpa [MDiffAtTangentField] using hX)
      (by simpa [MDiffAtTangentField] using hY)
  have huniq : covT σ = covClosed σ := by
    set Δ : (Π y : M, TM y) → (Π y : M, TM y) → TM y :=
      fun X Y => covT Y (X y) - covClosed Y (X y) with hΔ
    have hA : ∀ {X Y Z : Π y : M, TM y},
        MDiffAtTangentField X y → MDiffAtTangentField Y y →
          MDiffAtTangentField Z y →
            g.inner y (Δ X Y) (Z y) = -g.inner y (Δ X Z) (Y y) := by
      intro X Y Z hX hY hZ
      have h3 :
          g.inner y (covT Y (X y)) (Z y) + g.inner y (Y y) (covT Z (X y)) =
            g.inner y (covClosed Y (X y)) (Z y) +
              g.inner y (Y y) (covClosed Z (X y)) :=
        (hcompatT hY hZ (X y)).symm.trans (hcompatClosed hY hZ (X y))
      have e1 : g.inner y (Δ X Y) (Z y) =
          g.inner y (covT Y (X y)) (Z y) -
            g.inner y (covClosed Y (X y)) (Z y) := by
        simp [hΔ, map_sub]
      have e2 : g.inner y (Δ X Z) (Y y) =
          g.inner y (Y y) (covT Z (X y)) -
            g.inner y (Y y) (covClosed Z (X y)) := by
        rw [g.inner_symm y]
        simp [hΔ, map_sub]
      linarith
    have hB : ∀ {X Y : Π y : M, TM y},
        MDiffAtTangentField X y → MDiffAtTangentField Y y → Δ X Y = Δ Y X := by
      intro X Y hX hY
      have t1 := htorsionT hX hY
      have t1' := htorsionClosed hX hY
      have : (covT Y (X y) - covT X (Y y)) -
          (covClosed Y (X y) - covClosed X (Y y)) = 0 := by
        rw [t1, t1']
        abel
      simp only [hΔ]
      linear_combination (norm := module) this
    have hS3 : ∀ {X Y Z : Π y : M, TM y},
        MDiffAtTangentField X y → MDiffAtTangentField Y y →
          MDiffAtTangentField Z y → g.inner y (Δ X Y) (Z y) = 0 := by
      intro X Y Z hX hY hZ
      have s1 : g.inner y (Δ X Y) (Z y) =
          -g.inner y (Δ X Z) (Y y) := hA hX hY hZ
      have s2 : g.inner y (Δ X Z) (Y y) =
          g.inner y (Δ Z X) (Y y) := by rw [hB hX hZ]
      have s3 : g.inner y (Δ Z X) (Y y) =
          -g.inner y (Δ Z Y) (X y) := hA hZ hX hY
      have s4 : g.inner y (Δ Z Y) (X y) =
          g.inner y (Δ Y Z) (X y) := by rw [hB hZ hY]
      have s5 : g.inner y (Δ Y Z) (X y) =
          -g.inner y (Δ Y X) (Z y) := hA hY hZ hX
      have s6 : g.inner y (Δ Y X) (Z y) =
          g.inner y (Δ X Y) (Z y) := by rw [hB hY hX]
      linarith
    ext w
    have hw : Δ (extend E w) σ = covT σ w - covClosed σ w := by
      simp [hΔ]
    refine sub_eq_zero.mp (LeviCivitaExistence.metric_nondegenerate g y _ fun z' => ?_)
    have h0 : g.inner y (Δ (extend E w) σ) (extend E z' y) = 0 :=
      hS3
        (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend ..))
        hσ
        (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend ..))
    rw [hw] at h0
    simpa using h0
  simpa [covT, covClosed, covC, D, z,
    CovariantDerivative.chartTransportedLeviCivitaValueAt,
    CovariantDerivative.chartTransportedLeviCivitaModelValue] using
    congrArg (fun L : TM y →L[ℝ] TM y => L v) huniq

end LeviCivitaTransport

end Poincare
