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

open Bundle Set
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

end LeviCivitaTransport

end Poincare
