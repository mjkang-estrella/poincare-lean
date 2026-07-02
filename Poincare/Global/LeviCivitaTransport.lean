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

end ChartConnection

end CovariantDerivative
