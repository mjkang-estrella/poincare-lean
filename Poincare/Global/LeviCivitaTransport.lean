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
