/-
Chart transport: the metric of a manifold read in a chart.

For a metric `g` on `M` and a point `x₀`, the chart metric at
`z ∈ extChartAt I x₀ '' …` is the pullback of `g` through the tangent map
of the inverse chart — a metric on the model space, to which the
model-space theory (Christoffel form, smoothness, curvature) applies.
This module begins the transport of the model-space results to general
manifolds.
-/

import Poincare.ModelChristoffel

noncomputable section

open Bundle CovariantDerivative Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- The metric `g` read in the chart at `x₀`: the pullback through the
tangent map of the inverse chart. -/
def chartMetric [FiniteDimensional ℝ E]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.compl₁₂
        (LinearMap.mk₂ ℝ
          (fun a b : TangentSpace I ((extChartAt I x₀).symm z) ↦
            g ((extChartAt I x₀).symm z) a b)
          (fun a a' b ↦ by
            simp only [map_add, ContinuousLinearMap.add_apply])
          (fun c a b ↦ by
            simp only [map_smul, ContinuousLinearMap.smul_apply])
          (fun a b b' ↦ by simp only [map_add])
          (fun c a b ↦ by simp only [map_smul]))
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
          (range I) z).toLinearMap
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
          (range I) z).toLinearMap)

theorem chartMetric_apply [FiniteDimensional ℝ E]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) (z : E) (v w : E) :
    chartMetric g x₀ z v w =
      g ((extChartAt I x₀).symm z)
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z v)
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (range I) z w) :=
  rfl

/-- The chart metric inherits symmetry from `g`. -/
theorem chartMetric_symm [FiniteDimensional ℝ E]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (x₀ : M) (z : E) (v w : E) :
    chartMetric g x₀ z v w = chartMetric g x₀ z w v := by
  rw [chartMetric_apply, chartMetric_apply, hgsymm]

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- The chart metric is nondegenerate wherever the chart tangent map is
invertible. -/
theorem chartMetric_nondegenerate [FiniteDimensional ℝ E]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgnd : ∀ (y : M) (v : TangentSpace I y), (∀ w, g y v w = 0) → v = 0)
    (x₀ : M) {z : E}
    (hinv : (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
      (Set.range I) z).IsInvertible)
    (v : E) (hv : ∀ w, chartMetric g x₀ z v w = 0) : v = 0 := by
  obtain ⟨e, he⟩ := hinv
  have hDv : mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
      (Set.range I) z v = 0 := by
    apply hgnd ((extChartAt I x₀).symm z)
    intro t
    have h := hv (e.symm t)
    rw [chartMetric_apply] at h
    rwa [show (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
      (Set.range I) z) (e.symm t) = t from by
        rw [← he]; exact e.apply_symm_apply t] at h
  have : e v = 0 := by
    rw [← he] at hDv
    exact hDv
  calc v = e.symm (e v) := (e.symm_apply_apply v).symm
    _ = e.symm 0 := by rw [this]
    _ = 0 := map_zero _

/-- The chart metric inherits positive-definiteness wherever the chart
tangent map is invertible. -/
theorem chartMetric_posDef [FiniteDimensional ℝ E]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) {z : E}
    (hinv : (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
      (Set.range I) z).IsInvertible)
    {v : E} (hv : v ≠ 0) : 0 < chartMetric g x₀ z v v := by
  rw [chartMetric_apply]
  apply hgpos
  intro hzero
  apply hv
  obtain ⟨e, he⟩ := hinv
  rw [← he] at hzero
  calc v = e.symm (e v) := (e.symm_apply_apply v).symm
    _ = e.symm 0 := by rw [show e v = 0 from hzero]
    _ = 0 := map_zero _

/-- At the centre of the chart the tangent map is invertible, so the chart
metric is nondegenerate there. -/
theorem chartMetric_nondegenerate_center [FiniteDimensional ℝ E]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgnd : ∀ (y : M) (v : TangentSpace I y), (∀ w, g y v w = 0) → v = 0)
    (x₀ : M) (v : E)
    (hv : ∀ w, chartMetric g x₀ (extChartAt I x₀ x₀) v w = 0) : v = 0 :=
  chartMetric_nondegenerate g hgnd x₀
    (isInvertible_mfderivWithin_extChartAt_symm
      (mem_extChartAt_target (I := I) x₀)) v hv

end CovariantDerivative

namespace CovariantDerivative

/-- On the model space the chart metric is the metric itself. -/
theorem chartMetric_model_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : Π y : E, TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y
      →L[ℝ] ℝ)
    (x₀ z : E) (v w : E) :
    chartMetric g x₀ z v w = g z v w := by
  rw [chartMetric_apply]
  have hch : extChartAt 𝓘(ℝ, E) x₀ = PartialEquiv.refl E :=
    extChartAt_model_space_eq_id (𝕜 := ℝ) x₀
  have hD : mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
      ((extChartAt 𝓘(ℝ, E) x₀).symm) (Set.range (𝓘(ℝ, E))) z =
      ContinuousLinearMap.id ℝ E := by
    rw [hch]
    rw [show ((PartialEquiv.refl E).symm : E → E) = id from rfl,
      (𝓘(ℝ, E)).range_eq_univ, mfderivWithin_univ]
    exact mfderiv_id
  rw [hD, hch]
  simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
  rfl


/--
**Scalar reduction for chart-metric smoothness**: in finite dimensions, the
chart metric is `C^k` exactly when all its scalar evaluations are — the
form in which its smoothness will be discharged from chart-transition
regularity.
-/
theorem contDiff_chartMetric_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) {k : ℕ∞ω} :
    ContDiff ℝ k (chartMetric g x₀) ↔
      ∀ v w : E, ContDiff ℝ k (fun z ↦ chartMetric g x₀ z v w) := by
  rw [contDiff_clm_apply_iff]
  exact forall_congr' fun v ↦ contDiff_clm_apply_iff

end CovariantDerivative
