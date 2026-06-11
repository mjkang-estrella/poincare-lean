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


/--
**The inverse-chart tangent field is smooth**: pushing a constant vector
through the tangent map of the inverse chart gives a `C^m` bundle map on
the chart target, for every `m`. This is the field whose pairing computes
the chart metric.
-/
theorem contMDiffOn_inverseChart_tangentMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless]
    (x₀ : M) {m : ℕ∞ω} (hm : m + 1 ≤ (∞ : ℕ∞ω)) (v : E) :
    ContMDiffOn 𝓘(ℝ, E) I.tangent m
      (fun z ↦ tangentMapWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (extChartAt I x₀).target ⟨z, v⟩)
      (extChartAt I x₀).target := by
  have hf : ContMDiffOn 𝓘(ℝ, E) I ∞ ((extChartAt I x₀).symm)
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
  have hs : UniqueMDiffOn 𝓘(ℝ, E) (extChartAt I x₀).target :=
    (isOpen_extChartAt_target x₀).uniqueMDiffOn
  have h := hf.contMDiffOn_tangentMapWithin (m := m) hm hs
  have hsec : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent m
      (fun z : E ↦ (⟨z, v⟩ : TangentBundle 𝓘(ℝ, E) E))
      (extChartAt I x₀).target := by
    apply ContMDiff.contMDiffOn
    exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact h.comp hsec (fun z hz ↦ hz)


/--
On the chart target, the inverse-chart derivative within the target agrees
with the derivative within the model range — the bridge between the
tangent-field smoothness statement and the chart-metric definition.
-/
theorem mfderivWithin_extChartAt_symm_target_eq_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [I.Boundaryless]
    (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (extChartAt I x₀).target z =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z :=
  mfderivWithin_subset (extChartAt_target_subset_range x₀)
    ((isOpen_extChartAt_target x₀).uniqueMDiffOn z hz)
    ((contMDiffWithinAt_extChartAt_symm_range (n := 1) x₀
      hz).mdifferentiableWithinAt one_ne_zero)


section Blended

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [FiniteDimensional ℝ E]

/--
The blended chart metric: the chart metric glued to a reference inner
product by a cutoff `χ` supported where the chart tangent map is
invertible. This globalizes the chart metric over the whole model space,
where the model-space Levi-Civita theory applies.
-/
def blendedChartMetric (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  χ z • chartMetric g x₀ z + (1 - χ z) • G₀

theorem blendedChartMetric_apply (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) (z : E) (v w : E) :
    blendedChartMetric χ G₀ g x₀ z v w =
      χ z * chartMetric g x₀ z v w + (1 - χ z) * G₀ v w := by
  simp [blendedChartMetric]

theorem blendedChartMetric_symm (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀ : ∀ v w : E, G₀ v w = G₀ w v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (x₀ : M) (z : E) (v w : E) :
    blendedChartMetric χ G₀ g x₀ z v w =
      blendedChartMetric χ G₀ g x₀ z w v := by
  rw [blendedChartMetric_apply, blendedChartMetric_apply,
    chartMetric_symm g hgsymm, hG₀]

/--
**The blended chart metric is positive-definite** wherever the cutoff
takes values in `[0,1]` and is supported in the invertibility locus.
-/
theorem blendedChartMetric_posDef (χ : E → ℝ)
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) {z : E} (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1)
    (hsupp : χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    {v : E} (hv : v ≠ 0) :
    0 < blendedChartMetric χ G₀ g x₀ z v v := by
  rw [blendedChartMetric_apply]
  rcases eq_or_lt_of_le hχ0 with h0 | h0
  · rw [← h0]
    have := hG₀pos v hv
    nlinarith
  · have hchart := chartMetric_posDef g hgpos x₀ (hsupp (ne_of_gt h0)) hv
    rcases eq_or_lt_of_le hχ1 with h1 | h1
    · rw [h1]
      nlinarith
    · have := hG₀pos v hv
      nlinarith

end Blended

end CovariantDerivative
