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

/-- Positive-definiteness gives nondegeneracy of the blended metric. -/
theorem blendedChartMetric_nondegenerate (χ : E → ℝ)
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) {z : E} (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1)
    (hsupp : χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (v : E) (hv : ∀ w, blendedChartMetric χ G₀ g x₀ z v w = 0) : v = 0 := by
  by_contra hne
  have hpos := blendedChartMetric_posDef χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
    hsupp hne
  rw [hv v] at hpos
  exact lt_irrefl 0 hpos

/--
**A blending cutoff exists**: a smooth `[0,1]`-valued function supported in
the chart target and identically `1` near the chart centre — the cutoff
with which `blendedChartMetric` satisfies all its hypotheses.
-/
theorem exists_blending_cutoff [I.Boundaryless] (x₀ : M) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧
      (∀ z, χ z ≠ 0 → z ∈ (extChartAt I x₀).target) ∧
      (∀ᶠ z in nhds (extChartAt I x₀ x₀), χ z = 1) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target x₀) (extChartAt I x₀ x₀)
    (mem_extChartAt_target x₀)
  let f : ContDiffBump (extChartAt I x₀ x₀) :=
    ⟨ε / 2, ε, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, fun z ↦ f.nonneg, fun z ↦ f.le_one,
    fun z hz ↦ ?_, ?_⟩
  · exact hball (f.support_eq ▸ Function.mem_support.mpr hz)
  · filter_upwards [Metric.closedBall_mem_nhds _ (by positivity :
      (0 : ℝ) < ε / 2)] with z hz
    exact f.one_of_mem_closedBall hz

/--
**The global chart metric exists**: for any positive-definite symmetric
metric on `M` and any chart, there is a global metric on the model space —
symmetric, positive-definite everywhere — agreeing with the chart metric
near the chart centre. The model-space Levi-Civita theory applies to it
outright.
-/
theorem exists_global_chart_metric [I.Boundaryless]
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) :
    ∃ Ghat : E → E →L[ℝ] E →L[ℝ] ℝ,
      (∀ (z : E) (v w : E), Ghat z v w = Ghat z w v) ∧
      (∀ (z : E) (v : E), v ≠ 0 → 0 < Ghat z v v) ∧
      (∀ᶠ z in nhds (extChartAt I x₀ x₀), Ghat z = chartMetric g x₀ z) := by
  obtain ⟨χ, hχsm, hχ0, hχ1, hχsupp, hχone⟩ := exists_blending_cutoff (I := I) x₀
  refine ⟨blendedChartMetric χ G₀ g x₀,
    fun z v w ↦ blendedChartMetric_symm χ G₀ hG₀symm g hgsymm x₀ z v w,
    fun z v hv ↦ blendedChartMetric_posDef χ G₀ hG₀pos g hgpos x₀
      (hχ0 z) (hχ1 z)
      (fun hne ↦ isInvertible_mfderivWithin_extChartAt_symm
        (I := I) (hχsupp z hne)) hv, ?_⟩
  filter_upwards [hχone] with z hz
  ext v w
  rw [blendedChartMetric_apply, hz]
  simp

end Blended


section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/--
**Smoothness of the chart metric** (scalar form): if `g` is a `C^m` section
of the bilinear-form bundle, every scalar evaluation of the chart metric is
`C^m` on the chart target — the hom-bundle pairing of the inverse-chart
tangent fields.
-/
theorem contMDiffOn_chartMetric_pairing
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) {m : ℕ∞ω} (hm : m + 1 ≤ (∞ : ℕ∞ω))
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        y (g y)))
    (v w : E) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) m
      (fun z ↦ chartMetric g x₀ z v w) (extChartAt I x₀).target := by
  set c := ((extChartAt I x₀).symm : E → M) with hc
  have hcsm : ContMDiffOn 𝓘(ℝ, E) I m c (extChartAt I x₀).target :=
    (contMDiffOn_extChartAt_symm x₀).of_le (le_trans le_self_add hm)
  -- The metric section along the inverse chart.
  have hϕ : ContMDiffOn 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        (c z) (g (c z))) (extChartAt I x₀).target :=
    hg.comp_contMDiffOn hcsm
  -- The two tangent fields.
  have hv := contMDiffOn_inverseChart_tangentMap (I := I) x₀ (m := m) hm v
  have hw := contMDiffOn_inverseChart_tangentMap (I := I) x₀ (m := m) hm w
  -- First application: z ↦ g (c z) (D z v).
  have step1 := ContMDiffOn.clm_bundle_apply
    (F₁ := E) (E₁ := TangentSpace I)
    (F₂ := E →L[ℝ] ℝ)
    (E₂ := fun y ↦ TangentSpace I y →L[ℝ] ℝ)
    (b := c)
    (ϕ := fun z ↦ g (c z))
    (v := fun z ↦ mfderivWithin 𝓘(ℝ, E) I c (extChartAt I x₀).target z v)
    hϕ hv
  -- Second application: the scalar pairing.
  have step2 := ContMDiffOn.clm_bundle_apply
    (F₁ := E) (E₁ := TangentSpace I)
    (F₂ := ℝ)
    (E₂ := fun y ↦ Bundle.Trivial M ℝ y)
    (b := c)
    (ϕ := fun z ↦ g (c z)
      (mfderivWithin 𝓘(ℝ, E) I c (extChartAt I x₀).target z v))
    (v := fun z ↦ mfderivWithin 𝓘(ℝ, E) I c (extChartAt I x₀).target z w)
    step1 hw
  -- Extract the scalar from the trivial-bundle section.
  intro z₀ hz₀
  have h := step2 z₀ hz₀
  rw [contMDiffWithinAt_totalSpace] at h
  refine h.2.congr_of_mem ?_ hz₀
  intro z hz
  -- Identify the trivialized coordinate with the chart-metric evaluation.
  rw [chartMetric_apply,
    ← mfderivWithin_extChartAt_symm_target_eq_range x₀ hz]
  rfl

end Smoothness


section ChartConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- The blended chart metric as a family of bilinear forms. -/
def chartBilin (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (x₀ : M) (z : E) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w ↦ blendedChartMetric χ G₀ g x₀ z v w)
    (fun v v' w ↦ by simp)
    (fun c v w ↦ by simp)
    (fun v w w' ↦ by simp)
    (fun c v w ↦ by simp)

theorem chartBilin_nondegenerate (χ : E → ℝ)
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible) (z : E) :
    (chartBilin χ G₀ g x₀ z).Nondegenerate := by
  constructor
  · intro v hv
    exact blendedChartMetric_nondegenerate χ G₀ hG₀pos g hgpos x₀
      (hχ0 z) (hχ1 z) (hsupp z) v hv
  · intro w hw
    by_contra hne
    have hpos := blendedChartMetric_posDef χ G₀ hG₀pos g hgpos x₀
      (hχ0 z) (hχ1 z) (hsupp z) hne
    have := hw w
    simp only [chartBilin, LinearMap.mk₂_apply] at this
    rw [this] at hpos
    exact lt_irrefl 0 hpos

/--
**The chart Levi-Civita connection**: the Christoffel-form Levi-Civita
connection of the globalized chart metric — torsion-free and compatible
with the blended metric by the model-space theorems. This is the
connection through which the manifold's geometry is computed in the chart.
-/
noncomputable def chartLeviCivita (χ : E → ℝ)
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible) :
    CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
  modelLeviCivita (blendedChartMetric χ G₀ g x₀)
    (chartBilin χ G₀ g x₀)
    (chartBilin_nondegenerate χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp)

/-- The chart connection is torsion-free (model-space theorem applied to
the blended metric). -/
theorem chartLeviCivita_torsionFreeAt (χ : E → ℝ)
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hbl : Differentiable ℝ (blendedChartMetric χ G₀ g x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (z : E) :
    TorsionFreeAt
      (chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp) z :=
  modelLeviCivita_torsionFreeAt _ _ _ hbl
    (fun z' v w ↦ blendedChartMetric_symm χ G₀ hG₀symm g hgsymm x₀ z' v w) z

/-- The chart connection is compatible with the blended metric. -/
theorem chartLeviCivita_metricCompatibleAt (χ : E → ℝ)
    (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hbl : Differentiable ℝ (blendedChartMetric χ G₀ g x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (z : E) :
    MetricCompatibleAt (blendedChartMetric χ G₀ g x₀)
      (chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp) z :=
  modelLeviCivita_metricCompatibleAt _ _ _ hbl
    (fun z' v w ↦ blendedChartMetric_symm χ G₀ hG₀symm g hgsymm x₀ z' v w)
    (fun z' v w ↦ rfl) z

end ChartConnection

end CovariantDerivative
