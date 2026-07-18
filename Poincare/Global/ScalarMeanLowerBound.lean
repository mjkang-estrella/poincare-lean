import Poincare.Global.AntilipschitzMathlib

/-!
# Pointwise scalar lower bounds control mean scalar curvature

The normalized-flow convergence endpoint needs a positive lower bound for the
mean scalar.  On a closed smooth manifold this follows from the corresponding
pointwise scalar lower bound: total Riemannian volume is finite and strictly
positive, and integration preserves the inequality.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- An everywhere pointwise scalar-curvature lower bound is inherited by the
mean scalar curvature. -/
theorem le_meanScalar_of_forall_le_scalarAt
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) (c : ℝ)
    (hlower : ∀ x : M, c ≤ g.scalarAt x) :
    c ≤ meanScalar g := by
  let μ := volumeMeasure g
  letI : IsFiniteMeasure μ := volumeMeasure_isFiniteMeasure g
  have hvolne : μ Set.univ ≠ 0 := by
    simpa [μ] using
      (GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib g)
  have hvoltop : μ Set.univ ≠ (⊤ : ℝ≥0∞) := measure_ne_top μ Set.univ
  have hvolpos : 0 < (μ Set.univ).toReal :=
    ENNReal.toReal_pos hvolne hvoltop
  have hconst : Integrable (fun _ : M ↦ c) μ := integrable_const c
  have hscalar : Integrable (fun x : M ↦ g.scalarAt x) μ := by
    simpa [μ] using scalarAt_integrable g
  have hintegral :
      (∫ _ : M, c ∂μ) ≤ ∫ x : M, g.scalarAt x ∂μ :=
    integral_mono hconst hscalar hlower
  have hmul : c * (μ Set.univ).toReal ≤ totalScalar g := by
    simpa [μ, totalScalar, Measure.real, mul_comm] using hintegral
  unfold meanScalar
  change c ≤ totalScalar g / (μ Set.univ).toReal
  exact (le_div_iff₀ hvolpos).2 hmul

/-- An everywhere pointwise scalar-curvature upper bound is inherited by the
mean scalar curvature. -/
theorem meanScalar_le_of_forall_scalarAt_le
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) (c : ℝ)
    (hupper : ∀ x : M, g.scalarAt x ≤ c) :
    meanScalar g ≤ c := by
  let μ := volumeMeasure g
  letI : IsFiniteMeasure μ := volumeMeasure_isFiniteMeasure g
  have hvolne : μ Set.univ ≠ 0 := by
    simpa [μ] using
      (GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib g)
  have hvoltop : μ Set.univ ≠ (⊤ : ℝ≥0∞) := measure_ne_top μ Set.univ
  have hvolpos : 0 < (μ Set.univ).toReal :=
    ENNReal.toReal_pos hvolne hvoltop
  have hconst : Integrable (fun _ : M ↦ c) μ := integrable_const c
  have hscalar : Integrable (fun x : M ↦ g.scalarAt x) μ := by
    simpa [μ] using scalarAt_integrable g
  have hintegral :
      (∫ x : M, g.scalarAt x ∂μ) ≤ ∫ _ : M, c ∂μ :=
    integral_mono hscalar hconst hupper
  have hmul : totalScalar g ≤ c * (μ Set.univ).toReal := by
    simpa [μ, totalScalar, Measure.real, mul_comm] using hintegral
  unfold meanScalar
  change totalScalar g / (μ Set.univ).toReal ≤ c
  exact (div_le_iff₀ hvolpos).2 hmul

/-- A pointwise absolute scalar-curvature bound also bounds the absolute mean
scalar curvature by the same constant. -/
theorem abs_meanScalar_le_of_forall_abs_scalarAt_le
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) (c : ℝ)
    (habs : ∀ x : M, |g.scalarAt x| ≤ c) :
    |meanScalar g| ≤ c := by
  rw [abs_le]
  exact ⟨
    le_meanScalar_of_forall_le_scalarAt g (-c)
      (fun x ↦ (abs_le.mp (habs x)).1),
    meanScalar_le_of_forall_scalarAt_le g c
      (fun x ↦ (abs_le.mp (habs x)).2)⟩

/-- A strictly positive pointwise scalar lower bound gives strictly positive
mean scalar curvature. -/
theorem meanScalar_pos_of_forall_scalarAt_ge
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) {c : ℝ}
    (hc : 0 < c) (hlower : ∀ x : M, c ≤ g.scalarAt x) :
    0 < meanScalar g :=
  hc.trans_le (le_meanScalar_of_forall_le_scalarAt g c hlower)

end Poincare
