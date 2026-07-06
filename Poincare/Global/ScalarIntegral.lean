import Poincare.Global.ScalarRegularity
import Poincare.Global.VolumeFinitenessComparison
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Total and mean scalar curvature

This module packages the scalar-curvature regularity and finite Riemannian
volume results into the closed-manifold scalar integral functionals.
-/

noncomputable section

open scoped Manifold ContDiff MeasureTheory

universe u

namespace Poincare

section Regularity

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Scalar curvature is continuous on a closed smooth Riemannian manifold. -/
theorem scalarAt_continuous (g : ClosedSmoothRiemannianMetric n M) :
    Continuous (fun x : M ↦ g.scalarAt x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (scalarAt_mdifferentiableAt (g := g) x).continuousAt

/-- An everywhere-Einstein metric has constant scalar curvature `n * lam`. -/
theorem scalarAt_eq_nat_mul_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x) (x : M) :
    g.scalarAt x = n * lam :=
  g.scalarAt_eq_nat_mul_of_isEinsteinAt (hEin x)

end Regularity

section Integral

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Scalar curvature is integrable against the finite Riemannian volume measure. -/
theorem scalarAt_integrable (g : ClosedSmoothRiemannianMetric n M) :
    MeasureTheory.Integrable (fun x : M ↦ g.scalarAt x) (volumeMeasure g) := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasure g) :=
    volumeMeasure_isFiniteMeasure g
  exact (scalarAt_continuous (g := g)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace (fun x : M ↦ g.scalarAt x))

/-- Total scalar curvature of a closed smooth Riemannian metric. -/
noncomputable def totalScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  ∫ x, g.scalarAt x ∂(volumeMeasure g)

/-- Mean scalar curvature, normalized by total volume. -/
noncomputable def meanScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  totalScalar g / (volumeMeasure g Set.univ).toReal

/-- Total scalar curvature of an everywhere-Einstein metric. -/
theorem totalScalar_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x) :
    totalScalar g = (n * lam) * (volumeMeasure g Set.univ).toReal := by
  unfold totalScalar
  have hconst : (fun x : M ↦ g.scalarAt x) = fun _ : M ↦ n * lam := by
    funext x
    exact scalarAt_eq_nat_mul_of_forall_isEinsteinAt (g := g) hEin x
  rw [hconst]
  rw [MeasureTheory.integral_const]
  simp [MeasureTheory.Measure.real]
  ring

/--
Mean scalar curvature of an everywhere-Einstein metric, assuming the real
volume denominator is nonzero.
-/
theorem meanScalar_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x)
    (hvol : (volumeMeasure g Set.univ).toReal ≠ 0) :
    meanScalar g = n * lam := by
  unfold meanScalar
  rw [totalScalar_of_forall_isEinsteinAt (g := g) hEin]
  exact mul_div_cancel_right₀ (n * lam) hvol

/--
Mean scalar curvature of an everywhere-Einstein metric from nonzero finite
volume.
-/
theorem meanScalar_of_forall_isEinsteinAt_of_volume_ne_zero
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x)
    (hvol : volumeMeasure g Set.univ ≠ 0) :
    meanScalar g = n * lam := by
  apply meanScalar_of_forall_isEinsteinAt (g := g) hEin
  rw [ENNReal.toReal_ne_zero]
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasure g) :=
    volumeMeasure_isFiniteMeasure g
  exact ⟨hvol, MeasureTheory.measure_ne_top (volumeMeasure g) Set.univ⟩

end Integral

end Poincare
