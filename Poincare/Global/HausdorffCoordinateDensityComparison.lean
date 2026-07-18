import Poincare.Global.HausdorffCoordinateDensityVariation

/-!
# Order comparison for raw Hausdorff coordinate-density measures

The raw coordinate-density construction is monotone in its real density.
It also turns multiplication of the density by a nonnegative real constant
into scalar multiplication of the resulting measure.  These elementary
facts let pointwise relative density bounds be used directly in the local
Hausdorff epsilon squeeze.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory

namespace Poincare

variable {n : ℕ}

local notation "E" => ClosedSmoothModel n

/-- Pointwise order of real coordinate densities induces order of their raw
Hausdorff-normalized measures. -/
theorem rawHausdorffCoordinateDensityMeasure_mono
    {U : Set E} {δ η : U → ℝ} (hδη : ∀ z, δ z ≤ η z) :
    rawHausdorffCoordinateDensityMeasure U δ ≤
      rawHausdorffCoordinateDensityMeasure U η := by
  rw [rawHausdorffCoordinateDensityMeasure,
    rawHausdorffCoordinateDensityMeasure]
  apply withDensity_mono
  filter_upwards [] with z
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (hδη z) (by positivity)

/-- Multiplying a coordinate density by a nonnegative real constant scales
the resulting raw Hausdorff coordinate-density measure by its `ENNReal`
image. -/
theorem rawHausdorffCoordinateDensityMeasure_const_mul
    (U : Set E) (δ : U → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    rawHausdorffCoordinateDensityMeasure U (fun z ↦ a * δ z) =
      ENNReal.ofReal a • rawHausdorffCoordinateDensityMeasure U δ := by
  rw [rawHausdorffCoordinateDensityMeasure,
    rawHausdorffCoordinateDensityMeasure]
  rw [← withDensity_smul' (ENNReal.ofReal a)
    (fun z ↦ ENNReal.ofReal
      ((rawHausdorffLebesgueScale n : ℝ) * δ z)) ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show
      (rawHausdorffLebesgueScale n : ℝ) * (a * δ z) =
        a * ((rawHausdorffLebesgueScale n : ℝ) * δ z) by ring]
  rw [ENNReal.ofReal_mul ha]

/-- Pointwise relative bounds around a constant density become a two-sided
measure comparison with exactly the same scalar factors. -/
theorem rawHausdorffCoordinateDensityMeasure_relative_bounds
    (U : Set E) (δ : U → ℝ) (δ₀ a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ : ∀ z, a * δ₀ ≤ δ z ∧ δ z ≤ b * δ₀) :
    ENNReal.ofReal a •
          rawHausdorffCoordinateDensityMeasure U (fun _ ↦ δ₀) ≤
        rawHausdorffCoordinateDensityMeasure U δ ∧
      rawHausdorffCoordinateDensityMeasure U δ ≤
        ENNReal.ofReal b •
          rawHausdorffCoordinateDensityMeasure U (fun _ ↦ δ₀) := by
  constructor
  · rw [← rawHausdorffCoordinateDensityMeasure_const_mul U
      (fun _ ↦ δ₀) ha]
    exact rawHausdorffCoordinateDensityMeasure_mono fun z ↦ (hδ z).1
  · rw [← rawHausdorffCoordinateDensityMeasure_const_mul U
      (fun _ ↦ δ₀) hb]
    exact rawHausdorffCoordinateDensityMeasure_mono fun z ↦ (hδ z).2

end Poincare
