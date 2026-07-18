import Poincare.Global.HausdorffInverseChartLocalRestrictionSqueeze
import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Countable localization of measure inequalities

This file records a reusable local-to-global principle for nonnegative
measures on second-countable spaces.  If two measures satisfy a restriction
inequality on one measurable neighborhood of every point, then they satisfy
the same inequality globally.

The proof passes through `ℝ≥0∞`-valued vector measures, where Mathlib already
provides the countable-union restriction theorem and its internal
`disjointed` bookkeeping.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped MeasureTheory Topology ENNReal

universe u

namespace Poincare

/-- Restriction commutes with the canonical conversion of a nonnegative
measure to an `ℝ≥0∞`-valued vector measure. -/
theorem toENNRealVectorMeasure_restrict
    {α : Type u} [MeasurableSpace α] (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) :
    (μ.restrict s).toENNRealVectorMeasure =
      μ.toENNRealVectorMeasure.restrict s := by
  apply MeasureTheory.VectorMeasure.ext
  intro t ht
  rw [Measure.toENNRealVectorMeasure_apply_measurable ht]
  rw [Measure.restrict_apply ht]
  rw [MeasureTheory.VectorMeasure.restrict_apply _ hs ht]
  rw [Measure.toENNRealVectorMeasure_apply_measurable (ht.inter hs)]

/-- Order of nonnegative measures is preserved by conversion to
`ℝ≥0∞`-valued vector measures. -/
theorem toENNRealVectorMeasure_mono
    {α : Type u} [MeasurableSpace α] {μ ν : Measure α} (hμν : μ ≤ ν) :
    μ.toENNRealVectorMeasure ≤ ν.toENNRealVectorMeasure := by
  intro s hs
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs,
    Measure.toENNRealVectorMeasure_apply_measurable hs]
  exact hμν s

/-- A restriction inequality holding on a measurable neighborhood of every
point globalizes on a second-countable space. -/
theorem measure_le_of_restrict_le_on_nhds
    {α : Type u} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] (μ ν : Measure α)
    (hlocal : ∀ x : α, ∃ W : Set α,
      W ∈ 𝓝 x ∧ MeasurableSet W ∧ μ.restrict W ≤ ν.restrict W) :
    μ ≤ ν := by
  choose W hWnhds hWmeas hWle using hlocal
  rcases TopologicalSpace.countable_cover_nhds hWnhds with
    ⟨s, hsCountable, hsCover⟩
  let v := μ.toENNRealVectorMeasure
  let w := ν.toENNRealVectorMeasure
  have hlocalVector : ∀ x : α,
      v ≤[W x] w := by
    intro x
    rw [← toENNRealVectorMeasure_restrict μ (hWmeas x),
      ← toENNRealVectorMeasure_restrict ν (hWmeas x)]
    exact toENNRealVectorMeasure_mono (hWle x)
  haveI := hsCountable.toEncodable
  rw [biUnion_eq_iUnion] at hsCover
  have hglobalVector : v ≤ w := by
    have hcovered :=
      MeasureTheory.VectorMeasure.restrict_le_restrict_countable_iUnion
        v w (f := fun x : s ↦ W x) (fun x ↦ hWmeas x)
        (fun x ↦ hlocalVector x)
    rw [hsCover] at hcovered
    simpa only [MeasureTheory.VectorMeasure.restrict_univ] using hcovered
  apply Measure.le_iff.2
  intro t ht
  have htOrder := hglobalVector t ht
  simpa only [v, w,
    Measure.toENNRealVectorMeasure_apply_measurable ht] using htOrder

end Poincare
