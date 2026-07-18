import Poincare.Global.HausdorffMeasureCountableLocalization

/-!
# Passing scalar measure squeezes to the limit

The localized inverse-chart comparison produces inequalities whose four
nonnegative scalar coefficients tend to one.  This file isolates the final
order-topological step: scalar inequalities between measures pass to their
coefficient limits, including on sets of infinite measure.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory Topology

universe u v

namespace Poincare

/-- If scalar multiples of two measures are ordered along a filter and both
scalars tend to one, then the underlying measures are ordered.  The proof
uses closedness of the order relation on `ℝ≥0∞`; no finiteness hypothesis on
either measure is needed. -/
theorem measure_le_of_smul_le_smul_tendsto_one
    {α : Type u} {ι : Type v} [MeasurableSpace α]
    {l : Filter ι} [NeBot l]
    (μ ν : Measure α) (a b : ι → ℝ≥0∞)
    (ha : Tendsto a l (𝓝 1)) (hb : Tendsto b l (𝓝 1))
    (h : ∀ i : ι, a i • μ ≤ b i • ν) :
    μ ≤ ν := by
  apply Measure.le_iff.2
  intro s hs
  have hleft : Tendsto (fun i ↦ a i * μ s) l (𝓝 (μ s)) := by
    simpa only [one_mul] using
      ENNReal.Tendsto.mul ha (Or.inl one_ne_zero)
        tendsto_const_nhds (Or.inr ENNReal.one_ne_top)
  have hright : Tendsto (fun i ↦ b i * ν s) l (𝓝 (ν s)) := by
    simpa only [one_mul] using
      ENNReal.Tendsto.mul hb (Or.inl one_ne_zero)
        tendsto_const_nhds (Or.inr ENNReal.one_ne_top)
  apply OrderClosedTopology.isClosed_le'.mem_of_tendsto
    (hleft.prodMk_nhds hright)
  apply Eventually.of_forall
  intro i
  have hi := h i s
  simpa only [Measure.smul_apply, smul_eq_mul] using hi

/-- Two scalar measure comparisons whose coefficients all tend to one force
equality of the underlying measures. -/
theorem measure_eq_of_two_sided_smul_squeeze_tendsto_one
    {α : Type u} {ι : Type v} [MeasurableSpace α]
    {l : Filter ι} [NeBot l]
    (μ ν : Measure α) (a b c d : ι → ℝ≥0∞)
    (ha : Tendsto a l (𝓝 1)) (hb : Tendsto b l (𝓝 1))
    (hc : Tendsto c l (𝓝 1)) (hd : Tendsto d l (𝓝 1))
    (hμν : ∀ i : ι, a i • μ ≤ b i • ν)
    (hνμ : ∀ i : ι, c i • ν ≤ d i • μ) :
    μ = ν := by
  apply le_antisymm
  · exact measure_le_of_smul_le_smul_tendsto_one
      μ ν a b ha hb hμν
  · exact measure_le_of_smul_le_smul_tendsto_one
      ν μ c d hc hd hνμ

end Poincare

