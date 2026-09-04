import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Pointwise order from domination of continuous density measures

For a sigma-finite measure that is positive on every nonempty open set,
domination between measures with continuous `ENNReal` densities reflects the
pointwise order of those densities.  The measure inequality first gives the
order almost everywhere by testing every finite-measure measurable set.
Continuity then makes the order locus closed, while open positivity makes the
almost-everywhere locus dense.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

universe u v

namespace Poincare

/-- Mapping along a measurable embedding reflects the order on measures. -/
theorem measure_le_of_map_le_map_of_measurableEmbedding
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : MeasurableEmbedding f) {μ ν : Measure X}
    (h : Measure.map f μ ≤ Measure.map f ν) :
    μ ≤ ν := by
  intro s
  calc
    μ s = μ (f ⁻¹' (f '' s)) := by rw [hf.injective.preimage_image]
    _ = Measure.map f μ (f '' s) := (hf.map_apply μ (f '' s)).symm
    _ ≤ Measure.map f ν (f '' s) := h (f '' s)
    _ = ν (f ⁻¹' (f '' s)) := hf.map_apply ν (f '' s)
    _ = ν s := by rw [hf.injective.preimage_image]

/-- Continuous densities are pointwise ordered when their density measures
are ordered over a sigma-finite measure with full topological support. -/
theorem continuous_density_le_of_withDensity_le
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SigmaFinite μ] [μ.IsOpenPosMeasure]
    {f g : X → ℝ≥0∞} (hf : Continuous f) (hg : Continuous g)
    (h : μ.withDensity f ≤ μ.withDensity g) :
    ∀ x, f x ≤ g x := by
  have hae : f ≤ᵐ[μ] g := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf.measurable
    intro s hs _hfinite
    rw [← withDensity_apply f hs, ← withDensity_apply g hs]
    exact h s
  have hdense : Dense {x | f x ≤ g x} := μ.dense_of_ae hae
  have hclosed : IsClosed {x | f x ≤ g x} := isClosed_le hf hg
  have huniv : {x | f x ≤ g x} = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  intro x
  exact huniv.ge (Set.mem_univ x)

end Poincare
