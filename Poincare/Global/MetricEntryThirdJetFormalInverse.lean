import Poincare.Global.ClosedMetricThirdJetTopology

/-!
# Formal inverse metrics from scalar third-jet profiles

This module reconstructs a bilinear form from the value slots of an arbitrary
scalar third-jet profile.  It works on formal profiles and does not assert that
a profile comes from a smooth positive-definite metric.  The inverse result
isolates matrix inversion, the only singular rational operation in the metric
jet formulas, behind an explicit pointwise invertibility hypothesis.
-/

noncomputable section

open Bundle Function
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M
local notation "P" => MetricEntryThirdJetProfileTarget n M

/-- Reconstruct the formal metric at one anchor and model-space point from
the scalar value slots of a third-jet profile.  This definition applies to
formal profiles, without claiming that they are realized by metrics. -/
noncomputable def formalProfileMetricAt (p : P) (x : M) (z : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, ∑ j,
    p (.value x (b i) (b j)) z •
      (LinearMap.toContinuousLinearMap (b.coord i)).smulRight
        (LinearMap.toContinuousLinearMap (b.coord j))

/-- On the profile of a genuine metric, formal value-slot reconstruction is
exactly the cutoff-blended metric. -/
@[simp] theorem formalProfileMetricAt_profile (g : G) (x : M) (z : E) :
    formalProfileMetricAt (metricEntryThirdJetProfile g) x z =
      anchorBlendedMetricFamily (fun h : G ↦ h) x g z := by
  let b := Module.finBasis ℝ E
  let A := anchorBlendedMetricFamily (fun h : G ↦ h) x g z
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp [formalProfileMetricAt]
  change ∑ i, ∑ j, A (b i) (b j) * (b.coord i u * b.coord j v) = A u v
  calc
    _ = ∑ i, b.coord i u * (∑ j, b.coord j v * A (b i) (b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, b.coord i u * A (b i) v := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      conv_rhs => rw [← b.sum_repr v]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, smul_eq_mul, Module.Basis.coord_apply]
    _ = A u v := by
      conv_rhs => rw [← b.sum_repr u]
      rw [map_sum, ContinuousLinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        Module.Basis.coord_apply]

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Formal metric reconstruction is jointly continuous in the complete scalar
profile and the model-space coordinate. -/
theorem continuous_formalProfileMetricAt (x : M) :
    Continuous (fun q : P × E ↦ formalProfileMetricAt q.1 x q.2) := by
  unfold formalProfileMetricAt
  apply continuous_finsetSum Finset.univ
  intro i hi
  apply continuous_finsetSum Finset.univ
  intro j hj
  exact
    (((continuous_apply
      (MetricEntryThirdJetSlot.value x
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))).comp
          continuous_fst).eval continuous_snd).smul continuous_const

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- On compact sets of formal profiles and coordinates where every
reconstructed form is invertible, the corresponding formal inverse metrics
have compact image.  This isolates the singular inverse operation; it does not
claim that any formal profile is realized by a metric. -/
theorem isCompact_formalProfileMetricInverse_image
    (x : M) {S : Set P} {Q : Set E}
    (hS : IsCompact S) (hQ : IsCompact Q)
    (hnd : ∀ p ∈ S, ∀ z ∈ Q, (formalProfileMetricAt p x z).IsInvertible) :
    IsCompact
      ((fun q : P × E ↦ (formalProfileMetricAt q.1 x q.2).inverse) ''
        (S ×ˢ Q)) := by
  apply (hS.prod hQ).image_of_continuousOn
  intro q hq
  have hinv : (formalProfileMetricAt q.1 x q.2).IsInvertible :=
    hnd q.1 hq.1 q.2 hq.2
  have hinverse : ContinuousAt ContinuousLinearMap.inverse
      (formalProfileMetricAt q.1 x q.2) :=
    (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      (n := 0) hinv).continuousAt
  have hformal : ContinuousAt
      (fun r : P × E ↦ formalProfileMetricAt r.1 x r.2) q :=
    (continuous_formalProfileMetricAt x).continuousAt
  have hcomp : ContinuousAt
      (ContinuousLinearMap.inverse ∘
        fun r : P × E ↦ formalProfileMetricAt r.1 x r.2) q :=
    ContinuousAt.comp (f := fun r : P × E ↦
      formalProfileMetricAt r.1 x r.2) hinverse hformal
  simpa only [Function.comp_apply] using hcomp.continuousWithinAt

end Poincare
