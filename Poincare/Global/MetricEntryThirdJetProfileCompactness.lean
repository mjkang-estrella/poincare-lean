import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Poincare.Global.ClosedMetricThirdJetTopology

/-!
# Arzela--Ascoli compactness for scalar metric third-jet profiles

This module turns componentwise equicontinuity and pointwise compactness into
compactness of the closure of a metric family's scalar third-jet profiles.
The conclusion lives only in `MetricEntryThirdJetProfileTarget`: it does not
assert that every limiting profile is realized by a smooth positive metric.
Consequently, these results alone do not prove compactness of the metric orbit
in `ClosedSmoothRiemannianMetric n M`.
-/

noncomputable section

open Bundle Filter Function Set Topology
open scoped Manifold ContDiff NNReal Topology UniformConvergence

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M
local notation "S" => MetricEntryThirdJetSlot n M
local notation "P" => MetricEntryThirdJetProfileTarget n M

/-- Every scalar metric third-jet profile slot is differentiable in its
model-space coordinate.  For the third-jet slot, this uses the fourth spatial
derivative supplied by `anchorBlendedMetricFamily_contDiff_four`. -/
theorem metricEntryThirdJetProfile_differentiable
    (g : G) (slot : S) :
    Differentiable ℝ
      (fun z : E ↦ metricEntryThirdJetProfile g slot z) := by
  cases slot with
  | value x i j =>
      exact (((anchorBlendedMetricFamily_contDiff_four
        (fun h : G ↦ h) x g).clm_apply contDiff_const).clm_apply
          contDiff_const).differentiable (by norm_num)
  | first x u i j =>
      let A := anchorBlendedMetricFamily (fun h : G ↦ h) x g
      have hA : ContDiff ℝ 4 A :=
        anchorBlendedMetricFamily_contDiff_four (fun h : G ↦ h) x g
      have hD : ContDiff ℝ 3 (fun z ↦ fderiv ℝ A z u) := by
        simpa [A] using (hA.contDiff_fderiv_apply (m := 3) (by norm_num)).comp
          (contDiff_id.prodMk
            (contDiff_const : ContDiff ℝ 3 (fun _ : E ↦ u)))
      exact ((hD.clm_apply contDiff_const).clm_apply contDiff_const).differentiable
        (by norm_num)
  | second x u a i j =>
      let A := anchorBlendedMetricFamily (fun h : G ↦ h) x g
      have hA : ContDiff ℝ 4 A :=
        anchorBlendedMetricFamily_contDiff_four (fun h : G ↦ h) x g
      have hD₁ : ContDiff ℝ 3 (fun z ↦ fderiv ℝ A z u) := by
        simpa [A] using (hA.contDiff_fderiv_apply (m := 3) (by norm_num)).comp
          (contDiff_id.prodMk
            (contDiff_const : ContDiff ℝ 3 (fun _ : E ↦ u)))
      have hD₂ : ContDiff ℝ 2
          (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ A y u) z a) := by
        simpa [A] using (hD₁.contDiff_fderiv_apply (m := 2) (by norm_num)).comp
          (contDiff_id.prodMk
            (contDiff_const : ContDiff ℝ 2 (fun _ : E ↦ a)))
      exact ((hD₂.clm_apply contDiff_const).clm_apply contDiff_const).differentiable
        (by norm_num)
  | third x u a b i j =>
      let A := anchorBlendedMetricFamily (fun h : G ↦ h) x g
      have hA : ContDiff ℝ 4 A :=
        anchorBlendedMetricFamily_contDiff_four (fun h : G ↦ h) x g
      have hD₁ : ContDiff ℝ 3 (fun z ↦ fderiv ℝ A z u) := by
        simpa [A] using (hA.contDiff_fderiv_apply (m := 3) (by norm_num)).comp
          (contDiff_id.prodMk
            (contDiff_const : ContDiff ℝ 3 (fun _ : E ↦ u)))
      have hD₂ : ContDiff ℝ 2
          (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ A y u) z a) := by
        simpa [A] using (hD₁.contDiff_fderiv_apply (m := 2) (by norm_num)).comp
          (contDiff_id.prodMk
            (contDiff_const : ContDiff ℝ 2 (fun _ : E ↦ a)))
      have hD₃ : ContDiff ℝ 1
          (fun z ↦ fderiv ℝ
            (fun y ↦ fderiv ℝ (fun w ↦ fderiv ℝ A w u) y a) z b) := by
        simpa [A] using (hD₂.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
          (contDiff_id.prodMk
            (contDiff_const : ContDiff ℝ 1 (fun _ : E ↦ b)))
      exact ((hD₃.clm_apply contDiff_const).clm_apply contDiff_const).differentiable
        (by norm_num)

private theorem isCompact_closure_range_metricEntryThirdJetProfile_component
    {I : Type v} (gt : I → G) (slot : S)
    (hequicontinuous : Equicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)))
    (hpointwiseCompact : ∀ z : E, ∃ Q : Set ℝ,
      IsCompact Q ∧
        ∀ t : I, metricEntryThirdJetProfile (gt t) slot z ∈ Q) :
    IsCompact (closure (Set.range
      (fun t : I ↦ metricEntryThirdJetProfile (gt t) slot))) := by
  let s : Set C(E, ℝ) :=
    Set.range (fun t : I ↦ metricEntryThirdJetProfile (gt t) slot)
  change IsCompact (closure s)
  have hclosedEmbedding : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set E | IsCompact K} ∘
        ((↑) : C(E, ℝ) → E → ℝ)) := by
    have h : IsClosedEmbedding
        (ContinuousMap.toUniformOnFunIsCompact :
          C(E, ℝ) → E →ᵤ[{K | IsCompact K}] ℝ) := by
      refine
        ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding,
          ?_⟩
      rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOf_continuous
        CompactlyCoherentSpace.isCoherentWith
    simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using h
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := ((↑) : C(E, ℝ) → E → ℝ))
    (s := s) (fun K hK ↦ hK) hclosedEmbedding
  · intro K hK
    classical
    let pick : s → I := fun f ↦ Classical.choose f.property
    have hpick (f : s) :
        metricEntryThirdJetProfile (gt (pick f)) slot = f.1 :=
      Classical.choose_spec f.property
    have hsub : Equicontinuous
        (fun f : s ↦ ((f.1 : C(E, ℝ)) : E → ℝ)) := by
      have h := hequicontinuous.comp pick
      convert h using 1
      funext f z
      exact congrArg (fun q : C(E, ℝ) ↦ q z) (hpick f).symm
    simpa only [Function.comp_apply] using hsub.equicontinuousOn K
  · intro K hK z hz
    obtain ⟨Q, hQcompact, hQ⟩ := hpointwiseCompact z
    refine ⟨Q, hQcompact, ?_⟩
    intro f hf
    obtain ⟨t, rfl⟩ := hf
    exact hQ t

/-- Componentwise Arzela--Ascoli compactness, combined by Tychonoff, proves
compactness of the closure of the scalar third-jet profile orbit.  This is a
statement in the profile target only.  It does not say that a limit profile
comes from a smooth positive metric and therefore does not by itself prove
compactness of the metric orbit. -/
theorem isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise
    {I : Type v} (gt : I → G)
    (hequicontinuous : ∀ slot : S, Equicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)))
    (hpointwiseCompact : ∀ (slot : S) (z : E), ∃ Q : Set ℝ,
      IsCompact Q ∧
        ∀ t : I, metricEntryThirdJetProfile (gt t) slot z ∈ Q) :
    IsCompact (closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt))) := by
  let profile : I → P :=
    metricEntryThirdJetProfile (n := n) (M := M) ∘ gt
  let Q : S → Set C(E, ℝ) := fun slot ↦
    closure (Set.range (fun t : I ↦ profile t slot))
  have hQcompact : ∀ slot : S, IsCompact (Q slot) := by
    intro slot
    exact isCompact_closure_range_metricEntryThirdJetProfile_component
      gt slot (hequicontinuous slot) (hpointwiseCompact slot)
  have hproductCompact : IsCompact (Set.univ.pi Q) :=
    isCompact_univ_pi hQcompact
  change IsCompact (closure (Set.range profile))
  refine IsCompact.of_isClosed_subset hproductCompact isClosed_closure ?_
  apply closure_minimal
  · rintro p ⟨t, rfl⟩
    rw [Set.mem_pi]
    intro slot hslot
    exact subset_closure ⟨t, rfl⟩
  · exact isClosed_set_pi fun slot hslot ↦ (hQcompact slot).isClosed

/-- A real-valued pointwise boundedness hypothesis supplies the compact
pointwise sets needed by the componentwise profile Arzela--Ascoli theorem.
The conclusion remains compactness only in the scalar profile target, not in
the space of smooth positive metrics. -/
theorem isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_bounded
    {I : Type v} (gt : I → G)
    (hequicontinuous : ∀ slot : S, Equicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)))
    (hpointwiseBounded : ∀ (slot : S) (z : E),
      Bornology.IsBounded (Set.range
        (fun t : I ↦ metricEntryThirdJetProfile (gt t) slot z))) :
    IsCompact (closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt))) := by
  apply isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise
    gt hequicontinuous
  intro slot z
  refine ⟨closure (Set.range
    (fun t : I ↦ metricEntryThirdJetProfile (gt t) slot z)), ?_, ?_⟩
  · exact (hpointwiseBounded slot z).isCompact_closure
  · intro t
    exact subset_closure ⟨t, rfl⟩

/-- Uniform bounds on the spatial derivative of each scalar profile slot,
together with bounded values at the zero coordinate, imply compactness of the
profile orbit closure.  The bound is uniform over the family and the whole
model space for each slot.  In a `third` slot it is a genuine fourth-spatial-
jet estimate, since the bounded `fderiv` differentiates the third-jet profile.

The derivative bound gives a common Lipschitz constant for the slot family.
The mean-value estimate then transports boundedness from zero to every model-
space coordinate, so the componentwise bounded Ascoli theorem applies. -/
theorem isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_fderiv_bounded
    {I : Type v} (gt : I → G)
    (hfderivBounded : ∀ slot : S, ∃ C : ℝ≥0, ∀ (t : I) (z : E),
      ‖fderiv ℝ
        (fun w : E ↦ metricEntryThirdJetProfile (gt t) slot w) z‖₊ ≤ C)
    (hzeroBounded : ∀ slot : S,
      Bornology.IsBounded (Set.range
        (fun t : I ↦ metricEntryThirdJetProfile (gt t) slot (0 : E)))) :
    IsCompact (closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt))) := by
  apply isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_bounded
  · intro slot
    obtain ⟨C, hC⟩ := hfderivBounded slot
    exact (LipschitzWith.uniformEquicontinuous
      (fun t : I ↦
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)) C
      (fun t ↦ lipschitzWith_of_nnnorm_fderiv_le
        (metricEntryThirdJetProfile_differentiable (gt t) slot)
        (hC t))).equicontinuous
  · intro slot z
    obtain ⟨C, hC⟩ := hfderivBounded slot
    have hlip : ∀ t : I, LipschitzWith C
        (fun w : E ↦ metricEntryThirdJetProfile (gt t) slot w) :=
      fun t ↦ lipschitzWith_of_nnnorm_fderiv_le
        (metricEntryThirdJetProfile_differentiable (gt t) slot) (hC t)
    obtain ⟨B, hB⟩ := Metric.isBounded_range_iff.mp (hzeroBounded slot)
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * (C : ℝ) * dist z 0 + B, ?_⟩
    intro t s
    calc
      dist (metricEntryThirdJetProfile (gt t) slot z)
          (metricEntryThirdJetProfile (gt s) slot z) ≤
        dist (metricEntryThirdJetProfile (gt t) slot z)
            (metricEntryThirdJetProfile (gt t) slot 0) +
          dist (metricEntryThirdJetProfile (gt t) slot 0)
            (metricEntryThirdJetProfile (gt s) slot z) := dist_triangle _ _ _
      _ ≤ dist (metricEntryThirdJetProfile (gt t) slot z)
            (metricEntryThirdJetProfile (gt t) slot 0) +
          (dist (metricEntryThirdJetProfile (gt t) slot 0)
              (metricEntryThirdJetProfile (gt s) slot 0) +
            dist (metricEntryThirdJetProfile (gt s) slot 0)
              (metricEntryThirdJetProfile (gt s) slot z)) := by
        gcongr
        exact dist_triangle _ _ _
      _ = dist (metricEntryThirdJetProfile (gt t) slot z)
            (metricEntryThirdJetProfile (gt t) slot 0) +
          dist (metricEntryThirdJetProfile (gt t) slot 0)
            (metricEntryThirdJetProfile (gt s) slot 0) +
          dist (metricEntryThirdJetProfile (gt s) slot 0)
            (metricEntryThirdJetProfile (gt s) slot z) := by ring
      _ ≤ (C : ℝ) * dist z 0 + B + (C : ℝ) * dist 0 z := by
        gcongr
        · exact (hlip t).dist_le_mul z 0
        · exact hB t s
        · exact (hlip s).dist_le_mul 0 z
      _ = 2 * (C : ℝ) * dist z 0 + B := by
        rw [dist_comm 0 z]
        ring

end Poincare
