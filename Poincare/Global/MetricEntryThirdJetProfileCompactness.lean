import Mathlib.Topology.MetricSpace.ProperSpace.Real
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
open scoped Manifold ContDiff Topology UniformConvergence

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

end Poincare
