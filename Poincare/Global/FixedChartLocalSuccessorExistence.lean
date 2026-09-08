import Poincare.Global.CartanSuppliedDifferentialTransfer
import Poincare.Global.TangentAlignmentFiberCompactness
import Poincare.Global.UniformTangentAlignmentRigidity

/-!
# Compact control of retained normal domains

These estimates concern the actual retained patch domains. The uniform
strict differential and metric-pullback witnesses needed for successor data
are not constructed here.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartLocalSuccessorExistence
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3) (η : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
    z ∈ Q.sourceAnchors ∧ map Q ⟨x, p, L⟩ z ∈ Q.targetAnchors ∧
    z ∈ (germ Q ⟨x, p, L⟩).source ∧ Nonempty (Data Q ⟨x, p, L⟩ z)

/-- A compact set of retained anchors has a common normal source radius,
with retained successor anchors and arbitrarily small normal vectors. -/
theorem exists_uniform_normal_radius {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    {ρ : ℝ} (hρ : 0 < ρ) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ z : M, dist z x < η →
      z ∈ C.anchors ∧ z ∈ (C.normal x).source ∧ ‖C.normal x z‖ < ρ := by
  letI : MetricSpace M := g.toMetricSpace
  let W : Set (M × M) := C.rawLocalFamily.controlledSourceLocus ρ ∩
    Prod.snd ⁻¹' C.anchors
  have hW : IsOpen W :=
    (C.rawLocalFamily.isOpen_controlledSourceLocus ρ).inter
      (C.isOpen_anchors.preimage continuous_snd)
  have hdiag : IsCompact ((fun x : M => (x, x)) '' K) :=
    hK.image (continuous_id.prodMk continuous_id)
  have hsub : (fun x : M => (x, x)) '' K ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨⟨hKC hx, C.anchor_mem_normal_source x (hKC hx)⟩, ?_⟩, hKC hx⟩
    change C.normal x x ∈ ball (0 : E) ρ
    rw [C.normal_anchor x (hKC hx)]
    exact mem_ball_self hρ
  obtain ⟨η, hη, hηW⟩ := hdiag.exists_cthickening_subset_open hW hsub
  refine ⟨η, hη, ?_⟩
  intro x hx z hz
  have hmem : (x, z) ∈ cthickening η ((fun x : M => (x, x)) '' K) := by
    apply mem_cthickening_of_dist_le (x, z) (x, x) η
      ((fun x : M => (x, x)) '' K) ⟨x, hx, rfl⟩
    simpa [Prod.dist_eq] using hz.le
  have hw := hηW hmem
  refine ⟨hw.2, hw.1.1.2, ?_⟩
  simpa [CartanSourceExponential.LocalFamily.controlledSourceLocus,
    FixedChartUniformSourceNormal.Patch.rawLocalFamily, mem_ball, dist_eq_norm] using hw.1.2

end FixedChartLocalSuccessorExistence
end Poincare
