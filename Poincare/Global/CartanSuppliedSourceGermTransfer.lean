import Poincare.Global.CartanSuppliedSourceMap

/-!
# Neighborhood transport for supplied source Cartan germs

Agreement of supplied normal coordinates near an anchor transfers to the
Cartan maps and to the inverse normal coordinates near zero. The inverse
comparison uses the partial inverse laws only on their open domains.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanSuppliedSourceGermTransfer

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Normal-coordinate agreement near the anchor gives Cartan germ agreement. -/
theorem germ_eventuallyEq_of_normal_eventuallyEq
    (S S' : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E)
    (h : (S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E)) :
    (CartanSuppliedSourceMap.germ S F x p K : M → RoundSphere3)
      =ᶠ[𝓝 x]
    (CartanSuppliedSourceMap.germ S' F x p K : M → RoundSphere3) := by
  rw [CartanSuppliedSourceMap.germ_apply, CartanSuppliedSourceMap.germ_apply]
  filter_upwards [h] with z hz
  rw [hz]

/-- Inverse normal coordinates agree near zero by the local inverse laws. -/
theorem normal_symm_eventuallyEq_of_normal_eventuallyEq
    (S S' : CartanSourceExponential.Family g) (x : M)
    (h : (S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E)) :
    ((S.normal x).symm : E → M) =ᶠ[𝓝 (0 : E)]
      ((S'.normal x).symm : E → M) := by
  have hzero : (0 : E) ∈ (S.normal x).target := by
    simpa only [S.normal_anchor] using
      (S.normal x).map_source (S.anchor_mem_source x)
  have hinvzero : (S.normal x).symm (0 : E) = x := by
    simpa only [S.normal_anchor] using
      (S.normal x).left_inv (S.anchor_mem_source x)
  have htendsto : Tendsto (S.normal x).symm (𝓝 (0 : E)) (𝓝 x) := by
    simpa only [hinvzero] using (S.normal x).continuousAt_symm hzero |>.tendsto
  have hsource : ∀ᶠ v in 𝓝 (0 : E),
      (S.normal x).symm v ∈ (S'.normal x).source :=
    htendsto ((S'.normal x).open_source.mem_nhds (S'.anchor_mem_source x))
  filter_upwards [htendsto h, hsource,
    (S.normal x).open_target.mem_nhds hzero] with v hv hvs hvt
  have heq : S'.normal x ((S.normal x).symm v) = v :=
    hv.symm.trans ((S.normal x).right_inv hvt)
  calc
    (S.normal x).symm v =
        (S'.normal x).symm (S'.normal x ((S.normal x).symm v)) :=
      ((S'.normal x).left_inv hvs).symm
    _ = (S'.normal x).symm v := congrArg (S'.normal x).symm heq

/-- The agreeing Cartan germs share an open source neighborhood of the anchor. -/
theorem exists_open_common_source_agreement
    (S S' : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E)
    (h : (S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E)) :
    ∃ V, IsOpen V ∧ x ∈ V ∧
      V ⊆ (CartanSuppliedSourceMap.germ S F x p K).source ∩
        (CartanSuppliedSourceMap.germ S' F x p K).source ∧
      EqOn (CartanSuppliedSourceMap.germ S F x p K)
        (CartanSuppliedSourceMap.germ S' F x p K) V := by
  have hagree := germ_eventuallyEq_of_normal_eventuallyEq S S' F x p K h
  have hsource := (CartanSuppliedSourceMap.germ S F x p K).open_source.mem_nhds
    (CartanSuppliedSourceMap.anchor_mem_source S F x p K)
  have hsource' := (CartanSuppliedSourceMap.germ S' F x p K).open_source.mem_nhds
    (CartanSuppliedSourceMap.anchor_mem_source S' F x p K)
  rcases mem_nhds_iff.mp (inter_mem (inter_mem hsource hsource') hagree) with
    ⟨V, hV, hVopen, hxV⟩
  exact ⟨V, hVopen, hxV, fun z hz => (hV hz).1, fun z hz => (hV hz).2⟩

end CartanSuppliedSourceGermTransfer
end Poincare
