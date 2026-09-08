import Poincare.Global.CartanSuppliedUniformPatchSwitch

set_option autoImplicit false
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
namespace CartanSuppliedBufferedPairAgreement
open CartanSuppliedDifferentialSuccessor CartanSuppliedFinitePatchCover
open FixedChartUniformPreferredGermAgreement

/-- The derivative between two fixed hosts is the change between their
stored velocity frames, on the actual overlap. -/
theorem patchFrame_chartTransition {a b : M} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (D : FixedChartUniformSourceNormal.Patch g b V)
    (x : M) (hxC : x ∈ C.anchors) (hxD : x ∈ D.anchors) (v : E) :
    patchFrame D x (GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x) v) =
      patchFrame C x v := by
  have frame : ∀ {a : M} {U : Set E}
      (C : FixedChartUniformSourceNormal.Patch g a U) (hx : x ∈ C.anchors),
      (patchFrame C x : E →L[ℝ] E) = anchorFrame a x := by
    intro a U C hx
    unfold patchFrame
    rw [dif_pos hx]
    exact Classical.choose_spec (anchorFrame_isInvertible C x hx)
  let q := extChartAt I a x
  have hqa := (extChartAt I a).map_source hxC.1
  have hqb := (extChartAt I b).map_source hxD.1
  have hab : (extChartAt I a).symm q ∈ (extChartAt I b).source := by
    rw [(extChartAt I a).left_inv hxC.1]
    exact hxD.1
  have hbx : (extChartAt I b).symm (extChartAt I b x) ∈ (extChartAt I x).source := by
    rw [(extChartAt I b).left_inv hxD.1]
    exact mem_extChartAt_source x
  have hax : (extChartAt I a).symm q ∈ (extChartAt I x).source := by
    rw [(extChartAt I a).left_inv hxC.1]
    exact mem_extChartAt_source x
  have habq : GeodesicTransport.chartTransition a b q = extChartAt I b x := by
    exact congrArg (extChartAt I b) ((extChartAt I a).left_inv hxC.1)
  have hdab := (chartTransition_contDiffAt a b hqa hab).differentiableAt (by norm_num)
  have hdbx := (chartTransition_contDiffAt b x hqb hbx).differentiableAt (by norm_num)
  have hdax := (chartTransition_contDiffAt a x hqa hax).differentiableAt (by norm_num)
  have he : (GeodesicTransport.chartTransition b x ∘ GeodesicTransport.chartTransition a b)
      =ᶠ[𝓝 q] GeodesicTransport.chartTransition a x := by
    have hi := (continuousAt_extChartAt_symm'' hqa).tendsto
    filter_upwards [hi ((isOpen_extChartAt_source b).mem_nhds hab)] with z hz
    change extChartAt I x ((extChartAt I b).symm
      (extChartAt I b ((extChartAt I a).symm z))) = _
    rw [(extChartAt I b).left_inv hz]
    rfl
  rw [← habq] at hdbx
  have hd := ((hdbx.hasFDerivAt.comp q hdab.hasFDerivAt).congr_of_eventuallyEq
    he.symm).unique hdax.hasFDerivAt
  change (patchFrame D x : E →L[ℝ] E) _ = (patchFrame C x : E →L[ℝ] E) _
  rw [frame C hxC, frame D hxD]
  simpa only [anchorFrame, GeodesicTransport.chartTransitionDeriv, habq,
    ContinuousLinearMap.comp_apply] using congrArg (fun A : E →L[ℝ] E => A v) hd

/-- A fixed chart transition has one operator bound over a compact overlap. -/
theorem exists_uniform_chartTransition_bound {a b : M} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g a U)
    (D : FixedChartUniformSourceNormal.Patch g b V)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) (hKD : K ⊆ D.anchors) :
    ∃ R > (0 : ℝ), ∀ x ∈ K,
      ‖GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x)‖ ≤ R := by
  let J := fun x : M => GeodesicTransport.chartTransitionDeriv a b (extChartAt I a x)
  have hc : ContinuousOn J K := by
    intro x hx
    have ht := (extChartAt I a).map_source (hKC hx).1
    have hs : (extChartAt I a).symm (extChartAt I a x) ∈ (extChartAt I b).source := by
      rw [(extChartAt I a).left_inv (hKC hx).1]
      exact (hKD hx).1
    exact ((chartTransition_contDiffAt a b ht hs).continuousAt_fderiv (by norm_num)
      |>.comp (continuousAt_extChartAt' (hKC hx).1)).continuousWithinAt
  obtain ⟨R, hR, hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨R, hR, fun x hx => hb _ ⟨x, hx, rfl⟩⟩

end CartanSuppliedBufferedPairAgreement
end Poincare
