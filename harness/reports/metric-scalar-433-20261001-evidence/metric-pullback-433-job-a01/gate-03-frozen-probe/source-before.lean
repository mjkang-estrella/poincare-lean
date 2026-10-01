import Poincare.Global.SmoothInitialMetricDefinitions

noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
universe u

namespace Poincare.SmoothInitialMetricLocalPullback

open SmoothInitialMetricDefinitions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- A chart's pulled-back Euclidean bilinear form is symmetric everywhere. -/
theorem localEuclideanInner_symm (p x : M)
    (v w : TangentSpace (closedSmoothModelWithCorners 3) x) :
    localEuclideanInner p x v w = localEuclideanInner p x w v := by
  simp only [localEuclideanInner_apply]
  exact real_inner_comm _ _

/-- The coordinate map sends nonzero vectors to nonzero vectors on its domain. -/
theorem localEuclideanInner_pos (p x : M)
    (hx : x ∈ (trivializationAt (ClosedSmoothModel 3)
      (TangentSpace (closedSmoothModelWithCorners 3)) p).baseSet)
    (v : TangentSpace (closedSmoothModelWithCorners 3) x) (hv : v ≠ 0) :
    0 < localEuclideanInner p x v v := by
  rw [localEuclideanInner_apply]
  apply real_inner_self_pos.mpr
  intro hzero
  apply hv
  have h := (trivializationAt (ClosedSmoothModel 3)
    (TangentSpace (closedSmoothModelWithCorners 3)) p).symmL_continuousLinearMapAt
      (R := ℝ) hx v
  rw [hzero, map_zero] at h
  exact h.symm

set_option maxHeartbeats 1000000 in
/-- In the associated bilinear trivialization, the pullback has constant coordinates. -/
theorem localEuclideanInner_coordinates (p x : M)
    (hx : x ∈ (trivializationAt (ClosedSmoothModel 3)
      (TangentSpace (closedSmoothModelWithCorners 3)) p).baseSet) :
    let e := trivializationAt (ClosedSmoothModel 3)
      (TangentSpace (closedSmoothModelWithCorners 3)) p
    let eR := trivializationAt ℝ (fun _ : M ↦ ℝ) p
    ((e.continuousLinearMap (RingHom.id ℝ)
      (e.continuousLinearMap (RingHom.id ℝ) eR))
      ⟨x, localEuclideanInner p x⟩).2 = innerSL ℝ (E := ClosedSmoothModel 3) := by
  dsimp only
  let e := trivializationAt (ClosedSmoothModel 3)
    (TangentSpace (closedSmoothModelWithCorners 3)) p
  let eR := trivializationAt ℝ (fun _ : M ↦ ℝ) p
  let eHom := e.continuousLinearMap (RingHom.id ℝ) eR
  have hxHom : x ∈ eHom.baseSet := by simpa [eHom, eR, e] using hx
  ext a b
  simp only [Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ eHom hxHom]
  simp only [eHom, Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply]
  change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x
    (localEuclideanInner p x (e.symmL ℝ x a) (e.symmL ℝ x b)) = inner ℝ a b
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization]
  simp only [ContinuousLinearMap.id_apply, localEuclideanInner_apply]
  rw [Trivialization.continuousLinearMapAt_symmL _ hx,
    Trivialization.continuousLinearMapAt_symmL _ hx]

set_option synthInstance.maxHeartbeats 200000 in
/-- The actual bilinear bundle section is smooth on the coordinate domain. -/
theorem localEuclideanInner_contMDiffOn (p : M) :
    ContMDiffOn (closedSmoothModelWithCorners 3)
      ((closedSmoothModelWithCorners 3).prod
        𝓘(ℝ, ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)) ∞
      (fun x : M ↦ TotalSpace.mk'
        (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
        x (localEuclideanInner p x))
      (trivializationAt (ClosedSmoothModel 3)
        (TangentSpace (closedSmoothModelWithCorners 3)) p).baseSet := by
  let e := trivializationAt (ClosedSmoothModel 3)
    (TangentSpace (closedSmoothModelWithCorners 3)) p
  let eR := trivializationAt ℝ (fun _ : M ↦ ℝ) p
  let eBil := e.continuousLinearMap (RingHom.id ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) eR)
  have hbase : eBil.baseSet = e.baseSet := by simp [eBil, eR]
  rw [← hbase, eBil.contMDiffOn_section_baseSet_iff]
  refine (contMDiffOn_const
    (M' := ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
    (c := innerSL ℝ)).congr ?_
  intro x hx
  exact localEuclideanInner_coordinates p x (hbase ▸ hx)

end Poincare.SmoothInitialMetricLocalPullback
