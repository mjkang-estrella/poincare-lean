import Poincare.Global.DuhamelSolutionOperatorBound
import Poincare.Global.CompactCoefficientEllipticity

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.FrozenEllipticHeatOperator

open Set ParabolicHolder

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

theorem parabolicDist_comp_le (S : E →L[ℝ] E) (p q : ℝ × E) :
    parabolicDist (p.1, S p.2) (q.1, S q.2) ≤
      max 1 ‖S‖ * parabolicDist p q := by
  have hs : ‖S (p.2 - q.2)‖ ≤ max 1 ‖S‖ * ‖p.2 - q.2‖ :=
    (S.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have ht : Real.sqrt |p.1 - q.1| ≤ max 1 ‖S‖ * Real.sqrt |p.1 - q.1| := by
    simpa using mul_le_mul_of_nonneg_right (le_max_left 1 ‖S‖)
      (Real.sqrt_nonneg |p.1 - q.1|)
  simpa only [parabolicDist, map_sub, mul_add] using add_le_add hs ht

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] {α T : ℝ}

theorem holderBound_comp (hα : 0 ≤ α) (S : E →L[ℝ] E) (Q : F →L[ℝ] F')
    (f : Y («E» := E) α T F) :
    HasHolderBound α (cylinder T) (fun p => Q (f (p.1, S p.2)))
      (‖Q‖ * max 1 (‖S‖ ^ α) * holderSeminorm α (cylinder T) f) := by
  intro p hp q hq
  have hp' : (p.1, S p.2) ∈ cylinder T := ⟨hp.1, mem_univ _⟩
  have hq' : (q.1, S q.2) ∈ cylinder T := ⟨hq.1, mem_univ _⟩
  have hd : parabolicDist (p.1, S p.2) (q.1, S q.2) ^ α ≤
      max 1 (‖S‖ ^ α) * parabolicDist p q ^ α := by
    have h := Real.rpow_le_rpow (parabolicDist_nonneg _ _) (parabolicDist_comp_le S p q) hα
    simpa only [Real.mul_rpow (by positivity : 0 ≤ max 1 ‖S‖)
      (parabolicDist_nonneg p q), Real.rpow_max zero_le_one (norm_nonneg S) hα,
      Real.one_rpow] using h
  calc
    ‖Q (f (p.1, S p.2)) - Q (f (q.1, S q.2))‖ =
        ‖Q (f (p.1, S p.2) - f (q.1, S q.2))‖ := by rw [map_sub]
    _ ≤ ‖Q‖ * ‖f (p.1, S p.2) - f (q.1, S q.2)‖ := Q.le_opNorm _
    _ ≤ ‖Q‖ * (holderSeminorm α (cylinder T) f *
        parabolicDist (p.1, S p.2) (q.1, S q.2) ^ α) :=
      mul_le_mul_of_nonneg_left (hasHolderBound_seminorm f _ hp' _ hq') (norm_nonneg Q)
    _ ≤ ‖Q‖ * (holderSeminorm α (cylinder T) f *
        (max 1 (‖S‖ ^ α) * parabolicDist p q ^ α)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hd (holderSeminorm_nonneg f)) (norm_nonneg Q)
    _ = _ := by ring

/-- Simultaneous spatial substitution and a bounded linear map on the values. -/
def mapHolder (hα : 0 ≤ α) (S : E →L[ℝ] E) (Q : F →L[ℝ] F')
    (f : Y («E» := E) α T F) : Y («E» := E) α T F' :=
  ofFunction (fun p => Q (f (p.1, S p.2)))
    (fun p hp => by
      dsimp only
      rw [zero_off f (p := (p.1, S p.2)) (fun h => hp ⟨h.1, mem_univ _⟩), map_zero])
    ⟨‖Q‖ * supNorm (cylinder T) f, fun p _ =>
      (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left (le_supNorm f _) (norm_nonneg Q))⟩
    ⟨_, holderBound_comp hα S Q f⟩

theorem norm_mapHolder_le (hα : 0 ≤ α) (S : E →L[ℝ] E) (Q : F →L[ℝ] F')
    (f : Y («E» := E) α T F) :
    ‖mapHolder hα S Q f‖ ≤ ‖Q‖ * max 1 (‖S‖ ^ α) * ‖f‖ := by
  have hb := norm_le_of_bounds (mapHolder hα S Q f)
    (mul_nonneg (norm_nonneg Q) (supNorm_nonneg f))
    (mul_nonneg (mul_nonneg (norm_nonneg Q) (by positivity)) (holderSeminorm_nonneg f))
    (fun p _ => (Q.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (le_supNorm f (p.1, S p.2)) (norm_nonneg Q)))
    (holderBound_comp hα S Q f)
  have hm : ‖Q‖ * supNorm (cylinder T) f ≤
      ‖Q‖ * max 1 (‖S‖ ^ α) * supNorm (cylinder T) f := by
    have := mul_le_mul_of_nonneg_right (le_max_left 1 (‖S‖ ^ α))
      (mul_nonneg (norm_nonneg Q) (supNorm_nonneg f))
    nlinarith only [this]
  rw [ParabolicHolder.norm_eq f]
  nlinarith only [hb, hm]

theorem norm_forcing_pullback_le (hα : 0 ≤ α) (S : E →L[ℝ] E)
    (f : Y («E» := E) α T ℝ) :
    ‖mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) f‖ ≤ max 1 (‖S‖ ^ α) * ‖f‖ := by
  simpa only [ContinuousLinearMap.norm_id, one_mul] using
    norm_mapHolder_le hα S (ContinuousLinearMap.id ℝ ℝ) f

local instance instCovectorNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

local instance instCovectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

local instance instBilinNormedGroup : NormedAddCommGroup Bilin := inferInstance

local instance instBilinNormedSpace : NormedSpace ℝ Bilin :=
  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }

def covectorPullback (S : E →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E E ℝ).flip S

theorem norm_covectorPullback_le (S : E →L[ℝ] E) : ‖covectorPullback S‖ ≤ ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
  intro v
  exact (v.opNorm_comp_le S).trans_eq (mul_comm _ _)

def bilinearPullback (S : E →L[ℝ] E) : Bilin →L[ℝ] Bilin :=
  ((ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ)).flip S).comp
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)) (covectorPullback S))

theorem norm_bilinearPullback_le (S : E →L[ℝ] E) :
    ‖bilinearPullback S‖ ≤ ‖S‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg ‖S‖)
  intro B
  change ‖((covectorPullback S).comp B).comp S‖ ≤ _
  calc
    ‖((covectorPullback S).comp B).comp S‖ ≤ ‖(covectorPullback S).comp B‖ * ‖S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖covectorPullback S‖ * ‖B‖) * ‖S‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg S)
    _ ≤ (‖S‖ * ‖B‖) * ‖S‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_covectorPullback_le S) (norm_nonneg B)) (norm_nonneg S)
    _ = _ := by ring

end Poincare.FrozenEllipticHeatOperator
