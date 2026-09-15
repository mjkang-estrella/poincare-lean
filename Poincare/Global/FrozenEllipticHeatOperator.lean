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

/-- Pull back all four graph components and their genuine derivative relations. -/
def mapGraph (hα : 0 ≤ α) (S : E →L[ℝ] E)
    (H : ParabolicSolutionGraph.Graph («E» := E) α T) :
    ParabolicSolutionGraph.Graph («E» := E) α T where
  u := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) H.u
  ut := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) H.ut
  du := mapHolder hα S (covectorPullback S) H.du
  ddu := mapHolder hα S (bilinearPullback S) H.ddu
  zero_trace := fun x => H.zero_trace (S x)
  hasFDeriv := by
    intro t ht x
    exact (H.hasFDeriv t ht (S x)).comp x S.hasFDerivAt
  hasFDeriv_du := by
    intro t ht x
    exact (covectorPullback S).hasFDerivAt.comp x
      ((H.hasFDeriv_du t ht (S x)).comp x S.hasFDerivAt)
  hasDeriv_time := fun t ht x => H.hasDeriv_time t ht (S x)

theorem norm_mapGraph_le (hα : 0 ≤ α) (S : E →L[ℝ] E)
    (H : ParabolicSolutionGraph.Graph («E» := E) α T) :
    ‖mapGraph hα S H‖ ≤ max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α) * ‖H‖ := by
  let M := max 1 (‖S‖ ^ 2)
  let K := max 1 (‖S‖ ^ α)
  have hn : ‖S‖ ≤ M := by
    by_cases h : ‖S‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · have := le_max_right 1 (‖S‖ ^ 2)
      dsimp only [M]
      nlinarith
  have hb {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (Q : V →L[ℝ] W) (hQ : ‖Q‖ ≤ M) (f : Y («E» := E) α T V) :
      ‖mapHolder hα S Q f‖ ≤ M * K * ‖f‖ :=
    (norm_mapHolder_le hα S Q f).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hQ (by positivity : 0 ≤ K)) (norm_nonneg f))
  have hu := hb (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)) H.u
  have ht := hb (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)) H.ut
  have hd := hb (covectorPullback S) ((norm_covectorPullback_le S).trans hn) H.du
  have hdd := hb (bilinearPullback S)
    ((norm_bilinearPullback_le S).trans (le_max_right _ _)) H.ddu
  rw [ParabolicSolutionGraph.norm_eq, ParabolicSolutionGraph.norm_eq H]
  change ‖mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) H.u‖ +
    ‖mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) H.ut‖ +
    ‖mapHolder hα S (covectorPullback S) H.du‖ +
    ‖mapHolder hα S (bilinearPullback S) H.ddu‖ ≤ M * K * _
  nlinarith only [hu, ht, hd, hdd]

theorem trace_pullback (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w)) (H : Bilin) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      inner ℝ (S (e i)) (S (e j)) * H (S.symm (e i)) (S.symm (e j))) =
      ∑ k : Fin 3, H (e k) (e k) := by
  have hb (k : Fin 3) :
      ∑ i : Fin 3, inner ℝ (e i) (S (e k)) • S.symm (e i) = e k := by
    simpa only [map_sum, map_smul, S.symm_apply_apply] using
      congrArg S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr' (S (e k)))
  have hc (i j : Fin 3) : inner ℝ (S (e i)) (S (e j)) =
      ∑ k : Fin 3, inner ℝ (e i) (S (e k)) * inner ℝ (e j) (S (e k)) := by
    rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_inner_mul_inner (S (e i)) (S (e j))]
    apply Finset.sum_congr rfl
    intro k _
    rw [hS, ← hS (e k) (e j), real_inner_comm (S (e k)) (e j)]
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (inner ℝ (e i) (S (e k)) * inner ℝ (e j) (S (e k))) *
          H (S.symm (e i)) (S.symm (e j)) := by simp_rw [hc, Finset.sum_mul]
    _ = ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3,
        (inner ℝ (e i) (S (e k)) * inner ℝ (e j) (S (e k))) *
          H (S.symm (e i)) (S.symm (e j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
        (inner ℝ (e i) (S (e k)) * inner ℝ (e j) (S (e k))) *
          H (S.symm (e i)) (S.symm (e j)) := Finset.sum_comm
    _ = ∑ k : Fin 3,
        H (∑ i : Fin 3, inner ℝ (e i) (S (e k)) • S.symm (e i))
          (∑ j : Fin 3, inner ℝ (e j) (S (e k)) • S.symm (e j)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [hb]

theorem graph_heat_equation_of_duhamel (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ)
    (H : ParabolicSolutionGraph.Graph («E» := E) α T)
    (hH : ∀ p ∈ cylinder T, H.u p =
      ∫ s in (0 : ℝ)..p.1, heatSolution (p.1 - s) (fun y => f (s, y)) p.2) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      H.ut (t, x) = f (t, x) + ∑ i : Fin 3, H.ddu (t, x) (e i) (e i) := by
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t - s) (fun y => f (s, y)) x
  have hu (t : ℝ) (ht : t ∈ Icc 0 T) : (fun x => H.u (t, x)) = u t :=
    funext fun x => hH (t, x) ⟨ht, mem_univ x⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fun x => H.du (t, x)) = fderiv ℝ (u t) := by
    funext x
    rw [← hu t ht]
    exact (H.hasFDeriv t ht x).fderiv.symm
  have hdd (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
      H.ddu (t, x) = fderiv ℝ (fderiv ℝ (u t)) x := by
    rw [← hd t ht]
    exact (H.hasFDeriv_du t ht x).fderiv.symm
  have hf := DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound hα
    (ParabolicHolder.hasHolderBound f)
  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
      |f (t, x) - f (t, y)| ≤ ‖f‖ * ‖x - y‖ ^ α := by
    intro t ht x y
    simpa only [parabolicDist, sub_self, abs_zero, Real.sqrt_zero, add_zero,
      Real.norm_eq_abs] using ParabolicHolder.holder_le f
        (show (t, x) ∈ cylinder T from ⟨ht, mem_univ x⟩)
        (show (t, y) ∈ cylinder T from ⟨ht, mem_univ y⟩)
  have heq := (MovingLimitLeibniz.duhamel_solves_heat_equation α hα hα1 T hT hT1
    f ‖f‖ ‖f‖ (norm_nonneg f) (norm_nonneg f) hf
    (fun t _ x => ParabolicHolder.norm_le f (t, x)) hspace).2
  intro t ht x
  have htime := (heq t ht x).congr_of_mem
    (fun s hs => congrFun (hu s hs) x) ht
  have huniq := uniqueDiffOn_Icc hT t ht
  have hval := ((H.hasDeriv_time t ht x).derivWithin huniq).symm.trans
    (htime.derivWithin huniq)
  simpa only [hdd t ht x] using hval

theorem exists_solution_graph_bound_of_factorization :
    ∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ (A : Bilin) (S : E ≃L[ℝ] E),
      (∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w)) →
      (∀ v w : E, A v w = inner ℝ (S v) (S w)) →
    ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ f : Y («E» := E) α T ℝ,
      ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
        (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
          ∑ i : Fin 3, ∑ j : Fin 3, A (e i) (e j) * G.ddu (t, x) (e i) (e j)) ∧
        ‖G‖ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
          max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
          C * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖ := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := DuhamelSolutionOperatorBound.exists_solution_graph_bound α hα hα1
  refine ⟨C, hC, ?_⟩
  intro A S hS hA T hT hT1 f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  obtain ⟨H, hH, hHN⟩ := hCb T hT hT1 g
  let G := mapGraph hα.le (S.symm : E →L[ℝ] E) H
  refine ⟨G, ?_, ?_⟩
  · intro t ht x
    have heq := graph_heat_equation_of_duhamel hα hα1 hT hT1 g H hH t ht (S.symm x)
    change H.ut (t, S.symm x) = f (t, x) +
      ∑ i : Fin 3, ∑ j : Fin 3, A (e i) (e j) *
        H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
    simp_rw [hA]
    rw [trace_pullback S hS]
    simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq
  · have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
    have hb := norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H
    have hHN' := hHN.trans (mul_le_mul_of_nonneg_left hg hC.le)
    exact hb.trans (by
      calc
        _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
            max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
            (C * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
          mul_le_mul_of_nonneg_left hHN' (by positivity)
        _ = _ := by ring)

end Poincare.FrozenEllipticHeatOperator
