import Poincare.Global.RegularCoherentVariationalTwoRestartBridge

/-!
# Complete two-restart point-flow package from the coherent hierarchy

The remaining endpoint field-regularity input in the joint `C³` bootstrap is
made automatic here.  Local `C⁴` regularity of the autonomous time--point
field supplies a neighborhood on which it is `C²`.  Continuity of the exact
retained base selector at relative time zero supplies a positive time radius
whose central trajectory stays in that neighborhood.  Cutting the
synchronized restart core below this radius therefore provides both the
forward joint third-order tower and the backward joint first-order data for
one and the same selector.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section CompleteTwoRestartPackage

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]

/-- A local `C⁴` autonomous time--point field yields a complete two-restart
point-flow package.  Both restart families and both smooth-dependence towers
refer to the exact base selector of one regular coherent hierarchy. -/
theorem exists_twoRestartPointFlowPackage_of_timePoint_contDiffAt_four
    (V : ℝ → E → E) (z₀ : E) (Tmax : ℝ) (hTmax : 0 < Tmax)
    (hG : ContDiffAt ℝ 4
      (fun q : ℝ × E ↦ ((1 : ℝ), V q.1 q.2)) (0, z₀)) :
    ∃ t ∈ Ioo (0 : ℝ) Tmax,
      ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
        Nonempty (TwoRestartPointFlowPackage V Phi Psi t z₀ y₁) := by
  let p₀ : ℝ × E := (0, z₀)
  let G : (ℝ × E) → (ℝ × E) :=
    fun q ↦ ((1 : ℝ), V q.1 q.2)
  have hG' : ContDiffAt ℝ 4 G p₀ := by
    simpa only [G, p₀] using hG
  rcases exists_regularCoherentThreeLevelVariationalSelectorTower_of_contDiffAt_four
      G p₀ hG' with ⟨T⟩
  have hregular : {q : ℝ × E | ContDiffAt ℝ 2 G q} ∈ nhds p₀ :=
    (hG'.of_le (by norm_num : (2 : ℕ∞ω) ≤ 4)).eventually (by norm_num)
  have hzeroInterior : (0 : ℝ) ∈
      Ioo (-T.base.epsilon) T.base.epsilon :=
    ⟨by linarith [T.base.epsilon_pos], T.base.epsilon_pos⟩
  have hselectorJoint : ContinuousAt
      (Function.uncurry T.base.selector) (p₀, 0) :=
    T.base.selector_continuousAt hzeroInterior
  have hembed : ContinuousAt (fun s : ℝ ↦ (p₀, s)) 0 :=
    continuousAt_const.prodMk continuousAt_id
  have hpath : ContinuousAt (T.base.selector p₀) 0 := by
    have hcomp : ContinuousAt
        (fun s : ℝ ↦
          (Function.uncurry T.base.selector) (p₀, s)) 0 :=
      ContinuousAt.comp' hselectorJoint hembed
    simpa only [Function.uncurry] using hcomp
  have hselectorZero : T.base.selector p₀ 0 = p₀ :=
    (T.base.selector_data p₀
      (mem_closedBall_self (show (0 : ℝ) ≤ T.base.initialRadius by positivity))).1
  have hregularAtSelectorZero :
      {q : ℝ × E | ContDiffAt ℝ 2 G q} ∈
        nhds (T.base.selector p₀ 0) := by
    simpa only [hselectorZero] using hregular
  have hnear : (T.base.selector p₀) ⁻¹'
      {q : ℝ × E | ContDiffAt ℝ 2 G q} ∈ nhds (0 : ℝ) :=
    hpath hregularAtSelectorZero
  rcases Metric.mem_nhds_iff.mp hnear with
    ⟨delta, hdelta, hdeltaSub⟩
  let Tsmall : ℝ := min Tmax delta
  have hTsmall : 0 < Tsmall := by
    exact lt_min hTmax hdelta
  rcases T.base.exists_twoRestartPointFlowCoreWithSelector_eq
      V z₀ Tsmall hTsmall with
    ⟨t, ht, Phi, Psi, y₁, C, hselector, hrestart⟩
  have htTsmall : t < Tsmall :=
    ht.2.trans_le (min_le_left _ _)
  have htTmax : t < Tmax :=
    htTsmall.trans_le (by dsimp only [Tsmall]; exact min_le_left _ _)
  have htdelta : t < delta :=
    htTsmall.trans_le (by dsimp only [Tsmall]; exact min_le_right _ _)
  have htHalf : t < T.base.epsilon / 2 :=
    ht.2.trans_le (min_le_right _ _)
  have htBall : t ∈ ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht.1] using htdelta
  have hfield : ContDiffAt ℝ 2 G (T.base.selector p₀ t) :=
    hdeltaSub htBall
  have hpos : t ∈ Ioo (-(T.base.epsilon / 2))
      (T.base.epsilon / 2) := by
    constructor
    · linarith [ht.1, T.base.epsilon_pos]
    · exact htHalf
  have hneg : -t ∈ Ioo (-(T.base.epsilon / 2))
      (T.base.epsilon / 2) := by
    constructor
    · linarith
    · linarith [ht.1, T.base.epsilon_pos]
  have P : TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ := by
    apply C.toPointFlowPackage_of_regularCoherentTower
      T hselector hrestart hpos hneg
    simpa only [p₀] using hfield
  exact ⟨t, ⟨ht.1, htTmax⟩, Phi, Psi, y₁, ⟨P⟩⟩

end CompleteTwoRestartPackage

end Poincare
