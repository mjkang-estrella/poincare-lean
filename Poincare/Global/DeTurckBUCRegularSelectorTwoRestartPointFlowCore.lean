import Poincare.Global.DeTurckBUCTwoRestartPointFlowCore
import Poincare.Global.PicardLindelofRegularControlledSelector

/-!
# A two-restart core cut from a supplied regular selector

The ordinary two-restart existence theorem chooses its own Picard--Lindelof
selector.  Variational regularity, however, is proved for a particular
regular coherent selector tower.  This file closes that choice mismatch:
given the base selector of such a tower for the autonomous time--point
extension, it cuts both restart families from that exact selector.

The endpoint time is chosen inside the protected positive half interval and
so small that the endpoint extended state is still in the selector's initial
ball.  Hence the same retained family is valid at the restarted state.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 120000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section SuppliedRegularSelectorCore

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Cut a genuine two-restart point-flow core from one supplied regular
selector of the autonomous time--point extension.

In particular, the selector retained by the resulting core is definitionally
the selector supplied in `H`; no uniqueness comparison with an independently
chosen Picard--Lindelof family is required. -/
theorem LocalRegularControlledContinuousAutonomousSelector.exists_twoRestartPointFlowCoreWithSelector_eq
    (V : ℝ → E → E) (z₀ : E)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (fun q : ℝ × E ↦ (1, V q.1 q.2)) (0, z₀))
    (Tmax : ℝ) (hTmax : 0 < Tmax) :
    ∃ t ∈ Ioo (0 : ℝ) (min Tmax (H.epsilon / 2)),
      ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
        ∃ C : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁,
          C.selector = H.selector ∧
            (t, y₁) ∈ ball (0, z₀) (H.initialRadius : ℝ) := by
  let p₀ : ℝ × E := (0, z₀)
  have hp₀ : p₀ ∈ closedBall p₀ (H.initialRadius : ℝ) :=
    mem_closedBall_self (by positivity)
  have hzero : (0 : ℝ) ∈ Icc (-H.epsilon) H.epsilon :=
    ⟨by linarith [H.epsilon_pos], H.epsilon_pos.le⟩
  have hbaseAt : HasDerivAt (H.selector p₀)
      ((1, V (H.selector p₀ 0).1 (H.selector p₀ 0).2) : ℝ × E) 0 :=
    ((H.selector_data p₀ hp₀).2.1 0 hzero).hasDerivAt
      (Icc_mem_nhds (by linarith [H.epsilon_pos]) H.epsilon_pos)
  have hinitialReal : 0 < (H.initialRadius : ℝ) := by
    exact_mod_cast H.initialRadius_pos
  have hnear : (fun s ↦ H.selector p₀ s) ⁻¹'
      ball p₀ (H.initialRadius : ℝ) ∈ nhds (0 : ℝ) := by
    apply hbaseAt.continuousAt.preimage_mem_nhds
    rw [(H.selector_data p₀ hp₀).1]
    exact isOpen_ball.mem_nhds (mem_ball_self hinitialReal)
  rcases Metric.mem_nhds_iff.mp hnear with
    ⟨delta, hdelta, hdeltaSub⟩
  let m : ℝ := min delta
    (min (H.epsilon / 2) (min (H.initialRadius : ℝ) Tmax))
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hdelta
      (lt_min (half_pos H.epsilon_pos)
        (lt_min hinitialReal hTmax))
  let t : ℝ := m / 2
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have htm : t < m := by
    dsimp only [t]
    linarith
  have htdelta : t < delta :=
    htm.trans_le (by dsimp only [m]; exact min_le_left _ _)
  have htepsilonHalf : t < H.epsilon / 2 :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_left _ _))
  have htepsilon : t < H.epsilon := by
    linarith [H.epsilon_pos]
  have htinitial : t < (H.initialRadius : ℝ) :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_of_right_le (min_le_left _ _)))
  have htTmax : t < Tmax :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_of_right_le (min_le_right _ _)))
  have htUpper : t < min Tmax (H.epsilon / 2) :=
    lt_min htTmax htepsilonHalf
  have hinitialTube : (H.initialRadius : ℝ) ≤ (H.tubeRadius : ℝ) := by
    exact_mod_cast H.initialRadius_lt_tubeRadius.le
  have httube : t ≤ (H.tubeRadius : ℝ) :=
    htinitial.le.trans hinitialTube
  have htBig : t ∈ Icc (-H.epsilon) H.epsilon :=
    ⟨by linarith [ht], htepsilon.le⟩
  have htMetric : t ∈ ball (0 : ℝ) delta := by
    rw [mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htdelta
  have hendpointBall : H.selector p₀ t ∈
      ball p₀ (H.initialRadius : ℝ) :=
    hdeltaSub htMetric
  have htime : ∀ (p : ℝ × E),
      p ∈ closedBall p₀ (H.initialRadius : ℝ) →
      ∀ s ∈ Icc (-H.epsilon) H.epsilon,
        (H.selector p s).1 = p.1 + s := by
    intro p hp s hs
    apply inverseGaugePointFlow_time_eq_symmetric
      (fun tau x ↦ -V tau x) (H.selector_data p hp).1
      H.epsilon_pos.le (fun q hq ↦ ?_) s hs
    simpa only [p₀, inverseGaugePointExtendedField, neg_neg] using
      (H.selector_data p hp).2.1 q hq
  let Phi : ℝ → E → E := fun s x ↦ (H.selector (0, x) s).2
  let y₁ : E := Phi t z₀
  let Psi : ℝ → E → E :=
    fun s y ↦ (H.selector (t, y) (s - t)).2
  have hendpointState : (t, y₁) = H.selector p₀ t := by
    apply Prod.ext
    · simpa only [p₀, zero_add] using (htime p₀ hp₀ t htBig).symm
    · rfl
  have hrestartBall : (t, y₁) ∈
      ball p₀ (H.initialRadius : ℝ) := by
    rw [hendpointState]
    exact hendpointBall
  have hAlphaForwardContinuousAt :
      ContinuousAt (Function.uncurry H.selector) ((0, z₀), t) := by
    have hp₀Nhds : closedBall p₀ (H.initialRadius : ℝ) ∈ nhds p₀ :=
      closedBall_mem_nhds p₀ hinitialReal
    have htNhds : Icc (-H.epsilon) H.epsilon ∈ nhds t :=
      Icc_mem_nhds (by linarith [ht]) htepsilon
    have hprod : closedBall p₀ (H.initialRadius : ℝ) ×ˢ
        Icc (-H.epsilon) H.epsilon ∈ nhds (p₀, t) :=
      prod_mem_nhds hp₀Nhds htNhds
    simpa only [p₀] using H.selector_continuousOn.continuousAt hprod
  have hAlphaBackwardContinuousAt :
      ContinuousAt (Function.uncurry H.selector) ((t, y₁), -t) := by
    have hrestartNhds : closedBall p₀ (H.initialRadius : ℝ) ∈
        nhds (t, y₁) :=
      closedBall_mem_nhds_of_mem hrestartBall
    have hnegTimeNhds : Icc (-H.epsilon) H.epsilon ∈ nhds (-t) :=
      Icc_mem_nhds (by linarith) (by linarith)
    exact H.selector_continuousOn.continuousAt
      (prod_mem_nhds hrestartNhds hnegTimeNhds)
  have hsource : ∀ᶠ x in nhds z₀,
      (0, x) ∈ closedBall p₀ (H.initialRadius : ℝ) := by
    have hpair : ContinuousAt (fun x : E ↦ ((0 : ℝ), x)) z₀ :=
      continuousAt_const.prodMk continuousAt_id
    apply hpair
    have hopen : ball p₀ (H.initialRadius : ℝ) ∈ nhds p₀ :=
      isOpen_ball.mem_nhds (mem_ball_self hinitialReal)
    exact mem_of_superset hopen ball_subset_closedBall
  have htarget : ∀ᶠ y in nhds y₁,
      (t, y) ∈ closedBall p₀ (H.initialRadius : ℝ) := by
    have hpair : ContinuousAt (fun y : E ↦ (t, y)) y₁ :=
      continuousAt_const.prodMk continuousAt_id
    apply hpair
    have hopen : ball p₀ (H.initialRadius : ℝ) ∈ nhds (t, y₁) :=
      isOpen_ball.mem_nhds hrestartBall
    exact mem_of_superset hopen ball_subset_closedBall
  have hspatialMem : ∀ {p : ℝ × E} {s : ℝ},
      H.selector p s ∈ closedBall p₀ (H.tubeRadius : ℝ) →
        (H.selector p s).2 ∈ closedBall z₀ (H.tubeRadius : ℝ) := by
    intro p s hs
    rw [mem_closedBall] at hs ⊢
    calc
      dist (H.selector p s).2 z₀ ≤
          max (dist (H.selector p s).1 (0 : ℝ))
            (dist (H.selector p s).2 z₀) := le_max_right _ _
      _ = dist (H.selector p s) p₀ := by
        simpa only [p₀, Prod.dist_eq]
      _ ≤ (H.tubeRadius : ℝ) := hs
  have hpairMem : ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) t →
      ∀ {x : E}, x ∈ closedBall z₀ (H.tubeRadius : ℝ) →
        (s, x) ∈ closedBall p₀ (H.tubeRadius : ℝ) := by
    intro s hs x hx
    rw [mem_closedBall] at hx ⊢
    change max (dist s (0 : ℝ)) (dist x z₀) ≤ (H.tubeRadius : ℝ)
    rw [max_le_iff]
    exact ⟨by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs.1] using
        hs.2.trans httube, hx⟩
  have hLip : ∀ s ∈ Icc (0 : ℝ) t,
      LipschitzOnWith H.lipschitzConstant (V s)
        (closedBall z₀ (H.tubeRadius : ℝ)) := by
    intro s hs
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hxy := H.field_lipschitzOn.dist_le_mul
      (s, x) (hpairMem hs hx) (s, y) (hpairMem hs hy)
    calc
      dist (V s x) (V s y) ≤
          dist ((1, V s x) : ℝ × E) (1, V s y) := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      _ ≤ (H.lipschitzConstant : ℝ) * dist (s, x) (s, y) := hxy
      _ = (H.lipschitzConstant : ℝ) * dist x y := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  have hforward : ∀ᶠ x in nhds z₀,
      Phi 0 x = x ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Phi tau x) (V s (Phi s x)) s ∧
            Phi s x ∈ closedBall z₀ (H.tubeRadius : ℝ) := by
    filter_upwards [hsource] with x hx
    have hdata := H.selector_data (0, x) hx
    constructor
    · simpa only [Phi] using congrArg Prod.snd hdata.1
    · intro s hs
      have hsOpen : s ∈ Ioo (-H.epsilon) H.epsilon :=
        ⟨by linarith [hs.1], hs.2.trans_lt htepsilon⟩
      have hsClosed : s ∈ Icc (-H.epsilon) H.epsilon :=
        Ioo_subset_Icc_self hsOpen
      have hfull := (hdata.2.1 s hsClosed).hasDerivAt
        (Icc_mem_nhds hsOpen.1 hsOpen.2)
      have hsnd := hfull.hasFDerivAt.snd.hasDerivAt
      have htimeS := htime (0, x) hx s hsClosed
      constructor
      · simpa [Phi, htimeS] using hsnd
      · exact hspatialMem (hdata.2.2 s hsClosed)
  have hbackward : ∀ᶠ y in nhds y₁,
      Psi t y = y ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Psi tau y) (V s (Psi s y)) s ∧
            Psi s y ∈ closedBall z₀ (H.tubeRadius : ℝ) := by
    filter_upwards [htarget] with y hy
    have hdata := H.selector_data (t, y) hy
    constructor
    · simpa only [Psi, sub_self] using congrArg Prod.snd hdata.1
    · intro s hs
      have hshift : HasDerivAt (fun tau : ℝ ↦ tau - t) 1 s :=
        (hasDerivAt_id s).sub_const t
      have hsOpen : s - t ∈ Ioo (-H.epsilon) H.epsilon := by
        constructor <;> linarith [hs.1, hs.2, htepsilon]
      have hsClosed : s - t ∈ Icc (-H.epsilon) H.epsilon :=
        Ioo_subset_Icc_self hsOpen
      have houter := (hdata.2.1 (s - t) hsClosed).hasDerivAt
        (Icc_mem_nhds hsOpen.1 hsOpen.2)
      have hsnd := houter.hasFDerivAt.snd.hasDerivAt
      have hcomp := hsnd.scomp s hshift
      have htimeS := htime (t, y) hy (s - t) hsClosed
      have htimeS' : (H.selector (t, y) (s - t)).1 = s := by
        linarith [htimeS]
      constructor
      · simpa [Psi, htimeS', Function.comp_def] using hcomp
      · exact hspatialMem (hdata.2.2 (s - t) hsClosed)
  refine ⟨t, ⟨ht, htUpper⟩, Phi, Psi, y₁, ?_⟩
  refine ⟨
    { selector := H.selector
      forward_representation := rfl
      backward_representation := rfl
      forward_selector_continuousAt := hAlphaForwardContinuousAt
      backward_selector_continuousAt := hAlphaBackwardContinuousAt
      core :=
        { K := H.lipschitzConstant
          controlledSet := closedBall z₀ (H.tubeRadius : ℝ)
          endpoint_eq := ?_
          lipschitzOn := hLip
          forward_flow := hforward
          backward_flow := hbackward } }, rfl, by simpa only [p₀] using hrestartBall⟩
  rfl

/-- Compatibility form which forgets the explicit selector equality. -/
theorem LocalRegularControlledContinuousAutonomousSelector.exists_twoRestartPointFlowCoreWithSelector
    (V : ℝ → E → E) (z₀ : E)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (fun q : ℝ × E ↦ (1, V q.1 q.2)) (0, z₀))
    (Tmax : ℝ) (hTmax : 0 < Tmax) :
    ∃ t ∈ Ioo (0 : ℝ) (min Tmax (H.epsilon / 2)),
      ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
        Nonempty (TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁) := by
  rcases H.exists_twoRestartPointFlowCoreWithSelector_eq
      V z₀ Tmax hTmax with ⟨t, ht, Phi, Psi, y₁, C, _, _⟩
  exact ⟨t, ht, Phi, Psi, y₁, ⟨C⟩⟩

end SuppliedRegularSelectorCore

end Poincare
