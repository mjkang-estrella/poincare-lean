import Poincare.Global.DeTurckBUCTwoRestartPointFlowCore

/-!
# Two-restart core from a nonautonomous Picard--Lindelof tube

The projected reconstructed metric path need not be differentiable at time
zero.  Ordinary nonautonomous Picard--Lindelof theory does not require that
derivative: continuity in time and a uniform spatial Lipschitz bound suffice.

This module extracts the strongest conclusion currently justified by those
inputs.  A single symmetric Picard--Lindelof tube produces a forward selector
based at zero and a separately selected restart family based at a small
positive time.  Both families solve the same ODE in the same uniqueness
region, hence form a `TwoRestartPointFlowCore`.

No smooth-dependence conclusion is asserted.  Mathlib's current ODE API gives
continuous/Lipschitz dependence on the initial point, but not the third-order
parameter dependence required by `TwoRestartPointFlowPackage`.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped NNReal Topology

namespace Poincare

section NonautonomousCore

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A symmetric nonautonomous Picard--Lindelof tube yields a genuine
two-restart point-flow core at an arbitrarily short positive time.

Unlike the autonomous-time augmentation constructor, this theorem assumes no
time derivative of `V` at zero.  The restart selector is obtained by shrinking
the same quantitative tube and changing its initial time to the selected
positive endpoint. -/
theorem IsPicardLindelof.exists_twoRestartPointFlowCore_nonautonomous
    {V : ℝ → E → E} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {z₀ : E} {a r L K : ℝ≥0} (hr : 0 < r)
    (H : IsPicardLindelof V
      (tmin := -epsilon) (tmax := epsilon)
      ⟨0, ⟨neg_nonpos.mpr hepsilon.le, hepsilon.le⟩⟩
      z₀ a r L K)
    (Tmax : ℝ) (hTmax : 0 < Tmax) :
    ∃ t ∈ Ioo (0 : ℝ) Tmax,
      ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
        Nonempty (TwoRestartPointFlowCore V Phi Psi t z₀ y₁) := by
  have hrReal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hzero : (0 : ℝ) ∈ Icc (-epsilon) epsilon :=
    ⟨by linarith, hepsilon.le⟩
  have hz₀ : z₀ ∈ closedBall z₀ (r : ℝ) :=
    mem_closedBall_self hrReal.le
  rcases H.exists_controlled_continuous_selector with
    ⟨alpha, halpha, _hAlphaContinuous⟩
  have hbaseAt : HasDerivAt (alpha z₀)
      (V 0 (alpha z₀ 0)) 0 :=
    ((halpha z₀ hz₀).2.1 0 hzero).hasDerivAt
      (Icc_mem_nhds (by linarith) hepsilon)
  have hnear : (alpha z₀) ⁻¹' ball z₀ (r : ℝ) ∈ nhds (0 : ℝ) := by
    apply hbaseAt.continuousAt.preimage_mem_nhds
    rw [(halpha z₀ hz₀).1]
    exact isOpen_ball.mem_nhds (mem_ball_self hrReal)
  rcases Metric.mem_nhds_iff.mp hnear with
    ⟨delta, hdelta, hdeltaSub⟩
  let m : ℝ := min delta (min (epsilon / 4) (min (r : ℝ) Tmax))
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hdelta
      (lt_min (by positivity) (lt_min hrReal hTmax))
  let t : ℝ := m / 2
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have htm : t < m := by
    dsimp only [t]
    linarith
  have htdelta : t < delta :=
    htm.trans_le (by dsimp only [m]; exact min_le_left _ _)
  have htepsilonQuarter : t < epsilon / 4 :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_left _ _))
  have htepsilonHalf : t < epsilon / 2 := by
    linarith [hepsilon]
  have htepsilon : t < epsilon := by
    linarith [hepsilon]
  have htTmax : t < Tmax :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_of_right_le (min_le_right _ _)))
  have htMetric : t ∈ ball (0 : ℝ) delta := by
    rw [mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htdelta
  let Phi : ℝ → E → E := fun s x ↦ alpha x s
  let y₁ : E := Phi t z₀
  have hy₁Ball : y₁ ∈ ball z₀ (r : ℝ) := by
    simpa only [Phi, y₁] using hdeltaSub htMetric

  let restartTime : Icc (-(epsilon / 2)) (epsilon / 2) :=
    ⟨t, by constructor <;> linarith⟩
  have Hrestart : IsPicardLindelof V restartTime z₀ a r L K := by
    apply H.shrink restartTime
    · linarith [hepsilon]
    · linarith [hepsilon]
    · exact le_rfl
    · have hmax : max (epsilon / 2 - t) (t - (-(epsilon / 2))) ≤
          epsilon := by
        rw [max_le_iff]
        constructor <;> linarith [hepsilon, htepsilonHalf]
      calc
        (L : ℝ) * max (epsilon / 2 - restartTime)
            (restartTime - (-(epsilon / 2))) ≤
            (L : ℝ) * epsilon := by
          simpa only [restartTime] using
            mul_le_mul_of_nonneg_left hmax L.2
        _ ≤ (a : ℝ) - (r : ℝ) := by
          simpa only [sub_zero, zero_sub, neg_neg, max_self] using
            H.mul_max_le
  rcases Hrestart.exists_controlled_continuous_selector with
    ⟨beta, hbeta, _hBetaContinuous⟩
  let Psi : ℝ → E → E := fun s y ↦ beta y s

  have hsource : ∀ᶠ x in nhds z₀,
      x ∈ closedBall z₀ (r : ℝ) :=
    closedBall_mem_nhds z₀ hrReal
  have htarget : ∀ᶠ y in nhds y₁,
      y ∈ closedBall z₀ (r : ℝ) := by
    exact mem_of_superset
      (isOpen_ball.mem_nhds hy₁Ball) ball_subset_closedBall
  have hLip : ∀ s ∈ Icc (0 : ℝ) t,
      LipschitzOnWith K (V s) (closedBall z₀ (a : ℝ)) := by
    intro s hs
    exact H.lipschitzOnWith s
      ⟨(neg_nonpos.mpr hepsilon.le).trans hs.1,
        hs.2.trans htepsilon.le⟩
  have hforward : ∀ᶠ x in nhds z₀,
      Phi 0 x = x ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Phi tau x) (V s (Phi s x)) s ∧
            Phi s x ∈ closedBall z₀ (a : ℝ) := by
    filter_upwards [hsource] with x hx
    have hdata := halpha x hx
    constructor
    · simpa only [Phi] using hdata.1
    · intro s hs
      have hsOpen : s ∈ Ioo (-epsilon) epsilon :=
        ⟨by linarith [hepsilon, hs.1], hs.2.trans_lt htepsilon⟩
      have hsClosed : s ∈ Icc (-epsilon) epsilon :=
        Ioo_subset_Icc_self hsOpen
      constructor
      · simpa only [Phi] using
          (hdata.2.1 s hsClosed).hasDerivAt
            (Icc_mem_nhds hsOpen.1 hsOpen.2)
      · simpa only [Phi] using hdata.2.2 s hsClosed
  have hbackward : ∀ᶠ y in nhds y₁,
      Psi t y = y ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Psi tau y) (V s (Psi s y)) s ∧
            Psi s y ∈ closedBall z₀ (a : ℝ) := by
    filter_upwards [htarget] with y hy
    have hdata := hbeta y hy
    constructor
    · simpa only [Psi, restartTime] using hdata.1
    · intro s hs
      have hsOpen : s ∈ Ioo (-(epsilon / 2)) (epsilon / 2) :=
        ⟨by linarith [hepsilon, hs.1], hs.2.trans_lt htepsilonHalf⟩
      have hsClosed : s ∈ Icc (-(epsilon / 2)) (epsilon / 2) :=
        Ioo_subset_Icc_self hsOpen
      constructor
      · simpa only [Psi] using
          (hdata.2.1 s hsClosed).hasDerivAt
            (Icc_mem_nhds hsOpen.1 hsOpen.2)
      · simpa only [Psi] using hdata.2.2 s hsClosed
  exact ⟨t, ⟨ht, htTmax⟩, Phi, Psi, y₁, ⟨
    { K := K
      controlledSet := closedBall z₀ (a : ℝ)
      endpoint_eq := rfl
      lipschitzOn := hLip
      forward_flow := hforward
      backward_flow := hbackward }⟩⟩

/-- The exact smooth-dependence boundary after the nonautonomous construction.

The Picard--Lindelof tube constructs all ODE, restart, and uniqueness data.
Upgrading its two selected families to the downstream package requires only
the displayed endpoint regularities.  They are left as implications rather
than claimed consequences because neither Mathlib nor the current repository
proves third-order dependence on the initial point from one-sided field data. -/
theorem IsPicardLindelof.exists_twoRestartPointFlowCore_nonautonomous_with_package_boundary
    {V : ℝ → E → E} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {z₀ : E} {a r L K : ℝ≥0} (hr : 0 < r)
    (H : IsPicardLindelof V
      (tmin := -epsilon) (tmax := epsilon)
      ⟨0, ⟨neg_nonpos.mpr hepsilon.le, hepsilon.le⟩⟩
      z₀ a r L K)
    (Tmax : ℝ) (hTmax : 0 < Tmax) :
    ∃ t ∈ Ioo (0 : ℝ) Tmax,
      ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
        ∃ C : TwoRestartPointFlowCore V Phi Psi t z₀ y₁,
          ContDiffAt ℝ 3 (Function.uncurry Phi) (t, z₀) →
          ContDiffAt ℝ 1 (Function.uncurry Psi) (0, y₁) →
            Nonempty (TwoRestartPointFlowPackage V Phi Psi t z₀ y₁) := by
  rcases IsPicardLindelof.exists_twoRestartPointFlowCore_nonautonomous
      hepsilon hr H Tmax hTmax with
    ⟨t, ht, Phi, Psi, y₁, ⟨C⟩⟩
  exact ⟨t, ht, Phi, Psi, y₁, C,
    fun hPhi hPsi ↦ ⟨C.toPointFlowPackage hPhi hPsi⟩⟩

end NonautonomousCore

end Poincare
