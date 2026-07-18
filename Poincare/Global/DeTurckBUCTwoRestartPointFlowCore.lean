import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowTwoRestartAssembly
import Poincare.Global.DeTurckFlowSymmetricPhysicalTime
import Poincare.Global.PicardLindelofControlledContinuousSelector

/-!
# A concrete two-restart point-flow core from Picard--Lindelof

The Picard--Lindelof family for the autonomous time--point augmentation is
simultaneously defined for every nearby extended initial state.  Consequently
one and the same selected family supplies both a forward flow based at time
zero and a backward restart based at a sufficiently small positive endpoint.

This file extracts that fact, including a common invariant ball and a uniform
spatial Lipschitz constant.  The resulting core contains every field of
`TwoRestartPointFlowPackage` except smooth dependence on the initial point.
Thus the remaining point-flow boundary is stated exactly as forward joint
`C³` and backward joint `C¹` regularity.
-/

noncomputable section

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section AbstractTwoRestartCore

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ODE, restart, and uniqueness-region part of a two-restart point flow.

Unlike `TwoRestartPointFlowPackage`, this structure deliberately contains no
smooth-dependence assumption. -/
structure TwoRestartPointFlowCore
    (V : ℝ → E → E) (Phi Psi : ℝ → E → E)
    (t : ℝ) (z₀ y₁ : E) where
  K : ℝ≥0
  controlledSet : Set E
  endpoint_eq : Phi t z₀ = y₁
  lipschitzOn : ∀ s ∈ Icc (0 : ℝ) t,
    LipschitzOnWith K (V s) controlledSet
  forward_flow : ∀ᶠ q in nhds z₀,
    Phi 0 q = q ∧
      ∀ s ∈ Icc (0 : ℝ) t,
        HasDerivAt (fun tau ↦ Phi tau q) (V s (Phi s q)) s ∧
          Phi s q ∈ controlledSet
  backward_flow : ∀ᶠ q in nhds y₁,
    Psi t q = q ∧
      ∀ s ∈ Icc (0 : ℝ) t,
        HasDerivAt (fun tau ↦ Psi tau q) (V s (Psi s q)) s ∧
          Psi s q ∈ controlledSet

/-- A two-restart core together with the actual autonomous
Picard--Lindelof selector from which its forward and backward families are
cut out.

Keeping this selector prevents the existence theorem from erasing precisely
the object on which smooth dependence must be proved. -/
structure TwoRestartPointFlowCoreWithSelector
    (V : ℝ → E → E) (Phi Psi : ℝ → E → E)
    (t : ℝ) (z₀ y₁ : E) where
  selector : (ℝ × E) → ℝ → (ℝ × E)
  forward_representation :
    Phi = fun s x ↦ (selector (0, x) s).2
  backward_representation :
    Psi = fun s y ↦ (selector (t, y) (s - t)).2
  forward_selector_continuousAt :
    ContinuousAt (Function.uncurry selector) ((0, z₀), t)
  backward_selector_continuousAt :
    ContinuousAt (Function.uncurry selector) ((t, y₁), -t)
  core : TwoRestartPointFlowCore V Phi Psi t z₀ y₁

namespace TwoRestartPointFlowCore

variable {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
variable {t : ℝ} {z₀ y₁ : E}

/-- Adding precisely the two missing smooth-dependence facts upgrades the
concrete ODE core to the package consumed by the Ricci-flow assembly. -/
def toPointFlowPackage
    (H : TwoRestartPointFlowCore V Phi Psi t z₀ y₁)
    (hPhiC3 : ContDiffAt ℝ 3 (Function.uncurry Phi) (t, z₀))
    (hPsiC1 : ContDiffAt ℝ 1 (Function.uncurry Psi) (0, y₁)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ where
  K := H.K
  controlledSet := H.controlledSet
  endpoint_eq := H.endpoint_eq
  forward_jointC3 := hPhiC3
  backward_jointC1 := hPsiC1
  lipschitzOn := H.lipschitzOn
  forward_flow := H.forward_flow
  backward_flow := H.backward_flow

end TwoRestartPointFlowCore

variable [CompleteSpace E]

/-- A local `C¹` time-dependent vector field has a genuine two-restart flow
core, retaining its selected autonomous Picard--Lindelof family, at some
arbitrarily short positive time.

The construction uses the single Picard--Lindelof family of the autonomous
extended field `(time, point) ↦ (1, V time point)`.  The backward family is
not selected independently: it is that same family evaluated at extended
initial states `(t,y)` and relative time `s-t`.

The upper bound `Tmax` lets later applications choose the endpoint inside an
independently supplied analytic lifespan. -/
theorem exists_twoRestartPointFlowCoreWithSelector_of_contDiffAt_one
    (V : ℝ → E → E) (z₀ : E) (Tmax : ℝ) (hTmax : 0 < Tmax)
    (hV : ContDiffAt ℝ 1 (Function.uncurry V) (0, z₀)) :
    ∃ t ∈ Ioo (0 : ℝ) Tmax, ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
      Nonempty (TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁) := by
  let p₀ : ℝ × E := (0, z₀)
  let F : ℝ × E → ℝ × E := fun q ↦ (1, V q.1 q.2)
  have hF : ContDiffAt ℝ 1 F p₀ := by
    simpa only [F, p₀, Function.uncurry] using
      contDiffAt_const.prodMk hV
  rcases IsPicardLindelof.of_contDiffAt_one hF with
    ⟨epsilon, hepsilon, a, r, L, K, hr, hplAll⟩
  have hrReal : 0 < (r : ℝ) := by exact_mod_cast hr
  let hpl := hplAll (0 : ℝ)
  rcases hpl.exists_controlled_continuous_selector with
    ⟨alpha, halpha, hAlphaContinuousOn⟩
  have hzero : (0 : ℝ) ∈ Icc (-epsilon) epsilon :=
    ⟨by linarith, hepsilon.le⟩
  have hzeroShift : (0 : ℝ) ∈ Icc (0 - epsilon) (0 + epsilon) := by
    simpa only [zero_sub, zero_add] using hzero
  have hp₀ : p₀ ∈ closedBall p₀ (r : ℝ) :=
    mem_closedBall_self hr.le
  have hmul : (L : ℝ) * epsilon ≤ (a : ℝ) - (r : ℝ) := by
    simpa [hpl] using hpl.mul_max_le
  have hra : (r : ℝ) ≤ (a : ℝ) := by
    have hnonneg : 0 ≤ (L : ℝ) * epsilon :=
      mul_nonneg NNReal.zero_le_coe hepsilon.le
    exact sub_nonneg.mp (hnonneg.trans hmul)
  have htime : ∀ (p : ℝ × E), p ∈ closedBall p₀ (r : ℝ) →
      ∀ s ∈ Icc (-epsilon) epsilon, (alpha p s).1 = p.1 + s := by
    intro p hp s hs
    apply inverseGaugePointFlow_time_eq_symmetric
      (fun tau x ↦ -V tau x) (halpha p hp).1 hepsilon.le
      (fun q hq ↦ ?_) s hs
    simpa only [zero_sub, zero_add, F, inverseGaugePointExtendedField,
      neg_neg] using
      (halpha p hp).2.1 q
        (by simpa only [zero_sub, zero_add] using hq)
  have hbaseAt : HasDerivAt (alpha p₀) (F (alpha p₀ 0)) 0 :=
    ((halpha p₀ hp₀).2.1 0 hzeroShift).hasDerivAt
      (Icc_mem_nhds (by linarith) (by linarith))
  have hnear : (fun s ↦ alpha p₀ s) ⁻¹'
      ball p₀ (r : ℝ) ∈ nhds (0 : ℝ) := by
    apply hbaseAt.continuousAt.preimage_mem_nhds
    rw [(halpha p₀ hp₀).1]
    exact isOpen_ball.mem_nhds (mem_ball_self hr)
  rcases Metric.mem_nhds_iff.mp hnear with ⟨delta, hdelta, hdeltaSub⟩
  let m : ℝ := min delta (min epsilon (min (r : ℝ) Tmax))
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hdelta (lt_min hepsilon (lt_min hrReal hTmax))
  let t : ℝ := m / 2
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have htm : t < m := by
    dsimp only [t]
    linarith
  have htdelta : t < delta :=
    htm.trans_le (by dsimp only [m]; exact min_le_left _ _)
  have htepsilon : t < epsilon :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_left _ _))
  have htr : t < (r : ℝ) :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_of_right_le (min_le_left _ _)))
  have htTmax : t < Tmax :=
    htm.trans_le (by
      dsimp only [m]
      exact min_le_of_right_le (min_le_of_right_le (min_le_right _ _)))
  have hta : t ≤ (a : ℝ) := htr.le.trans hra
  have htBig : t ∈ Icc (-epsilon) epsilon :=
    ⟨by linarith, htepsilon.le⟩
  have htMetric : t ∈ ball (0 : ℝ) delta := by
    rw [mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htdelta
  have hendpointBall : alpha p₀ t ∈ ball p₀ (r : ℝ) :=
    hdeltaSub htMetric
  let Phi : ℝ → E → E := fun s x ↦ (alpha (0, x) s).2
  let y₁ : E := Phi t z₀
  let Psi : ℝ → E → E := fun s y ↦ (alpha (t, y) (s - t)).2
  have hendpointState : (t, y₁) = alpha p₀ t := by
    apply Prod.ext
    · simpa only [p₀, zero_add] using (htime p₀ hp₀ t htBig).symm
    · rfl
  have hrestartBall : (t, y₁) ∈ ball p₀ (r : ℝ) := by
    rw [hendpointState]
    exact hendpointBall
  have hAlphaForwardContinuousAt :
      ContinuousAt (Function.uncurry alpha) ((0, z₀), t) := by
    have hp₀Nhds : closedBall p₀ (r : ℝ) ∈ nhds p₀ :=
      closedBall_mem_nhds p₀ hrReal
    have htNhds : Icc (0 - epsilon) (0 + epsilon) ∈ nhds t :=
      Icc_mem_nhds (by linarith) (by simpa only [zero_add] using htepsilon)
    have hprod : closedBall p₀ (r : ℝ) ×ˢ
        Icc (0 - epsilon) (0 + epsilon) ∈
        nhds (p₀, t) := prod_mem_nhds hp₀Nhds htNhds
    simpa only [p₀] using hAlphaContinuousOn.continuousAt hprod
  have hAlphaBackwardContinuousAt :
      ContinuousAt (Function.uncurry alpha) ((t, y₁), -t) := by
    have hrestartNhds : closedBall p₀ (r : ℝ) ∈ nhds (t, y₁) :=
      closedBall_mem_nhds_of_mem hrestartBall
    have hnegTimeNhds : Icc (0 - epsilon) (0 + epsilon) ∈ nhds (-t) :=
      Icc_mem_nhds (by linarith) (by linarith)
    exact hAlphaContinuousOn.continuousAt
      (prod_mem_nhds hrestartNhds hnegTimeNhds)
  have hsource : ∀ᶠ x in nhds z₀,
      (0, x) ∈ closedBall p₀ (r : ℝ) := by
    have hpair : ContinuousAt (fun x : E ↦ ((0 : ℝ), x)) z₀ :=
      continuousAt_const.prodMk continuousAt_id
    apply hpair
    have hopen : ball p₀ (r : ℝ) ∈ nhds p₀ :=
      isOpen_ball.mem_nhds (mem_ball_self hr)
    exact mem_of_superset hopen ball_subset_closedBall
  have htarget : ∀ᶠ y in nhds y₁,
      (t, y) ∈ closedBall p₀ (r : ℝ) := by
    have hpair : ContinuousAt (fun y : E ↦ (t, y)) y₁ :=
      continuousAt_const.prodMk continuousAt_id
    apply hpair
    have hopen : ball p₀ (r : ℝ) ∈ nhds (t, y₁) :=
      isOpen_ball.mem_nhds hrestartBall
    exact mem_of_superset hopen ball_subset_closedBall
  have hspatialMem : ∀ {p : ℝ × E} {s : ℝ},
      alpha p s ∈ closedBall p₀ (a : ℝ) →
        (alpha p s).2 ∈ closedBall z₀ (a : ℝ) := by
    intro p s hs
    rw [mem_closedBall] at hs ⊢
    calc
      dist (alpha p s).2 z₀ ≤
          max (dist (alpha p s).1 (0 : ℝ))
            (dist (alpha p s).2 z₀) := le_max_right _ _
      _ = dist (alpha p s) p₀ := by
        simpa only [p₀, Prod.dist_eq]
      _ ≤ (a : ℝ) := hs
  have hpairMem : ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) t →
      ∀ {x : E}, x ∈ closedBall z₀ (a : ℝ) →
        (s, x) ∈ closedBall p₀ (a : ℝ) := by
    intro s hs x hx
    rw [mem_closedBall] at hx ⊢
    change max (dist s (0 : ℝ)) (dist x z₀) ≤ (a : ℝ)
    rw [max_le_iff]
    exact ⟨by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs.1] using
        hs.2.trans hta, hx⟩
  have hLip : ∀ s ∈ Icc (0 : ℝ) t,
      LipschitzOnWith K (V s) (closedBall z₀ (a : ℝ)) := by
    intro s hs
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hxy := (hpl.lipschitzOnWith 0 hzeroShift).dist_le_mul
      (s, x) (hpairMem hs hx) (s, y) (hpairMem hs hy)
    calc
      dist (V s x) (V s y) ≤ dist (F (s, x)) (F (s, y)) := by
        change dist (V s x) (V s y) ≤
          dist ((1, V s x) : ℝ × E) (1, V s y)
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      _ ≤ (K : ℝ) * dist (s, x) (s, y) := hxy
      _ = (K : ℝ) * dist x y := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  have hforward : ∀ᶠ x in nhds z₀,
      Phi 0 x = x ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Phi tau x) (V s (Phi s x)) s ∧
            Phi s x ∈ closedBall z₀ (a : ℝ) := by
    filter_upwards [hsource] with x hx
    have hdata := halpha (0, x) hx
    constructor
    · simpa only [Phi] using congrArg Prod.snd hdata.1
    · intro s hs
      have hsOpen : s ∈ Ioo (-epsilon) epsilon :=
        ⟨by linarith [hs.1], hs.2.trans_lt htepsilon⟩
      have hsClosed : s ∈ Icc (-epsilon) epsilon :=
        Ioo_subset_Icc_self hsOpen
      have hsClosedShift : s ∈ Icc (0 - epsilon) (0 + epsilon) := by
        simpa only [zero_sub, zero_add] using hsClosed
      have hfull := (hdata.2.1 s hsClosedShift).hasDerivAt
        (Icc_mem_nhds (by simpa only [zero_sub] using hsOpen.1)
          (by simpa only [zero_add] using hsOpen.2))
      have hsnd := hfull.hasFDerivAt.snd.hasDerivAt
      have htimeS := htime (0, x) hx s hsClosed
      constructor
      · simpa [Phi, F, htimeS] using hsnd
      · exact hspatialMem (hdata.2.2 s hsClosedShift)
  have hbackward : ∀ᶠ y in nhds y₁,
      Psi t y = y ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Psi tau y) (V s (Psi s y)) s ∧
            Psi s y ∈ closedBall z₀ (a : ℝ) := by
    filter_upwards [htarget] with y hy
    have hdata := halpha (t, y) hy
    constructor
    · simpa only [Psi, sub_self] using congrArg Prod.snd hdata.1
    · intro s hs
      have hshift : HasDerivAt (fun tau : ℝ ↦ tau - t) 1 s :=
        (hasDerivAt_id s).sub_const t
      have hsOpen : s - t ∈ Ioo (-epsilon) epsilon := by
        constructor <;> linarith [hs.1, hs.2, htepsilon]
      have hsClosed : s - t ∈ Icc (-epsilon) epsilon :=
        Ioo_subset_Icc_self hsOpen
      have hsClosedShift : s - t ∈ Icc (0 - epsilon) (0 + epsilon) := by
        simpa only [zero_sub, zero_add] using hsClosed
      have houter := (hdata.2.1 (s - t) hsClosedShift).hasDerivAt
        (Icc_mem_nhds (by simpa only [zero_sub] using hsOpen.1)
          (by simpa only [zero_add] using hsOpen.2))
      have hsnd := houter.hasFDerivAt.snd.hasDerivAt
      have hcomp := hsnd.scomp s hshift
      have htimeS := htime (t, y) hy (s - t) hsClosed
      have htimeS' : (alpha (t, y) (s - t)).1 = s := by
        linarith [htimeS]
      constructor
      · simpa [Psi, F, htimeS', Function.comp_def] using hcomp
      · exact hspatialMem (hdata.2.2 (s - t) hsClosedShift)
  refine ⟨t, ⟨ht, htTmax⟩, Phi, Psi, y₁, ?_⟩
  refine ⟨
    { selector := alpha
      forward_representation := rfl
      backward_representation := rfl
      forward_selector_continuousAt := hAlphaForwardContinuousAt
      backward_selector_continuousAt := hAlphaBackwardContinuousAt
      core :=
        { K := K
          controlledSet := closedBall z₀ (a : ℝ)
          endpoint_eq := ?_
          lipschitzOn := hLip
          forward_flow := hforward
          backward_flow := hbackward } }⟩
  rfl

/-- Compatibility form of the concrete two-restart constructor.  It is a
corollary of the selector-retaining theorem, so downstream code using the old
core API is unchanged while smooth-dependence arguments can use the stronger
result above. -/
theorem exists_twoRestartPointFlowCore_of_contDiffAt_one
    (V : ℝ → E → E) (z₀ : E) (Tmax : ℝ) (hTmax : 0 < Tmax)
    (hV : ContDiffAt ℝ 1 (Function.uncurry V) (0, z₀)) :
    ∃ t ∈ Ioo (0 : ℝ) Tmax, ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
      Nonempty (TwoRestartPointFlowCore V Phi Psi t z₀ y₁) := by
  rcases
      exists_twoRestartPointFlowCoreWithSelector_of_contDiffAt_one
        V z₀ Tmax hTmax hV with
    ⟨t, ht, Phi, Psi, y₁, ⟨H⟩⟩
  exact ⟨t, ht, Phi, Psi, y₁, ⟨H.core⟩⟩

end AbstractTwoRestartCore

end Poincare
