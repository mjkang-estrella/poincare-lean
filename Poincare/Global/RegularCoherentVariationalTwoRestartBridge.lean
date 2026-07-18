import Poincare.Global.DeTurckBUCRegularSelectorTwoRestartPointFlowCore
import Poincare.Global.RegularVariationalSelectorJointC1
import Poincare.Global.RegularVariationalSelectorJointC3

/-!
# Backward restart data from a synchronized regular coherent tower

The supplied-selector restart constructor and the joint `C¹` theorem are
combined here.  A regular coherent tower for the autonomous time--point
extension first cuts a two-restart core from its exact base selector.  The
restart endpoint remains in that selector's initial ball, so the tower's
first variational level supplies local joint first-order data at the negative
relative restart time.  This removes the backward smooth-dependence premise
from the core-to-package upgrade.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section RegularTowerBackwardData

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [FiniteDimensional ℝ X]

namespace RegularCoherentThreeLevelVariationalSelectorTower

variable {F : X → X} {x q : X} {s : ℝ}

/-- The first level of a regular coherent tower gives joint first-order data
for its base selector at every nearby state and protected interior time. -/
def baseUncurriedSelector_firstOrderDataAt
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    (hq : q ∈ ball x (T.base.initialRadius : ℝ))
    (hs : s ∈ Ioo (-(T.base.epsilon / 2)) (T.base.epsilon / 2)) :
    LocalFirstOrderVariationalData
      (Function.uncurry T.base.selector) (q, s) := by
  have hqFirst : q ∈ ball x (T.first.initialRadius : ℝ) := by
    simpa only [base] using hq
  have hsFirst : s ∈ Ioo (-(T.first.epsilon / 2))
      (T.first.epsilon / 2) := by
    simpa only [base] using hs
  simpa only [base] using
    T.first.projectedUncurriedSelector_firstOrderDataAt hqFirst hsFirst

end RegularCoherentThreeLevelVariationalSelectorTower

end RegularTowerBackwardData

section TwoRestartBackwardBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Transport the tower's backward first-order data to a two-restart core
whose retained selector is that exact tower selector. -/
def TwoRestartPointFlowCoreWithSelector.backwardFirstOrderData_of_regularCoherentTower
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    {G : (ℝ × E) → (ℝ × E)}
    (C : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁)
    (T : RegularCoherentThreeLevelVariationalSelectorTower G (0, z₀))
    (hselector : C.selector = T.base.selector)
    (hrestart : (t, y₁) ∈
      ball (0, z₀) (T.base.initialRadius : ℝ))
    (hneg : -t ∈ Ioo (-(T.base.epsilon / 2))
      (T.base.epsilon / 2)) :
    LocalFirstOrderVariationalData
      (Function.uncurry C.selector) ((t, y₁), -t) := by
  rw [hselector]
  exact T.baseUncurriedSelector_firstOrderDataAt hrestart hneg

/-- Once forward third-order joint data are supplied, a synchronized regular
coherent tower discharges the backward premise of the core-to-package
upgrade automatically. -/
def TwoRestartPointFlowCoreWithSelector.toPointFlowPackage_of_forwardTower_and_regularCoherentTower
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    {G : (ℝ × E) → (ℝ × E)}
    (C : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁)
    (T : RegularCoherentThreeLevelVariationalSelectorTower G (0, z₀))
    (hselector : C.selector = T.base.selector)
    (hrestart : (t, y₁) ∈
      ball (0, z₀) (T.base.initialRadius : ℝ))
    (hneg : -t ∈ Ioo (-(T.base.epsilon / 2))
      (T.base.epsilon / 2))
    (hForward : LocalThirdOrderVariationalTower
      (Function.uncurry C.selector) ((0, z₀), t)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ :=
  C.toPointFlowPackage_of_variationalTowers hForward
    (C.backwardFirstOrderData_of_regularCoherentTower
      T hselector hrestart hneg)

/-- A synchronized regular coherent tower discharges both smooth-dependence
premises once the autonomous field is locally `C²` at the selected forward
endpoint. -/
def TwoRestartPointFlowCoreWithSelector.toPointFlowPackage_of_regularCoherentTower
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    {G : (ℝ × E) → (ℝ × E)}
    (C : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁)
    (T : RegularCoherentThreeLevelVariationalSelectorTower G (0, z₀))
    (hselector : C.selector = T.base.selector)
    (hrestart : (t, y₁) ∈
      ball (0, z₀) (T.base.initialRadius : ℝ))
    (hpos : t ∈ Ioo (-(T.base.epsilon / 2))
      (T.base.epsilon / 2))
    (hneg : -t ∈ Ioo (-(T.base.epsilon / 2))
      (T.base.epsilon / 2))
    (hfield : ContDiffAt ℝ 2 G (T.base.selector (0, z₀) t)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ := by
  have hForwardT := T.baseUncurriedSelector_thirdOrderTower hpos hfield
  have hForward : LocalThirdOrderVariationalTower
      (Function.uncurry C.selector) ((0, z₀), t) := by
    rw [hselector]
    exact hForwardT
  exact C.toPointFlowPackage_of_forwardTower_and_regularCoherentTower
    T hselector hrestart hneg hForward

variable [CompleteSpace E]

/-- A local `C⁴` autonomous time--point field produces a synchronized
two-restart core together with complete backward joint first-order data for
the core's retained selector. -/
theorem exists_twoRestartPointFlowCoreWithSelector_and_backwardFirstOrderData_of_contDiffAt_four
    (V : ℝ → E → E) (z₀ : E) (Tmax : ℝ) (hTmax : 0 < Tmax)
    (hG : ContDiffAt ℝ 4
      (fun q : ℝ × E ↦ ((1 : ℝ), V q.1 q.2)) (0, z₀)) :
    ∃ T : RegularCoherentThreeLevelVariationalSelectorTower
        (fun q : ℝ × E ↦ ((1 : ℝ), V q.1 q.2)) (0, z₀),
      ∃ t ∈ Ioo (0 : ℝ) (min Tmax (T.base.epsilon / 2)),
        ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
          ∃ C : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁,
            ∃ B : LocalFirstOrderVariationalData
                (Function.uncurry C.selector) ((t, y₁), -t),
              C.selector = T.base.selector := by
  let G : (ℝ × E) → (ℝ × E) :=
    fun q ↦ (1, V q.1 q.2)
  rcases exists_regularCoherentThreeLevelVariationalSelectorTower_of_contDiffAt_four
      G (0, z₀) (by simpa only [G] using hG) with ⟨T⟩
  rcases T.base.exists_twoRestartPointFlowCoreWithSelector_eq
      V z₀ Tmax hTmax with
    ⟨t, ht, Phi, Psi, y₁, C, hselector, hrestart⟩
  have htHalf : t < T.base.epsilon / 2 :=
    ht.2.trans_le (min_le_right _ _)
  have hneg : -t ∈ Ioo (-(T.base.epsilon / 2))
      (T.base.epsilon / 2) := by
    constructor
    · linarith
    · linarith [ht.1, T.base.epsilon_pos]
  have hbackward :=
    C.backwardFirstOrderData_of_regularCoherentTower
      T hselector hrestart hneg
  exact ⟨T, t, ht, Phi, Psi, y₁, C, hbackward, hselector⟩

end TwoRestartBackwardBridge

end Poincare
