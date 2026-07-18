import Poincare.Global.PicardLindelofControlledContinuousSelector
import Poincare.Global.DeTurckPointFlowVariationalFields

/-!
# Controlled selectors for a three-level variational tower

With one spare derivative, an autonomous `C⁴` field and all three of its
iterated variational augmentations are locally `C¹`.  Picard--Lindelof
therefore supplies a controlled jointly continuous selector at every level.
This module packages those four genuine solution families; the remaining
smooth-flow step is to identify their endpoint components successively as
the first, second, and third Frechet derivatives of the base selector.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section OneSelector

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A local autonomous Picard--Lindelof selector retaining both its invariant
tube and joint continuity. -/
structure LocalControlledContinuousAutonomousSelector
    (F : X → X) (x₀ : X) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  tubeRadius : ℝ≥0
  initialRadius : ℝ≥0
  speedBound : ℝ≥0
  lipschitzConstant : ℝ≥0
  initialRadius_pos : 0 < initialRadius
  selector : X → ℝ → X
  field_lipschitzOn :
    LipschitzOnWith lipschitzConstant F
      (closedBall x₀ (tubeRadius : ℝ))
  selector_data : ∀ x ∈ closedBall x₀ (initialRadius : ℝ),
    selector x 0 = x ∧
      (∀ t ∈ Icc (-epsilon) epsilon,
        HasDerivWithinAt (selector x) (F (selector x t))
          (Icc (-epsilon) epsilon) t) ∧
      ∀ t ∈ Icc (-epsilon) epsilon,
        selector x t ∈ closedBall x₀ (tubeRadius : ℝ)
  selector_continuousOn : ContinuousOn (Function.uncurry selector)
    (closedBall x₀ (initialRadius : ℝ) ×ˢ Icc (-epsilon) epsilon)

namespace LocalControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ : X}

/-- The retained selector is continuous at every time strictly inside its
interval, at the central initial state. -/
theorem selector_continuousAt
    (H : LocalControlledContinuousAutonomousSelector F x₀)
    {t : ℝ} (ht : t ∈ Ioo (-H.epsilon) H.epsilon) :
    ContinuousAt (Function.uncurry H.selector) (x₀, t) := by
  have hrReal : 0 < (H.initialRadius : ℝ) := by
    exact_mod_cast H.initialRadius_pos
  have hball : closedBall x₀ (H.initialRadius : ℝ) ∈ nhds x₀ :=
    closedBall_mem_nhds x₀ hrReal
  have htime : Icc (-H.epsilon) H.epsilon ∈ nhds t :=
    Icc_mem_nhds ht.1 ht.2
  exact H.selector_continuousOn.continuousAt
    (prod_mem_nhds hball htime)

end LocalControlledContinuousAutonomousSelector

variable [CompleteSpace X]

/-- Every locally `C¹` autonomous field has a controlled jointly continuous
selector centered at the prescribed state and relative time zero. -/
theorem exists_localControlledContinuousAutonomousSelector_of_contDiffAt_one
    (F : X → X) (x₀ : X) (hF : ContDiffAt ℝ 1 F x₀) :
    Nonempty (LocalControlledContinuousAutonomousSelector F x₀) := by
  rcases IsPicardLindelof.of_contDiffAt_one hF with
    ⟨epsilon, hepsilon, a, r, L, K, hr, hplAll⟩
  let hpl := hplAll (0 : ℝ)
  rcases hpl.exists_controlled_continuous_selector with
    ⟨alpha, halpha, hcontinuous⟩
  refine ⟨
    { epsilon := epsilon
      epsilon_pos := hepsilon
      tubeRadius := a
      initialRadius := r
      speedBound := L
      lipschitzConstant := K
      initialRadius_pos := hr
      selector := alpha
      field_lipschitzOn := ?_
      selector_data := ?_
      selector_continuousOn := ?_ }⟩
  · have hzero : (0 : ℝ) ∈ Icc (0 - epsilon) (0 + epsilon) := by
      constructor <;> linarith
    simpa only using hpl.lipschitzOnWith 0 hzero
  · intro x hx
    simpa only [zero_sub, zero_add] using halpha x hx
  · simpa only [zero_sub, zero_add] using hcontinuous

end OneSelector

section SelectorTower

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

-- Name the nested operator-norm layers explicitly.  Without these names,
-- typeclass search treats the expanded variational-state abbreviations as a
-- possible recursive instance loop at the third level.
local instance selectorBaseEndNormedGroup :
    NormedAddCommGroup (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance selectorBaseEndNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedSpace

local instance selectorFirstStateNormedGroup :
    NormedAddCommGroup (FirstVariationalState X) := inferInstance

local instance selectorFirstStateNormedSpace :
    NormedSpace ℝ (FirstVariationalState X) := inferInstance

local instance selectorFirstEndNormedGroup :
    NormedAddCommGroup
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance selectorFirstEndNormedSpace :
    NormedSpace ℝ
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance selectorSecondStateNormedGroup :
    NormedAddCommGroup (SecondVariationalState X) := inferInstance

local instance selectorSecondStateNormedSpace :
    NormedSpace ℝ (SecondVariationalState X) := inferInstance

local instance selectorSecondEndNormedGroup :
    NormedAddCommGroup
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance selectorSecondEndNormedSpace :
    NormedSpace ℝ
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

/-- Four genuine local solution selectors: the base point flow and the first
three iterated variational augmented flows. -/
structure ThreeLevelVariationalSelectorTower
    (F : X → X) (x : X)
    (J : X →L[ℝ] X)
    (K : FirstVariationalState X →L[ℝ] FirstVariationalState X)
    (L : SecondVariationalState X →L[ℝ] SecondVariationalState X) where
  base : LocalControlledContinuousAutonomousSelector F x
  first : LocalControlledContinuousAutonomousSelector
    (firstVariationalAugmentedField F) (x, J)
  second : LocalControlledContinuousAutonomousSelector
    (secondVariationalAugmentedField F) ((x, J), K)
  third : LocalControlledContinuousAutonomousSelector
    (thirdVariationalAugmentedField F) (((x, J), K), L)

variable [CompleteSpace X]

/-- A local `C⁴` autonomous field admits controlled continuous selectors at
the base and all three variational levels. -/
theorem exists_threeLevelVariationalSelectorTower_of_contDiffAt_four
    (F : X → X) (x : X)
    (J : X →L[ℝ] X)
    (K : FirstVariationalState X →L[ℝ] FirstVariationalState X)
    (L : SecondVariationalState X →L[ℝ] SecondVariationalState X)
    (hF : ContDiffAt ℝ 4 F x) :
    Nonempty (ThreeLevelVariationalSelectorTower F x J K L) := by
  letI : CompleteSpace (X →L[ℝ] X) := inferInstance
  letI : CompleteSpace (FirstVariationalState X) := inferInstance
  letI : CompleteSpace
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) := inferInstance
  letI : CompleteSpace (SecondVariationalState X) := inferInstance
  letI : CompleteSpace
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) := inferInstance
  letI : CompleteSpace (ThirdVariationalState X) := inferInstance
  have hlevels :=
    variationalAugmentedFields_lipschitzRegularities_of_contDiffAt_four
      F x J K L hF
  rcases exists_localControlledContinuousAutonomousSelector_of_contDiffAt_one
      F x (hF.of_le (by norm_num)) with ⟨base⟩
  rcases exists_localControlledContinuousAutonomousSelector_of_contDiffAt_one
      (firstVariationalAugmentedField F) (x, J)
      (hlevels.1.of_le (by norm_num)) with ⟨first⟩
  rcases exists_localControlledContinuousAutonomousSelector_of_contDiffAt_one
      (secondVariationalAugmentedField F) ((x, J), K)
      (hlevels.2.1.of_le (by norm_num)) with ⟨second⟩
  rcases exists_localControlledContinuousAutonomousSelector_of_contDiffAt_one
      (thirdVariationalAugmentedField F) (((x, J), K), L)
      hlevels.2.2 with ⟨third⟩
  exact ⟨⟨base, first, second, third⟩⟩

end SelectorTower

end Poincare
