import Poincare.Global.PicardLindelofRegularSelectorProjection
import Poincare.Global.PointFlowCoherentVariationalSelectorTower

/-!
# A regular coherent three-level variational tower

Starting from one regular selector for the third variational augmentation,
three applications of `projectFirstVariational` produce the second, first,
and base selectors.  All four levels share exactly the same interval and tube
radii, and every lower selector is definitionally a projection of the next.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

open Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section RegularCoherentTower

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance regularTowerBaseEndNormedGroup :
    NormedAddCommGroup (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance regularTowerBaseEndNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedSpace

local instance regularTowerFirstStateNormedGroup :
    NormedAddCommGroup (FirstVariationalState X) := inferInstance

local instance regularTowerFirstStateNormedSpace :
    NormedSpace ℝ (FirstVariationalState X) := inferInstance

local instance regularTowerFirstEndNormedGroup :
    NormedAddCommGroup
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance regularTowerFirstEndNormedSpace :
    NormedSpace ℝ
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance regularTowerSecondStateNormedGroup :
    NormedAddCommGroup (SecondVariationalState X) := inferInstance

local instance regularTowerSecondStateNormedSpace :
    NormedSpace ℝ (SecondVariationalState X) := inferInstance

local instance regularTowerSecondEndNormedGroup :
    NormedAddCommGroup
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance regularTowerSecondEndNormedSpace :
    NormedSpace ℝ
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

/-- One regular top selector determines every lower variational selector. -/
structure RegularCoherentThreeLevelVariationalSelectorTower
    (F : X → X) (x : X) where
  third : LocalRegularControlledContinuousAutonomousSelector
    (thirdVariationalAugmentedField F) (coherentThirdCenter x)

namespace RegularCoherentThreeLevelVariationalSelectorTower

variable {F : X → X} {x : X}

/-- The regular second-level selector package. -/
def second
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    LocalRegularControlledContinuousAutonomousSelector
      (secondVariationalAugmentedField F) (coherentSecondCenter x) :=
  T.third.projectFirstVariational

/-- The regular first-level selector package. -/
def first
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F) (coherentFirstCenter x) :=
  T.second.projectFirstVariational

/-- The regular base selector package. -/
def base
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    LocalRegularControlledContinuousAutonomousSelector F x :=
  T.first.projectFirstVariational

/-- Forgetting regularity recovers the previously compiled coherent tower. -/
def toCoherent
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    CoherentThreeLevelVariationalSelectorTower F x where
  top := T.third.toLocalControlledContinuousAutonomousSelector

/-- The second selector is definitionally the first projection of the top
selector at identity initial variation. -/
theorem second_selector_eq
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    T.second.selector = T.toCoherent.secondSelector := rfl

/-- The first selector is definitionally the next coherent projection. -/
theorem first_selector_eq
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    T.first.selector = T.toCoherent.firstSelector := rfl

/-- The base selector is definitionally the final coherent projection. -/
theorem base_selector_eq
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    T.base.selector = T.toCoherent.baseSelector := rfl

end RegularCoherentThreeLevelVariationalSelectorTower

variable [CompleteSpace X]

/-- A local `C⁴` autonomous field admits one regular coherent selector tower. -/
theorem exists_regularCoherentThreeLevelVariationalSelectorTower_of_contDiffAt_four
    (F : X → X) (x : X) (hF : ContDiffAt ℝ 4 F x) :
    Nonempty (RegularCoherentThreeLevelVariationalSelectorTower F x) := by
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
      F x (ContinuousLinearMap.id ℝ X)
      (ContinuousLinearMap.id ℝ (FirstVariationalState X))
      (ContinuousLinearMap.id ℝ (SecondVariationalState X)) hF
  rcases
      exists_localRegularControlledContinuousAutonomousSelector_of_contDiffAt_one
        (thirdVariationalAugmentedField F) (coherentThirdCenter x)
        hlevels.2.2 with ⟨third⟩
  exact ⟨⟨third⟩⟩

end RegularCoherentTower

end Poincare
