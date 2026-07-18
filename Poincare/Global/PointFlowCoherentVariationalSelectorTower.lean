import Poincare.Global.PointFlowVariationalSelectorTower

/-!
# A coherent variational selector tower

Choosing the base and three augmented Picard--Lindelof selectors separately
creates unnecessary compatibility obligations.  The third augmented field
already contains every lower equation in its successive first components.
This file therefore chooses only the top selector and defines all lower
selectors by projection.  Their compatibility is then definitional, rather
than an application of ODE uniqueness.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section CoherentTower

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

-- Name every nested operator-norm layer explicitly.  This prevents instance
-- synthesis from treating the expanded state abbreviations recursively.
local instance coherentBaseEndNormedGroup :
    NormedAddCommGroup (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coherentBaseEndNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedSpace

local instance coherentFirstStateNormedGroup :
    NormedAddCommGroup (FirstVariationalState X) := inferInstance

local instance coherentFirstStateNormedSpace :
    NormedSpace ℝ (FirstVariationalState X) := inferInstance

local instance coherentFirstEndNormedGroup :
    NormedAddCommGroup
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coherentFirstEndNormedSpace :
    NormedSpace ℝ
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance coherentSecondStateNormedGroup :
    NormedAddCommGroup (SecondVariationalState X) := inferInstance

local instance coherentSecondStateNormedSpace :
    NormedSpace ℝ (SecondVariationalState X) := inferInstance

local instance coherentSecondEndNormedGroup :
    NormedAddCommGroup
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coherentSecondEndNormedSpace :
    NormedSpace ℝ
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

/-- The first canonical variational centre. -/
def coherentFirstCenter (x : X) : FirstVariationalState X :=
  (x, ContinuousLinearMap.id ℝ X)

/-- The second canonical variational centre. -/
def coherentSecondCenter (x : X) : SecondVariationalState X :=
  (coherentFirstCenter x,
    ContinuousLinearMap.id ℝ (FirstVariationalState X))

/-- The third canonical variational centre. -/
def coherentThirdCenter (x : X) : ThirdVariationalState X :=
  (coherentSecondCenter x,
    ContinuousLinearMap.id ℝ (SecondVariationalState X))

/-- One top-level selector contains the base and all three variational
equations in its nested first components. -/
structure CoherentThreeLevelVariationalSelectorTower
    (F : X → X) (x : X) where
  top : LocalControlledContinuousAutonomousSelector
    (thirdVariationalAugmentedField F) (coherentThirdCenter x)

namespace CoherentThreeLevelVariationalSelectorTower

variable {F : X → X} {x : X}

/-- The second-level selector obtained by fixing the top initial variation
to the identity and projecting the top selector. -/
def secondSelector
    (T : CoherentThreeLevelVariationalSelectorTower F x) :
    SecondVariationalState X → ℝ → SecondVariationalState X :=
  fun z t ↦
    (T.top.selector
      (z, ContinuousLinearMap.id ℝ (SecondVariationalState X)) t).1

/-- The first-level selector obtained by the next identity embedding and
projection. -/
def firstSelector
    (T : CoherentThreeLevelVariationalSelectorTower F x) :
    FirstVariationalState X → ℝ → FirstVariationalState X :=
  fun z t ↦
    (T.secondSelector
      (z, ContinuousLinearMap.id ℝ (FirstVariationalState X)) t).1

/-- The base point selector obtained from the nested top selector. -/
def baseSelector
    (T : CoherentThreeLevelVariationalSelectorTower F x) : X → ℝ → X :=
  fun z t ↦
    (T.firstSelector (z, ContinuousLinearMap.id ℝ X) t).1

/-- The top selector projects exactly to the second selector. -/
theorem top_fst_eq_secondSelector
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    (z : SecondVariationalState X) (t : ℝ) :
    (T.top.selector
      (z, ContinuousLinearMap.id ℝ (SecondVariationalState X)) t).1 =
      T.secondSelector z t := rfl

/-- The second selector projects exactly to the first selector. -/
theorem secondSelector_fst_eq_firstSelector
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    (z : FirstVariationalState X) (t : ℝ) :
    (T.secondSelector
      (z, ContinuousLinearMap.id ℝ (FirstVariationalState X)) t).1 =
      T.firstSelector z t := rfl

/-- The first selector projects exactly to the base selector. -/
theorem firstSelector_fst_eq_baseSelector
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    (z : X) (t : ℝ) :
    (T.firstSelector (z, ContinuousLinearMap.id ℝ X) t).1 =
      T.baseSelector z t := rfl

/-- Embedding a second-level initial state with the identity preserves its
distance from the canonical centre. -/
private theorem second_embedding_mem_closedBall
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    {z : SecondVariationalState X}
    (hz : z ∈ closedBall (coherentSecondCenter x)
      (T.top.initialRadius : ℝ)) :
    (z, ContinuousLinearMap.id ℝ (SecondVariationalState X)) ∈
      closedBall (coherentThirdCenter x) (T.top.initialRadius : ℝ) := by
  rw [Metric.mem_closedBall] at hz ⊢
  change max (dist z (coherentSecondCenter x))
      (dist (ContinuousLinearMap.id ℝ (SecondVariationalState X))
        (ContinuousLinearMap.id ℝ (SecondVariationalState X))) ≤
    (T.top.initialRadius : ℝ)
  rw [dist_self]
  rw [max_eq_left (dist_nonneg :
    0 ≤ dist z (coherentSecondCenter x))]
  exact hz

/-- The projected second selector has the exact initial value, ODE, and
invariant tube inherited from the top selector. -/
theorem secondSelector_data
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    (z : SecondVariationalState X)
    (hz : z ∈ closedBall (coherentSecondCenter x)
      (T.top.initialRadius : ℝ)) :
    T.secondSelector z 0 = z ∧
      (∀ t ∈ Icc (-T.top.epsilon) T.top.epsilon,
        HasDerivWithinAt (T.secondSelector z)
          (secondVariationalAugmentedField F (T.secondSelector z t))
          (Icc (-T.top.epsilon) T.top.epsilon) t) ∧
      ∀ t ∈ Icc (-T.top.epsilon) T.top.epsilon,
        T.secondSelector z t ∈
          closedBall (coherentSecondCenter x) (T.top.tubeRadius : ℝ) := by
  have htop := T.top.selector_data
    (z, ContinuousLinearMap.id ℝ (SecondVariationalState X))
    (second_embedding_mem_closedBall T hz)
  refine ⟨congrArg Prod.fst htop.1, ?_, ?_⟩
  · intro t ht
    have hfst :=
      (htop.2.1 t ht).hasFDerivWithinAt.fst.hasDerivWithinAt
    convert hfst using 1 <;>
      simp [secondSelector, thirdVariationalAugmentedField,
        secondVariationalAugmentedField, firstVariationalAugmentedField]
  · intro t ht
    have hmem := htop.2.2 t ht
    rw [Metric.mem_closedBall, Prod.dist_eq] at hmem
    rw [Metric.mem_closedBall]
    change dist
      (T.top.selector
        (z, ContinuousLinearMap.id ℝ (SecondVariationalState X)) t).1
        (coherentThirdCenter x).1 ≤ (T.top.tubeRadius : ℝ)
    exact (le_max_left _ _).trans hmem

/-- Embedding a first-level state with the identity preserves its distance
from the canonical second centre. -/
private theorem first_embedding_mem_closedBall
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    {z : FirstVariationalState X}
    (hz : z ∈ closedBall (coherentFirstCenter x)
      (T.top.initialRadius : ℝ)) :
    (z, ContinuousLinearMap.id ℝ (FirstVariationalState X)) ∈
      closedBall (coherentSecondCenter x) (T.top.initialRadius : ℝ) := by
  rw [Metric.mem_closedBall] at hz ⊢
  rw [coherentSecondCenter, Prod.dist_eq, dist_self]
  rw [max_eq_left (dist_nonneg :
    0 ≤ dist z (coherentFirstCenter x))]
  exact hz

/-- The projected first selector inherits its exact initial value, ODE, and
invariant tube. -/
theorem firstSelector_data
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    (z : FirstVariationalState X)
    (hz : z ∈ closedBall (coherentFirstCenter x)
      (T.top.initialRadius : ℝ)) :
    T.firstSelector z 0 = z ∧
      (∀ t ∈ Icc (-T.top.epsilon) T.top.epsilon,
        HasDerivWithinAt (T.firstSelector z)
          (firstVariationalAugmentedField F (T.firstSelector z t))
          (Icc (-T.top.epsilon) T.top.epsilon) t) ∧
      ∀ t ∈ Icc (-T.top.epsilon) T.top.epsilon,
        T.firstSelector z t ∈
          closedBall (coherentFirstCenter x) (T.top.tubeRadius : ℝ) := by
  have hsecond := T.secondSelector_data
    (z, ContinuousLinearMap.id ℝ (FirstVariationalState X))
    (first_embedding_mem_closedBall T hz)
  refine ⟨congrArg Prod.fst hsecond.1, ?_, ?_⟩
  · intro t ht
    have hfst :=
      (hsecond.2.1 t ht).hasFDerivWithinAt.fst.hasDerivWithinAt
    convert hfst using 1 <;>
      simp [firstSelector, secondVariationalAugmentedField,
        firstVariationalAugmentedField]
  · intro t ht
    have hmem := hsecond.2.2 t ht
    rw [Metric.mem_closedBall, Prod.dist_eq] at hmem
    rw [Metric.mem_closedBall]
    change dist
      (T.secondSelector
        (z, ContinuousLinearMap.id ℝ (FirstVariationalState X)) t).1
        (coherentSecondCenter x).1 ≤ (T.top.tubeRadius : ℝ)
    exact (le_max_left _ _).trans hmem

/-- Embedding a base state with the identity preserves its distance from the
canonical first centre. -/
private theorem base_embedding_mem_closedBall
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    {z : X}
    (hz : z ∈ closedBall x (T.top.initialRadius : ℝ)) :
    (z, ContinuousLinearMap.id ℝ X) ∈
      closedBall (coherentFirstCenter x) (T.top.initialRadius : ℝ) := by
  rw [Metric.mem_closedBall] at hz ⊢
  rw [coherentFirstCenter, Prod.dist_eq, dist_self]
  rw [max_eq_left (dist_nonneg : 0 ≤ dist z x)]
  exact hz

/-- The projected base selector inherits its exact initial value, ODE, and
invariant tube. -/
theorem baseSelector_data
    (T : CoherentThreeLevelVariationalSelectorTower F x)
    (z : X) (hz : z ∈ closedBall x (T.top.initialRadius : ℝ)) :
    T.baseSelector z 0 = z ∧
      (∀ t ∈ Icc (-T.top.epsilon) T.top.epsilon,
        HasDerivWithinAt (T.baseSelector z)
          (F (T.baseSelector z t))
          (Icc (-T.top.epsilon) T.top.epsilon) t) ∧
      ∀ t ∈ Icc (-T.top.epsilon) T.top.epsilon,
        T.baseSelector z t ∈ closedBall x (T.top.tubeRadius : ℝ) := by
  have hfirst := T.firstSelector_data
    (z, ContinuousLinearMap.id ℝ X)
    (base_embedding_mem_closedBall T hz)
  refine ⟨congrArg Prod.fst hfirst.1, ?_, ?_⟩
  · intro t ht
    have hfst :=
      (hfirst.2.1 t ht).hasFDerivWithinAt.fst.hasDerivWithinAt
    convert hfst using 1 <;>
      simp [baseSelector, firstVariationalAugmentedField]
  · intro t ht
    have hmem := hfirst.2.2 t ht
    rw [Metric.mem_closedBall, Prod.dist_eq] at hmem
    rw [Metric.mem_closedBall]
    change dist
      (T.firstSelector (z, ContinuousLinearMap.id ℝ X) t).1
        (coherentFirstCenter x).1 ≤ (T.top.tubeRadius : ℝ)
    exact (le_max_left _ _).trans hmem

/-- Joint continuity of the top selector descends to the second selector. -/
theorem secondSelector_continuousOn
    (T : CoherentThreeLevelVariationalSelectorTower F x) :
    ContinuousOn (Function.uncurry T.secondSelector)
      (closedBall (coherentSecondCenter x) (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon) := by
  let embed : SecondVariationalState X × ℝ → ThirdVariationalState X × ℝ :=
    fun q ↦
      ((q.1, ContinuousLinearMap.id ℝ (SecondVariationalState X)), q.2)
  have hembed : Continuous embed :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hmap : MapsTo embed
      (closedBall (coherentSecondCenter x) (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon)
      (closedBall (coherentThirdCenter x) (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon) := by
    intro q hq
    exact ⟨second_embedding_mem_closedBall T hq.1, hq.2⟩
  have hcomp := T.top.selector_continuousOn.comp hembed.continuousOn hmap
  simpa only [Function.uncurry, secondSelector, embed] using hcomp.fst

/-- Joint continuity descends once more to the first selector. -/
theorem firstSelector_continuousOn
    (T : CoherentThreeLevelVariationalSelectorTower F x) :
    ContinuousOn (Function.uncurry T.firstSelector)
      (closedBall (coherentFirstCenter x) (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon) := by
  let embed : FirstVariationalState X × ℝ → SecondVariationalState X × ℝ :=
    fun q ↦
      ((q.1, ContinuousLinearMap.id ℝ (FirstVariationalState X)), q.2)
  have hembed : Continuous embed :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hmap : MapsTo embed
      (closedBall (coherentFirstCenter x) (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon)
      (closedBall (coherentSecondCenter x) (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon) := by
    intro q hq
    exact ⟨first_embedding_mem_closedBall T hq.1, hq.2⟩
  have hcomp := T.secondSelector_continuousOn.comp hembed.continuousOn hmap
  simpa only [Function.uncurry, firstSelector, embed] using hcomp.fst

/-- Joint continuity finally descends to the base selector. -/
theorem baseSelector_continuousOn
    (T : CoherentThreeLevelVariationalSelectorTower F x) :
    ContinuousOn (Function.uncurry T.baseSelector)
      (closedBall x (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon) := by
  let embed : X × ℝ → FirstVariationalState X × ℝ :=
    fun q ↦ ((q.1, ContinuousLinearMap.id ℝ X), q.2)
  have hembed : Continuous embed :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hmap : MapsTo embed
      (closedBall x (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon)
      (closedBall (coherentFirstCenter x) (T.top.initialRadius : ℝ) ×ˢ
        Icc (-T.top.epsilon) T.top.epsilon) := by
    intro q hq
    exact ⟨base_embedding_mem_closedBall T hq.1, hq.2⟩
  have hcomp := T.firstSelector_continuousOn.comp hembed.continuousOn hmap
  simpa only [Function.uncurry, baseSelector, embed] using hcomp.fst

end CoherentThreeLevelVariationalSelectorTower

variable [CompleteSpace X]

/-- A local `C⁴` field admits one coherent selector carrying all three
variational levels. -/
theorem exists_coherentThreeLevelVariationalSelectorTower_of_contDiffAt_four
    (F : X → X) (x : X) (hF : ContDiffAt ℝ 4 F x) :
    Nonempty (CoherentThreeLevelVariationalSelectorTower F x) := by
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
  rcases exists_localControlledContinuousAutonomousSelector_of_contDiffAt_one
      (thirdVariationalAugmentedField F) (coherentThirdCenter x)
      hlevels.2.2 with ⟨top⟩
  exact ⟨⟨top⟩⟩

end CoherentTower

end Poincare
