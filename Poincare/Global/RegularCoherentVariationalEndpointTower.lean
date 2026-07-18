import Poincare.Global.RegularVariationalSelectorEndpointDerivative
import Poincare.Global.PointFlowVariationalExtractionIdentities

/-!
# Three endpoint derivatives from the regular coherent selector tower

The one-level residual theorem is applied successively to the first, second,
and third regular selectors.  Chain rules for the canonical identity
embeddings and the compiled extraction identities turn the resulting full
augmented derivatives into the ordinary first, second, and third endpoint
derivative fields.  This discharges all three conditional fields in
`VariationalSelectorEndpointIdentifications` on the positive protected half
interval.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section EndpointAssembly

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [FiniteDimensional ℝ X]

local instance regularEndpointBaseEndNormedGroup :
    NormedAddCommGroup (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance regularEndpointBaseEndNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedSpace

local instance regularEndpointFirstStateNormedGroup :
    NormedAddCommGroup (FirstVariationalState X) := inferInstance

local instance regularEndpointFirstStateNormedSpace :
    NormedSpace ℝ (FirstVariationalState X) := inferInstance

local instance regularEndpointFirstEndNormedGroup :
    NormedAddCommGroup
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance regularEndpointFirstEndNormedSpace :
    NormedSpace ℝ
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance regularEndpointSecondStateNormedGroup :
    NormedAddCommGroup (SecondVariationalState X) := inferInstance

local instance regularEndpointSecondStateNormedSpace :
    NormedSpace ℝ (SecondVariationalState X) := inferInstance

local instance regularEndpointSecondEndNormedGroup :
    NormedAddCommGroup
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance regularEndpointSecondEndNormedSpace :
    NormedSpace ℝ
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance regularEndpointSecondDerivativeNormedGroup :
    NormedAddCommGroup (X →L[ℝ] (X →L[ℝ] X)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance regularEndpointSecondDerivativeNormedSpace :
    NormedSpace ℝ (X →L[ℝ] (X →L[ℝ] X)) :=
  ContinuousLinearMap.toNormedSpace

namespace RegularCoherentThreeLevelVariationalSelectorTower

variable {F : X → X} {x : X}

/-- Forget the retained regularity while preserving all four coherent
selectors. -/
def toSelectorTower
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x) :
    ThreeLevelVariationalSelectorTower F x
      (ContinuousLinearMap.id ℝ X)
      (ContinuousLinearMap.id ℝ (FirstVariationalState X))
      (ContinuousLinearMap.id ℝ (SecondVariationalState X)) where
  base := T.base.toLocalControlledContinuousAutonomousSelector
  first := T.first.toLocalControlledContinuousAutonomousSelector
  second := T.second.toLocalControlledContinuousAutonomousSelector
  third := T.third.toLocalControlledContinuousAutonomousSelector

/-- The canonical first identity embedding has derivative
`baseVariationEmbedding`. -/
private theorem canonicalFirst_hasFDerivAt (q : X) :
    HasFDerivAt (canonicalFirstVariationalInitial (X := X))
      (baseVariationEmbedding (X := X)) q := by
  simpa only [canonicalFirstVariationalInitial, baseVariationEmbedding] using
    hasFDerivAt_prodMk_left (𝕜 := ℝ) q (ContinuousLinearMap.id ℝ X)

/-- The canonical second identity embedding has derivative
`baseVariationEmbeddingSecond`. -/
private theorem canonicalSecond_hasFDerivAt (q : X) :
    HasFDerivAt (canonicalSecondVariationalInitial (X := X))
      (baseVariationEmbeddingSecond (X := X)) q := by
  have houter := hasFDerivAt_prodMk_left (𝕜 := ℝ)
    (canonicalFirstVariationalInitial q)
    (ContinuousLinearMap.id ℝ (FirstVariationalState X))
  have hcomp := houter.comp q (canonicalFirst_hasFDerivAt (X := X) q)
  simpa only [canonicalSecondVariationalInitial,
    baseVariationEmbeddingSecond] using hcomp

/-- Base endpoint derivative supplied by the first regular variational
selector. -/
theorem baseEndpoint_hasFDerivAt
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    {q : X}
    (hq : q ∈ ball x (T.base.initialRadius : ℝ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T.third.epsilon / 2)) :
    HasFDerivAt (fun y : X ↦ T.toSelectorTower.base.selector y t)
      (firstVariationalEndpointField T.toSelectorTower.first.selector t q) q := by
  have h := T.first.projectedEndpoint_hasFDerivAt hq ht
  simpa only [toSelectorTower, firstVariationalEndpointField,
    canonicalFirstVariationalInitial, first, base,
    LocalRegularControlledContinuousAutonomousSelector.projectFirstVariational_selector]
    using h

/-- Derivative of the first endpoint operator, extracted from the second
regular variational selector. -/
theorem firstEndpoint_hasFDerivAt
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    {q : X}
    (hq : q ∈ ball x (T.base.initialRadius : ℝ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T.third.epsilon / 2)) :
    HasFDerivAt
      (firstVariationalEndpointField T.toSelectorTower.first.selector t)
      (secondVariationalEndpointField T.toSelectorTower.second.selector t q) q := by
  have hqFirst : canonicalFirstVariationalInitial q ∈
      ball (coherentFirstCenter x) (T.second.initialRadius : ℝ) := by
    rw [Metric.mem_ball] at hq ⊢
    rw [canonicalFirstVariationalInitial, coherentFirstCenter, Prod.dist_eq,
      dist_self, max_eq_left (dist_nonneg : 0 ≤ dist q x)]
    exact hq
  have hfull := T.second.projectedEndpoint_hasFDerivAt hqFirst ht
  have hpre := hfull.comp q (canonicalFirst_hasFDerivAt (X := X) q)
  have hpost :=
    (ContinuousLinearMap.snd ℝ X (X →L[ℝ] X)).hasFDerivAt.comp q hpre
  simpa only [toSelectorTower, firstVariationalEndpointField,
    secondVariationalEndpointField, canonicalFirstVariationalInitial,
    canonicalSecondVariationalInitial, first, second,
    LocalRegularControlledContinuousAutonomousSelector.projectFirstVariational_selector,
    secondVariationExtraction_eq_projection_comp] using hpost

/-- Derivative of the second endpoint operator, extracted from the third
regular variational selector. -/
theorem secondEndpoint_hasFDerivAt
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    {q : X}
    (hq : q ∈ ball x (T.base.initialRadius : ℝ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T.third.epsilon / 2)) :
    HasFDerivAt
      (secondVariationalEndpointField T.toSelectorTower.second.selector t)
      (thirdVariationalEndpointField T.toSelectorTower.third.selector t q) q := by
  have hqSecond : canonicalSecondVariationalInitial q ∈
      ball (coherentSecondCenter x) (T.third.initialRadius : ℝ) := by
    rw [Metric.mem_ball] at hq ⊢
    calc
      dist (canonicalSecondVariationalInitial q) (coherentSecondCenter x) =
          dist q x := by
        simp [canonicalSecondVariationalInitial, coherentSecondCenter,
          canonicalFirstVariationalInitial, coherentFirstCenter,
          Prod.dist_eq, max_eq_left (dist_nonneg : 0 ≤ dist q x)]
      _ < (T.third.initialRadius : ℝ) := by
        simpa only [base, first, second] using hq
  have hfull := T.third.projectedEndpoint_hasFDerivAt hqSecond ht
  have hpre := hfull.comp q (canonicalSecond_hasFDerivAt (X := X) q)
  let projection : SecondVariationalState X →L[ℝ]
      (X →L[ℝ] (X →L[ℝ] X)) :=
    (secondVariationExtraction (X := X)).comp
      (ContinuousLinearMap.snd ℝ (FirstVariationalState X)
        (FirstVariationalState X →L[ℝ] FirstVariationalState X))
  have hpost := projection.hasFDerivAt.comp q hpre
  simpa only [toSelectorTower, secondVariationalEndpointField,
    thirdVariationalEndpointField, canonicalSecondVariationalInitial,
    canonicalThirdVariationalInitial, second, projection,
    LocalRegularControlledContinuousAutonomousSelector.projectFirstVariational_selector,
    thirdVariationExtraction_eq_projection_comp] using hpost

/-- All three endpoint identities hold on one neighborhood for every time in
the positive protected half interval. -/
def endpointIdentifications
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T.third.epsilon / 2)) :
    VariationalSelectorEndpointIdentifications T.toSelectorTower t where
  base_hasFDerivAt_eventually := by
    refine ⟨ball x (T.base.initialRadius : ℝ), ?_, ?_⟩
    · exact ball_mem_nhds x (by exact_mod_cast T.base.initialRadius_pos)
    · intro q hq
      exact T.baseEndpoint_hasFDerivAt hq ht
  first_hasFDerivAt_eventually := by
    refine ⟨ball x (T.base.initialRadius : ℝ), ?_, ?_⟩
    · exact ball_mem_nhds x (by exact_mod_cast T.base.initialRadius_pos)
    · intro q hq
      exact T.firstEndpoint_hasFDerivAt hq ht
  second_hasFDerivAt_eventually := by
    refine ⟨ball x (T.base.initialRadius : ℝ), ?_, ?_⟩
    · exact ball_mem_nhds x (by exact_mod_cast T.base.initialRadius_pos)
    · intro q hq
      exact T.secondEndpoint_hasFDerivAt hq ht

/-- The regular coherent selector tower yields a complete local third-order
variational tower for each positive protected time. -/
def toLocalThirdOrderVariationalTower
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T.third.epsilon / 2)) :
    LocalThirdOrderVariationalTower
      (fun q : X ↦ T.toSelectorTower.base.selector q t) x := by
  have hinterior : t ∈ Ioo (-T.toSelectorTower.third.epsilon)
      T.toSelectorTower.third.epsilon := by
    rcases ht with ⟨ht0, htUpper⟩
    constructor <;> dsimp only [toSelectorTower] at * <;>
      linarith [T.third.epsilon_pos]
  exact T.toSelectorTower.toLocalThirdOrderVariationalTower
    (T.endpointIdentifications ht) hinterior

end RegularCoherentThreeLevelVariationalSelectorTower

end EndpointAssembly

end Poincare
