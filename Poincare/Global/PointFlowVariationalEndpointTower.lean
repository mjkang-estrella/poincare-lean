import Poincare.Global.PointFlowVariationalSelectorTower
import Poincare.Global.DeTurckBUCPointFlowVariationalSmoothDependence

/-!
# Endpoint derivative fields extracted from variational selectors

For the canonical identity initial variations, the first augmented selector
contains the first derivative of the base endpoint.  The second and third
augmented selectors contain the derivatives of the preceding augmented
flows.  Continuous-linear projection and restriction extract the ordinary
second and third endpoint derivatives.

This file proves that continuity of the top selector automatically supplies
the top-continuity field in `LocalThirdOrderVariationalTower`.  Thus only the
three endpoint `HasFDerivAt` identifications remain to be supplied by the
residual/Gronwall comparison.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

open Filter Function Metric Set
open scoped ContDiff Topology

namespace Poincare

-- Give every finite operator-norm layer a named instance.  The unfolded
-- variational-state abbreviations otherwise look recursive to typeclass
-- search once the second and third endpoint extractions are elaborated.
variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance endpointBaseEndNormedGroup :
    NormedAddCommGroup (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance endpointBaseEndNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedSpace

local instance endpointFirstStateNormedGroup :
    NormedAddCommGroup (FirstVariationalState X) := inferInstance

local instance endpointFirstStateNormedSpace :
    NormedSpace ℝ (FirstVariationalState X) := inferInstance

local instance endpointFirstEndNormedGroup :
    NormedAddCommGroup
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance endpointFirstEndNormedSpace :
    NormedSpace ℝ
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance endpointSecondStateNormedGroup :
    NormedAddCommGroup (SecondVariationalState X) := inferInstance

local instance endpointSecondStateNormedSpace :
    NormedSpace ℝ (SecondVariationalState X) := inferInstance

local instance endpointSecondEndNormedGroup :
    NormedAddCommGroup
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance endpointSecondEndNormedSpace :
    NormedSpace ℝ
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance endpointThirdStateNormedGroup :
    NormedAddCommGroup (ThirdVariationalState X) := inferInstance

local instance endpointThirdStateNormedSpace :
    NormedSpace ℝ (ThirdVariationalState X) := inferInstance

local instance endpointSecondDerivativeNormedGroup :
    NormedAddCommGroup (X →L[ℝ] (X →L[ℝ] X)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance endpointSecondDerivativeNormedSpace :
    NormedSpace ℝ (X →L[ℝ] (X →L[ℝ] X)) :=
  ContinuousLinearMap.toNormedSpace

local instance endpointThirdDerivativeNormedGroup :
    NormedAddCommGroup (X →L[ℝ] (X →L[ℝ] (X →L[ℝ] X))) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance endpointThirdDerivativeNormedSpace :
    NormedSpace ℝ (X →L[ℝ] (X →L[ℝ] (X →L[ℝ] X))) :=
  ContinuousLinearMap.toNormedSpace

section CanonicalExtractions

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Embed a base-state variation into the first augmented state, keeping the
initial identity variation fixed. -/
def baseVariationEmbedding : X →L[ℝ] FirstVariationalState X :=
  ContinuousLinearMap.inl ℝ X (X →L[ℝ] X)

/-- Embed a base-state variation into the second augmented state, keeping
both identity initial variations fixed. -/
def baseVariationEmbeddingSecond : X →L[ℝ] SecondVariationalState X :=
  (ContinuousLinearMap.inl ℝ (FirstVariationalState X)
      (FirstVariationalState X →L[ℝ] FirstVariationalState X)).comp
    (baseVariationEmbedding (X := X))

/-- Restrict the derivative of the first augmented endpoint to variations
of the base initial state and project to its linear-variation component. -/
def secondVariationExtraction :
    (FirstVariationalState X →L[ℝ] FirstVariationalState X) →L[ℝ]
      (X →L[ℝ] (X →L[ℝ] X)) :=
  let precomposeBase :
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) →L[ℝ]
        (X →L[ℝ] FirstVariationalState X) :=
    (ContinuousLinearMap.apply ℝ (X →L[ℝ] FirstVariationalState X)
      (baseVariationEmbedding (X := X))).comp
        (ContinuousLinearMap.compL ℝ X
          (FirstVariationalState X) (FirstVariationalState X))
  let projectVariation :
      (X →L[ℝ] FirstVariationalState X) →L[ℝ]
        (X →L[ℝ] (X →L[ℝ] X)) :=
    (ContinuousLinearMap.compL ℝ X (FirstVariationalState X)
      (X →L[ℝ] X))
      (ContinuousLinearMap.snd ℝ X (X →L[ℝ] X))
  projectVariation.comp precomposeBase

/-- Restrict the derivative of the second augmented endpoint to base-state
variations, project to the change of the first augmented derivative, and
apply `secondVariationExtraction`. -/
def thirdVariationExtraction :
    (SecondVariationalState X →L[ℝ] SecondVariationalState X) →L[ℝ]
      (X →L[ℝ] (X →L[ℝ] (X →L[ℝ] X))) :=
  let precomposeBase :
      (SecondVariationalState X →L[ℝ] SecondVariationalState X) →L[ℝ]
        (X →L[ℝ] SecondVariationalState X) :=
    (ContinuousLinearMap.apply ℝ (X →L[ℝ] SecondVariationalState X)
      (baseVariationEmbeddingSecond (X := X))).comp
        (ContinuousLinearMap.compL ℝ X
          (SecondVariationalState X) (SecondVariationalState X))
  let projectFirstDerivative :
      (X →L[ℝ] SecondVariationalState X) →L[ℝ]
        (X →L[ℝ]
          (FirstVariationalState X →L[ℝ] FirstVariationalState X)) :=
    (ContinuousLinearMap.compL ℝ X (SecondVariationalState X)
      (FirstVariationalState X →L[ℝ] FirstVariationalState X))
      (ContinuousLinearMap.snd ℝ (FirstVariationalState X)
        (FirstVariationalState X →L[ℝ] FirstVariationalState X))
  let extractPointwise :
      (X →L[ℝ]
        (FirstVariationalState X →L[ℝ] FirstVariationalState X)) →L[ℝ]
        (X →L[ℝ] (X →L[ℝ] (X →L[ℝ] X))) :=
    (ContinuousLinearMap.compL ℝ X
      (FirstVariationalState X →L[ℝ] FirstVariationalState X)
      (X →L[ℝ] (X →L[ℝ] X)))
      (secondVariationExtraction (X := X))
  extractPointwise.comp (projectFirstDerivative.comp precomposeBase)

/-- Canonical first augmented initial state. -/
def canonicalFirstVariationalInitial (x : X) : FirstVariationalState X :=
  (x, ContinuousLinearMap.id ℝ X)

/-- Canonical second augmented initial state. -/
def canonicalSecondVariationalInitial (x : X) : SecondVariationalState X :=
  (canonicalFirstVariationalInitial x,
    ContinuousLinearMap.id ℝ (FirstVariationalState X))

/-- Canonical third augmented initial state. -/
def canonicalThirdVariationalInitial (x : X) : ThirdVariationalState X :=
  (canonicalSecondVariationalInitial x,
    ContinuousLinearMap.id ℝ (SecondVariationalState X))

/-- First endpoint derivative candidate carried by the first augmented
selector. -/
def firstVariationalEndpointField
    (alpha₁ : FirstVariationalState X → ℝ → FirstVariationalState X)
    (s : ℝ) : X → X →L[ℝ] X :=
  fun x ↦ (alpha₁ (canonicalFirstVariationalInitial x) s).2

/-- Second endpoint derivative candidate extracted from the second augmented
selector. -/
def secondVariationalEndpointField
    (alpha₂ : SecondVariationalState X → ℝ → SecondVariationalState X)
    (s : ℝ) : X → X →L[ℝ] (X →L[ℝ] X) :=
  fun x ↦ secondVariationExtraction
    (alpha₂ (canonicalSecondVariationalInitial x) s).2

/-- Third endpoint derivative candidate extracted from the third augmented
selector. -/
def thirdVariationalEndpointField
    (alpha₃ : ThirdVariationalState X → ℝ → ThirdVariationalState X)
    (s : ℝ) : X → X →L[ℝ] (X →L[ℝ] (X →L[ℝ] X)) :=
  fun x ↦ thirdVariationExtraction
    (alpha₃ (canonicalThirdVariationalInitial x) s).2

end CanonicalExtractions

section EndpointTowerAssembly

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {F : X → X} {x : X} {s : ℝ}

/-- The three residual/Gronwall endpoint identifications, separated from the
selector existence and top-continuity arguments. -/
structure VariationalSelectorEndpointIdentifications
    (T : ThreeLevelVariationalSelectorTower F x
      (ContinuousLinearMap.id ℝ X)
      (ContinuousLinearMap.id ℝ (FirstVariationalState X))
      (ContinuousLinearMap.id ℝ (SecondVariationalState X)))
    (s : ℝ) : Prop where
  base_hasFDerivAt_eventually :
    ∃ U ∈ nhds x, ∀ q ∈ U,
      HasFDerivAt (fun y ↦ T.base.selector y s)
        (firstVariationalEndpointField T.first.selector s q) q
  first_hasFDerivAt_eventually :
    ∃ U ∈ nhds x, ∀ q ∈ U,
      HasFDerivAt (firstVariationalEndpointField T.first.selector s)
        (secondVariationalEndpointField T.second.selector s q) q
  second_hasFDerivAt_eventually :
    ∃ U ∈ nhds x, ∀ q ∈ U,
      HasFDerivAt (secondVariationalEndpointField T.second.selector s)
        (thirdVariationalEndpointField T.third.selector s q) q

namespace ThreeLevelVariationalSelectorTower

/-- The canonical third initial-state embedding is smooth. -/
theorem canonicalThirdVariationalInitial_contDiff
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ContDiff ℝ ∞ (canonicalThirdVariationalInitial (X := X)) := by
  have hbase : ContDiff ℝ ∞
      (fun x : X ↦ canonicalFirstVariationalInitial x) :=
    contDiff_id.prodMk contDiff_const
  have hsecond : ContDiff ℝ ∞
      (fun x : X ↦ canonicalSecondVariationalInitial x) :=
    hbase.prodMk contDiff_const
  exact hsecond.prodMk contDiff_const

/-- The third derivative candidate is continuous at the base point whenever
the top selector is evaluated strictly inside its local interval. -/
theorem thirdVariationalEndpointField_continuousAt
    (T : ThreeLevelVariationalSelectorTower F x
      (ContinuousLinearMap.id ℝ X)
      (ContinuousLinearMap.id ℝ (FirstVariationalState X))
      (ContinuousLinearMap.id ℝ (SecondVariationalState X)))
    (hs : s ∈ Ioo (-T.third.epsilon) T.third.epsilon) :
    ContinuousAt (thirdVariationalEndpointField T.third.selector s) x := by
  have hselector := T.third.selector_continuousAt hs
  have hinput : ContinuousAt
      (fun q : X ↦ (canonicalThirdVariationalInitial q, s)) x :=
    (canonicalThirdVariationalInitial_contDiff X).continuous.continuousAt.prodMk
      continuousAt_const
  have hstate : ContinuousAt
      (fun q : X ↦ T.third.selector (canonicalThirdVariationalInitial q) s) x := by
    simpa only [Function.uncurry, Function.comp_apply] using
      hselector.comp
        (f := fun q : X ↦ (canonicalThirdVariationalInitial q, s)) hinput
  have hhighest : ContinuousAt
      (fun q : X ↦
        (T.third.selector (canonicalThirdVariationalInitial q) s).2) x :=
    hstate.snd
  exact (thirdVariationExtraction (X := X)).continuous.continuousAt.comp hhighest

/-- The third derivative candidate is `C⁰` on a neighborhood of the base
point.  Unlike mere pointwise continuity, this is exactly the germ strength
required by `contDiffAt_succ_iff_hasFDerivAt`. -/
theorem thirdVariationalEndpointField_contDiffAt_zero
    (T : ThreeLevelVariationalSelectorTower F x
      (ContinuousLinearMap.id ℝ X)
      (ContinuousLinearMap.id ℝ (FirstVariationalState X))
      (ContinuousLinearMap.id ℝ (SecondVariationalState X)))
    (hs : s ∈ Ioo (-T.third.epsilon) T.third.epsilon) :
    ContDiffAt ℝ 0 (thirdVariationalEndpointField T.third.selector s) x := by
  let initial : X → ThirdVariationalState X :=
    canonicalThirdVariationalInitial
  let U : Set X := initial ⁻¹'
    closedBall (canonicalThirdVariationalInitial x)
      (T.third.initialRadius : ℝ)
  have hInitialContinuous : Continuous initial := by
    simpa only [initial] using
      (canonicalThirdVariationalInitial_contDiff X).continuous
  have hrReal : 0 < (T.third.initialRadius : ℝ) := by
    exact_mod_cast T.third.initialRadius_pos
  have hU : U ∈ nhds x := by
    apply hInitialContinuous.continuousAt.preimage_mem_nhds
    exact closedBall_mem_nhds (canonicalThirdVariationalInitial x) hrReal
  have hsClosed : s ∈ Icc (-T.third.epsilon) T.third.epsilon :=
    Ioo_subset_Icc_self hs
  have hinputOn : ContinuousOn (fun q : X ↦ (initial q, s)) U :=
    hInitialContinuous.continuousOn.prodMk continuousOn_const
  have hselectorOn : ContinuousOn
      (fun q : X ↦ T.third.selector (initial q) s) U := by
    apply T.third.selector_continuousOn.comp hinputOn
    intro q hq
    have hq' : initial q ∈
        closedBall (canonicalThirdVariationalInitial x)
          (T.third.initialRadius : ℝ) := by
      exact hq
    exact ⟨hq', hsClosed⟩
  have hhighestOn : ContinuousOn
      (fun q : X ↦ (T.third.selector (initial q) s).2) U :=
    hselectorOn.snd
  have hextractedOn : ContinuousOn
      (fun q : X ↦ thirdVariationExtraction
        (T.third.selector (initial q) s).2) U :=
    (thirdVariationExtraction (X := X)).continuous.comp_continuousOn
      hhighestOn
  rw [contDiffAt_zero]
  refine ⟨U, hU, ?_⟩
  simpa only [thirdVariationalEndpointField, initial] using hextractedOn

/-- Controlled selectors, the three endpoint identifications, and strict
interiority of the top time assemble the complete local third-order
variational tower for the base endpoint map. -/
def toLocalThirdOrderVariationalTower
    (T : ThreeLevelVariationalSelectorTower F x
      (ContinuousLinearMap.id ℝ X)
      (ContinuousLinearMap.id ℝ (FirstVariationalState X))
      (ContinuousLinearMap.id ℝ (SecondVariationalState X)))
    (H : VariationalSelectorEndpointIdentifications T s)
    (hs : s ∈ Ioo (-T.third.epsilon) T.third.epsilon) :
    LocalThirdOrderVariationalTower (fun q ↦ T.base.selector q s) x where
  D₁ := firstVariationalEndpointField T.first.selector s
  D₂ := secondVariationalEndpointField T.second.selector s
  D₃ := thirdVariationalEndpointField T.third.selector s
  f_hasFDerivAt_eventually := H.base_hasFDerivAt_eventually
  D₁_hasFDerivAt_eventually := H.first_hasFDerivAt_eventually
  D₂_hasFDerivAt_eventually := H.second_hasFDerivAt_eventually
  D₃_contDiffAt_zero :=
    T.thirdVariationalEndpointField_contDiffAt_zero hs

end ThreeLevelVariationalSelectorTower

end EndpointTowerAssembly

end Poincare
