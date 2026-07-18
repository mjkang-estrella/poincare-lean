import Poincare.Global.PointFlowVariationalEndpointTower

/-!
# Algebraic identities for variational endpoint extraction

The endpoint extraction maps were defined compositionally so the chain-rule
derivatives obtained from the coherent selector tower agree exactly with the
ordinary second- and third-derivative candidates.  These lemmas expose those
compositions in a form convenient for `HasFDerivAt.comp`.
-/

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

namespace Poincare

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance extractionBaseEndNormedGroup :
    NormedAddCommGroup (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance extractionBaseEndNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X) :=
  ContinuousLinearMap.toNormedSpace

local instance extractionFirstStateNormedGroup :
    NormedAddCommGroup (FirstVariationalState X) := inferInstance

local instance extractionFirstStateNormedSpace :
    NormedSpace ℝ (FirstVariationalState X) := inferInstance

local instance extractionFirstEndNormedGroup :
    NormedAddCommGroup
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance extractionFirstEndNormedSpace :
    NormedSpace ℝ
      (FirstVariationalState X →L[ℝ] FirstVariationalState X) :=
  ContinuousLinearMap.toNormedSpace

local instance extractionSecondStateNormedGroup :
    NormedAddCommGroup (SecondVariationalState X) := inferInstance

local instance extractionSecondStateNormedSpace :
    NormedSpace ℝ (SecondVariationalState X) := inferInstance

local instance extractionSecondDerivativeNormedGroup :
    NormedAddCommGroup (X →L[ℝ] (X →L[ℝ] X)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance extractionSecondDerivativeNormedSpace :
    NormedSpace ℝ (X →L[ℝ] (X →L[ℝ] X)) :=
  ContinuousLinearMap.toNormedSpace

/-- The second-variation extraction is restriction to base variations,
followed by projection to the operator component. -/
theorem secondVariationExtraction_eq_projection_comp
    (A : FirstVariationalState X →L[ℝ] FirstVariationalState X) :
    secondVariationExtraction (X := X) A =
      (ContinuousLinearMap.snd ℝ X (X →L[ℝ] X)).comp
        (A.comp (baseVariationEmbedding (X := X))) := by
  ext h k
  simp [secondVariationExtraction, baseVariationEmbedding]

/-- The third-variation extraction is the second endpoint projection after
restricting the full second-level derivative to base variations. -/
theorem thirdVariationExtraction_eq_projection_comp
    (A : SecondVariationalState X →L[ℝ] SecondVariationalState X) :
    thirdVariationExtraction (X := X) A =
      ((secondVariationExtraction (X := X)).comp
          (ContinuousLinearMap.snd ℝ (FirstVariationalState X)
            (FirstVariationalState X →L[ℝ] FirstVariationalState X))).comp
        (A.comp (baseVariationEmbeddingSecond (X := X))) := by
  ext h k l
  simp [thirdVariationExtraction, secondVariationExtraction,
    baseVariationEmbeddingSecond, baseVariationEmbedding]

end Poincare
