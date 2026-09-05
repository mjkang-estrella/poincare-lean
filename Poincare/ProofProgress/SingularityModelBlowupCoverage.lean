import Poincare.ProofProgress.SurgeryPerelmanPackageLayer

/-!
# Componentwise coverage of singularity-model blow-ups

The repaired blow-up-classification interface asks classified singularity
models to cover every pointed rescaling index.  The relevant map is a
five-stage composite through asymptotic solitons, curvature-operator tests,
structure models, and curvature normalizations.  This module separates that
single coverage theorem into the five corresponding surjectivity obligations.

The converse is intentionally not claimed: surjectivity of a composite does
not force its four earlier factors to be surjective.
-/

open scoped Manifold ContDiff

namespace Poincare

universe u

/-- Surjectivity at every classification stage makes the complete map from
classified singularity models to pointed rescalings surjective. -/
theorem singularityModelToPointedRescalingIndex_surjective_of_components
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (source : SingularityModelClassificationPayloadSource flow)
    (hSingularityToSoliton : Function.Surjective
      source.payload.singularityModelToAsymptoticSoliton)
    (hSolitonToCurvatureTest : Function.Surjective
      source.asymptoticSolitonSource.payload.asymptoticSolitonToCurvatureOperatorTest)
    (hCurvatureTestToStructure : Function.Surjective
      source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.payload.curvatureOperatorTestToStructureModel)
    (hStructureToNormalization : Function.Surjective
      source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.payload.structureModelToCurvatureNormalizationIndex)
    (hNormalizationToRescaling : Function.Surjective
      source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.curvatureNormalizationSource.payload.curvatureNormalizationToPointedRescalingIndex) :
    Function.Surjective source.singularityModelToPointedRescalingIndex :=
  hNormalizationToRescaling.comp
    (hStructureToNormalization.comp
      (hCurvatureTestToStructure.comp
        (hSolitonToCurvatureTest.comp hSingularityToSoliton)))

/-- Componentwise coverage constructs the content-bearing blow-up
classification interface. -/
def HasSingularityModelBlowupClassification.of_component_surjectivity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (source : SingularityModelClassificationPayloadSource flow)
    (hSingularityToSoliton : Function.Surjective
      source.payload.singularityModelToAsymptoticSoliton)
    (hSolitonToCurvatureTest : Function.Surjective
      source.asymptoticSolitonSource.payload.asymptoticSolitonToCurvatureOperatorTest)
    (hCurvatureTestToStructure : Function.Surjective
      source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.payload.curvatureOperatorTestToStructureModel)
    (hStructureToNormalization : Function.Surjective
      source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.payload.structureModelToCurvatureNormalizationIndex)
    (hNormalizationToRescaling : Function.Surjective
      source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.curvatureNormalizationSource.payload.curvatureNormalizationToPointedRescalingIndex) :
    HasSingularityModelBlowupClassification flow :=
  HasSingularityModelBlowupClassification.of_classification_payload_source
    source
    (singularityModelToPointedRescalingIndex_surjective_of_components
      source hSingularityToSoliton hSolitonToCurvatureTest
      hCurvatureTestToStructure hStructureToNormalization
      hNormalizationToRescaling)

end Poincare
