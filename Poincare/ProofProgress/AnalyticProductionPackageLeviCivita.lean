/-
Production analytic-package bridge for the first Levi-Civita and curvature fields.

This module is intentionally small: it records the concrete bridge now available
in the production analytic interface and names the next constructorless
analytic field after existence, uniqueness, torsion-freeness, and metric
compatibility, connection-theory, Riemann-curvature construction,
Riemann-curvature symmetry, first-Bianchi, second-Bianchi, and
Riemann-curvature-theory, Ricci tensor contraction-formula data, and
scalar-curvature contraction-formula data, and Ricci contraction-theory data
are supplied; the metric family itself supplies time-dependent metric
regularity, and explicit metric time-derivative data supplies the next field.
-/

import Poincare.AnalyticFoundation

universe u v w

open Bundle
open scoped Manifold ContDiff

namespace Poincare

/--
A time-indexed bundled tangent covariant derivative constructs the first field
stored by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_leviCivitaExistence_of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) :=
  hasLeviCivitaConnectionExistence_of_connectionField connectionAtTime

/--
Unique time-indexed bundled tangent covariant-derivative data constructs the
second field stored by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_leviCivitaUniqueness_of_uniqueConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (uniqueConnectionAtTime :
      UniqueTimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionUniqueness
      (metric_of_ricci_flow_data flow) :=
  hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField
    uniqueConnectionAtTime

/--
A unique connection-field witness closes the first two analytic package fields:
existence and uniqueness.
-/
theorem analyticProductionPackage_leviCivitaExistenceAndUniqueness_of_uniqueConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (uniqueConnectionAtTime :
      UniqueTimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) :=
  ⟨analyticProductionPackage_leviCivitaExistence_of_connectionField
      uniqueConnectionAtTime.connectionAtTime,
    analyticProductionPackage_leviCivitaUniqueness_of_uniqueConnectionField
      uniqueConnectionAtTime⟩

/--
Zero-torsion time-dependent connection data constructs the third field stored by
`RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_leviCivitaTorsionFree_of_torsionFreeConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (torsionFreeConnectionAtTime :
      TorsionFreeTimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaTorsionFreeProperty
      (metric_of_ricci_flow_data flow) :=
  hasLeviCivitaTorsionFreeProperty_of_torsionFreeConnectionField
    torsionFreeConnectionAtTime

/--
A torsion-free connection-field witness closes the first three analytic package
fields: existence, uniqueness, and torsion-freeness.
-/
theorem analyticProductionPackage_leviCivitaFirstThree_of_torsionFreeConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (torsionFreeConnectionAtTime :
      TorsionFreeTimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) :=
  let firstTwo :=
    analyticProductionPackage_leviCivitaExistenceAndUniqueness_of_uniqueConnectionField
      torsionFreeConnectionAtTime.uniqueConnectionAtTime
  ⟨firstTwo.1, firstTwo.2,
    analyticProductionPackage_leviCivitaTorsionFree_of_torsionFreeConnectionField
      torsionFreeConnectionAtTime⟩

/--
Metric-compatible time-dependent connection data constructs the fourth field
stored by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_leviCivitaMetricCompatibility_of_metricCompatibleConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (metricCompatibleConnectionAtTime :
      MetricCompatibleTimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaMetricCompatibility
      (metric_of_ricci_flow_data flow) :=
  hasLeviCivitaMetricCompatibility_of_metricCompatibleConnectionField
    metricCompatibleConnectionAtTime

/--
A metric-compatible connection-field witness closes the first four analytic
package fields: existence, uniqueness, torsion-freeness, and metric
compatibility.
-/
theorem analyticProductionPackage_leviCivitaFirstFour_of_metricCompatibleConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (metricCompatibleConnectionAtTime :
      MetricCompatibleTimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) :=
  let firstThree :=
    analyticProductionPackage_leviCivitaFirstThree_of_torsionFreeConnectionField
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  ⟨firstThree.1, firstThree.2.1, firstThree.2.2,
    analyticProductionPackage_leviCivitaMetricCompatibility_of_metricCompatibleConnectionField
      metricCompatibleConnectionAtTime⟩

/--
Smooth metric-compatible time-dependent connection data constructs the fifth
field stored by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_leviCivitaConnectionTheory_of_connectionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (connectionTheoryAtTime :
      LeviCivitaTimeDependentConnectionTheoryData
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionTheory
      (metric_of_ricci_flow_data flow) :=
  hasLeviCivitaConnectionTheory_of_connectionTheoryData
    connectionTheoryAtTime

/--
A connection-theory witness closes the first five analytic package fields:
existence, uniqueness, torsion-freeness, metric compatibility, and the broader
Levi-Civita connection-theory field.
-/
theorem analyticProductionPackage_leviCivitaFirstFive_of_connectionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (connectionTheoryAtTime :
      LeviCivitaTimeDependentConnectionTheoryData
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) :=
  let firstFour :=
    analyticProductionPackage_leviCivitaFirstFour_of_metricCompatibleConnectionField
      connectionTheoryAtTime.metricCompatibleConnectionAtTime
  ⟨firstFour.1, firstFour.2.1, firstFour.2.2.1, firstFour.2.2.2,
    analyticProductionPackage_leviCivitaConnectionTheory_of_connectionTheoryData
      connectionTheoryAtTime⟩

/--
Concrete Riemann-curvature construction data constructs the sixth field stored
by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_riemannCurvatureConstruction_of_curvatureConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data flow)) :
    HasRiemannCurvatureTensorConstruction
      (metric_of_ricci_flow_data flow) :=
  hasRiemannCurvatureTensorConstruction_of_curvatureConstructionData
    curvatureConstructionAtTime

/--
A Riemann-curvature construction witness closes the first six analytic package
fields: the five Levi-Civita fields and curvature-tensor construction.
-/
theorem analyticProductionPackage_firstSix_of_curvatureConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) :=
  let firstFive :=
    analyticProductionPackage_leviCivitaFirstFive_of_connectionTheoryData
      curvatureConstructionAtTime.connectionTheoryAtTime
  ⟨firstFive.1, firstFive.2.1, firstFive.2.2.1, firstFive.2.2.2.1,
    firstFive.2.2.2.2,
    analyticProductionPackage_riemannCurvatureConstruction_of_curvatureConstructionData
      curvatureConstructionAtTime⟩

/--
Concrete Riemann-curvature symmetry data constructs the seventh field stored by
`RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_riemannCurvatureSymmetries_of_curvatureSymmetryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureSymmetryAtTime :
      RiemannCurvatureTensorSymmetryData
        (metric_of_ricci_flow_data flow)) :
    HasRiemannCurvatureTensorSymmetries
      (metric_of_ricci_flow_data flow) :=
  hasRiemannCurvatureTensorSymmetries_of_curvatureSymmetryData
    curvatureSymmetryAtTime

/--
A Riemann-curvature symmetry witness closes the first seven analytic package
fields: the five Levi-Civita fields, curvature-tensor construction, and
curvature-tensor symmetries.
-/
theorem analyticProductionPackage_firstSeven_of_curvatureSymmetryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureSymmetryAtTime :
      RiemannCurvatureTensorSymmetryData
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) :=
  let firstSix :=
    analyticProductionPackage_firstSix_of_curvatureConstructionData
      curvatureSymmetryAtTime.curvatureConstructionAtTime
  ⟨firstSix.1, firstSix.2.1, firstSix.2.2.1, firstSix.2.2.2.1,
    firstSix.2.2.2.2.1, firstSix.2.2.2.2.2,
    analyticProductionPackage_riemannCurvatureSymmetries_of_curvatureSymmetryData
      curvatureSymmetryAtTime⟩

/--
Concrete first-Bianchi data constructs the eighth field stored by
`RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_firstBianchi_of_firstBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (firstBianchiAtTime :
      RiemannCurvatureFirstBianchiData
        (metric_of_ricci_flow_data flow)) :
    HasFirstBianchiIdentity
      (metric_of_ricci_flow_data flow) :=
  hasFirstBianchiIdentity_of_firstBianchiData
    firstBianchiAtTime

/--
A first-Bianchi witness closes the first eight analytic package fields: the
five Levi-Civita fields, curvature construction, curvature symmetries, and the
first Bianchi identity.
-/
theorem analyticProductionPackage_firstEight_of_firstBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (firstBianchiAtTime :
      RiemannCurvatureFirstBianchiData
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) :=
  let firstSeven :=
    analyticProductionPackage_firstSeven_of_curvatureSymmetryData
      firstBianchiAtTime.curvatureSymmetryAtTime
  ⟨firstSeven.1, firstSeven.2.1, firstSeven.2.2.1,
    firstSeven.2.2.2.1, firstSeven.2.2.2.2.1,
    firstSeven.2.2.2.2.2.1, firstSeven.2.2.2.2.2.2,
    analyticProductionPackage_firstBianchi_of_firstBianchiData
      firstBianchiAtTime⟩

/--
Concrete second-Bianchi data constructs the ninth field stored by
`RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_secondBianchi_of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data flow)) :
    HasSecondBianchiIdentity
      (metric_of_ricci_flow_data flow) :=
  hasSecondBianchiIdentity_of_secondBianchiData
    secondBianchiAtTime

/--
Concrete second-Bianchi data also constructs the Riemann-curvature-theory field
stored after the two Bianchi identity fields.
-/
theorem analyticProductionPackage_riemannCurvatureTheory_of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data flow)) :
    HasRiemannCurvatureTensorTheory
      (metric_of_ricci_flow_data flow) :=
  hasRiemannCurvatureTensorTheory_of_secondBianchiData
    secondBianchiAtTime

/--
A second-Bianchi witness closes the first ten analytic package fields: the five
Levi-Civita fields, curvature construction, curvature symmetries, both Bianchi
identities, and Riemann-curvature tensor theory.
-/
theorem analyticProductionPackage_firstTen_of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) :=
  riemannCurvatureFirstTen_of_secondBianchiData
    secondBianchiAtTime

/--
Concrete Ricci contraction-formula data constructs the eleventh field stored by
`RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_ricciTensorContractionFormula_of_contractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    RicciTensorContractionFormulaData curvature →
      HasRicciTensorContractionFormula curvature :=
  hasRicciTensorContractionFormula_of_contractionFormulaData

/--
Concrete Ricci contraction-formula data closes the first eleven analytic
package fields.
-/
theorem analyticProductionPackage_firstEleven_of_contractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciContractionFormulaAtTime :
      RicciTensorContractionFormulaData
        (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) :=
  riemannCurvatureFirstEleven_of_ricciContractionFormulaData
    ricciContractionFormulaAtTime

/--
Concrete scalar-curvature contraction-formula data constructs the twelfth field
stored by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_scalarCurvatureContractionFormula_of_contractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    ScalarCurvatureContractionFormulaData curvature →
      HasScalarCurvatureContractionFormula curvature :=
  hasScalarCurvatureContractionFormula_of_contractionFormulaData

/--
Concrete scalar-curvature contraction-formula data closes the first twelve
analytic package fields.
-/
theorem analyticProductionPackage_firstTwelve_of_scalarContractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarContractionFormulaAtTime :
      ScalarCurvatureContractionFormulaData
        (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) :=
  riemannCurvatureFirstTwelve_of_scalarContractionFormulaData
    scalarContractionFormulaAtTime

/--
Concrete Ricci contraction-theory data constructs the thirteenth field stored
by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_ricciContractionTheory_of_contractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    RicciContractionTheoryData curvature →
      HasRicciContractionTheory curvature :=
  hasRicciContractionTheory_of_contractionTheoryData

/--
Concrete Ricci contraction-theory data closes the first thirteen analytic
package fields.
-/
theorem analyticProductionPackage_firstThirteen_of_ricciContractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData
        (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) :=
  riemannCurvatureFirstThirteen_of_ricciContractionTheoryData
    ricciContractionTheoryAtTime

/--
The production time-dependent metric itself constructs the fourteenth field
stored by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_timeDependentMetricRegularity_of_metric
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    HasTimeDependentMetricRegularity g :=
  hasTimeDependentMetricRegularity_of_metric g

/--
Concrete Ricci contraction-theory data, together with the production metric
family, closes the first fourteen analytic package fields.
-/
theorem analyticProductionPackage_firstFourteen_of_ricciContractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData
        (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) :=
  analyticFirstFourteen_of_ricciContractionTheoryData
    ricciContractionTheoryAtTime

/--
Concrete metric time-derivative data constructs the fifteenth field stored by
`RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_metricTimeDerivativeTheory_of_metricTimeDerivativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricTimeDerivativeAtTime : MetricTimeDerivativeData g) :
    HasMetricTimeDerivativeTheory g :=
  hasMetricTimeDerivativeTheory_of_metricTimeDerivativeData
    metricTimeDerivativeAtTime

/--
Concrete metric time-derivative data, together with Ricci contraction-theory
data, closes the first fifteen analytic package fields.
-/
theorem analyticProductionPackage_firstFifteen_of_metricTimeDerivativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (metricTimeDerivativeAtTime :
      MetricTimeDerivativeData (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) :=
  analyticFirstFifteen_of_metricTimeDerivativeData
    ricciContractionTheoryAtTime metricTimeDerivativeAtTime

/--
Concrete scalar-curvature theory data constructs the sixteenth analytic package
field stored by `RicciFlowAnalyticFoundationPackage`.
-/
theorem analyticProductionPackage_scalarCurvatureTheory_of_scalarCurvatureTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow)) :
    HasScalarCurvatureTheory
      (curvature_data_of_ricci_flow_data flow) :=
  hasScalarCurvatureTheory_of_scalarCurvatureTheoryData
    scalarCurvatureTheoryAtTime

/--
Scalar-curvature theory data, together with explicit metric time-derivative
data, closes the first sixteen analytic package fields.
-/
theorem analyticProductionPackage_firstSixteen_of_scalarCurvatureTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (metricTimeDerivativeAtTime :
      MetricTimeDerivativeData (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) :=
  analyticFirstSixteen_of_scalarCurvatureTheoryData
    scalarCurvatureTheoryAtTime metricTimeDerivativeAtTime

/--
Concrete Ricci-flow equation verification constructs the seventeenth analytic
package field: derivation of the Ricci-flow equation.
-/
theorem analyticProductionPackage_equationDerivation_of_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    HasRicciFlowEquationDerivation flow :=
  hasRicciFlowEquationDerivation_of_ricciFlowEquationVerification
    equationVerificationAtTime

/--
Scalar-curvature theory data and Ricci-flow equation verification close the
first seventeen analytic package fields.
-/
theorem analyticProductionPackage_firstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow :=
  analyticFirstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime

/--
The time-zero metric slice stored by `RicciFlowData` constructs the eighteenth
analytic package field: initial-metric compatibility.
-/
theorem analyticProductionPackage_initialMetricCompatibility_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    HasInitialMetricCompatibility flow :=
  hasInitialMetricCompatibility_of_flow flow

/--
Scalar-curvature theory data and Ricci-flow equation verification close the
first eighteen analytic package fields.
-/
theorem analyticProductionPackage_firstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow :=
  analyticFirstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime

/--
The time-zero metric slice stored by `RicciFlowData` supplies DeTurck
gauge-fixing input via the canonical DeTurck background metric.
-/
theorem analyticProductionPackage_deturckGaugeFixing_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    HasDeTurckGaugeFixing flow :=
  hasDeTurckGaugeFixing_of_flow flow

/--
The same canonical background metric proves DeTurck background-metric
compatibility.
-/
theorem analyticProductionPackage_deturckBackgroundMetricCompatibility_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    HasDeTurckBackgroundMetricCompatibility flow :=
  hasDeTurckBackgroundMetricCompatibility_of_flow flow

/--
Scalar-curvature theory data and Ricci-flow equation verification close the
first nineteen analytic package fields through DeTurck gauge fixing.
-/
theorem analyticProductionPackage_firstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    (HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow :=
  analyticFirstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime

/--
Scalar-curvature theory data and Ricci-flow equation verification close the
first twenty analytic package fields through DeTurck background compatibility.
-/
theorem analyticProductionPackage_firstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    ((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow :=
  analyticFirstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime

/--
Concrete connection-difference trace data proves DeTurck vector-field
construction.
-/
theorem analyticProductionPackage_deturckVectorFieldConstruction_of_vectorFieldConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow) :
    HasDeTurckVectorFieldConstruction flow :=
  hasDeTurckVectorFieldConstruction_of_vectorFieldConstructionData
    vectorFieldAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, and DeTurck
vector-field construction data close the first twenty-one analytic package
fields.
-/
theorem analyticProductionPackage_firstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow) :
    (((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow :=
  analyticFirstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime

/--
Concrete Ricci-DeTurck equation data proves the DeTurck equation-derivation
interface.
-/
theorem analyticProductionPackage_deturckEquationDerivation_of_ricciDeTurckEquationDerivationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (equationAtTime : RicciDeTurckEquationDerivationData flow) :
    HasDeTurckEquationDerivation flow :=
  hasDeTurckEquationDerivation_of_ricciDeTurckEquationDerivationData
    equationAtTime

/--
After scalar-curvature theory data, equation verification, and DeTurck
vector-field construction data, Ricci-DeTurck equation data closes the first
twenty-two analytic package fields.
-/
theorem analyticProductionPackage_firstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow) :
    ((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow :=
  analyticFirstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime

/--
Concrete Ricci-DeTurck linearization data proves the linearization interface.
-/
theorem analyticProductionPackage_ricciDeTurckLinearization_of_ricciDeTurckLinearizationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (linearizationAtTime : RicciDeTurckLinearizationData flow) :
    HasRicciDeTurckLinearization flow :=
  hasRicciDeTurckLinearization_of_ricciDeTurckLinearizationData
    linearizationAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, and Ricci-DeTurck
linearization data close the first twenty-three analytic package fields.
-/
theorem analyticProductionPackage_firstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow) :
    (((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow :=
  analyticFirstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime

/--
Concrete principal-symbol data proves strict parabolicity of the DeTurck system.
-/
theorem analyticProductionPackage_strictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow) :
    HasStrictlyParabolicDeTurckSystem flow :=
  hasStrictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData
    strictParabolicAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, and Ricci-DeTurck
linearization data, strict-parabolicity data closes the first twenty-four
analytic package fields.
-/
theorem analyticProductionPackage_firstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow) :
    ((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow :=
  analyticFirstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime

/--
Concrete solution-operator data proves linear parabolic theory for the DeTurck
system.
-/
theorem analyticProductionPackage_parabolicLinearTheory_of_parabolicLinearTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (linearTheoryAtTime : ParabolicLinearTheoryData flow) :
    HasParabolicLinearTheory flow :=
  hasParabolicLinearTheory_of_parabolicLinearTheoryData
    linearTheoryAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, and linear parabolic theory data close the first
twenty-five analytic package fields.
-/
theorem analyticProductionPackage_firstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow) :
    (((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow :=
  analyticFirstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime

/--
Concrete contraction data proves the nonlinear DeTurck fixed-point argument.
-/
theorem analyticProductionPackage_parabolicFixedPointArgument_of_parabolicFixedPointArgumentData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow) :
    HasParabolicFixedPointArgument flow :=
  hasParabolicFixedPointArgument_of_parabolicFixedPointArgumentData
    fixedPointAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, and linear parabolic theory data close the first
twenty-six analytic package fields.
-/
theorem analyticProductionPackage_firstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow) :
    ((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow :=
  analyticFirstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime

/--
Concrete positive-time solution data proves the production short-time
Ricci-DeTurck existence field.
-/
theorem analyticProductionPackage_deturckShortTimeExistence_of_deturckShortTimeExistenceData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow) :
    HasDeTurckShortTimeExistence flow :=
  hasDeTurckShortTimeExistence_of_deturckShortTimeExistenceData
    shortTimeAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field data,
Ricci-DeTurck equation data, linearization data, strict-parabolicity data,
linear theory data, fixed-point data, and positive-time solution data close the
first twenty-seven production analytic fields.
-/
theorem analyticProductionPackage_firstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow) :
    (((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow :=
  analyticFirstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime

/--
Concrete short-time regularity data proves the production regularity-bootstrap
field.
-/
theorem analyticProductionPackage_shortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow) :
    HasShortTimeRegularityBootstrap flow :=
  hasShortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData
    regularityAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field data,
Ricci-DeTurck equation data, linearization data, strict-parabolicity data,
linear theory data, fixed-point data, positive-time solution data, and
regularity-bootstrap data close the first twenty-eight production analytic
fields.
-/
theorem analyticProductionPackage_firstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow) :
    ((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow :=
  analyticFirstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime

/--
Concrete diffeomorphism-flow data proves the production DeTurck ODE field.
-/
theorem analyticProductionPackage_deturckDiffeomorphismODE_of_deturckDiffeomorphismODEData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (odeAtTime : DeTurckDiffeomorphismODEData flow) :
    HasDeTurckDiffeomorphismODE flow :=
  hasDeTurckDiffeomorphismODE_of_deturckDiffeomorphismODEData
    odeAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field data,
Ricci-DeTurck equation data, linearization data, strict-parabolicity data,
linear theory data, fixed-point data, positive-time solution data,
regularity-bootstrap data, and diffeomorphism-flow data close the first
twenty-nine production analytic fields.
-/
theorem analyticProductionPackage_firstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow) :
    (((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow :=
  analyticFirstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime

/--
Concrete pulled-back metric/RHS identity data proves the production DeTurck
pullback equation-identity field.
-/
theorem analyticProductionPackage_deturckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasDeTurckPullbackEquationIdentity flow :=
  hasDeTurckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData
    pullbackIdentityAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field data,
Ricci-DeTurck equation data, linearization data, strict-parabolicity data,
linear theory data, fixed-point data, positive-time solution data,
regularity-bootstrap data, diffeomorphism-flow data, and pullback equation
identity data close the first thirty production analytic fields.
-/
theorem analyticProductionPackage_firstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow :=
  analyticFirstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete pullback-to-Ricci-flow data proves the production pullback field.
-/
theorem analyticProductionPackage_deturckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow) :
    HasDeTurckPullbackToRicciFlow flow :=
  hasDeTurckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData
    pullbackToRicciFlowAtTime

/--
Pullback equation identity data carries enough metric/RHS identities to prove
the production pullback-to-Ricci-flow field.
-/
theorem analyticProductionPackage_deturckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasDeTurckPullbackToRicciFlow flow :=
  hasDeTurckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData
    pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-one analytic
package fields.
-/
theorem analyticProductionPackage_firstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow :=
  analyticFirstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete short-time Ricci-flow solution data proves the production short-time
solution field.
-/
theorem analyticProductionPackage_shortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow) :
    HasShortTimeRicciFlowSolution flow :=
  hasShortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData
    shortTimeRicciAtTime

/--
Pullback-to-Ricci-flow data carries the positive interval and metric/RHS
identities needed for the production short-time Ricci-flow solution field.
-/
theorem analyticProductionPackage_shortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow) :
    HasShortTimeRicciFlowSolution flow :=
  hasShortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData
    pullbackToRicciFlowAtTime

/--
Pullback equation identity data builds the DeTurck pullback-to-Ricci-flow data
and hence the production short-time Ricci-flow solution field.
-/
theorem analyticProductionPackage_shortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasShortTimeRicciFlowSolution flow :=
  hasShortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData
    pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-two production
analytic fields.
-/
theorem analyticProductionPackage_firstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow :=
  analyticFirstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete maximal-time interval data proves the production maximal interval
field.
-/
theorem analyticProductionPackage_ricciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow) :
    HasRicciFlowMaximalTimeInterval flow :=
  hasRicciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData
    maximalIntervalAtTime

/--
Short-time Ricci-flow solution data carries the positive endpoint needed for
the production maximal-time interval field.
-/
theorem analyticProductionPackage_ricciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow) :
    HasRicciFlowMaximalTimeInterval flow :=
  hasRicciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData
    shortTimeRicciAtTime

/--
Pullback equation identity data builds the pullback/short-time data and hence
the production maximal-time interval field.
-/
theorem analyticProductionPackage_ricciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasRicciFlowMaximalTimeInterval flow :=
  hasRicciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData
    pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-three
production analytic fields.
-/
theorem analyticProductionPackage_firstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow :=
  analyticFirstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete continuation-criterion data proves the production continuation
field.
-/
theorem analyticProductionPackage_ricciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (continuationCriterionAtTime :
      RicciFlowContinuationCriterionData flow) :
    HasRicciFlowContinuationCriterion flow :=
  hasRicciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData
    continuationCriterionAtTime

/--
Maximal-interval data, scalar-curvature theory, and Ricci-flow equation
verification prove the production continuation field.
-/
theorem analyticProductionPackage_ricciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow) :
    HasRicciFlowContinuationCriterion flow :=
  hasRicciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData
    scalarCurvatureTheoryAtTime equationVerificationAtTime
    maximalIntervalAtTime

/--
Pullback equation identity data builds the interval data needed for the
production continuation field.
-/
theorem analyticProductionPackage_ricciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasRicciFlowContinuationCriterion flow :=
  hasRicciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData
    scalarCurvatureTheoryAtTime equationVerificationAtTime
    pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-four
production analytic fields.
-/
theorem analyticProductionPackage_firstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow :=
  analyticFirstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete curvature blow-up data proves the production blow-up continuation
criterion field.
-/
theorem analyticProductionPackage_curvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow) :
    HasCurvatureBlowUpContinuationCriterion flow :=
  hasCurvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData
    curvatureBlowUpAtTime

/--
Continuation-criterion data carries the flow curvature data needed for the
production curvature blow-up alternative field.
-/
theorem analyticProductionPackage_curvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (continuationCriterionAtTime :
      RicciFlowContinuationCriterionData flow) :
    HasCurvatureBlowUpContinuationCriterion flow :=
  hasCurvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData
    continuationCriterionAtTime

/--
Pullback equation identity data builds the continuation criterion and hence the
production curvature blow-up alternative field.
-/
theorem analyticProductionPackage_curvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasCurvatureBlowUpContinuationCriterion flow :=
  hasCurvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData
    scalarCurvatureTheoryAtTime equationVerificationAtTime
    pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-five
production analytic fields.
-/
theorem analyticProductionPackage_firstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow :=
  analyticFirstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete maximal-solution extension data proves the production extension
field.
-/
theorem analyticProductionPackage_maximalSolutionExtension_of_maximalSolutionExtensionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (extensionAtTime : MaximalSolutionExtensionData flow) :
    HasMaximalSolutionExtension flow :=
  hasMaximalSolutionExtension_of_maximalSolutionExtensionData
    extensionAtTime

/--
Curvature blow-up alternative data carries the endpoint and curvature data
needed for the production maximal-solution extension field.
-/
theorem analyticProductionPackage_maximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow) :
    HasMaximalSolutionExtension flow :=
  hasMaximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData
    curvatureBlowUpAtTime

/--
Pullback equation identity data builds the curvature blow-up data and hence the
production maximal-solution extension field.
-/
theorem analyticProductionPackage_maximalSolutionExtension_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasMaximalSolutionExtension flow :=
  hasMaximalSolutionExtension_of_deturckPullbackEquationIdentityData
    scalarCurvatureTheoryAtTime equationVerificationAtTime
    pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-six production
analytic fields.
-/
theorem analyticProductionPackage_firstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow :=
  analyticFirstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete parabolic Schauder estimate data proves the production Schauder field.
-/
theorem analyticProductionPackage_parabolicSchauderEstimates_of_parabolicSchauderEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (schauderAtTime : ParabolicSchauderEstimateData flow) :
    HasParabolicSchauderEstimates flow :=
  hasParabolicSchauderEstimates_of_parabolicSchauderEstimateData
    schauderAtTime

/--
Short-time regularity bootstrap data and maximal-solution extension data carry
the linear and higher-order estimate witnesses needed for the production
Schauder field.
-/
theorem analyticProductionPackage_parabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (maximalExtensionAtTime : MaximalSolutionExtensionData flow) :
    HasParabolicSchauderEstimates flow :=
  hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData
    regularityAtTime maximalExtensionAtTime

/--
Pullback equation identity data builds the continuation/maximal-extension layer,
and short-time regularity data supplies the Schauder estimate constants.
-/
theorem analyticProductionPackage_parabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasParabolicSchauderEstimates flow :=
  hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData
    scalarCurvatureTheoryAtTime equationVerificationAtTime
    regularityAtTime pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-seven
production analytic fields.
-/
theorem analyticProductionPackage_firstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow :=
  analyticFirstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Concrete Ricci-flow parabolic regularity data proves the production regularity
field.
-/
theorem analyticProductionPackage_ricciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : RicciFlowParabolicRegularityData flow) :
    HasRicciFlowParabolicRegularity flow :=
  hasRicciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData
    regularityAtTime

/--
Parabolic Schauder estimate data carries the flow-gauge metric and inherited
linear/bootstrap estimates needed for the production Ricci-flow parabolic
regularity field.
-/
theorem analyticProductionPackage_ricciFlowParabolicRegularity_of_parabolicSchauderEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (schauderAtTime : ParabolicSchauderEstimateData flow) :
    HasRicciFlowParabolicRegularity flow :=
  hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimateData
    schauderAtTime

/--
Any concrete Schauder-estimate witness carries enough data to prove the
production Ricci-flow parabolic regularity field.
-/
theorem analyticProductionPackage_ricciFlowParabolicRegularity_of_parabolicSchauderEstimates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (schauderAtTime : HasParabolicSchauderEstimates flow) :
    HasRicciFlowParabolicRegularity flow :=
  hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates
    schauderAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-eight
production analytic fields.
-/
theorem analyticProductionPackage_firstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow :=
  analyticFirstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data close the first thirty-nine
production analytic fields.
-/
theorem analyticProductionPackage_firstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow :=
  analyticFirstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data now close the first forty analytic
fields, through curvature-derivative bootstrap.
-/
theorem analyticProductionPackage_firstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow :=
  analyticFirstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, and pullback equation identity data now close the first forty-one analytic
fields, through Hamilton's maximum principle.
-/
theorem analyticProductionPackage_firstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow :=
  analyticFirstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, pullback equation identity data, and an initial-metric uniqueness theorem
now close the first forty-two analytic fields, through Ricci-flow uniqueness.
-/
theorem analyticProductionPackage_firstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow) :
    ((((((((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow :=
  analyticFirstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime uniquenessByInitialMetric

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, pullback equation identity data, and an initial-metric uniqueness theorem
now close the first forty-three analytic fields, through the metric evolution
equation.
-/
theorem analyticProductionPackage_firstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow) :
    (((((((((((((((((((((((((HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow :=
  analyticFirstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime uniquenessByInitialMetric

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, pullback equation identity data, an initial-metric uniqueness theorem,
and concrete Ricci tensor evolution-equation data close the first forty-four
analytic package fields.
-/
theorem analyticProductionPackage_firstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t) :
    ((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow :=
  analyticFirstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime uniquenessByInitialMetric
    ricciTensorDerivativeAtTime ricciTensorEvolutionRHSAtTime
    ricciTensorEvolutionAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, pullback equation identity data, an initial-metric uniqueness theorem,
concrete Ricci tensor evolution-equation data, and concrete scalar curvature
evolution-equation data close the first forty-five analytic package fields.
-/
theorem analyticProductionPackage_firstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t) :
    (((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow) ∧
      HasScalarCurvatureEvolutionEquation flow :=
  analyticFirstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime uniquenessByInitialMetric
    ricciTensorDerivativeAtTime ricciTensorEvolutionRHSAtTime
    ricciTensorEvolutionAtTime scalarCurvatureDerivativeAtTime
    scalarCurvatureEvolutionRHSAtTime scalarCurvatureEvolutionAtTime

/--
Scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, pullback equation identity data, an initial-metric uniqueness theorem,
concrete Ricci/scalar evolution data, and concrete curvature-norm inequality
data close the first forty-six analytic package fields.
-/
theorem analyticProductionPackage_firstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t)
    (curvatureNormAtTime : ℝ → M → ℝ)
    (curvatureNorm_nonnegativeAtTime :
      ∀ (t : ℝ) (x : M), 0 ≤ curvatureNormAtTime t x)
    (curvatureNormDerivativeAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionRHSAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionInequalityAtTime :
      ∀ (t : ℝ) (x : M),
        curvatureNormDerivativeAtTime t x ≤
          curvatureNormEvolutionRHSAtTime t x) :
    ((((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow) ∧
      HasScalarCurvatureEvolutionEquation flow) ∧
      HasCurvatureNormEvolutionInequality flow :=
  analyticFirstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime uniquenessByInitialMetric
    ricciTensorDerivativeAtTime ricciTensorEvolutionRHSAtTime
    ricciTensorEvolutionAtTime scalarCurvatureDerivativeAtTime
    scalarCurvatureEvolutionRHSAtTime scalarCurvatureEvolutionAtTime
    curvatureNormAtTime curvatureNorm_nonnegativeAtTime
    curvatureNormDerivativeAtTime curvatureNormEvolutionRHSAtTime
    curvatureNormEvolutionInequalityAtTime

/--
After scalar-curvature theory data, equation verification, DeTurck vector-field
construction data, Ricci-DeTurck equation data, Ricci-DeTurck linearization
data, strict-parabolicity data, linear parabolic theory data, fixed-point data,
positive-time solution data, regularity-bootstrap data, diffeomorphism-flow
data, pullback equation identity data, an initial-metric uniqueness theorem,
concrete Ricci/scalar/norm evolution data, and concrete Riemann curvature
evolution data are supplied, all explicit `Has*` fields of the analytic
foundation package are available.
-/
theorem analyticProductionPackage_firstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t)
    (curvatureNormAtTime : ℝ → M → ℝ)
    (curvatureNorm_nonnegativeAtTime :
      ∀ (t : ℝ) (x : M), 0 ≤ curvatureNormAtTime t x)
    (curvatureNormDerivativeAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionRHSAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionInequalityAtTime :
      ∀ (t : ℝ) (x : M),
        curvatureNormDerivativeAtTime t x ≤
          curvatureNormEvolutionRHSAtTime t x)
    (riemannSecondBianchiAtTime :
      RiemannCurvatureSecondBianchiData (metric_of_ricci_flow_data flow))
    (riemannCurvatureDerivativeAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionRHSAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionAtTime :
      ∀ t,
        riemannCurvatureDerivativeAtTime t =
          riemannCurvatureEvolutionRHSAtTime t) :
    (((((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow) ∧
      HasScalarCurvatureEvolutionEquation flow) ∧
      HasCurvatureNormEvolutionInequality flow) ∧
      HasCurvatureEvolutionEquations flow :=
  analyticFirstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    scalarCurvatureTheoryAtTime equationVerificationAtTime vectorFieldAtTime
    ricciDeTurckEquationAtTime linearizationAtTime strictParabolicAtTime
    linearTheoryAtTime fixedPointAtTime shortTimeAtTime regularityAtTime
    odeAtTime pullbackIdentityAtTime uniquenessByInitialMetric
    ricciTensorDerivativeAtTime ricciTensorEvolutionRHSAtTime
    ricciTensorEvolutionAtTime scalarCurvatureDerivativeAtTime
    scalarCurvatureEvolutionRHSAtTime scalarCurvatureEvolutionAtTime
    curvatureNormAtTime curvatureNorm_nonnegativeAtTime
    curvatureNormDerivativeAtTime curvatureNormEvolutionRHSAtTime
    curvatureNormEvolutionInequalityAtTime riemannSecondBianchiAtTime
    riemannCurvatureDerivativeAtTime riemannCurvatureEvolutionRHSAtTime
    riemannCurvatureEvolutionAtTime

/--
A completed analytic-foundation package selects one Ricci-flow datum and keeps
the named analytic sub-obligation payload, Ricci-flow equation evidence, the
Levi-Civita input fields, and the terminal curvature-evolution fields tied to
that same selected flow.
-/
theorem analyticProductionPackage_selected_payload_leviCivita_and_terminal_curvature_fields
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        AnalyticFoundationSubobligationsPayload flow ∧
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionUniqueness
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaTorsionFreeProperty
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaMetricCompatibility
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionTheory
          (metric_of_ricci_flow_data flow) ∧
        HasCurvatureNormEvolutionInequality flow ∧
        HasCurvatureEvolutionEquations flow := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  rcases analytic_foundation_payload_of_analytic_foundation_package
      package with
    ⟨ _statement, _derivationStatement, subobligations, equationEvidence⟩
  exact
    ⟨ flow
    , rfl
    , subobligations
    , equationEvidence
    , levi_civita_existence_of_analytic_foundation_package package
    , levi_civita_uniqueness_of_analytic_foundation_package package
    , levi_civita_torsion_free_of_analytic_foundation_package package
    , levi_civita_metric_compatibility_of_analytic_foundation_package
        package
    , levi_civita_theory_of_analytic_foundation_package package
    , curvature_norm_evolution_inequality_of_analytic_foundation_package
        package
    , curvature_evolution_of_analytic_foundation_package package
    ⟩

/--
A completed analytic-foundation package also keeps the selected Ricci-flow
datum tied to the DeTurck construction route, the pulled-back short-time Ricci
flow solution, and the continuation criterion.  This records the analytic
middle of the package separately from the Levi-Civita and terminal curvature
field endpoint above.
-/
theorem analyticProductionPackage_selected_payload_deturck_shortTime_and_continuation_fields
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        AnalyticFoundationSubobligationsPayload flow ∧
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow) ∧
        HasRicciFlowEquationDerivation flow ∧
        HasInitialMetricCompatibility flow ∧
        HasDeTurckGaugeFixing flow ∧
        HasDeTurckBackgroundMetricCompatibility flow ∧
        HasDeTurckVectorFieldConstruction flow ∧
        HasDeTurckEquationDerivation flow ∧
        HasRicciDeTurckLinearization flow ∧
        HasStrictlyParabolicDeTurckSystem flow ∧
        HasParabolicLinearTheory flow ∧
        HasParabolicFixedPointArgument flow ∧
        HasDeTurckShortTimeExistence flow ∧
        HasShortTimeRegularityBootstrap flow ∧
        HasDeTurckDiffeomorphismODE flow ∧
        HasDeTurckPullbackEquationIdentity flow ∧
        HasDeTurckPullbackToRicciFlow flow ∧
        HasShortTimeRicciFlowSolution flow ∧
        HasRicciFlowMaximalTimeInterval flow ∧
        HasRicciFlowContinuationCriterion flow := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  rcases analytic_foundation_payload_of_analytic_foundation_package
      package with
    ⟨ _statement, _derivationStatement, subobligations, equationEvidence⟩
  exact
    ⟨ flow
    , rfl
    , subobligations
    , equationEvidence
    , equation_derivation_of_analytic_foundation_package package
    , initial_metric_compatibility_of_analytic_foundation_package package
    , deturck_gauge_fixing_of_analytic_foundation_package package
    , deturck_background_metric_compatibility_of_analytic_foundation_package
        package
    , deturck_vector_field_construction_of_analytic_foundation_package
        package
    , deturck_equation_derivation_of_analytic_foundation_package package
    , ricci_deturck_linearization_of_analytic_foundation_package package
    , strictly_parabolic_deturck_of_analytic_foundation_package package
    , parabolic_linear_theory_of_analytic_foundation_package package
    , parabolic_fixed_point_argument_of_analytic_foundation_package package
    , deturck_short_time_existence_of_analytic_foundation_package package
    , short_time_regularity_bootstrap_of_analytic_foundation_package package
    , deturck_diffeomorphism_ode_of_analytic_foundation_package package
    , deturck_pullback_equation_identity_of_analytic_foundation_package
        package
    , deturck_pullback_to_ricci_flow_of_analytic_foundation_package package
    , short_time_existence_of_analytic_foundation_package package
    , maximal_time_interval_of_analytic_foundation_package package
    , continuation_criterion_of_analytic_foundation_package package
    ⟩

/--
A completed analytic-foundation package keeps the selected Ricci-flow datum
tied to the continuation/regularity layer and the metric/Ricci/scalar
evolution fields that feed the finite-extinction curvature estimates.
-/
theorem analyticProductionPackage_selected_payload_regularization_and_evolution_fields
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        AnalyticFoundationSubobligationsPayload flow ∧
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow) ∧
        HasCurvatureBlowUpContinuationCriterion flow ∧
        HasMaximalSolutionExtension flow ∧
        HasParabolicSchauderEstimates flow ∧
        HasRicciFlowParabolicRegularity flow ∧
        HasShiDerivativeEstimates flow ∧
        HasCurvatureDerivativeBootstrap flow ∧
        HasHamiltonMaximumPrinciple flow ∧
        HasRicciFlowUniquenessTheory flow ∧
        HasMetricEvolutionEquation flow ∧
        HasRicciTensorEvolutionEquation flow ∧
        HasScalarCurvatureEvolutionEquation flow ∧
        HasCurvatureNormEvolutionInequality flow ∧
        HasCurvatureEvolutionEquations flow := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  rcases analytic_foundation_payload_of_analytic_foundation_package
      package with
    ⟨ _statement, _derivationStatement, subobligations, equationEvidence⟩
  exact
    ⟨ flow
    , rfl
    , subobligations
    , equationEvidence
    , curvature_blowup_criterion_of_analytic_foundation_package package
    , maximal_solution_extension_of_analytic_foundation_package package
    , parabolic_schauder_estimates_of_analytic_foundation_package package
    , parabolic_regularity_of_analytic_foundation_package package
    , shi_derivative_estimates_of_analytic_foundation_package package
    , curvature_derivative_bootstrap_of_analytic_foundation_package package
    , hamilton_maximum_principle_of_analytic_foundation_package package
    , uniqueness_theory_of_analytic_foundation_package package
    , metric_evolution_equation_of_analytic_foundation_package package
    , ricci_tensor_evolution_equation_of_analytic_foundation_package package
    , scalar_curvature_evolution_equation_of_analytic_foundation_package
        package
    , curvature_norm_evolution_inequality_of_analytic_foundation_package
        package
    , curvature_evolution_of_analytic_foundation_package package
    ⟩

/--
A completed analytic-foundation package keeps the pulled-back short-time Ricci
flow route, continuation criterion, regularization layer, and terminal
curvature-evolution estimates tied to one selected Ricci-flow datum.  This is
the finite-extinction-facing analytic endpoint: consumers get the short-time
solution and the curvature-control fields from the same completed package.
-/
theorem analyticProductionPackage_selected_payload_shortTime_regularization_and_evolution_fields
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        AnalyticFoundationSubobligationsPayload flow ∧
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow) ∧
        HasDeTurckPullbackToRicciFlow flow ∧
        HasShortTimeRicciFlowSolution flow ∧
        HasRicciFlowMaximalTimeInterval flow ∧
        HasRicciFlowContinuationCriterion flow ∧
        HasCurvatureBlowUpContinuationCriterion flow ∧
        HasMaximalSolutionExtension flow ∧
        HasParabolicSchauderEstimates flow ∧
        HasRicciFlowParabolicRegularity flow ∧
        HasShiDerivativeEstimates flow ∧
        HasCurvatureDerivativeBootstrap flow ∧
        HasHamiltonMaximumPrinciple flow ∧
        HasRicciFlowUniquenessTheory flow ∧
        HasMetricEvolutionEquation flow ∧
        HasRicciTensorEvolutionEquation flow ∧
        HasScalarCurvatureEvolutionEquation flow ∧
        HasCurvatureNormEvolutionInequality flow ∧
        HasCurvatureEvolutionEquations flow := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  rcases analytic_foundation_payload_of_analytic_foundation_package
      package with
    ⟨ _statement, _derivationStatement, subobligations, equationEvidence⟩
  exact
    ⟨ flow
    , rfl
    , subobligations
    , equationEvidence
    , deturck_pullback_to_ricci_flow_of_analytic_foundation_package package
    , short_time_existence_of_analytic_foundation_package package
    , maximal_time_interval_of_analytic_foundation_package package
    , continuation_criterion_of_analytic_foundation_package package
    , curvature_blowup_criterion_of_analytic_foundation_package package
    , maximal_solution_extension_of_analytic_foundation_package package
    , parabolic_schauder_estimates_of_analytic_foundation_package package
    , parabolic_regularity_of_analytic_foundation_package package
    , shi_derivative_estimates_of_analytic_foundation_package package
    , curvature_derivative_bootstrap_of_analytic_foundation_package package
    , hamilton_maximum_principle_of_analytic_foundation_package package
    , uniqueness_theory_of_analytic_foundation_package package
    , metric_evolution_equation_of_analytic_foundation_package package
    , ricci_tensor_evolution_equation_of_analytic_foundation_package package
    , scalar_curvature_evolution_equation_of_analytic_foundation_package
        package
    , curvature_norm_evolution_inequality_of_analytic_foundation_package
        package
    , curvature_evolution_of_analytic_foundation_package package
    ⟩

/--
A completed analytic-foundation package selects one Ricci-flow datum and keeps
the full theorem-facing analytic route on that same flow: the named
sub-obligation payload, Ricci-flow equation evidence, Levi-Civita foundation,
DeTurck short-time route, continuation/regularization layer, and terminal
curvature-evolution fields.  This is the unified endpoint for downstream
finite-extinction consumers that need the analytic package as one synchronized
selected-flow certificate.
-/
theorem analyticProductionPackage_selected_payload_full_foundation_to_curvature_fields
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        AnalyticFoundationSubobligationsPayload flow ∧
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionUniqueness
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaTorsionFreeProperty
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaMetricCompatibility
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionTheory
          (metric_of_ricci_flow_data flow) ∧
        HasRicciFlowEquationDerivation flow ∧
        HasInitialMetricCompatibility flow ∧
        HasDeTurckGaugeFixing flow ∧
        HasDeTurckBackgroundMetricCompatibility flow ∧
        HasDeTurckVectorFieldConstruction flow ∧
        HasDeTurckEquationDerivation flow ∧
        HasRicciDeTurckLinearization flow ∧
        HasStrictlyParabolicDeTurckSystem flow ∧
        HasParabolicLinearTheory flow ∧
        HasParabolicFixedPointArgument flow ∧
        HasDeTurckShortTimeExistence flow ∧
        HasShortTimeRegularityBootstrap flow ∧
        HasDeTurckDiffeomorphismODE flow ∧
        HasDeTurckPullbackEquationIdentity flow ∧
        HasDeTurckPullbackToRicciFlow flow ∧
        HasShortTimeRicciFlowSolution flow ∧
        HasRicciFlowMaximalTimeInterval flow ∧
        HasRicciFlowContinuationCriterion flow ∧
        HasCurvatureBlowUpContinuationCriterion flow ∧
        HasMaximalSolutionExtension flow ∧
        HasParabolicSchauderEstimates flow ∧
        HasRicciFlowParabolicRegularity flow ∧
        HasShiDerivativeEstimates flow ∧
        HasCurvatureDerivativeBootstrap flow ∧
        HasHamiltonMaximumPrinciple flow ∧
        HasRicciFlowUniquenessTheory flow ∧
        HasMetricEvolutionEquation flow ∧
        HasRicciTensorEvolutionEquation flow ∧
        HasScalarCurvatureEvolutionEquation flow ∧
        HasCurvatureNormEvolutionInequality flow ∧
        HasCurvatureEvolutionEquations flow := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  rcases analytic_foundation_payload_of_analytic_foundation_package
      package with
    ⟨ _statement, _derivationStatement, subobligations, equationEvidence⟩
  exact
    ⟨ flow
    , rfl
    , subobligations
    , equationEvidence
    , levi_civita_existence_of_analytic_foundation_package package
    , levi_civita_uniqueness_of_analytic_foundation_package package
    , levi_civita_torsion_free_of_analytic_foundation_package package
    , levi_civita_metric_compatibility_of_analytic_foundation_package
        package
    , levi_civita_theory_of_analytic_foundation_package package
    , equation_derivation_of_analytic_foundation_package package
    , initial_metric_compatibility_of_analytic_foundation_package package
    , deturck_gauge_fixing_of_analytic_foundation_package package
    , deturck_background_metric_compatibility_of_analytic_foundation_package
        package
    , deturck_vector_field_construction_of_analytic_foundation_package
        package
    , deturck_equation_derivation_of_analytic_foundation_package package
    , ricci_deturck_linearization_of_analytic_foundation_package package
    , strictly_parabolic_deturck_of_analytic_foundation_package package
    , parabolic_linear_theory_of_analytic_foundation_package package
    , parabolic_fixed_point_argument_of_analytic_foundation_package package
    , deturck_short_time_existence_of_analytic_foundation_package package
    , short_time_regularity_bootstrap_of_analytic_foundation_package package
    , deturck_diffeomorphism_ode_of_analytic_foundation_package package
    , deturck_pullback_equation_identity_of_analytic_foundation_package
        package
    , deturck_pullback_to_ricci_flow_of_analytic_foundation_package package
    , short_time_existence_of_analytic_foundation_package package
    , maximal_time_interval_of_analytic_foundation_package package
    , continuation_criterion_of_analytic_foundation_package package
    , curvature_blowup_criterion_of_analytic_foundation_package package
    , maximal_solution_extension_of_analytic_foundation_package package
    , parabolic_schauder_estimates_of_analytic_foundation_package package
    , parabolic_regularity_of_analytic_foundation_package package
    , shi_derivative_estimates_of_analytic_foundation_package package
    , curvature_derivative_bootstrap_of_analytic_foundation_package package
    , hamilton_maximum_principle_of_analytic_foundation_package package
    , uniqueness_theory_of_analytic_foundation_package package
    , metric_evolution_equation_of_analytic_foundation_package package
    , ricci_tensor_evolution_equation_of_analytic_foundation_package package
    , scalar_curvature_evolution_equation_of_analytic_foundation_package
        package
    , curvature_norm_evolution_inequality_of_analytic_foundation_package
        package
    , curvature_evolution_of_analytic_foundation_package package
    ⟩

/--
A completed analytic-foundation package also retains a concrete selected
time-dependent tangent connection field witnessing the Levi-Civita existence
surface.  This strengthens the unified selected-flow endpoint by keeping the
package-level analytic route synchronized with the actual connection-field
object consumed by lower-level analytic interfaces.
-/
theorem analyticProductionPackage_selected_connectionField_full_foundation_to_curvature_fields
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
    ∃ connectionAtTime :
      TimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow),
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        AnalyticFoundationSubobligationsPayload flow ∧
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow) ∧
        (∃ leviCivitaExistence :
          HasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data flow),
          leviCivitaExistence =
            hasLeviCivitaConnectionExistence_of_connectionField
              (g := metric_of_ricci_flow_data flow) connectionAtTime) ∧
        HasLeviCivitaConnectionUniqueness
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaTorsionFreeProperty
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaMetricCompatibility
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionTheory
          (metric_of_ricci_flow_data flow) ∧
        HasRicciFlowEquationDerivation flow ∧
        HasInitialMetricCompatibility flow ∧
        HasDeTurckGaugeFixing flow ∧
        HasDeTurckBackgroundMetricCompatibility flow ∧
        HasDeTurckVectorFieldConstruction flow ∧
        HasDeTurckEquationDerivation flow ∧
        HasRicciDeTurckLinearization flow ∧
        HasStrictlyParabolicDeTurckSystem flow ∧
        HasParabolicLinearTheory flow ∧
        HasParabolicFixedPointArgument flow ∧
        HasDeTurckShortTimeExistence flow ∧
        HasShortTimeRegularityBootstrap flow ∧
        HasDeTurckDiffeomorphismODE flow ∧
        HasDeTurckPullbackEquationIdentity flow ∧
        HasDeTurckPullbackToRicciFlow flow ∧
        HasShortTimeRicciFlowSolution flow ∧
        HasRicciFlowMaximalTimeInterval flow ∧
        HasRicciFlowContinuationCriterion flow ∧
        HasCurvatureBlowUpContinuationCriterion flow ∧
        HasMaximalSolutionExtension flow ∧
        HasParabolicSchauderEstimates flow ∧
        HasRicciFlowParabolicRegularity flow ∧
        HasShiDerivativeEstimates flow ∧
        HasCurvatureDerivativeBootstrap flow ∧
        HasHamiltonMaximumPrinciple flow ∧
        HasRicciFlowUniquenessTheory flow ∧
        HasMetricEvolutionEquation flow ∧
        HasRicciTensorEvolutionEquation flow ∧
        HasScalarCurvatureEvolutionEquation flow ∧
        HasCurvatureNormEvolutionInequality flow ∧
        HasCurvatureEvolutionEquations flow := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  have connectionField :
      Nonempty
        (TimeDependentTangentConnectionField
          (metric_of_ricci_flow_data flow)) :=
    (hasLeviCivitaConnectionExistence_iff_connectionField_nonempty
      (metric_of_ricci_flow_data flow)).1
        (levi_civita_existence_of_analytic_foundation_package package)
  rcases connectionField with ⟨connectionAtTime⟩
  rcases analytic_foundation_payload_of_analytic_foundation_package
      package with
    ⟨ _statement, _derivationStatement, subobligations, equationEvidence⟩
  exact
    ⟨ flow
    , connectionAtTime
    , rfl
    , subobligations
    , equationEvidence
    , ⟨ hasLeviCivitaConnectionExistence_of_connectionField
          (g := metric_of_ricci_flow_data flow) connectionAtTime
      , rfl⟩
    , levi_civita_uniqueness_of_analytic_foundation_package package
    , levi_civita_torsion_free_of_analytic_foundation_package package
    , levi_civita_metric_compatibility_of_analytic_foundation_package
        package
    , levi_civita_theory_of_analytic_foundation_package package
    , equation_derivation_of_analytic_foundation_package package
    , initial_metric_compatibility_of_analytic_foundation_package package
    , deturck_gauge_fixing_of_analytic_foundation_package package
    , deturck_background_metric_compatibility_of_analytic_foundation_package
        package
    , deturck_vector_field_construction_of_analytic_foundation_package
        package
    , deturck_equation_derivation_of_analytic_foundation_package package
    , ricci_deturck_linearization_of_analytic_foundation_package package
    , strictly_parabolic_deturck_of_analytic_foundation_package package
    , parabolic_linear_theory_of_analytic_foundation_package package
    , parabolic_fixed_point_argument_of_analytic_foundation_package package
    , deturck_short_time_existence_of_analytic_foundation_package package
    , short_time_regularity_bootstrap_of_analytic_foundation_package package
    , deturck_diffeomorphism_ode_of_analytic_foundation_package package
    , deturck_pullback_equation_identity_of_analytic_foundation_package
        package
    , deturck_pullback_to_ricci_flow_of_analytic_foundation_package package
    , short_time_existence_of_analytic_foundation_package package
    , maximal_time_interval_of_analytic_foundation_package package
    , continuation_criterion_of_analytic_foundation_package package
    , curvature_blowup_criterion_of_analytic_foundation_package package
    , maximal_solution_extension_of_analytic_foundation_package package
    , parabolic_schauder_estimates_of_analytic_foundation_package package
    , parabolic_regularity_of_analytic_foundation_package package
    , shi_derivative_estimates_of_analytic_foundation_package package
    , curvature_derivative_bootstrap_of_analytic_foundation_package package
    , hamilton_maximum_principle_of_analytic_foundation_package package
    , uniqueness_theory_of_analytic_foundation_package package
    , metric_evolution_equation_of_analytic_foundation_package package
    , ricci_tensor_evolution_equation_of_analytic_foundation_package package
    , scalar_curvature_evolution_equation_of_analytic_foundation_package
        package
    , curvature_norm_evolution_inequality_of_analytic_foundation_package
        package
    , curvature_evolution_of_analytic_foundation_package package
    ⟩

/--
A completed analytic-foundation package retains the theorem-shaped analytic
statement and fixed-flow derivation statement together with the selected
connection-field witness and the full selected-flow route.  This keeps the
statement-level analytic certificate synchronized with the concrete
Levi-Civita connection field and the downstream short-time, continuation,
regularization, uniqueness, and curvature-evolution fields.
-/
theorem analyticProductionPackage_selected_statement_connectionField_full_foundation_to_curvature_fields
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
    ∃ statement : RicciFlowAnalyticFoundationStatement I n M,
    ∃ derivationStatement : AnalyticFoundationDerivationStatement flow,
    ∃ connectionAtTime :
      TimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow),
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        statement = ⟨flow, derivationStatement⟩ ∧
        AnalyticFoundationSubobligationsPayload flow ∧
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow) ∧
        (∃ leviCivitaExistence :
          HasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data flow),
          leviCivitaExistence =
            hasLeviCivitaConnectionExistence_of_connectionField
              (g := metric_of_ricci_flow_data flow) connectionAtTime) ∧
        HasLeviCivitaConnectionUniqueness
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaTorsionFreeProperty
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaMetricCompatibility
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionTheory
          (metric_of_ricci_flow_data flow) ∧
        HasRicciFlowEquationDerivation flow ∧
        HasInitialMetricCompatibility flow ∧
        HasDeTurckGaugeFixing flow ∧
        HasDeTurckBackgroundMetricCompatibility flow ∧
        HasDeTurckVectorFieldConstruction flow ∧
        HasDeTurckEquationDerivation flow ∧
        HasRicciDeTurckLinearization flow ∧
        HasStrictlyParabolicDeTurckSystem flow ∧
        HasParabolicLinearTheory flow ∧
        HasParabolicFixedPointArgument flow ∧
        HasDeTurckShortTimeExistence flow ∧
        HasShortTimeRegularityBootstrap flow ∧
        HasDeTurckDiffeomorphismODE flow ∧
        HasDeTurckPullbackEquationIdentity flow ∧
        HasDeTurckPullbackToRicciFlow flow ∧
        HasShortTimeRicciFlowSolution flow ∧
        HasRicciFlowMaximalTimeInterval flow ∧
        HasRicciFlowContinuationCriterion flow ∧
        HasCurvatureBlowUpContinuationCriterion flow ∧
        HasMaximalSolutionExtension flow ∧
        HasParabolicSchauderEstimates flow ∧
        HasRicciFlowParabolicRegularity flow ∧
        HasShiDerivativeEstimates flow ∧
        HasCurvatureDerivativeBootstrap flow ∧
        HasHamiltonMaximumPrinciple flow ∧
        HasRicciFlowUniquenessTheory flow ∧
        HasMetricEvolutionEquation flow ∧
        HasRicciTensorEvolutionEquation flow ∧
        HasScalarCurvatureEvolutionEquation flow ∧
        HasCurvatureNormEvolutionInequality flow ∧
        HasCurvatureEvolutionEquations flow := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  have connectionField :
      Nonempty
        (TimeDependentTangentConnectionField
          (metric_of_ricci_flow_data flow)) :=
    (hasLeviCivitaConnectionExistence_iff_connectionField_nonempty
      (metric_of_ricci_flow_data flow)).1
        (levi_civita_existence_of_analytic_foundation_package package)
  rcases connectionField with ⟨connectionAtTime⟩
  rcases analytic_foundation_payload_of_analytic_foundation_package
      package with
    ⟨statement, derivationStatement, subobligations, equationEvidence⟩
  have statement_eq :
      statement = ⟨flow, derivationStatement⟩ := by
    simpa [flow] using
      analytic_foundation_statement_of_analytic_foundation_package_eq
        package
  exact
    ⟨ flow
    , statement
    , derivationStatement
    , connectionAtTime
    , rfl
    , statement_eq
    , subobligations
    , equationEvidence
    , ⟨ hasLeviCivitaConnectionExistence_of_connectionField
          (g := metric_of_ricci_flow_data flow) connectionAtTime
      , rfl⟩
    , levi_civita_uniqueness_of_analytic_foundation_package package
    , levi_civita_torsion_free_of_analytic_foundation_package package
    , levi_civita_metric_compatibility_of_analytic_foundation_package
        package
    , levi_civita_theory_of_analytic_foundation_package package
    , equation_derivation_of_analytic_foundation_package package
    , initial_metric_compatibility_of_analytic_foundation_package package
    , deturck_gauge_fixing_of_analytic_foundation_package package
    , deturck_background_metric_compatibility_of_analytic_foundation_package
        package
    , deturck_vector_field_construction_of_analytic_foundation_package
        package
    , deturck_equation_derivation_of_analytic_foundation_package package
    , ricci_deturck_linearization_of_analytic_foundation_package package
    , strictly_parabolic_deturck_of_analytic_foundation_package package
    , parabolic_linear_theory_of_analytic_foundation_package package
    , parabolic_fixed_point_argument_of_analytic_foundation_package package
    , deturck_short_time_existence_of_analytic_foundation_package package
    , short_time_regularity_bootstrap_of_analytic_foundation_package package
    , deturck_diffeomorphism_ode_of_analytic_foundation_package package
    , deturck_pullback_equation_identity_of_analytic_foundation_package
        package
    , deturck_pullback_to_ricci_flow_of_analytic_foundation_package package
    , short_time_existence_of_analytic_foundation_package package
    , maximal_time_interval_of_analytic_foundation_package package
    , continuation_criterion_of_analytic_foundation_package package
    , curvature_blowup_criterion_of_analytic_foundation_package package
    , maximal_solution_extension_of_analytic_foundation_package package
    , parabolic_schauder_estimates_of_analytic_foundation_package package
    , parabolic_regularity_of_analytic_foundation_package package
    , shi_derivative_estimates_of_analytic_foundation_package package
    , curvature_derivative_bootstrap_of_analytic_foundation_package package
    , hamilton_maximum_principle_of_analytic_foundation_package package
    , uniqueness_theory_of_analytic_foundation_package package
    , metric_evolution_equation_of_analytic_foundation_package package
    , ricci_tensor_evolution_equation_of_analytic_foundation_package package
    , scalar_curvature_evolution_equation_of_analytic_foundation_package
        package
    , curvature_norm_evolution_inequality_of_analytic_foundation_package
        package
    , curvature_evolution_of_analytic_foundation_package package
    ⟩

end Poincare
