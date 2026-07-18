import Poincare.Global.DeTurckBUCCoefficientIdentification

/-!
# Identifying the `BUC` heat generator with the coordinate Laplacian

The strong heat-generator value already propagated by the semilinear solver
is the flat componentwise Laplacian at every positive heat time.  This follows
by comparing two derivatives of the same scalar heat orbit:

* generator-domain invariance gives the derivative `H_t Au`;
* the proved positive-time heat equation gives `Δ(H_t u)`.

Consequently, identifying the initial generator at one coordinate requires
only the classical consistency limit

`Δ(H_t u)(z) → Δu(z)` as `t ↓ 0`.

In particular no second `BUC` coefficient representing `Δu`, and no second
strong-generator graph witness, is needed.  The remaining limit is stated
explicitly because it is the precise local heat-kernel boundary not supplied
by the current positive-time Cauchy theory.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace Laplacian
  BoundedContinuousFunction Manifold ContDiff BigOperators

namespace Poincare

section CoordinateGeneratorLaplacian

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- At positive time, the scalar coordinate of the propagated strong heat
generator is exactly the flat Laplacian of the propagated coefficient. -/
theorem coordinateMetricLaplacianValue_vectorHeatSemigroupBUCExtended_eq_generator
    (u Au : CoordinateBUCTensor E)
    (hu : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u Au)
    {t : ℝ} (ht : 0 < t) (z v w : E) :
    coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w =
      coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t Au) z v w := by
  have hgeneratorBUC : HasDerivWithinAt
      (fun s : ℝ ↦ vectorHeatSemigroupBUCExtended
        (E := E) (F := CoordinateTwoTensor E) s u)
      (vectorHeatSemigroupBUCExtended
        (E := E) (F := CoordinateTwoTensor E) t Au)
      (Set.Ici t) t :=
    hu.hasDerivWithinAt_semigroup_orbit ht.le
  have hgenerator :=
    Poincare.HasDerivWithinAt.coordinateMetricValue
      hgeneratorBUC z v w
  have hpde :=
    (coordinateMetricValue_heatOrbit_hasDerivAt_laplacian
      u ht z v w).hasDerivWithinAt (s := Set.Ici t)
  have heq := (uniqueDiffOn_Ici t).eq Set.self_mem_Ici hpde hgenerator
  simpa [coordinateMetricHeatOrbit] using
    congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) heq

/-- A pointwise zero-time consistency limit for positive-time Laplacians
identifies the already-existing strong generator with the classical flat
Laplacian.  This is the source-only replacement for a second generator-graph
witness representing the Laplacian. -/
theorem coordinateMetricValue_generator_eq_laplacian_of_tendsto
    (u Au : CoordinateBUCTensor E)
    (hu : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u Au)
    (z v w : E)
    (hlaplacian : Tendsto
      (fun t : ℝ ↦ coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (coordinateMetricLaplacianValue u z v w))) :
    coordinateMetricValue Au z v w =
      coordinateMetricLaplacianValue u z v w := by
  let L := coordinateMetricEvaluationCLM z v w
  have hgenerator : Tendsto
      (fun t : ℝ ↦ coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t Au) z v w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (coordinateMetricValue Au z v w)) := by
    simpa [L] using
      L.continuous.continuousAt.tendsto.comp
        (tendsto_vectorHeatSemigroupBUCExtended_apply_zero
          (E := E) (F := CoordinateTwoTensor E) Au)
  have heventually :
      (fun t : ℝ ↦ coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ ↦ coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t Au) z v w) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact coordinateMetricLaplacianValue_vectorHeatSemigroupBUCExtended_eq_generator
      u Au hu (Set.mem_Ioi.mp ht) z v w
  have hgenerator' : Tendsto
      (fun t : ℝ ↦ coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (coordinateMetricValue Au z v w)) :=
    hgenerator.congr' heventually.symm
  exact tendsto_nhds_unique hgenerator' hlaplacian

end CoordinateGeneratorLaplacian

end Poincare
