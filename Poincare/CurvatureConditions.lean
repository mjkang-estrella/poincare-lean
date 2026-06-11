/-
Curvature conditions.

With the genuine Ricci tensor and scalar curvature available, the classical
curvature hypotheses of geometric analysis (Einstein metrics, Ricci
positivity, positive scalar curvature) become stateable with content.  The
flat model realizes the degenerate cases.
-/

import Poincare.EuclideanLeviCivitaCheck

noncomputable section

open Bundle CovariantDerivative
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
variable [ContMDiffCovariantDerivative cov 1]
variable (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)

/-- The Einstein condition at a point: `Ric = λ g`. -/
def IsEinsteinAt (lam : ℝ) (x : M) : Prop :=
  ∀ u w : TangentSpace I x, ricciBilinearAt cov x u w = lam * g x u w

/-- Nonnegative Ricci curvature at a point. -/
def HasNonnegRicciAt (x : M) : Prop :=
  ∀ u : TangentSpace I x, 0 ≤ ricciBilinearAt cov x u u

/-- Positive Ricci curvature at a point. -/
def HasPosRicciAt (x : M) : Prop :=
  ∀ u : TangentSpace I x, u ≠ 0 → 0 < ricciBilinearAt cov x u u

end CovariantDerivative

namespace CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- **Euclidean space is Ricci-flat**: the flat connection is Einstein with
constant `0` for the Euclidean metric. -/
theorem flat_isEinsteinAt_zero (x : F) :
    IsEinsteinAt (flatCovariantDerivative ℝ F)
      (euclideanBundleMetric (F := F)) 0 x := by
  intro u w
  rw [flat_ricciBilinearAt_eq_zero]
  ring

/-- Euclidean space has (trivially) nonnegative Ricci curvature. -/
theorem flat_hasNonnegRicciAt (x : F) :
    HasNonnegRicciAt (flatCovariantDerivative ℝ F) x := by
  intro u
  rw [flat_ricciBilinearAt_eq_zero]

end CovariantDerivative
