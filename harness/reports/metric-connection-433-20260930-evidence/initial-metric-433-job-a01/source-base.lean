import Poincare.Global.RiemannianContext
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
universe u v

namespace Poincare.SmoothInitialMetricDefinitions

/-- The positive symmetric cone used by smooth bundle-section gluing. -/
def positiveSymmetricBilinearForms
    (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Set (V →L[ℝ] V →L[ℝ] ℝ) :=
  {q | (∀ a b, q a b = q b a) ∧ ∀ a, a ≠ 0 → 0 < q a a}

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- A chart's Euclidean inner product pulled back to each tangent fiber.
The coordinate map is defined globally and is invertible on the chart domain. -/
def localEuclideanInner (p x : M) :
    TangentSpace (closedSmoothModelWithCorners 3) x →L[ℝ]
      TangentSpace (closedSmoothModelWithCorners 3) x →L[ℝ] ℝ :=
  let A := (trivializationAt (ClosedSmoothModel 3)
    (TangentSpace (closedSmoothModelWithCorners 3)) p).continuousLinearMapAt ℝ x
  ((ContinuousLinearMap.precomp (𝕜₁ := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (G := ℝ) A).comp (innerSL ℝ (E := ClosedSmoothModel 3))).comp A

theorem localEuclideanInner_apply (p x : M)
    (a b : TangentSpace (closedSmoothModelWithCorners 3) x) :
    localEuclideanInner p x a b =
      inner ℝ
        ((trivializationAt (ClosedSmoothModel 3)
          (TangentSpace (closedSmoothModelWithCorners 3)) p).continuousLinearMapAt ℝ x a)
        ((trivializationAt (ClosedSmoothModel 3)
          (TangentSpace (closedSmoothModelWithCorners 3)) p).continuousLinearMapAt ℝ x b) := by
  simp [localEuclideanInner, ContinuousLinearMap.precomp]

end Poincare.SmoothInitialMetricDefinitions
