import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
open scoped Manifold ContDiff
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
example (f : M → ℝ) : extDerivFun I f = mvfderiv I f := rfl
example (f : M → ℝ) (x : M) :
    mvfderiv I f x =
      (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, ℝ) f x) := rfl
