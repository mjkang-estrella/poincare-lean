import Poincare.Global.FiniteAtlasParabolicTensorSpace

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Poincare.GlobalParametrixAssembly
open FiniteAtlasParabolicTensorSpace
universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

abbrev SourceGraphs (α T : ℝ) := (Fin 3 × Fin 3) → Jet α T
abbrev Transports (A : AtlasData M) (α T : ℝ) :=
  Fin A.cover.chartCount → Fin A.cover.chartCount → Fin 3 → Fin 3 →
    SourceGraphs α T →L[ℝ] Jet α T

/-- Apply the same genuine scalar local solver to each source component. -/
def localGraphs (A : AtlasData M) (α T : ℝ)
    (S : Fin A.cover.chartCount → Scalar α T →L[ℝ] Jet α T)
    (j : Fin A.cover.chartCount) : Y_M A α T →L[ℝ] SourceGraphs α T :=
  ContinuousLinearMap.pi fun k => (S j).comp
    ((ContinuousLinearMap.proj (j, k.1, k.2)).comp
      (tensorSubmodule A (evalY α T)).subtypeL)

/-- The actual finite transported local-solver sum, before codomain restriction. -/
def ambient (A : AtlasData M) (α T : ℝ)
    (S : Fin A.cover.chartCount → Scalar α T →L[ℝ] Jet α T)
    (B : Transports A α T) : Y_M A α T →L[ℝ] LocalProduct A (Jet α T) :=
  ContinuousLinearMap.pi fun k => ∑ j : Fin A.cover.chartCount,
    (B k.1 j k.2.1 k.2.2).comp (localGraphs A α T S j)

end Poincare.GlobalParametrixAssembly
