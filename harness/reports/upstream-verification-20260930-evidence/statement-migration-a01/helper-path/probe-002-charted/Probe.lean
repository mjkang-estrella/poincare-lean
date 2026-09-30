import Mathlib.Geometry.Manifold.PoincareConjecture
open scoped Manifold ContDiff
namespace Probe
variable {X : Type} [TopologicalSpace X] [Nonempty X]
variable {e : X → EuclideanSpace ℝ (Fin 3)} (h : Topology.IsOpenEmbedding e)
@[implicit_reducible]
noncomputable def Charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X :=
  h.singletonChartedSpace

theorem baseline :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X := Charts h
    ContMDiff (𝓡 3) (𝓡 3) ∞ e := by
  simpa using contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) h

theorem controlled :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X := Charts h
    ContMDiff (𝓡 3) (𝓡 3) ∞ e := by
  simpa only [Charts] using contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) h

theorem expanded :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X := Charts h
    ContMDiff (𝓡 3) (𝓡 3) ∞ e := by
  dsimp only [Charts]
  exact contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) h

theorem backwardFalse :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X := Charts h
    ContMDiff (𝓡 3) (𝓡 3) ∞ e := by
  set_option backward.isDefEq.respectTransparency false in
    simpa using contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) h
end Probe
