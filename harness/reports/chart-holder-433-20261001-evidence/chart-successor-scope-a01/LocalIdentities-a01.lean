import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.MeanValue
import Poincare.FlatModelConnection
noncomputable section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology
namespace ChartSuccessorProbe
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

example {f : M → 𝕜} {x : M} (hf : MDiffAt f x) :
    mfderiv% f x = fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x f)
      (range I) (extChartAt I x x) := by
  exact hf.mfderiv

example {f : M → 𝕜} {x : M} :
    writtenInExtChartAt I 𝓘(𝕜, 𝕜) x f = f ∘ (extChartAt I x).symm := by
  funext z
  simp only [writtenInExtChartAt, extChartAt_self_eq, modelWithCornersSelf_coe,
    Function.id_comp]

example {f : M → 𝕜} {x : M} :
    (extChartAt 𝓘(𝕜, 𝕜) (f x)) ∘ f ∘ (extChartAt I x).symm =
      f ∘ (extChartAt I x).symm := by
  funext z
  rfl

section Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]

example (x : M) (z : E) (hz : z ∈ (extChartAt I x).target) :
    let e := extChartAt I x
    let y := e.symm z
    let L : TangentSpace I y →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (e : M → E) y
    L.IsInvertible := by
  intro e y L
  have hySrc : y ∈ e.source := e.map_target hz
  simpa only [L] using!
    (isInvertible_mfderiv_extChartAt (I := I) (x := x) (y := y) hySrc :
      (mfderiv I 𝓘(ℝ, E)
        ((extChartAt I x : PartialEquiv M E) : M → E) y).IsInvertible)

example (f : M → ℝ) (x y : M) (w : TangentSpace I y)
    (hzro : fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)
      (mfderiv I 𝓘(ℝ,E) (extChartAt I x) y w) = 0) :
    let e := extChartAt I x
    let F : E → ℝ := f ∘ e.symm
    let L : TangentSpace I y →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (e : M → E) y
    fderiv ℝ F (e y) (L w) = 0 := by
  intro e F L
  simpa only [F, L] using! hzro

example (x : M) (X Y : (y : M) → TangentSpace I y) :
    lieBracketWithin ℝ
      (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm X)
      (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm Y) univ
      (extChartAt I x x) =
    lieBracket ℝ
      (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm X)
      (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm Y)
      (extChartAt I x x) := by
  exact lieBracketWithin_univ
end Real
end ChartSuccessorProbe
