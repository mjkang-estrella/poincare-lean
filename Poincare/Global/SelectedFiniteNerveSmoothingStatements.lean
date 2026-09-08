import Poincare.Global.SmoothabilitySimultaneousLocalConjugacy
import Poincare.Global.TopologicalCompletionBridge

/-!
# Selected finite-nerve smoothing

The smallest smoothing input, in the repository's finite-atlas vocabulary,
that the landed assembly turns into existence-shaped smoothability: for every
compact simply connected topological 3-manifold, one finite atlas nerve
reduction whose transitions carry simultaneous local smooth conjugacies.
Existence of that input is an open Moise-type obligation; only the edge to
`ExistsSmoothabilitySmoothManifoldStatement` is proved here.  See
`harness/reports/smoothability-bridge-survey_done.md`, section 5.2.
-/

set_option autoImplicit false
open scoped Manifold ContDiff
namespace Poincare
universe u

namespace SelectedFiniteNerveSmoothing
open SmoothabilityFiniteAtlasNerveReduction SmoothabilitySimultaneousLocalConjugacy

/-- One finite nerve reduction per manifold, together with simultaneous local
smooth conjugacies of all its transitions.  Open obligation. -/
def SelectedFiniteNerveSmoothingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∃ r : FiniteAtlasNerveReduction3 M,
        Nonempty (FiniteNerveSimultaneousLocalConjugacySmoothing3 r)

/-- The landed local-transition-atlas assembly turns the selected smoothing
input into existence-shaped smoothability. -/
theorem existsSmoothability_of_selectedFiniteNerveSmoothing
    (h : SelectedFiniteNerveSmoothingStatement.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} := by
  intro M _ _ _ _ _
  obtain ⟨r, ⟨s⟩⟩ := h M
  exact nonempty_cInfinityLocalTransitionAtlasData3_iff_exists_smoothAtlas.mp
    s.nonempty_cInfinityLocalTransitionAtlasData3

end SelectedFiniteNerveSmoothing
end Poincare
