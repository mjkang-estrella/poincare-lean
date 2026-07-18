import Poincare.Smoothability
import Poincare.Statement
import Poincare.Global.PinchedLimitInterface
import Poincare.Global.EinsteinInterface
import Poincare.Global.RoundSphereSimpleConnected

/-!
# Topological completion from the global smooth-manifold theorem

The global Ricci-flow/Cartan pipeline concludes the repository's
`PoincareConjecture`, whose quantified manifolds already carry a smooth
structure.  The canonical project target `PoincareConjectureStatement` starts
with a compact topological three-manifold instead.  This file records the
direct bridge between those statements once the honest smoothability input is
available.

Compactness supplies sigma-compactness.  A sigma-compact charted space over
the second-countable Euclidean model is second countable, and simple
connectivity supplies connectedness.  Thus all extra instances required by
the global statement are derived rather than assumed.
-/

noncomputable section

open scoped Manifold ContDiff

universe u

namespace Poincare

/--
Existence-shaped smoothability for the canonical topological statement.

The input topological atlas is used only to state that `M` is a topological
three-manifold.  The conclusion selects a possibly different charted-space
instance carrying a smooth structure.  This is the mathematically correct
quantifier order: it does not require every ambient topological atlas to be a
smooth atlas.
-/
def ExistsSmoothabilitySmoothManifoldStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
        IsManifold (𝓡 3) ∞ M

/-- The existence-shaped smoothability interface exposes its quantifiers. -/
theorem existsSmoothabilitySmoothManifoldStatement_eq :
    ExistsSmoothabilitySmoothManifoldStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
            letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
            IsManifold (𝓡 3) ∞ M) :=
  rfl

/-- Ambient-atlas smoothability implies the weaker existence-shaped form. -/
theorem existsSmoothabilitySmoothManifoldStatement_of_smoothability
    (smoothable : SmoothabilitySmoothManifoldStatement.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} := by
  intro M _top _t2 _charted _simplyConnected _compact
  exact ⟨inferInstance, smoothable M⟩

/--
An existence-shaped smoothability theorem converts the global smooth-manifold
Poincare theorem into the canonical topological statement by selecting its
smooth atlas before invoking the global theorem.
-/
theorem poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (smoothable : ExistsSmoothabilitySmoothManifoldStatement.{u})
    (globalPoincare : PoincareConjecture.{u}) :
    PoincareConjectureStatement.{u} := by
  intro M _top _t2 _ambient _simplyConnected _compact
  rcases smoothable M with ⟨charted, hsmooth⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
  letI : IsManifold (𝓡 3) ∞ M := hsmooth
  letI : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact
      (H := EuclideanSpace ℝ (Fin 3)) M
  letI : ConnectedSpace M := inferInstance
  exact globalPoincare M

/--
The stronger ambient-atlas smoothability interface converts the global
smooth-manifold Poincare theorem into the canonical topological statement.
Unlike `ExistsSmoothabilitySmoothManifoldStatement`, this premise requires the
already-selected ambient atlas itself to be smooth.
-/
theorem poincareConjectureStatement_of_smoothability_and_globalPoincareConjecture
    (smoothable : SmoothabilitySmoothManifoldStatement.{u})
    (globalPoincare : PoincareConjecture.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_smoothability smoothable)
    globalPoincare

/--
The current Hamilton-convergence and compatible-Cartan-atlas interfaces,
together with universal smoothability, imply the canonical topological
Poincare statement.
-/
theorem poincareConjectureStatement_of_smoothability_of_hamiltonConvergence_of_compatibleCartanAtlas
    (smoothable : SmoothabilitySmoothManifoldStatement.{u})
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3 N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_smoothability_and_globalPoincareConjecture
    smoothable
    (RoundSphereSimpleConnected.poincareConjecture_of_hamiltonConvergence_of_compatibleCartanAtlas
      hHamilton hAtlas)

/--
After scalar-curvature regularity has been discharged for every closed smooth
metric, the canonical topological statement needs only the reduced Hamilton
limit payload, universal smoothability, and the compatible Cartan atlas.
-/
theorem poincareConjectureStatement_of_smoothability_of_hamiltonConvergenceCore_of_compatibleCartanAtlas
    (smoothable : SmoothabilitySmoothManifoldStatement.{u})
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_smoothability_of_hamiltonConvergence_of_compatibleCartanAtlas
    smoothable
    (fun N _ _ _ _ _ _ _ _ =>
      (hamiltonConvergencePinchedLimit3_iff_core (M := N)).mpr
        (hHamilton N))
    hAtlas

/--
A universal positive Einstein metric output from normalized Ricci flow is a
concrete sufficient replacement for the Hamilton limit payload in the direct
topological completion theorem.
-/
theorem poincareConjectureStatement_of_smoothability_of_positiveEinstein_of_compatibleCartanAtlas
    (smoothable : SmoothabilitySmoothManifoldStatement.{u})
    (hEinstein :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          PositiveEinsteinMetric3 N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_smoothability_of_hamiltonConvergence_of_compatibleCartanAtlas
    smoothable
    (fun N _ _ _ _ _ _ _ _ =>
      hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3
        (hEinstein N))
    hAtlas

/--
The direct, existence-shaped completion route: an honestly selected smooth
atlas, the reduced Hamilton limit payload, and compatible Cartan germs imply
the canonical topological Poincare statement.
-/
theorem poincareConjectureStatement_of_exists_smoothability_of_hamiltonConvergenceCore_of_compatibleCartanAtlas
    (smoothable : ExistsSmoothabilitySmoothManifoldStatement.{u})
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    smoothable
    (RoundSphereSimpleConnected.poincareConjecture_of_hamiltonConvergence_of_compatibleCartanAtlas
      (fun N _ _ _ _ _ _ _ _ =>
        (hamiltonConvergencePinchedLimit3_iff_core (M := N)).mpr
          (hHamilton N))
      hAtlas)

/--
The same existence-shaped completion route with the concrete positive
Einstein output substituted for the Hamilton limit payload.
-/
theorem poincareConjectureStatement_of_exists_smoothability_of_positiveEinstein_of_compatibleCartanAtlas
    (smoothable : ExistsSmoothabilitySmoothManifoldStatement.{u})
    (hEinstein :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          PositiveEinsteinMetric3 N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    smoothable
    (RoundSphereSimpleConnected.poincareConjecture_of_hamiltonConvergence_of_compatibleCartanAtlas
      (fun N _ _ _ _ _ _ _ _ =>
        hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3
          (hEinstein N))
      hAtlas)

end Poincare
