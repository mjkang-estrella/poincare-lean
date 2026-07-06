import Poincare.Global.ScalarVariation
import Poincare.Global.Statement

/-!
# Conditional sphere theorem interface

This module isolates the positive space-form recognition theorem as a named
hypothesis and uses it to connect the proved constant-curvature limit algebra
to the statement-layer sphere conclusion.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/--
The narrow positive constant-curvature space-form recognition interface.

This is the named hypothesis for the hard differential-geometric input: the
Killing-Hopf space-form theorem, specialized to closed connected simply
connected smooth 3-manifolds.  In mathematical terms, a complete simply
connected Riemannian manifold of constant sectional curvature `κ > 0` is
isometric to the round sphere of radius `1 / sqrt κ`; hence, in dimension three,
it is homeomorphic to the standard `S^3`.  References: Killing-Hopf space-form
classification, as in do Carmo, *Riemannian Geometry*, Chapter 8, or Petersen,
*Riemannian Geometry*, section on space forms.

The Lean statement deliberately exposes only the downstream topological
conclusion and consumes the already-proved repository predicate
`HasConstantSectionalCurvature3`.  It is a hypothesis interface, not a global
postulate and not an instantiable certificate.
-/
def PositiveConstantCurvatureSpaceForm3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ (g : ClosedSmoothRiemannianMetric 3 M) (κ : ℝ),
    HasConstantSectionalCurvature3 g κ →
      0 < κ →
        Nonempty
          (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))

/-- The space-form interface expands to the intended theorem-shaped hypothesis. -/
theorem positiveConstantCurvatureSpaceForm3_eq :
    PositiveConstantCurvatureSpaceForm3 M =
      (∀ (g : ClosedSmoothRiemannianMetric 3 M) (κ : ℝ),
        HasConstantSectionalCurvature3 g κ →
          0 < κ →
            Nonempty
              (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))) :=
  rfl

/--
Shape check for the target of the interface: on the literal statement-layer
round sphere, the requested homeomorphism target is inhabited by the identity.
-/
theorem positiveConstantCurvatureSpaceForm3_roundSphere_target_nonempty :
    Nonempty
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ) ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  ⟨Homeomorph.refl _⟩

/--
The conditional sphere theorem for a pinched limit metric.

The proved geometry input
`hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_connected`
turns vanishing traceless Ricci, scalar regularity, and connectedness into
constant sectional curvature `κ = R0 / 6`.  Positivity of the scalar curvature
at one point gives `κ > 0`, and the named space-form recognition interface
then supplies the statement-layer homeomorphism to the literal round `S^3`.
-/
theorem sphere_of_pinched_limit
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hScalarDiff : ∀ x : M,
      MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
        (fun y : M ↦ g.scalarAt y) x)
    (htr : ∀ x : M, g.tracelessRicciNormSqAt x = 0)
    (hpos : ∃ x : M, 0 < g.scalarAt x)
    (hSpaceForm : PositiveConstantCurvatureSpaceForm3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases hpos with ⟨x₀, hx₀pos⟩
  let R₀ : ℝ := g.scalarAt x₀
  have hR₀ : ∃ x₀ : M, g.scalarAt x₀ = R₀ := ⟨x₀, rfl⟩
  have hcurv : HasConstantSectionalCurvature3 g (R₀ / 6) :=
    hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_connected
      (g := g) (R₀ := R₀) hScalarDiff htr hR₀
  have hκpos : 0 < R₀ / 6 := by
    exact div_pos hx₀pos (by norm_num)
  exact hSpaceForm g (R₀ / 6) hcurv hκpos

/--
The named upstream Hamilton-convergence interface needed by the sphere
recognition endgame.

This is the honest limit-output boundary for the analytic Ricci-flow work: it
does not construct a flow or prove convergence.  It says that the upstream
Hamilton estimates and convergence theory have produced a closed smooth limit
metric whose scalar curvature is differentiable, whose traceless Ricci tensor
vanishes everywhere, and whose scalar curvature is positive somewhere.  Those
are exactly the concrete hypotheses consumed by `sphere_of_pinched_limit`.
-/
def HamiltonConvergencePinchedLimit3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ g : ClosedSmoothRiemannianMetric 3 M,
    (∀ x : M,
      MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
        (fun y : M ↦ g.scalarAt y) x) ∧
    (∀ x : M, g.tracelessRicciNormSqAt x = 0) ∧
    (∃ x : M, 0 < g.scalarAt x)

/-- The Hamilton-convergence interface expands to its limit-metric payload. -/
theorem hamiltonConvergencePinchedLimit3_eq :
    HamiltonConvergencePinchedLimit3 M =
      (∃ g : ClosedSmoothRiemannianMetric 3 M,
        (∀ x : M,
          MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
            (fun y : M ↦ g.scalarAt y) x) ∧
        (∀ x : M, g.tracelessRicciNormSqAt x = 0) ∧
        (∃ x : M, 0 < g.scalarAt x)) :=
  rfl

/--
Statement-layer conclusion for one manifold under the two honest interfaces.

Interfaces used:
* `HamiltonConvergencePinchedLimit3`: upstream Ricci-flow estimates/convergence
  provide a pinched positive scalar limit metric.
* `PositiveConstantCurvatureSpaceForm3`: the Killing-Hopf positive
  space-form recognition theorem identifies positive constant-curvature,
  simply connected closed 3-manifolds with the round sphere.

The conclusion is exactly the per-manifold target appearing in
`PoincareConjecture` from `Poincare/Global/Statement.lean`.
-/
theorem poincareConjecture_conclusion_of_hamiltonConvergencePinchedLimit3
    (hHamilton : HamiltonConvergencePinchedLimit3 M)
    (hSpaceForm : PositiveConstantCurvatureSpaceForm3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases hHamilton with ⟨g, hScalarDiff, htr, hpos⟩
  exact sphere_of_pinched_limit
    (g := g) hScalarDiff htr hpos hSpaceForm

/--
Universal statement-chain composition.

If the Hamilton convergence interface and the positive space-form recognition
interface are available for every manifold in the `PoincareConjecture` context,
then the repository's frozen `PoincareConjecture` statement follows.  This is a
conditional assembly theorem only; both named interfaces remain explicit
hypotheses.
-/
theorem poincareConjecture_of_hamiltonConvergencePinchedLimit3
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3 N)
    (hSpaceForm :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          PositiveConstantCurvatureSpaceForm3 N) :
    PoincareConjecture.{u} := by
  intro N _top _t2 _second _charted _smooth _compact _connected _simply
  exact
    poincareConjecture_conclusion_of_hamiltonConvergencePinchedLimit3
      (M := N) (hHamilton N) (hSpaceForm N)

end Poincare

namespace Poincare

variable {M' : Type u}
variable [TopologicalSpace M'] [T2Space M'] [SecondCountableTopology M']
variable [ChartedSpace (ClosedSmoothModel 3) M']
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M']
variable [CompactSpace M'] [ConnectedSpace M'] [SimplyConnectedSpace M']

/--
Unit-curvature sphere recognition: the Killing-Hopf interface specialized to
sectional curvature exactly `1`.  This is one of the two independently
attackable factors of `PositiveConstantCurvatureSpaceForm3`: it removes the
curvature-scale quantifier and asks only for recognition of the unit round
metric.  It remains a named hypothesis interface.
-/
def UnitConstantCurvatureSphereRecognition3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      Nonempty
        (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))

/--
Constant-curvature normalization: from any metric of constant positive
sectional curvature `κ`, produce a metric of constant sectional curvature `1`
on the same manifold.  Classically this is the rescaling `g' = κ • g`, whose
Levi-Civita connection agrees with that of `g` and whose four-linear curvature
scales by `κ`, so the sectional curvature scales by `1 / κ`.  This factor is
pure tensor calculus with no topological content, and is therefore a strictly
easier target than the full space-form theorem.  It remains a named
hypothesis interface until the rescaling construction is formalized.
-/
def ConstantCurvatureNormalization3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ (g : ClosedSmoothRiemannianMetric 3 M) (κ : ℝ),
    HasConstantSectionalCurvature3 g κ →
      0 < κ →
        ∃ g' : ClosedSmoothRiemannianMetric 3 M,
          HasConstantSectionalCurvature3 g' 1

/--
Composition of the two factors: normalization plus unit-curvature recognition
discharge the full positive space-form interface.  This shrinks the remaining
Killing-Hopf obligation to the unit case and separates out the (much easier)
rescaling lemma.
-/
theorem positiveConstantCurvatureSpaceForm3_of_normalization_of_unitRecognition
    (hnorm : ConstantCurvatureNormalization3 M')
    (hunit : UnitConstantCurvatureSphereRecognition3 M') :
    PositiveConstantCurvatureSpaceForm3 M' := by
  intro g κ hcurv hκpos
  rcases hnorm g κ hcurv hκpos with ⟨g', hg'⟩
  exact hunit g' hg'

end Poincare
