import Poincare.Global.SphereTheorem

/-!
# Positive Einstein metrics discharge the Hamilton convergence payload

Hamilton's 1982 convergence theory, in its normalized-flow formulation,
produces a positive Einstein metric on the closed 3-manifold.  This module
records the honest reduction: existence of a positive Einstein metric (with
constant Einstein factor `lam > 0`) implies the repository's
`HamiltonConvergencePinchedLimit3` payload.  The scalar-differentiability
conjunct is free here because an Einstein metric with constant factor has the
constant scalar curvature `3 * lam`; the traceless-Ricci conjunct is the
proven equality case of the pinching inequality; positivity comes from
`lam > 0` at any point of the (connected, hence nonempty) manifold.

Consequently the frozen `PoincareConjecture` statement follows from exactly
two named hypotheses: positive-Einstein existence and unit-curvature sphere
recognition.  Both remain hypothesis interfaces, never axioms.
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
Existence of a positive Einstein metric with constant Einstein factor: the
classical output shape of Hamilton's normalized Ricci-flow convergence on
closed 3-manifolds of positive Ricci curvature.  This is a named hypothesis
interface, not a global postulate and not an instantiable certificate.
-/
def PositiveEinsteinMetric3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
    0 < lam ∧ ∀ x : M, g.IsEinsteinAt lam x

/-- The positive-Einstein interface expands to its metric payload. -/
theorem positiveEinsteinMetric3_eq :
    PositiveEinsteinMetric3 M =
      (∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
        0 < lam ∧ ∀ x : M, g.IsEinsteinAt lam x) :=
  rfl

/--
A positive Einstein metric supplies the full Hamilton pinched-limit payload:
constant scalar curvature `3 * lam` (hence differentiable and positive
somewhere) and vanishing traceless Ricci (the equality case of pinching).
-/
theorem hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3
    (h : PositiveEinsteinMetric3 M) :
    HamiltonConvergencePinchedLimit3 M := by
  rcases h with ⟨g, lam, hlam, hEin⟩
  have hscalar : ∀ y : M, g.scalarAt y = 3 * lam := by
    intro y
    have hy := g.scalarAt_eq_nat_mul_of_isEinsteinAt (hEin y)
    push_cast at hy
    exact hy
  have hconst : (fun y : M ↦ g.scalarAt y) = fun _ : M ↦ 3 * lam :=
    funext hscalar
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x
    rw [hconst]
    exact mdifferentiableAt_const
  · have hEin3 : g.IsEinstein3 := by
      intro x u w
      have hpt := (g.isEinsteinAt_iff lam x).1 (hEin x) u w
      rw [hpt, hscalar x]
      ring
    exact g.forall_tracelessRicciNormSqAt_eq_zero_of_isEinstein3 hEin3
  · obtain ⟨x₀⟩ : Nonempty M := inferInstance
    exact ⟨x₀, by rw [hscalar x₀]; exact mul_pos (by norm_num) hlam⟩

end Poincare

namespace Poincare

variable {W : Type u}
variable [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
variable [ChartedSpace (ClosedSmoothModel 3) W]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ W]
variable [CompactSpace W] [ConnectedSpace W] [SimplyConnectedSpace W]

/--
Einstein-form statement-chain composition: the frozen `PoincareConjecture`
statement follows from positive-Einstein existence plus unit-curvature sphere
recognition.  Both named interfaces remain explicit hypotheses.
-/
theorem poincareConjecture_of_positiveEinstein_of_unitRecognition
    (hEin :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          PositiveEinsteinMetric3 N)
    (hUnit :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitConstantCurvatureSphereRecognition3 N) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergence_of_unitRecognition
    (fun N _ _ _ _ _ _ _ _ =>
      hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3 (hEin N))
    hUnit

end Poincare
