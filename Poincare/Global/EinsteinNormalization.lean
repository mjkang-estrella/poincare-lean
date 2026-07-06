import Poincare.Global.EinsteinInterface
import Poincare.Global.ScalarRegularity

/-!
# Positive Einstein metrics normalize to unit constant curvature

This module materializes the proven bridge between the Einstein form of the
analytic wall and the unit-curvature recognition interface: a positive
Einstein metric (constant factor `lam > 0`) has vanishing traceless Ricci and
constant scalar `3 * lam`, hence constant sectional curvature `lam / 2` by the
Schur route, and the constant rescaling normalizes it to curvature one.  No
interface is consumed: every link is a repository theorem.
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

/-- An everywhere-Einstein metric with constant factor has constant scalar
curvature `3 * lam`. -/
theorem scalarAt_eq_three_mul_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric 3 M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x) (y : M) :
    g.scalarAt y = 3 * lam := by
  have hy := g.scalarAt_eq_nat_mul_of_isEinsteinAt (hEin y)
  push_cast at hy
  exact hy

/-- An everywhere-Einstein metric with constant factor has vanishing traceless
Ricci norm. -/
theorem tracelessRicciNormSqAt_eq_zero_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric 3 M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x) (x : M) :
    g.tracelessRicciNormSqAt x = 0 := by
  have hEin3 : g.IsEinstein3 := by
    intro z u w
    have hpt := (g.isEinsteinAt_iff lam z).1 (hEin z) u w
    rw [hpt, scalarAt_eq_three_mul_of_forall_isEinsteinAt g hEin z]
    ring
  exact g.forall_tracelessRicciNormSqAt_eq_zero_of_isEinstein3 hEin3 x

/--
A positive Einstein metric has constant sectional curvature `lam / 2`:
traceless Ricci vanishes, scalar curvature is the constant `3 * lam`, and the
Schur/connectedness route pins the sectional curvature at `(3 * lam) / 6`.
-/
theorem hasConstantSectionalCurvature_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric 3 M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x) :
    HasConstantSectionalCurvature3 g (lam / 2) := by
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  have hcurv : HasConstantSectionalCurvature3 g ((3 * lam) / 6) :=
    hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_connected
      (g := g) (R₀ := 3 * lam)
      (fun x => scalarAt_mdifferentiableAt g x)
      (tracelessRicciNormSqAt_eq_zero_of_forall_isEinsteinAt g hEin)
      ⟨x₀, scalarAt_eq_three_mul_of_forall_isEinsteinAt g hEin x₀⟩
  have hhalf : (3 * lam) / 6 = lam / 2 := by ring
  rw [hhalf] at hcurv
  exact hcurv

/--
Positive Einstein existence yields a unit-constant-curvature metric on the
same manifold, by constant rescaling.  This connects the Einstein form of the
analytic wall directly to `UnitConstantCurvatureSphereRecognition3` without
passing through the space-form interface.
-/
theorem exists_unitConstantCurvature_of_positiveEinsteinMetric3
    (h : PositiveEinsteinMetric3 M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  rcases h with ⟨g, lam, hlam, hEin⟩
  have hcurv : HasConstantSectionalCurvature3 g (lam / 2) :=
    hasConstantSectionalCurvature_of_forall_isEinsteinAt g hEin
  have hκ : (0 : ℝ) < lam / 2 := by linarith
  exact ⟨g.constSMul (lam / 2) hκ,
    ClosedSmoothRiemannianMetric.constSMul_hasConstantSectionalCurvature3_one
      g hκ hcurv⟩

/--
Per-manifold sphere conclusion from positive-Einstein existence and
unit-curvature recognition alone: the direct two-step composition.
-/
theorem sphereConclusion_of_positiveEinstein_of_unitRecognition
    (h : PositiveEinsteinMetric3 M)
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases exists_unitConstantCurvature_of_positiveEinsteinMetric3 h with ⟨g', hg'⟩
  exact hUnit g' hg'

end Poincare
