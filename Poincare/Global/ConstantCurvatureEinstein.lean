import Poincare.Global.RoundSphereWitness
import Poincare.Global.EinsteinInterface
import Poincare.Statement

/-!
# Constant curvature contracts to Einstein in dimension three

This module uses the existing raised-basis Ricci trace and Kulkarni-Nomizu
trace lemmas to contract the repository's dimension-three constant-curvature
identity.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

/--
Contracting the constant-sectional-curvature four-linear identity gives
`Ric = 2κ g` in dimension three.  With this repository's slot/sign
convention, the existing trace lemma gives
`tr_g KN(g,g)(·,u,w,·) = -4 g(u,w)`, so
`-(κ / 2) * (-4) = 2κ`.
-/
theorem isEinsteinAt_of_hasConstantSectionalCurvature3
    (g : ClosedSmoothRiemannianMetric 3 M) {κ : ℝ}
    (h : HasConstantSectionalCurvature3 g κ) (x : M) :
    g.IsEinsteinAt (2 * κ) x := by
  rw [g.isEinsteinAt_iff]
  intro u w
  classical
  letI : FiniteDimensional ℝ (TM3 x) :=
    inferInstanceAs (FiniteDimensional ℝ E3)
  let b := Module.finBasis ℝ (TM3 x)
  let sharp : Fin (Module.finrank ℝ (TM3 x)) → TM3 x :=
    fun i => metricDualVectorAt g x (b.coord i)
  have hRic :
      g.ricciAt x u w =
        ∑ i, g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (b i)) (extend E3 u) (extend E3 w) x) (sharp i) := by
    simpa [b, sharp] using
      (ricciAt_eq_curvature_inner_contraction (g := g) (x := x) u w)
  have hCurvTrace :
      (∑ i, g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (b i)) (extend E3 u) (extend E3 w) x) (sharp i)) =
        ∑ i, (-(κ / 2) *
          ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
            (n := 3) (M := M) x
            (fun p q => g.inner x p q) (fun p q => g.inner x p q)
            (b i) u w (sharp i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact h x (b i) u w (sharp i)
  have hKN :
      (∑ i, ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
        (n := 3) (M := M) x
        (fun p q => g.inner x p q) (fun p q => g.inner x p q)
        (b i) u w (sharp i)) =
        -4 * g.inner x u w := by
    simpa [b, sharp] using
      (metricKulkarniNomizuAt_finBasis_trace_eq
        (g := g) (hn := rfl) (x := x) u w)
  calc
    g.ricciAt x u w =
        ∑ i, g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (b i)) (extend E3 u) (extend E3 w) x) (sharp i) := hRic
    _ = ∑ i, (-(κ / 2) *
          ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
            (n := 3) (M := M) x
            (fun p q => g.inner x p q) (fun p q => g.inner x p q)
            (b i) u w (sharp i)) := hCurvTrace
    _ = -(κ / 2) *
        (∑ i, ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
          (n := 3) (M := M) x
          (fun p q => g.inner x p q) (fun p q => g.inner x p q)
          (b i) u w (sharp i)) := by
          rw [Finset.mul_sum]
    _ = -(κ / 2) * (-4 * g.inner x u w) := by rw [hKN]
    _ = (2 * κ) * g.inner x u w := by ring

/-- The round metric on `S³` is Einstein with Einstein constant `2`. -/
theorem roundSphereMetric3_isEinsteinAt_two :
    ∀ x : RoundSphere3, roundSphereMetric3.IsEinsteinAt 2 x := by
  intro x
  have hEin :=
    isEinsteinAt_of_hasConstantSectionalCurvature3
      (g := roundSphereMetric3) (κ := 1)
      roundSphereMetric3_hasConstantSectionalCurvature_one x
  simpa using hEin

local instance : ConnectedSpace RoundSphere3 :=
  threeSphere_connectedSpace

/-- The statement-layer round `S³` carries a positive Einstein metric. -/
theorem positiveEinsteinMetric3_roundSphere :
    PositiveEinsteinMetric3 RoundSphere3 := by
  refine ⟨roundSphereMetric3, 2, by norm_num, ?_⟩
  exact roundSphereMetric3_isEinsteinAt_two

end Poincare
