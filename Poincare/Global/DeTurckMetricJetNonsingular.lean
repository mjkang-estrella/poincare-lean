import Poincare.Global.DeTurckPrincipalSecondJet

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Poincare.DeTurckMetricJetNonsingular
open DeTurckPrincipalSecondJet

/-- An invertible metric form has an invertible coordinate matrix, without
requiring symmetry or positive definiteness. -/
theorem coordinate_matrix_isUnit (G0 : Bilin) (hG0 : G0.IsInvertible) :
    @IsUnit (Matrix (Fin 3) (Fin 3) ℝ) Matrix.semiring.toMonoidWithZero.toMonoid
      (fun i j : Fin 3 => G0 (basis3 i) (basis3 j)) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => G0 (b i) (b j)
  let N : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    b.coord j (G0.inverse (LinearMap.toContinuousLinearMap (b.coord i)))
  have hleft : N * A = 1 := by
    ext i k
    change (∑ j, b.coord j (G0.inverse (LinearMap.toContinuousLinearMap (b.coord i))) *
      G0 (b j) (b k)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i k
    let r := G0.inverse (LinearMap.toContinuousLinearMap (b.coord i))
    have hraise : G0 r = LinearMap.toContinuousLinearMap (b.coord i) :=
      (hG0.inverse_apply_eq.mp rfl).symm
    calc
      _ = G0 (∑ j, b.repr r j • b j) (b k) := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply, r]
      _ = G0 r (b k) := by rw [b.sum_repr]
      _ = _ := by
        rw [hraise]
        simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
          Module.Basis.repr_self_apply, Matrix.one_apply]
        simp only [eq_comm]
  exact (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_left_inverse hleft)

end Poincare.DeTurckMetricJetNonsingular
