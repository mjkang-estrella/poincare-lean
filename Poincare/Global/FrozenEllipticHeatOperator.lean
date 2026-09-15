import Poincare.Global.DuhamelSolutionOperatorBound
import Poincare.Global.CompactCoefficientEllipticity

noncomputable section

namespace Poincare.FrozenEllipticHeatOperator

open Set ParabolicHolder

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

theorem parabolicDist_comp_le (S : E →L[ℝ] E) (p q : ℝ × E) :
    parabolicDist (p.1, S p.2) (q.1, S q.2) ≤
      max 1 ‖S‖ * parabolicDist p q := by
  have hs : ‖S (p.2 - q.2)‖ ≤ max 1 ‖S‖ * ‖p.2 - q.2‖ :=
    (S.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have ht : Real.sqrt |p.1 - q.1| ≤ max 1 ‖S‖ * Real.sqrt |p.1 - q.1| := by
    simpa using mul_le_mul_of_nonneg_right (le_max_left 1 ‖S‖)
      (Real.sqrt_nonneg |p.1 - q.1|)
  simpa only [parabolicDist, map_sub, mul_add] using add_le_add hs ht

end Poincare.FrozenEllipticHeatOperator
