import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

end Poincare.NearFrozenParabolicRightInverse
