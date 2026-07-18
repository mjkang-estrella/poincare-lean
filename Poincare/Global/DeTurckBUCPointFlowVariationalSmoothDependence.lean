import Poincare.Global.DeTurckBUCPointFlowSelectorSmoothDependence
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Variational-tower criterion for point-flow smooth dependence

The selected Picard--Lindelof flow is smooth in its initial state once its
first three variational endpoint fields exist locally and the top field is
continuous.  This file records that standard bootstrap directly through
`contDiffAt_succ_iff_hasFDerivAt`.

It replaces a black-box `C³` selector premise by explicit first-, second-, and
third-variation data.  Constructing these fields for the concrete augmented
DeTurck selector is the remaining analytic ODE task; all logical conversion
from that tower to the supplied Ricci-flow point-flow package is proved here.
-/

noncomputable section

open Filter Function
open scoped ContDiff Topology

namespace Poincare

section AbstractVariationalTowers

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

-- Typeclass search deliberately avoids recursively reusing the generic
-- operator-norm instance at the same head symbol.  Naming the two
-- intermediate operator spaces makes the finite variational tower explicit.
local instance firstVariationNormedGroup :
    NormedAddCommGroup (X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance firstVariationNormedSpace :
    NormedSpace ℝ (X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace

local instance secondVariationNormedGroup :
    NormedAddCommGroup (X →L[ℝ] (X →L[ℝ] Y)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance secondVariationNormedSpace :
    NormedSpace ℝ (X →L[ℝ] (X →L[ℝ] Y)) :=
  ContinuousLinearMap.toNormedSpace

/-- Local first-variation data: a locally valid derivative field which is
`C⁰` at the base point. -/
structure LocalFirstOrderVariationalData (f : X → Y) (x : X) where
  D₁ : X → X →L[ℝ] Y
  hasFDerivAt_eventually :
    ∃ U ∈ nhds x, ∀ q ∈ U, HasFDerivAt f (D₁ q) q
  D₁_contDiffAt_zero : ContDiffAt ℝ 0 D₁ x

namespace LocalFirstOrderVariationalData

/-- Local first-variation data assemble `C¹` regularity. -/
theorem contDiffAt_one
    {f : X → Y} {x : X} (H : LocalFirstOrderVariationalData f x) :
    ContDiffAt ℝ 1 f x := by
  exact
    (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0)
      (f := f) (x := x)).2
      ⟨H.D₁, H.hasFDerivAt_eventually, H.D₁_contDiffAt_zero⟩

end LocalFirstOrderVariationalData

/-- A complete local third-order variational tower for `f`.

`D₂` is the derivative field of `D₁`, and `D₃` is the derivative field of
`D₂`.  Continuity of `D₃` closes the recursive `ContDiffAt` bootstrap. -/
structure LocalThirdOrderVariationalTower (f : X → Y) (x : X) where
  D₁ : X → X →L[ℝ] Y
  D₂ : X → X →L[ℝ] (X →L[ℝ] Y)
  D₃ : X → X →L[ℝ] (X →L[ℝ] (X →L[ℝ] Y))
  f_hasFDerivAt_eventually :
    ∃ U ∈ nhds x, ∀ q ∈ U, HasFDerivAt f (D₁ q) q
  D₁_hasFDerivAt_eventually :
    ∃ U ∈ nhds x, ∀ q ∈ U, HasFDerivAt D₁ (D₂ q) q
  D₂_hasFDerivAt_eventually :
    ∃ U ∈ nhds x, ∀ q ∈ U, HasFDerivAt D₂ (D₃ q) q
  D₃_contDiffAt_zero : ContDiffAt ℝ 0 D₃ x

namespace LocalThirdOrderVariationalTower

/-- A three-level variational tower assembles joint `C³` regularity. -/
theorem contDiffAt_three
    {f : X → Y} {x : X} (H : LocalThirdOrderVariationalTower f x) :
    ContDiffAt ℝ 3 f x := by
  have hD₂ : ContDiffAt ℝ 1 H.D₂ x := by
    exact
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0)
        (f := H.D₂) (x := x)).2
        ⟨H.D₃, H.D₂_hasFDerivAt_eventually, H.D₃_contDiffAt_zero⟩
  have hD₁ : ContDiffAt ℝ 2 H.D₁ x := by
    exact
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)
        (f := H.D₁) (x := x)).2
        ⟨H.D₂, H.D₁_hasFDerivAt_eventually, hD₂⟩
  exact
    (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 2)
      (f := f) (x := x)).2
      ⟨H.D₁, H.f_hasFDerivAt_eventually, hD₁⟩

end LocalThirdOrderVariationalTower

end AbstractVariationalTowers

section SelectorTowerUpgrade

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Upgrade the concrete two-restart point-flow core from explicit
variational towers for one representing autonomous augmented selector.

The forward selector point needs three levels.  The backward selector point
needs only the first level because downstream invertibility consumes a `C¹`
local inverse. -/
def TwoRestartPointFlowCore.toPointFlowPackage_of_selectorVariationalTowers
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    (H : TwoRestartPointFlowCore V Phi Psi t z₀ y₁)
    (alpha : (ℝ × E) → ℝ → (ℝ × E))
    (hPhi : Phi = autonomousSelectorForwardSpatialFlow alpha)
    (hPsi : Psi = autonomousSelectorBackwardSpatialFlow alpha t)
    (hForward : LocalThirdOrderVariationalTower
      (Function.uncurry alpha) ((0, z₀), t))
    (hBackward : LocalFirstOrderVariationalData
      (Function.uncurry alpha) ((t, y₁), -t)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ :=
  H.toPointFlowPackage_of_selectorSmoothDependence alpha hPhi hPsi
    hForward.contDiffAt_three hBackward.contDiffAt_one

/-- The selector-retaining Picard--Lindelof core upgrades directly from the
forward third-order and backward first-order variational data of its retained
selector. -/
def TwoRestartPointFlowCoreWithSelector.toPointFlowPackage_of_variationalTowers
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    (H : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁)
    (hForward : LocalThirdOrderVariationalTower
      (Function.uncurry H.selector) ((0, z₀), t))
    (hBackward : LocalFirstOrderVariationalData
      (Function.uncurry H.selector) ((t, y₁), -t)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ :=
  H.toPointFlowPackage_of_smoothDependence
    hForward.contDiffAt_three hBackward.contDiffAt_one

end SelectorTowerUpgrade

end Poincare
