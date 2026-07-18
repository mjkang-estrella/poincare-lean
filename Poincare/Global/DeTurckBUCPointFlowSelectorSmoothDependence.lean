import Poincare.Global.DeTurckBUCTwoRestartPointFlowCore

/-!
# Smooth-dependence bridge for the selected augmented point flow

Mathlib's Picard--Lindelof API constructs a common family of solutions and
proves Lipschitz dependence on the initial value, but it currently exports no
`ContDiff` smooth-parameter-dependence theorem for that selected family.

This file isolates the exact missing statement at the selector level.  If the
autonomous augmented selector is jointly `C³` in its initial extended state
and relative time at the two points used by the forward flow and backward
restart, elementary composition proves the two regularity fields of
`TwoRestartPointFlowPackage`.  All ODE, tube, restart, and inverse-law data
remain supplied by the concrete `TwoRestartPointFlowCore`.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Poincare

section SelectorSlices

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The forward physical point family cut out of an autonomous augmented
solution selector.  The selector parameter is an extended initial state
`(initial time, initial point)` and its second argument is relative time. -/
def autonomousSelectorForwardSpatialFlow
    (alpha : (ℝ × E) → ℝ → (ℝ × E)) : ℝ → E → E :=
  fun s x ↦ (alpha (0, x) s).2

/-- The backward restart cut out of the same autonomous augmented solution
selector.  At physical time `s`, its relative-time argument is `s - t`. -/
def autonomousSelectorBackwardSpatialFlow
    (alpha : (ℝ × E) → ℝ → (ℝ × E)) (t : ℝ) :
    ℝ → E → E :=
  fun s y ↦ (alpha (t, y) (s - t)).2

/-- Joint `C³` regularity of the augmented selector at the forward selector
point gives joint `C³` regularity of the forward spatial flow. -/
theorem autonomousSelectorForwardSpatialFlow_jointContDiffAt_three
    (alpha : (ℝ × E) → ℝ → (ℝ × E)) (t : ℝ) (z₀ : E)
    (hAlpha : ContDiffAt ℝ 3 (Function.uncurry alpha) ((0, z₀), t)) :
    ContDiffAt ℝ 3
      (Function.uncurry (autonomousSelectorForwardSpatialFlow alpha))
      (t, z₀) := by
  have hinitial : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ ((0 : ℝ), p.2)) (t, z₀) :=
    contDiffAt_const.prodMk contDiffAt_snd
  have hinput : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ (((0 : ℝ), p.2), p.1)) (t, z₀) :=
    hinitial.prodMk contDiffAt_fst
  have hcomp := hAlpha.comp (t, z₀) hinput
  simpa only [autonomousSelectorForwardSpatialFlow, Function.uncurry] using
    hcomp.snd

/-- Joint `C¹` regularity of the augmented selector at the backward selector
point gives joint `C¹` regularity of the backward spatial restart. -/
theorem autonomousSelectorBackwardSpatialFlow_jointContDiffAt_one
    (alpha : (ℝ × E) → ℝ → (ℝ × E)) (t : ℝ) (y₁ : E)
    (hAlpha : ContDiffAt ℝ 1 (Function.uncurry alpha) ((t, y₁), -t)) :
    ContDiffAt ℝ 1
      (Function.uncurry (autonomousSelectorBackwardSpatialFlow alpha t))
      (0, y₁) := by
  have hinitial : ContDiffAt ℝ 1
      (fun p : ℝ × E ↦ (t, p.2)) (0, y₁) :=
    contDiffAt_const.prodMk contDiffAt_snd
  have hrelative : ContDiffAt ℝ 1
      (fun p : ℝ × E ↦ p.1 - t) (0, y₁) :=
    contDiffAt_fst.sub contDiffAt_const
  have hinput : ContDiffAt ℝ 1
      (fun p : ℝ × E ↦ ((t, p.2), p.1 - t)) (0, y₁) :=
    hinitial.prodMk hrelative
  have hAlpha' :
      ContDiffAt ℝ 1 (Function.uncurry alpha)
        ((t, y₁), (0 : ℝ) - t) := by
    simpa only [zero_sub] using hAlpha
  have hcomp := hAlpha'.comp (0, y₁) hinput
  simpa only [autonomousSelectorBackwardSpatialFlow, Function.uncurry,
    zero_sub] using hcomp.snd

/-- A globally `C³` augmented selector supplies both local slice facts. -/
theorem autonomousSelector_spatialFlows_jointRegularity_of_contDiff_three
    (alpha : (ℝ × E) → ℝ → (ℝ × E)) (t : ℝ) (z₀ y₁ : E)
    (hAlpha : ContDiff ℝ 3 (Function.uncurry alpha)) :
    ContDiffAt ℝ 3
        (Function.uncurry (autonomousSelectorForwardSpatialFlow alpha))
        (t, z₀) ∧
      ContDiffAt ℝ 1
        (Function.uncurry (autonomousSelectorBackwardSpatialFlow alpha t))
        (0, y₁) := by
  constructor
  · exact autonomousSelectorForwardSpatialFlow_jointContDiffAt_three
      alpha t z₀ hAlpha.contDiffAt
  · exact autonomousSelectorBackwardSpatialFlow_jointContDiffAt_one
      alpha t y₁ (hAlpha.of_le (by norm_num)).contDiffAt

end SelectorSlices

section CoreUpgrade

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Upgrade a concrete two-restart ODE core when its two endpoint families
are represented by one augmented selector with the required local smooth
dependence.

These two local `ContDiffAt` assumptions are the exact residue left by the
current Mathlib ODE API. -/
def TwoRestartPointFlowCore.toPointFlowPackage_of_selectorSmoothDependence
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    (H : TwoRestartPointFlowCore V Phi Psi t z₀ y₁)
    (alpha : (ℝ × E) → ℝ → (ℝ × E))
    (hPhi : Phi = autonomousSelectorForwardSpatialFlow alpha)
    (hPsi : Psi = autonomousSelectorBackwardSpatialFlow alpha t)
    (hAlphaForward :
      ContDiffAt ℝ 3 (Function.uncurry alpha) ((0, z₀), t))
    (hAlphaBackward :
      ContDiffAt ℝ 1 (Function.uncurry alpha) ((t, y₁), -t)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ := by
  have hPhiC3 : ContDiffAt ℝ 3 (Function.uncurry Phi) (t, z₀) := by
    rw [hPhi]
    exact autonomousSelectorForwardSpatialFlow_jointContDiffAt_three
      alpha t z₀ hAlphaForward
  have hPsiC1 : ContDiffAt ℝ 1 (Function.uncurry Psi) (0, y₁) := by
    rw [hPsi]
    exact autonomousSelectorBackwardSpatialFlow_jointContDiffAt_one
      alpha t y₁ hAlphaBackward
  exact H.toPointFlowPackage hPhiC3 hPsiC1

/-- Global `C³` smooth dependence of a representing augmented selector is a
single sufficient hypothesis for upgrading the concrete ODE core. -/
def TwoRestartPointFlowCore.toPointFlowPackage_of_selectorContDiff_three
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    (H : TwoRestartPointFlowCore V Phi Psi t z₀ y₁)
    (alpha : (ℝ × E) → ℝ → (ℝ × E))
    (hPhi : Phi = autonomousSelectorForwardSpatialFlow alpha)
    (hPsi : Psi = autonomousSelectorBackwardSpatialFlow alpha t)
    (hAlpha : ContDiff ℝ 3 (Function.uncurry alpha)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ :=
  H.toPointFlowPackage_of_selectorSmoothDependence alpha hPhi hPsi
    hAlpha.contDiffAt (hAlpha.of_le (by norm_num)).contDiffAt

/-- The selector-retaining core upgrades directly from local selector
smoothness, without requiring downstream code to reconstruct or identify the
Picard--Lindelof family erased by the older core interface. -/
def TwoRestartPointFlowCoreWithSelector.toPointFlowPackage_of_smoothDependence
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    (H : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁)
    (hForward :
      ContDiffAt ℝ 3 (Function.uncurry H.selector) ((0, z₀), t))
    (hBackward :
      ContDiffAt ℝ 1 (Function.uncurry H.selector) ((t, y₁), -t)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ := by
  apply H.core.toPointFlowPackage_of_selectorSmoothDependence H.selector
  · simpa only [autonomousSelectorForwardSpatialFlow] using
      H.forward_representation
  · simpa only [autonomousSelectorBackwardSpatialFlow] using
      H.backward_representation
  · exact hForward
  · exact hBackward

/-- A globally `C³` retained selector is a one-premise upgrade of the
selector-retaining core. -/
def TwoRestartPointFlowCoreWithSelector.toPointFlowPackage_of_contDiff_three
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    (H : TwoRestartPointFlowCoreWithSelector V Phi Psi t z₀ y₁)
    (hSelector : ContDiff ℝ 3 (Function.uncurry H.selector)) :
    TwoRestartPointFlowPackage V Phi Psi t z₀ y₁ :=
  H.toPointFlowPackage_of_smoothDependence
    hSelector.contDiffAt (hSelector.of_le (by norm_num)).contDiffAt

end CoreUpgrade

end Poincare
