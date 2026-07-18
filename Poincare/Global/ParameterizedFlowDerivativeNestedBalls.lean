import Poincare.Global.ParameterizedFlowDerivative

/-!
# Parameterized flow derivatives on nested tubes

The original residual theorem uses the convenient fixed enlargement
`closedBall p (a + 1)`.  Picard--Lindelof supplies instead a strict but
arbitrarily small margin between an inner trajectory tube and an outer
regularity tube.  This file records the same proof with radii `inner < outer`.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Asymptotics Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

variable {P X : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Frechet differentiability of a parameterized flow endpoint when the
trajectories remain in a strict inner ball and Lipschitz/Taylor control is
available on a possibly much thinner outer ball. -/
theorem parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually_nestedBalls
    {F : X → X} {beta : P → ℝ → X} {q : P}
    {J : P →L[ℝ] X} {Psi : P → ℝ → X} {D : P →L[ℝ] X}
    {T inner outer : ℝ} {K : ℝ≥0} {p : X} {t : ℝ}
    (hT : 0 < T)
    (hinnerOuter : inner < outer)
    (hLip : LipschitzOnWith K F (closedBall p outer))
    (hTaylor :
      ∀ epsilon > (0 : ℝ), ∃ rho > (0 : ℝ),
        ∀ base ∈ closedBall p outer, ∀ x ∈ closedBall p outer,
          ‖x - base‖ ≤ rho →
            ‖F x - F base - fderiv ℝ F base (x - base)‖ ≤
              epsilon * ‖x - base‖)
    (hbase_der : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (beta q) (F (beta q tau))
        (Icc (0 : ℝ) T) tau)
    (hbase_mem : ∀ tau ∈ Icc (0 : ℝ) T,
      beta q tau ∈ closedBall p inner)
    (hpert : ∀ᶠ h in nhds (0 : P),
      beta (q + h) 0 = beta q 0 + J h ∧
        (∀ tau ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (beta (q + h)) (F (beta (q + h) tau))
            (Icc (0 : ℝ) T) tau) ∧
        ∀ tau ∈ Icc (0 : ℝ) T,
          beta (q + h) tau ∈ closedBall p inner)
    (hPsiD : ∀ᶠ h in nhds (0 : P),
      Psi h 0 = J h ∧
        (∀ tau ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Psi h)
            (fderiv ℝ F (beta q tau) (Psi h tau))
            (Icc (0 : ℝ) T) tau) ∧
        Psi h t = D h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (fun y : P ↦ beta y t) D q := by
  let R : P → ℝ → X := fun h tau ↦
    beta (q + h) tau - beta q tau - Psi h tau
  let Rder : P → ℝ → X := fun h tau ↦
    F (beta (q + h) tau) - F (beta q tau) -
      fderiv ℝ F (beta q tau) (Psi h tau)
  let C : ℝ := Real.exp ((K : ℝ) * T) * ‖J‖
  have hTnonneg : 0 ≤ T := hT.le
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hIco : Ico (0 : ℝ) T ⊆ Icc (0 : ℝ) T := Ico_subset_Icc_self
  have hinnerSubset : closedBall p inner ⊆ closedBall p outer :=
    closedBall_subset_closedBall hinnerOuter.le
  have hclose : ∀ᶠ h in nhds (0 : P),
      ∀ tau ∈ Ico (0 : ℝ) T,
        ‖beta (q + h) tau - beta q tau‖ ≤ C * ‖h‖ := by
    filter_upwards [hpert] with h hh
    intro tau htau
    have htauIcc : tau ∈ Icc (0 : ℝ) T := hIco htau
    have hpertCont : ContinuousOn (beta (q + h)) (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn
        (f' := fun r ↦ F (beta (q + h) r)) (fun r hr ↦ hh.2.1 r hr)
    have hbaseCont : ContinuousOn (beta q) (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn
        (f' := fun r ↦ F (beta q r)) (fun r hr ↦ hbase_der r hr)
    have hdist :
        dist (beta (q + h) tau) (beta q tau) ≤
          dist (beta (q + h) 0) (beta q 0) *
            Real.exp ((K : ℝ) * (tau - 0)) := by
      exact dist_le_of_trajectories_ODE_of_mem
        (v := fun _ : ℝ ↦ F) (s := fun _ : ℝ ↦ closedBall p outer)
        (K := K) (a := 0) (b := T)
        (fun _ _ ↦ hLip) hpertCont
        (fun r hr ↦
          (hh.2.1 r (hIco hr)).mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
        (fun r hr ↦ hinnerSubset (hh.2.2 r (hIco hr)))
        hbaseCont
        (fun r hr ↦
          (hbase_der r (hIco hr)).mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
        (fun r hr ↦ hinnerSubset (hbase_mem r (hIco hr)))
        le_rfl tau htauIcc
    have hexp :
        Real.exp ((K : ℝ) * (tau - 0)) ≤ Real.exp ((K : ℝ) * T) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by simpa using htauIcc.2) K.2
    have hinitial :
        dist (beta (q + h) 0) (beta q 0) ≤ ‖J‖ * ‖h‖ := by
      rw [hh.1, dist_eq_norm]
      simpa using ContinuousLinearMap.le_opNorm J h
    calc
      ‖beta (q + h) tau - beta q tau‖ =
          dist (beta (q + h) tau) (beta q tau) := by rw [dist_eq_norm]
      _ ≤ dist (beta (q + h) 0) (beta q 0) *
          Real.exp ((K : ℝ) * (tau - 0)) := hdist
      _ ≤ (‖J‖ * ‖h‖) * Real.exp ((K : ℝ) * T) :=
        mul_le_mul hinitial hexp (Real.exp_pos _).le
          (mul_nonneg (norm_nonneg J) (norm_nonneg h))
      _ = C * ‖h‖ := by simp [C]; ring
  have hRcont : ∀ᶠ h in nhds (0 : P),
      ContinuousOn (R h) (Icc (0 : ℝ) T) := by
    filter_upwards [hpert, hPsiD] with h hh hlin
    have hpertCont : ContinuousOn (beta (q + h)) (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn
        (f' := fun r ↦ F (beta (q + h) r)) (fun r hr ↦ hh.2.1 r hr)
    have hbaseCont : ContinuousOn (beta q) (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn
        (f' := fun r ↦ F (beta q r)) (fun r hr ↦ hbase_der r hr)
    have hPsiCont : ContinuousOn (Psi h) (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn
        (f' := fun r ↦ fderiv ℝ F (beta q r) (Psi h r))
        (fun r hr ↦ hlin.2.1 r hr)
    simpa [R] using (hpertCont.sub hbaseCont).sub hPsiCont
  have hRderiv : ∀ᶠ h in nhds (0 : P),
      ∀ tau ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (R h) (Rder h tau) (Ici tau) tau := by
    filter_upwards [hpert, hPsiD] with h hh hlin
    intro tau htau
    have htauIcc : tau ∈ Icc (0 : ℝ) T := hIco htau
    have hnhds : Icc (0 : ℝ) T ∈ nhdsWithin tau (Ici tau) :=
      Icc_mem_nhdsGE_of_mem ⟨htau.1, htau.2⟩
    have hp := (hh.2.1 tau htauIcc).mono_of_mem_nhdsWithin hnhds
    have hb := (hbase_der tau htauIcc).mono_of_mem_nhdsWithin hnhds
    have hl := (hlin.2.1 tau htauIcc).mono_of_mem_nhdsWithin hnhds
    simpa [R, Rder] using (hp.sub hb).sub hl
  have hRzero : ∀ᶠ h in nhds (0 : P), R h 0 = 0 := by
    filter_upwards [hpert, hPsiD] with h hh hlin
    simp [R, hh.1, hlin.1]
  have hbound : ∀ mu > (0 : ℝ), ∀ᶠ h in nhds (0 : P),
      ∀ tau ∈ Ico (0 : ℝ) T,
        ‖Rder h tau‖ ≤ (K : ℝ) * ‖R h tau‖ + mu * ‖h‖ := by
    intro mu hmu
    let theta : ℝ := mu / (C + 1)
    have hden : 0 < C + 1 := by positivity
    have htheta : 0 < theta := by dsimp only [theta]; positivity
    have hthetaC : theta * C ≤ mu := by
      dsimp only [theta]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [hmu.le, hCnonneg]
    rcases hTaylor theta htheta with ⟨rho, hrho, hrem⟩
    have hsmall : ∀ᶠ h in nhds (0 : P), C * ‖h‖ ≤ rho :=
      eventually_const_mul_norm_le_nhds_zero_normed
        (P := P) hCnonneg hrho
    filter_upwards [hpert, hclose, hsmall] with h hh hhclose hsmallh
    intro tau htau
    have htauIcc : tau ∈ Icc (0 : ℝ) T := hIco htau
    let base : X := beta q tau
    let y : X := beta (q + h) tau
    let A : X →L[ℝ] X := fderiv ℝ F base
    have hbaseInner : base ∈ closedBall p inner := by
      simpa [base] using hbase_mem tau htauIcc
    have hyInner : y ∈ closedBall p inner := by
      simpa [y] using hh.2.2 tau htauIcc
    have hbaseOuter : base ∈ closedBall p outer := hinnerSubset hbaseInner
    have hyOuter : y ∈ closedBall p outer := hinnerSubset hyInner
    have hdiff : ‖y - base‖ ≤ C * ‖h‖ := by
      simpa [y, base] using hhclose tau htau
    have hcloseRho : ‖y - base‖ ≤ rho := hdiff.trans hsmallh
    have hremTheta :
        ‖F y - F base - A (y - base)‖ ≤ theta * ‖y - base‖ := by
      simpa [A] using hrem base hbaseOuter y hyOuter hcloseRho
    have hremMu :
        ‖F y - F base - A (y - base)‖ ≤ mu * ‖h‖ := by
      calc
        ‖F y - F base - A (y - base)‖ ≤ theta * ‖y - base‖ := hremTheta
        _ ≤ theta * (C * ‖h‖) :=
          mul_le_mul_of_nonneg_left hdiff htheta.le
        _ = (theta * C) * ‖h‖ := by ring
        _ ≤ mu * ‖h‖ :=
          mul_le_mul_of_nonneg_right hthetaC (norm_nonneg h)
    have hbaseNhd : closedBall p outer ∈ nhds base := by
      apply closedBall_mem_nhds_of_mem
      rw [Metric.mem_ball]
      exact (mem_closedBall.mp hbaseInner).trans_lt hinnerOuter
    have hAnorm : ‖A‖ ≤ (K : ℝ) := by
      have hfd := norm_fderiv_le_of_lipschitzOn
        (𝕜 := ℝ) hbaseNhd hLip
      simpa [A] using hfd
    have hlinear :
        ‖A (y - base - Psi h tau)‖ ≤
          (K : ℝ) * ‖y - base - Psi h tau‖ := by
      calc
        ‖A (y - base - Psi h tau)‖ ≤
            ‖A‖ * ‖y - base - Psi h tau‖ :=
          ContinuousLinearMap.le_opNorm A _
        _ ≤ (K : ℝ) * ‖y - base - Psi h tau‖ :=
          mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    have hrewrite :
        Rder h tau =
          (F y - F base - A (y - base)) +
            A (y - base - Psi h tau) := by
      simp only [Rder, A, y, base, map_sub]
      abel
    have hraw :
        ‖Rder h tau‖ ≤
          (K : ℝ) * ‖y - base - Psi h tau‖ + mu * ‖h‖ := by
      calc
        ‖Rder h tau‖ =
            ‖(F y - F base - A (y - base)) +
              A (y - base - Psi h tau)‖ := by rw [hrewrite]
        _ ≤ ‖F y - F base - A (y - base)‖ +
              ‖A (y - base - Psi h tau)‖ := norm_add_le _ _
        _ ≤ mu * ‖h‖ + (K : ℝ) * ‖y - base - Psi h tau‖ :=
          add_le_add hremMu hlinear
        _ = (K : ℝ) * ‖y - base - Psi h tau‖ + mu * ‖h‖ := by ring
    simpa [R, Rder, y, base] using hraw
  have huniform :
      ∀ epsilon > (0 : ℝ), ∀ᶠ h in nhds (0 : P),
        ∀ tau ∈ Icc (0 : ℝ) T, ‖R h tau‖ ≤ epsilon * ‖h‖ :=
    residual_uniform_isLittleO_on_Icc_of_gronwall_bound_param
      (R := R) (R' := Rder) hTnonneg K.2 hRcont hRderiv hRzero hbound
  have hres :
      (fun h : P ↦ R h t) =o[nhds (0 : P)] (fun h : P ↦ h) :=
    residual_isLittleO_at_fixedTime_of_uniform_param (R := R) huniform ht
  have hres' :
      (fun h : P ↦ beta (q + h) t - beta q t - D h)
        =o[nhds (0 : P)] (fun h : P ↦ h) := by
    rw [isLittleO_iff] at hres ⊢
    intro c hc
    filter_upwards [hres hc, hPsiD] with h hsmall hlin
    simpa [R, hlin.2.2] using hsmall
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only using hres'

end Poincare
