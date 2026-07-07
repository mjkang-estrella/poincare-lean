import Poincare.Global.OmegaGronwall
import Poincare.Global.EndpointContinuity

/-!
# Transition landing boundary

This module records the non-global residual variant needed by the hosted
third-variation assembly.  The hosted `Ω` producer is local in the perturbation
variable, while the older residual consumer asked for global `∀ h` data.  The
lemmas below keep the same Gronwall proof but require the linearized endpoint
data only eventually near zero.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Asymptotics Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
Frechet endpoint derivative for a local flow when the linearized endpoint
family and its representing CLM are known only eventually near the zero
perturbation.

This is the same residual/Gronwall comparison as
`flowEndpoint_hasFDerivAt_of_linearized_gronwall`, but with the exact
eventual shape supplied by hosted Picard-Lindelöf families.
-/
theorem flowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
    {F : X → X} {β : X → ℝ → X}
    {z : X} {Ψ : X → ℝ → X} {D : X →L[ℝ] X}
    {T a : ℝ} {K : ℝ≥0} {p : X} {t : ℝ}
    (hT : 0 < T)
    (hLip : LipschitzOnWith K F (closedBall p (a + 1)))
    (hTaylor :
      ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ base ∈ closedBall p (a + 1),
        ∀ q ∈ closedBall p (a + 1),
          ‖q - base‖ ≤ ρ →
            ‖F q - F base - fderiv ℝ F base (q - base)‖ ≤
              ε * ‖q - base‖)
    (hbase0 : β z 0 = z)
    (hbase_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β z) (F (β z τ)) (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T, β z τ ∈ closedBall p a)
    (hpert : ∀ᶠ h in 𝓝 (0 : X),
      β (z + h) 0 = z + h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (z + h)) (F (β (z + h) τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T, β (z + h) τ ∈ closedBall p a)
    (hΨD : ∀ᶠ h in 𝓝 (0 : X),
      Ψ h 0 = h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ψ h)
            (fderiv ℝ F (β z τ) (Ψ h τ)) (Icc (0 : ℝ) T) τ) ∧
        Ψ h t = D h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (fun y : X => β y t) D z := by
  let R : X → ℝ → X := fun h τ =>
    β (z + h) τ - β z τ - Ψ h τ
  let Rder : X → ℝ → X := fun h τ =>
    F (β (z + h) τ) - F (β z τ) -
      fderiv ℝ F (β z τ) (Ψ h τ)
  let C : ℝ := Real.exp ((K : ℝ) * T)
  have hT_nonneg : 0 ≤ T := hT.le
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hIco_subset : Ico (0 : ℝ) T ⊆ Icc (0 : ℝ) T :=
    Ico_subset_Icc_self
  have hclose : ∀ᶠ h in 𝓝 (0 : X),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖β (z + h) τ - β z τ‖ ≤ C * ‖h‖ := by
    filter_upwards [hpert] with h hh
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    have hpert_cont : ContinuousOn (β (z + h)) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β (z + h) r)) (by
          intro r hr
          simpa using hh.2.1 r hr)
    have hbase_cont : ContinuousOn (β z) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β z r)) (by
          intro r hr
          simpa using hbase_der r hr)
    have hdist :
        dist (β (z + h) τ) (β z τ) ≤
          dist (z + h) z * Real.exp ((K : ℝ) * (τ - 0)) := by
      exact
        dist_le_of_trajectories_ODE_of_mem
          (v := fun _ : ℝ => F)
          (s := fun _ : ℝ => closedBall p (a + 1))
          (K := K) (a := 0) (b := T)
          (by
            intro _ _
            simpa using hLip)
          hpert_cont
          (by
            intro r hr
            have hrIcc : r ∈ Icc (0 : ℝ) T := hIco_subset hr
            exact (hh.2.1 r hrIcc).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
          (by
            intro r hr
            exact closedBall_subset_closedBall (by linarith)
              (hh.2.2 r (hIco_subset hr)))
          hbase_cont
          (by
            intro r hr
            have hrIcc : r ∈ Icc (0 : ℝ) T := hIco_subset hr
            exact (hbase_der r hrIcc).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
          (by
            intro r hr
            exact closedBall_subset_closedBall (by linarith)
              (hbase_mem r (hIco_subset hr)))
          (by
            rw [hh.1, hbase0])
          τ hτIcc
    have hexp_le :
        Real.exp ((K : ℝ) * (τ - 0)) ≤ Real.exp ((K : ℝ) * T) := by
      apply Real.exp_le_exp.mpr
      have hτ_le : τ ≤ T := hτIcc.2
      have hK_nonneg : 0 ≤ (K : ℝ) := K.2
      nlinarith
    calc
      ‖β (z + h) τ - β z τ‖ =
          dist (β (z + h) τ) (β z τ) := by
            rw [dist_eq_norm]
      _ ≤ dist (z + h) z * Real.exp ((K : ℝ) * (τ - 0)) :=
          hdist
      _ ≤ ‖h‖ * Real.exp ((K : ℝ) * T) := by
          have hdist0 : dist (z + h) z = ‖h‖ := by
            simp [dist_eq_norm]
          rw [hdist0]
          exact mul_le_mul_of_nonneg_left hexp_le (norm_nonneg h)
      _ = C * ‖h‖ := by
          simp [C]
          ring
  have hRcont : ∀ᶠ h in 𝓝 (0 : X),
      ContinuousOn (R h) (Icc (0 : ℝ) T) := by
    filter_upwards [hpert, hΨD] with h hh hlin
    have hpert_cont : ContinuousOn (β (z + h)) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β (z + h) r)) (by
          intro r hr
          simpa using hh.2.1 r hr)
    have hbase_cont : ContinuousOn (β z) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β z r)) (by
          intro r hr
          simpa using hbase_der r hr)
    have hΨ_cont : ContinuousOn (Ψ h) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => fderiv ℝ F (β z r) (Ψ h r)) (by
          intro r hr
          exact hlin.2.1 r hr)
    simpa [R] using (hpert_cont.sub hbase_cont).sub hΨ_cont
  have hRderiv : ∀ᶠ h in 𝓝 (0 : X),
      ∀ τ ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (R h) (Rder h τ) (Ici τ) τ := by
    filter_upwards [hpert, hΨD] with h hh hlin
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    have hnhds : Icc (0 : ℝ) T ∈ 𝓝[Ici τ] τ :=
      Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩
    have hpert_der :
        HasDerivWithinAt (β (z + h))
          (F (β (z + h) τ)) (Ici τ) τ := by
      simpa using (hh.2.1 τ hτIcc).mono_of_mem_nhdsWithin hnhds
    have hbase_der' :
        HasDerivWithinAt (β z) (F (β z τ)) (Ici τ) τ := by
      simpa using (hbase_der τ hτIcc).mono_of_mem_nhdsWithin hnhds
    have hΨ_der' :
        HasDerivWithinAt (Ψ h)
          (fderiv ℝ F (β z τ) (Ψ h τ)) (Ici τ) τ := by
      simpa using (hlin.2.1 τ hτIcc).mono_of_mem_nhdsWithin hnhds
    simpa [R, Rder] using (hpert_der.sub hbase_der').sub hΨ_der'
  have hR0 : ∀ᶠ h in 𝓝 (0 : X), R h 0 = 0 := by
    filter_upwards [hpert, hΨD] with h hh hlin
    simp [R, hh.1, hbase0, hlin.1]
  have hbound : ∀ μ > (0 : ℝ), ∀ᶠ h in 𝓝 (0 : X),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖Rder h τ‖ ≤ (K : ℝ) * ‖R h τ‖ + μ * ‖h‖ := by
    intro μ hμ
    let θ : ℝ := μ / (C + 1)
    have hden_pos : 0 < C + 1 := by positivity
    have hθ_pos : 0 < θ := by
      dsimp [θ]
      positivity
    have hθC_le : θ * C ≤ μ := by
      dsimp [θ]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
      nlinarith [hμ.le, hC_nonneg]
    rcases hTaylor θ hθ_pos with
      ⟨ρ, hρ_pos, hrem⟩
    have hsmall : ∀ᶠ h in 𝓝 (0 : X), C * ‖h‖ ≤ ρ :=
      eventually_const_mul_norm_le_nhds_zero_normed
        (P := X) hC_nonneg hρ_pos
    filter_upwards [hpert, hclose, hsmall] with h hh hhclose hsmall_h
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    let base : X := β z τ
    let q : X := β (z + h) τ
    let A : X →L[ℝ] X := fderiv ℝ F base
    have hbase_mem_small : base ∈ closedBall p a := by
      simpa [base] using hbase_mem τ hτIcc
    have hq_mem_small : q ∈ closedBall p a := by
      simpa [q] using hh.2.2 τ hτIcc
    have hbase_mem_wide : base ∈ closedBall p (a + 1) :=
      closedBall_subset_closedBall (by linarith) hbase_mem_small
    have hq_mem_wide : q ∈ closedBall p (a + 1) :=
      closedBall_subset_closedBall (by linarith) hq_mem_small
    have hdiff : ‖q - base‖ ≤ C * ‖h‖ := by
      simpa [q, base] using hhclose τ hτ
    have hcloseρ : ‖q - base‖ ≤ ρ := hdiff.trans hsmall_h
    have hremθ :
        ‖F q - F base - A (q - base)‖ ≤ θ * ‖q - base‖ := by
      simpa [A] using
        hrem base hbase_mem_wide q hq_mem_wide hcloseρ
    have hremμ :
        ‖F q - F base - A (q - base)‖ ≤ μ * ‖h‖ := by
      calc
        ‖F q - F base - A (q - base)‖
            ≤ θ * ‖q - base‖ := hremθ
        _ ≤ θ * (C * ‖h‖) :=
          mul_le_mul_of_nonneg_left hdiff hθ_pos.le
        _ = (θ * C) * ‖h‖ := by ring
        _ ≤ μ * ‖h‖ :=
          mul_le_mul_of_nonneg_right hθC_le (norm_nonneg h)
    have hbase_nhds : closedBall p (a + 1) ∈ 𝓝 base :=
      closedBall_radius_add_one_mem_nhds hbase_mem_small
    have hAnorm : ‖A‖ ≤ (K : ℝ) := by
      have hfd : ‖fderiv ℝ F base‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hbase_nhds hLip
      simpa [A] using hfd
    have hlinear :
        ‖A (q - base - Ψ h τ)‖ ≤
          (K : ℝ) * ‖q - base - Ψ h τ‖ := by
      calc
        ‖A (q - base - Ψ h τ)‖
            ≤ ‖A‖ * ‖q - base - Ψ h τ‖ :=
          ContinuousLinearMap.le_opNorm A (q - base - Ψ h τ)
        _ ≤ (K : ℝ) * ‖q - base - Ψ h τ‖ :=
          mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    have hrewrite :
        Rder h τ =
          (F q - F base - A (q - base)) + A (q - base - Ψ h τ) := by
      simp only [Rder, A, q, base, map_sub]
      abel
    have hraw :
        ‖Rder h τ‖ ≤
          (K : ℝ) * ‖q - base - Ψ h τ‖ + μ * ‖h‖ := by
      calc
        ‖Rder h τ‖ =
            ‖(F q - F base - A (q - base)) +
                A (q - base - Ψ h τ)‖ := by
              rw [hrewrite]
        _ ≤ ‖F q - F base - A (q - base)‖ +
              ‖A (q - base - Ψ h τ)‖ :=
            norm_add_le _ _
        _ ≤ μ * ‖h‖ + (K : ℝ) * ‖q - base - Ψ h τ‖ :=
            add_le_add hremμ hlinear
        _ = (K : ℝ) * ‖q - base - Ψ h τ‖ + μ * ‖h‖ := by
            ring
    simpa [R, Rder, q, base] using hraw
  have hunif :
      ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝 (0 : X),
        ∀ τ ∈ Icc (0 : ℝ) T, ‖R h τ‖ ≤ ε * ‖h‖ :=
    residual_uniform_isLittleO_on_Icc_of_gronwall_bound_param
      (R := R) (R' := Rder) hT_nonneg K.2 hRcont hRderiv hR0 hbound
  have hres :
      (fun h : X => R h t) =o[𝓝 (0 : X)] (fun h : X => h) :=
    residual_isLittleO_at_fixedTime_of_uniform_param (R := R) hunif ht
  have hres' :
      (fun h : X => β (z + h) t - β z t - D h)
        =o[𝓝 (0 : X)] (fun h : X => h) := by
    rw [isLittleO_iff] at hres ⊢
    intro c hc
    filter_upwards [hres hc, hΨD] with h hsmall hlin
    simpa [R, hlin.2.2] using hsmall
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only using hres'

namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
/--
Local-eventual version of the doubly augmented endpoint derivative theorem.

The only change from `DoublyResidual` is the final third-variation package:
`Ω h 0 = h`, the third-variation ODE, and `Ω h t = D h` are required only
eventually near `h = 0`.
-/
theorem chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A}
    {y : A × A} {Ω : A × A → ℝ → A × A}
    {D : (A × A) →L[ℝ] (A × A)}
    {T a : ℝ} {p : A × A} {t : ℝ}
    (hT : 0 < T)
    (hbaseβ0 : β y.1 0 = y.1)
    (hbaseβder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β y.1)
        (augmentedGeodesicFlowField (chartChristoffelField g x₀) (β y.1 τ))
        (Icc (0 : ℝ) T) τ)
    (hbaseΞ0 : Ξ y.1 y.2 0 = y.2)
    (hbaseΞder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ξ y.1 y.2)
        (secondVariationFlowFieldAlong (chartChristoffelField g x₀)
          (β y.1) τ (Ξ y.1 y.2 τ))
        (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T,
      (β y.1 τ, Ξ y.1 y.2 τ) ∈ closedBall p a)
    (hpert : ∀ᶠ h in 𝓝 (0 : A × A),
      β (y + h).1 0 = (y + h).1 ∧
        Ξ (y + h).1 (y + h).2 0 = (y + h).2 ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (y + h).1)
            (augmentedGeodesicFlowField (chartChristoffelField g x₀)
              (β (y + h).1 τ))
            (Icc (0 : ℝ) T) τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ξ (y + h).1 (y + h).2)
            (secondVariationFlowFieldAlong (chartChristoffelField g x₀)
              (β (y + h).1) τ (Ξ (y + h).1 (y + h).2 τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T,
          (β (y + h).1 τ, Ξ (y + h).1 (y + h).2 τ) ∈ closedBall p a)
    (hΩD : ∀ᶠ h in 𝓝 (0 : A × A),
      Ω h 0 = h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ω h)
            (fderiv ℝ
              (fun y' : A × A =>
                let F : A → A :=
                  augmentedGeodesicFlowField (chartChristoffelField g x₀)
                (F y'.1, (fderiv ℝ F y'.1) y'.2))
              (β y.1 τ, Ξ y.1 y.2 τ) (Ω h τ))
            (Icc (0 : ℝ) T) τ) ∧
        Ω h t = D h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt
      (fun y' : A × A => (β y'.1 t, Ξ y'.1 y'.2 t)) D y := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : A → A := augmentedGeodesicFlowField Γ
  let doubleF : A × A → A × A := fun y' =>
    (F y'.1, (fderiv ℝ F y'.1) y'.2)
  let Υ : A × A → ℝ → A × A := fun y' τ =>
    (β y'.1 τ, Ξ y'.1 y'.2 τ)
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
        (g := g) (x₀ := x₀) (p := (0 : A)) (a := 0) with
    ⟨hF_two, _hFLip⟩
  have hbase : ContDiff ℝ 1 (fun y' : A × A => F y'.1) :=
    (hF_two.of_le (by norm_num)).comp contDiff_fst
  have hlin :
      ContDiff ℝ 1
        (fun y' : A × A => (fderiv ℝ F y'.1 : A →L[ℝ] A) y'.2) := by
    simpa [F, Γ] using
      (hF_two.contDiff_fderiv_apply (m := 1) (by norm_num))
  have hdouble : ContDiff ℝ 1 doubleF := by
    simpa [doubleF] using hbase.prodMk hlin
  rcases hdouble.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall p (a + 1))
      (isCompact_closedBall p (a + 1)) with
    ⟨K, hLip⟩
  have hTaylor :
      ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ base ∈ closedBall p (a + 1),
        ∀ q ∈ closedBall p (a + 1),
          ‖q - base‖ ≤ ρ →
            ‖doubleF q - doubleF base -
                fderiv ℝ doubleF base (q - base)‖ ≤
              ε * ‖q - base‖ := by
    simpa [doubleF, F, Γ] using
      chartChristoffel_doublyAugmentedGeodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
        (g := g) (x₀ := x₀)
        (Kset := closedBall p (a + 1))
        (isCompact_closedBall p (a + 1))
        (convex_closedBall p (a + 1))
  have hbase0 : Υ y 0 = y := by
    change (β y.1 0, Ξ y.1 y.2 0) = y
    rw [hbaseβ0, hbaseΞ0]
  have hbase_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Υ y) (doubleF (Υ y τ)) (Icc (0 : ℝ) T) τ := by
    intro τ hτ
    simpa [Υ, doubleF, F, Γ, secondVariationFlowFieldAlong,
      secondVariationFlowOperator] using
      (hbaseβder τ hτ).prodMk (hbaseΞder τ hτ)
  have hpert_double : ∀ᶠ h in 𝓝 (0 : A × A),
      Υ (y + h) 0 = y + h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Υ (y + h))
            (doubleF (Υ (y + h) τ)) (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T, Υ (y + h) τ ∈ closedBall p a := by
    filter_upwards [hpert] with h hh
    rcases hh with ⟨hβ0, hΞ0, hβder, hΞder, hmem⟩
    constructor
    · change
        (β (y + h).1 0, Ξ (y + h).1 (y + h).2 0) = y + h
      rw [hβ0, hΞ0]
    constructor
    · intro τ hτ
      simpa [Υ, doubleF, F, Γ, secondVariationFlowFieldAlong,
        secondVariationFlowOperator] using
        (hβder τ hτ).prodMk (hΞder τ hτ)
    · intro τ hτ
      simpa [Υ] using hmem τ hτ
  have hΩD' : ∀ᶠ h in 𝓝 (0 : A × A),
      Ω h 0 = h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ω h)
            (fderiv ℝ doubleF (Υ y τ) (Ω h τ))
            (Icc (0 : ℝ) T) τ) ∧
        Ω h t = D h := by
    filter_upwards [hΩD] with h hh
    rcases hh with ⟨h0, hder, hD⟩
    exact
      ⟨h0, by
        intro τ hτ
        simpa [Υ, doubleF, F, Γ] using hder τ hτ,
        hD⟩
  have hresult :=
    flowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
      (F := doubleF) (β := Υ) (z := y) (Ψ := Ω) (D := D)
      (T := T) (a := a) (K := K) (p := p) (t := t)
      hT hLip hTaylor hbase0 hbase_der hbase_mem hpert_double hΩD' ht
  simpa [Υ] using hresult

omit [T2Space M] in
/--
Projected endpoint derivative for the second-variation endpoint field from
eventual third-variation data.
-/
theorem chartChristoffel_secondVariation_endpoint_hasFDerivAt_of_thirdVariation_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A}
    {y : A × A} {Ω : A × A → ℝ → A × A}
    {D : (A × A) →L[ℝ] (A × A)}
    {T a : ℝ} {p : A × A} {t : ℝ}
    (hT : 0 < T)
    (hbaseβ0 : β y.1 0 = y.1)
    (hbaseβder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β y.1)
        (augmentedGeodesicFlowField (chartChristoffelField g x₀) (β y.1 τ))
        (Icc (0 : ℝ) T) τ)
    (hbaseΞ0 : Ξ y.1 y.2 0 = y.2)
    (hbaseΞder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ξ y.1 y.2)
        (secondVariationFlowFieldAlong (chartChristoffelField g x₀)
          (β y.1) τ (Ξ y.1 y.2 τ))
        (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T,
      (β y.1 τ, Ξ y.1 y.2 τ) ∈ closedBall p a)
    (hpert : ∀ᶠ h in 𝓝 (0 : A × A),
      β (y + h).1 0 = (y + h).1 ∧
        Ξ (y + h).1 (y + h).2 0 = (y + h).2 ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (y + h).1)
            (augmentedGeodesicFlowField (chartChristoffelField g x₀)
              (β (y + h).1 τ))
            (Icc (0 : ℝ) T) τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ξ (y + h).1 (y + h).2)
            (secondVariationFlowFieldAlong (chartChristoffelField g x₀)
              (β (y + h).1) τ (Ξ (y + h).1 (y + h).2 τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T,
          (β (y + h).1 τ, Ξ (y + h).1 (y + h).2 τ) ∈ closedBall p a)
    (hΩD : ∀ᶠ h in 𝓝 (0 : A × A),
      Ω h 0 = h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ω h)
            (fderiv ℝ
              (fun y' : A × A =>
                let F : A → A :=
                  augmentedGeodesicFlowField (chartChristoffelField g x₀)
                (F y'.1, (fderiv ℝ F y'.1) y'.2))
              (β y.1 τ, Ξ y.1 y.2 τ) (Ω h τ))
            (Icc (0 : ℝ) T) τ) ∧
        Ω h t = D h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt
      (fun y' : A × A => Ξ y'.1 y'.2 t)
      ((ContinuousLinearMap.snd ℝ A A).comp D) y := by
  have hpaired :
      HasFDerivAt
        (fun y' : A × A => (β y'.1 t, Ξ y'.1 y'.2 t)) D y :=
    chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_eventually
      (g := g) (x₀ := x₀) (β := β) (Ξ := Ξ) (y := y) (Ω := Ω)
      (D := D) (T := T) (a := a) (p := p) (t := t)
      hT hbaseβ0 hbaseβder hbaseΞ0 hbaseΞder hbase_mem hpert
      hΩD ht
  simpa using hpaired.snd

end GeodesicTransport
end Poincare
