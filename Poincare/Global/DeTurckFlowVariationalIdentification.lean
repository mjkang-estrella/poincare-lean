import Poincare.Global.DeTurckInverseGaugeODE
import Poincare.Global.GeodesicLinearized
import Poincare.Global.ParameterizedFlowDerivative

/-!
# Variational identification for the inverse DeTurck coordinate flow

This file closes the coordinate-level smooth-dependence step.  A common local
Picard--Lindelof point flow is constructed in the autonomous `(time, point)`
space.  The linearized equation is solved on the same (shrunk) interval, and
the repository's residual/Gronwall endpoint theorem identifies that solution
with the Frechet derivative of the point flow in its initial point.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology NNReal

namespace Poincare

section CoordinatePointFlow

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Autonomous `(time, point)` form of the inverse-gauge ODE. -/
def inverseGaugePointExtendedField (W : ℝ → E → E) : ℝ × E → ℝ × E :=
  fun q => (1, -W q.1 q.2)

/-- Joint `C¹` regularity of the time-dependent field gives `C¹` regularity
of its autonomous point extension. -/
theorem contDiff_one_inverseGaugePointExtendedField
    (W : ℝ → E → E)
    (hW : ContDiff ℝ 1 (Function.uncurry W)) :
    ContDiff ℝ 1 (inverseGaugePointExtendedField W) := by
  have htx : ContDiff ℝ 1 (fun q : ℝ × E => (q.1, q.2)) :=
    contDiff_fst.prodMk contDiff_snd
  have hWq : ContDiff ℝ 1 (fun q : ℝ × E => W q.1 q.2) := by
    simpa [Function.uncurry] using hW.comp htx
  simpa [inverseGaugePointExtendedField] using contDiff_const.prodMk hWq.neg

/-- The derivative of the autonomous point field in a pure point direction.
Only the spatial derivative of `W` enters; the time component is zero. -/
theorem fderiv_inverseGaugePointExtendedField_apply_inr
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDW : ∀ t x, HasFDerivAt (W t) (DW t x) x)
    (t : ℝ) (x h : E) :
    fderiv ℝ (inverseGaugePointExtendedField W) (t, x) (0, h) =
      (0, -(DW t x h)) := by
  let path : ℝ → ℝ × E := fun s => (t, x + s • h)
  have hline : HasDerivAt (fun s : ℝ => x + s • h) h 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const h).const_add x
  have hpath : HasDerivAt path (0, h) 0 := by
    simpa [path] using (hasDerivAt_const (x := (0 : ℝ)) t).prodMk hline
  have hfieldCurve : HasDerivAt
      (inverseGaugePointExtendedField W ∘ path)
      (fderiv ℝ (inverseGaugePointExtendedField W) (t, x) (0, h)) 0 := by
    have hf : HasFDerivAt (inverseGaugePointExtendedField W)
        (fderiv ℝ (inverseGaugePointExtendedField W) (t, x)) (path 0) := by
      simpa [path] using
        ((contDiff_one_inverseGaugePointExtendedField W hW).differentiable
          (by norm_num) (t, x)).hasFDerivAt
    exact hf.comp_hasDerivAt 0 hpath
  have hWcurve : HasDerivAt (fun s : ℝ => W t (x + s • h))
      (DW t x h) 0 :=
    (by
      have hw : HasFDerivAt (W t) (DW t x) (x + (0 : ℝ) • h) := by
        simpa using hDW t x
      exact hw.comp_hasDerivAt 0 hline)
  have hexplicit : HasDerivAt
      (inverseGaugePointExtendedField W ∘ path)
      (0, -(DW t x h)) 0 := by
    simpa [inverseGaugePointExtendedField, path, Function.comp_def] using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).prodMk hWcurve.neg
  exact hfieldCurve.unique hexplicit

/-- The time coordinate of an autonomous point-flow solution is `t₀ + s`. -/
theorem inverseGaugePointFlow_time_eq
    (W : ℝ → E → E) {gamma : ℝ → ℝ × E}
    {t₀ T : ℝ} {x₀ : E}
    (hgamma₀ : gamma 0 = (t₀, x₀))
    (hgamma : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt gamma (inverseGaugePointExtendedField W (gamma s))
        (Icc (0 : ℝ) T) s) :
    ∀ s ∈ Icc (0 : ℝ) T, (gamma s).1 = t₀ + s := by
  have hder : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r : ℝ => (gamma r).1 - (t₀ + r)) 0
        (Icc (0 : ℝ) T) s := by
    intro s hs
    have hfst := (hgamma s hs).hasFDerivWithinAt.fst.hasDerivWithinAt
    have hline : HasDerivWithinAt (fun r : ℝ => t₀ + r) 1
        (Icc (0 : ℝ) T) s :=
      ((hasDerivAt_id s).const_add t₀).hasDerivWithinAt
    simpa [inverseGaugePointExtendedField] using hfst.sub hline
  intro s hs
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T :=
    ⟨le_rfl, hs.1.trans hs.2⟩
  have hmvt :=
    (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r : ℝ => (gamma r).1 - (t₀ + r))
      (f' := fun _ : ℝ => (0 : ℝ)) (C := (0 : ℝ)) hder
      (fun _ _ => by simp)
      hzero hs
  have hnorm : ‖(gamma s).1 - (t₀ + s)‖ ≤ 0 := by
    simpa [hgamma₀] using hmvt
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Local point-flow differentiability in the initial point.

The theorem constructs one common Picard--Lindelof family `phi`, an
operator-valued solution `D` of the variational equation, and proves that at
every time in a common positive interval `D(s)` is the Frechet derivative of
`x ↦ phi x s` at `x₀`.
-/
theorem exists_local_inverseGaugePointFlow_variationalIdentification
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDWcont : ContDiff ℝ 1 (Function.uncurry DW))
    (hDW : ∀ t x, HasFDerivAt (W t) (DW t x) x)
    (t₀ : ℝ) (x₀ : E) :
    ∃ T > (0 : ℝ), ∃ r > (0 : ℝ),
      ∃ phi : E → ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
        (∀ x ∈ closedBall x₀ r,
          phi x 0 = x ∧
            ∀ s ∈ Icc (0 : ℝ) T,
              HasDerivWithinAt (phi x) (-W (t₀ + s) (phi x s))
                (Icc (0 : ℝ) T) s) ∧
        D 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ s ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt D
            (-((DW (t₀ + s) (phi x₀ s)).comp (D s)))
            (Icc (0 : ℝ) T) s) ∧
        ∀ s ∈ Icc (0 : ℝ) T,
          HasFDerivAt (fun x : E => phi x s) (D s) x₀ := by
  let z₀ : ℝ × E := (t₀, x₀)
  let F : ℝ × E → ℝ × E := inverseGaugePointExtendedField W
  have hF : ContDiff ℝ 1 F := by
    simpa [F] using contDiff_one_inverseGaugePointExtendedField W hW
  have hF₀ : ContDiffAt ℝ 1 F z₀ := hF.contDiffAt
  rcases IsPicardLindelof.of_contDiffAt_one hF₀ with
    ⟨ε, hε, a, r, L, K₀, hr, hplAll⟩
  let hpl := hplAll (0 : ℝ)
  rcases hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    with ⟨alpha, halpha⟩
  have hz₀ : z₀ ∈ closedBall z₀ (r : ℝ) :=
    mem_closedBall_self hr.le
  have hbase := halpha z₀ hz₀
  have hbaseDerFull : ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt (alpha z₀) (F (alpha z₀ s)) (Icc (-ε) ε) s := by
    simpa only [zero_sub, zero_add] using hbase.2.1
  have hbaseContOn : ContinuousOn (alpha z₀) (Icc (-ε) ε) :=
    HasDerivWithinAt.continuousOn hbaseDerFull
  let clamp : ℝ → ℝ := fun s =>
    (Set.projIcc (-ε) ε (by linarith [hε]) s : ℝ)
  let base : ℝ → ℝ × E := fun s => alpha z₀ (clamp s)
  have hclamp : Continuous clamp := by
    exact continuous_subtype_val.comp continuous_projIcc
  have hbaseCont : Continuous base := by
    simpa [base, clamp, Function.comp_def] using
      hbaseContOn.comp_continuous hclamp
        (fun s => (Set.projIcc (-ε) ε (by linarith [hε]) s).property)
  have hDWbase : Continuous (fun s => DW (base s).1 (base s).2) := by
    have hp : Continuous (fun s => ((base s).1, (base s).2)) :=
      hbaseCont.fst.prodMk hbaseCont.snd
    simpa [Function.uncurry] using hDWcont.continuous.comp hp
  let AD : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := fun s =>
    (ContinuousLinearMap.compL ℝ E E E) (-(DW (base s).1 (base s).2))
  have hAD : Continuous AD := by
    have hc : Continuous
        (fun s => (ContinuousLinearMap.compL ℝ E E E)
          (-(DW (base s).1 (base s).2))) :=
      (ContinuousLinearMap.compL ℝ E E E).continuous.comp hDWbase.neg
    simpa [AD] using hc
  rcases Poincare.exists_solution_continuous_linearODE
      AD hAD (ContinuousLinearMap.id ℝ E) with
    ⟨εD, hεD, D, hD₀, hDder⟩
  let T : ℝ := min ε εD / 2
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hTε : T ≤ ε := by
    dsimp [T]
    linarith [min_le_left ε εD, hε]
  have hTεD : T ≤ εD := by
    dsimp [T]
    linarith [min_le_right ε εD, hεD]
  have hsmall : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hε, hs.1], hs.2.trans hTε⟩
  have hsmallPL : Icc (0 : ℝ) T ⊆ Icc (0 - ε) (0 + ε) := by
    simpa only [zero_sub, zero_add] using hsmall
  have hsmallD : Icc (0 : ℝ) T ⊆ Icc (-εD) εD := by
    intro s hs
    exact ⟨by linarith [hεD, hs.1], hs.2.trans hTεD⟩
  let phi : E → ℝ → E := fun x s => (alpha (t₀, x) s).2
  have hstateMem (x : E) (hx : x ∈ closedBall x₀ (r : ℝ)) :
      (t₀, x) ∈ closedBall z₀ (r : ℝ) := by
    rw [Metric.mem_closedBall]
    change dist (t₀, x) (t₀, x₀) ≤ (r : ℝ)
    simpa [z₀] using hx
  have htime (x : E) (hx : x ∈ closedBall x₀ (r : ℝ)) :
      ∀ s ∈ Icc (0 : ℝ) T, (alpha (t₀, x) s).1 = t₀ + s := by
    have hax := halpha (t₀, x) (hstateMem x hx)
    exact inverseGaugePointFlow_time_eq W hax.1
      (fun s hs => (hax.2.1 s (hsmallPL hs)).mono hsmallPL)
  have hphi : ∀ x ∈ closedBall x₀ (r : ℝ),
      phi x 0 = x ∧
        ∀ s ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (phi x) (-W (t₀ + s) (phi x s))
            (Icc (0 : ℝ) T) s := by
    intro x hx
    have hax := halpha (t₀, x) (hstateMem x hx)
    constructor
    · simpa [phi] using congrArg Prod.snd hax.1
    · intro s hs
      have hstate := (hax.2.1 s (hsmallPL hs)).mono hsmallPL
      have hsnd := hstate.hasFDerivWithinAt.snd.hasDerivWithinAt
      simpa [phi, F, inverseGaugePointExtendedField, htime x hx s hs] using hsnd
  have hx₀ : x₀ ∈ closedBall x₀ (r : ℝ) := mem_closedBall_self hr.le
  have hDvar : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt D
        (-((DW (t₀ + s) (phi x₀ s)).comp (D s)))
        (Icc (0 : ℝ) T) s := by
    intro s hs
    have hd := (hDder s (hsmallD hs)).mono hsmallD
    have hclamp_s : clamp s = s := by
      simp [clamp, Set.projIcc_of_mem (by linarith [hε]) (hsmall hs)]
    have hbase_s : base s = alpha z₀ s := by
      simp [base, hclamp_s]
    simpa [AD, hbase_s, z₀, phi, htime x₀ hx₀ s hs] using hd
  have hwideCompact : IsCompact (closedBall z₀ ((a : ℝ) + 1)) :=
    isCompact_closedBall z₀ ((a : ℝ) + 1)
  rcases hF.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall z₀ ((a : ℝ) + 1)) hwideCompact with
    ⟨K, hLip⟩
  have hTaylor :
      ∀ theta > (0 : ℝ), ∃ rho > (0 : ℝ),
        ∀ b ∈ closedBall z₀ ((a : ℝ) + 1),
          ∀ q ∈ closedBall z₀ ((a : ℝ) + 1),
            ‖q - b‖ ≤ rho →
              ‖F q - F b - fderiv ℝ F b (q - b)‖ ≤ theta * ‖q - b‖ :=
    uniform_taylor_remainder_norm_le_on_compact_convex
      hF hwideCompact (convex_closedBall z₀ ((a : ℝ) + 1))
  let beta : E → ℝ → ℝ × E := fun x s => alpha (t₀, x) s
  let J : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  have hbaseDer : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (beta x₀) (F (beta x₀ s)) (Icc (0 : ℝ) T) s := by
    intro s hs
    simpa [beta, z₀] using
      (hbase.2.1 s (hsmallPL hs)).mono hsmallPL
  have hbaseMem : ∀ s ∈ Icc (0 : ℝ) T,
      beta x₀ s ∈ closedBall z₀ (a : ℝ) := by
    intro s hs
    simpa [beta, z₀] using hbase.2.2 s (by simpa using hsmall hs)
  have hpert : ∀ᶠ h in 𝓝 (0 : E),
      beta (x₀ + h) 0 = beta x₀ 0 + J h ∧
        (∀ s ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (beta (x₀ + h)) (F (beta (x₀ + h) s))
            (Icc (0 : ℝ) T) s) ∧
        ∀ s ∈ Icc (0 : ℝ) T,
          beta (x₀ + h) s ∈ closedBall z₀ (a : ℝ) := by
    have hev : ∀ᶠ h in 𝓝 (0 : E), h ∈ closedBall 0 (r : ℝ) :=
      closedBall_mem_nhds 0 hr
    filter_upwards [hev] with h hh
    have hz : (t₀, x₀ + h) ∈ closedBall z₀ (r : ℝ) := by
      rw [Metric.mem_closedBall]
      change dist (t₀, x₀ + h) (t₀, x₀) ≤ (r : ℝ)
      simpa [dist_eq_norm, z₀] using hh
    have hah := halpha (t₀, x₀ + h) hz
    refine ⟨?_, ?_, ?_⟩
    · simp [beta, J, hah.1, hbase.1, z₀]
    · intro s hs
      simpa [beta] using
        (hah.2.1 s (hsmallPL hs)).mono hsmallPL
    · intro s hs
      simpa [beta] using hah.2.2 s (by simpa using hsmall hs)
  have hendpoint : ∀ s ∈ Icc (0 : ℝ) T,
      HasFDerivAt (fun x : E => phi x s) (D s) x₀ := by
    intro s hs
    let Psi : E → ℝ → ℝ × E := fun h tau => (0, D tau h)
    let Dfull : E →L[ℝ] ℝ × E :=
      (ContinuousLinearMap.inr ℝ ℝ E).comp (D s)
    have hPsi : ∀ᶠ h in 𝓝 (0 : E),
        Psi h 0 = J h ∧
          (∀ tau ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (Psi h)
              (fderiv ℝ F (beta x₀ tau) (Psi h tau))
              (Icc (0 : ℝ) T) tau) ∧
          Psi h s = Dfull h := by
      apply Filter.Eventually.of_forall
      intro h
      refine ⟨?_, ?_, ?_⟩
      · simp [Psi, J, hD₀]
      · intro tau htau
        have hdapp : HasDerivWithinAt (fun q => D q h)
            (-((DW (t₀ + tau) (phi x₀ tau)).comp (D tau)) h)
            (Icc (0 : ℝ) T) tau := by
          have hc : HasDerivWithinAt (fun _ : ℝ => h) 0
              (Icc (0 : ℝ) T) tau :=
            (hasDerivAt_const tau h).hasDerivWithinAt
          simpa using (hDvar tau htau).clm_apply hc
        have hpair : HasDerivWithinAt (Psi h)
            (0, -((DW (t₀ + tau) (phi x₀ tau)) (D tau h)))
            (Icc (0 : ℝ) T) tau := by
          simpa [Psi, ContinuousLinearMap.comp_apply] using
            (hasDerivWithinAt_const tau (Icc (0 : ℝ) T) (0 : ℝ)).prodMk hdapp
        have hfder := fderiv_inverseGaugePointExtendedField_apply_inr
          W DW hW hDW (t₀ + tau) (phi x₀ tau) (D tau h)
        have hbeta_eq : beta x₀ tau = (t₀ + tau, phi x₀ tau) := by
          ext
          · exact htime x₀ hx₀ tau htau
          · rfl
        simpa [F, Psi, hbeta_eq, hfder] using hpair
      · rfl
    have hfull : HasFDerivAt (fun x : E => beta x s) Dfull x₀ :=
      parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
        (F := F) (β := beta) (q := x₀) (J := J)
        (Ψ := Psi) (D := Dfull) (T := T) (a := (a : ℝ))
        (K := K) (p := z₀) (t := s)
        hT hLip hTaylor hbaseDer hbaseMem hpert hPsi hs
    have hproj := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp x₀ hfull
    simpa [phi, beta, Dfull, ContinuousLinearMap.comp_apply] using hproj
  exact ⟨T, hT, (r : ℝ), by exact_mod_cast hr, phi, D,
    hphi, hD₀, hDvar, hendpoint⟩

end CoordinatePointFlow

end Poincare
