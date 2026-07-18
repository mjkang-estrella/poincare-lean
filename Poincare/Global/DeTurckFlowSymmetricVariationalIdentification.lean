import Poincare.Global.DeTurckFlowVariationalIdentification

/-!
# Symmetric-time variational identification for the inverse DeTurck point flow

The Picard--Lindelof family used by
`exists_local_inverseGaugePointFlow_variationalIdentification` is already
defined on a symmetric interval.  This module keeps that single family and
uses time reflection only in the endpoint Gronwall estimate, thereby
identifying the initial-point derivative on both sides of the restart time.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology NNReal

namespace Poincare

section SymmetricParameterizedFlow

variable {P X : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
The parameterized-flow endpoint theorem on a symmetric interval.

For a negative endpoint we apply the existing positive-time theorem to the
same trajectories precomposed with `t ↦ -t` and to the reflected autonomous
field `-F`.  Thus this is a statement about one two-sided trajectory family,
not a gluing of independently selected one-sided solutions.
-/
theorem parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually_symmetric
    {F : X → X} {β : P → ℝ → X} {q : P}
    {J : P →L[ℝ] X} {Ψ : P → ℝ → X} {D : P →L[ℝ] X}
    {T a : ℝ} {K : ℝ≥0} {p : X} {t : ℝ}
    (hT : 0 < T)
    (hLip : LipschitzOnWith K F (closedBall p (a + 1)))
    (hTaylor :
      ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ base ∈ closedBall p (a + 1),
        ∀ x ∈ closedBall p (a + 1),
          ‖x - base‖ ≤ ρ →
            ‖F x - F base - fderiv ℝ F base (x - base)‖ ≤
              ε * ‖x - base‖)
    (hbase_der : ∀ τ ∈ Icc (-T) T,
      HasDerivWithinAt (β q) (F (β q τ)) (Icc (-T) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (-T) T, β q τ ∈ closedBall p a)
    (hpert : ∀ᶠ h in 𝓝 (0 : P),
      β (q + h) 0 = β q 0 + J h ∧
        (∀ τ ∈ Icc (-T) T,
          HasDerivWithinAt (β (q + h)) (F (β (q + h) τ))
            (Icc (-T) T) τ) ∧
        ∀ τ ∈ Icc (-T) T, β (q + h) τ ∈ closedBall p a)
    (hΨD : ∀ᶠ h in 𝓝 (0 : P),
      Ψ h 0 = J h ∧
        (∀ τ ∈ Icc (-T) T,
          HasDerivWithinAt (Ψ h)
            (fderiv ℝ F (β q τ) (Ψ h τ)) (Icc (-T) T) τ) ∧
        Ψ h t = D h)
    (ht : t ∈ Icc (-T) T) :
    HasFDerivAt (fun y : P => β y t) D q := by
  have hpos : Icc (0 : ℝ) T ⊆ Icc (-T) T := by
    intro τ hτ
    exact ⟨by linarith [hT, hτ.1], hτ.2⟩
  by_cases ht_nonneg : 0 ≤ t
  · have htpos : t ∈ Icc (0 : ℝ) T := ⟨ht_nonneg, ht.2⟩
    have hbase_der_pos : ∀ τ ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (β q) (F (β q τ)) (Icc (0 : ℝ) T) τ := by
      intro τ hτ
      exact (hbase_der τ (hpos hτ)).mono hpos
    have hpert_pos : ∀ᶠ h in 𝓝 (0 : P),
        β (q + h) 0 = β q 0 + J h ∧
          (∀ τ ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (β (q + h)) (F (β (q + h) τ))
              (Icc (0 : ℝ) T) τ) ∧
          ∀ τ ∈ Icc (0 : ℝ) T, β (q + h) τ ∈ closedBall p a := by
      filter_upwards [hpert] with h hh
      exact ⟨hh.1, fun τ hτ => (hh.2.1 τ (hpos hτ)).mono hpos,
        fun τ hτ => hh.2.2 τ (hpos hτ)⟩
    have hΨD_pos : ∀ᶠ h in 𝓝 (0 : P),
        Ψ h 0 = J h ∧
          (∀ τ ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (Ψ h)
              (fderiv ℝ F (β q τ) (Ψ h τ)) (Icc (0 : ℝ) T) τ) ∧
          Ψ h t = D h := by
      filter_upwards [hΨD] with h hh
      exact ⟨hh.1, fun τ hτ => (hh.2.1 τ (hpos hτ)).mono hpos, hh.2.2⟩
    exact
      parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
        (F := F) (β := β) (q := q) (J := J) (Ψ := Ψ) (D := D)
        (T := T) (a := a) (K := K) (p := p) (t := t)
        hT hLip hTaylor hbase_der_pos
        (fun τ hτ => hbase_mem τ (hpos hτ)) hpert_pos hΨD_pos htpos
  · have ht_nonpos : t ≤ 0 := le_of_not_ge ht_nonneg
    let Fneg : X → X := fun x => -F x
    let βneg : P → ℝ → X := fun y τ => β y (-τ)
    let Ψneg : P → ℝ → X := fun h τ => Ψ h (-τ)
    let u : ℝ := -t
    have hu : u ∈ Icc (0 : ℝ) T := by
      dsimp [u]
      constructor <;> linarith [ht.1]
    have hneg : MapsTo Neg.neg (Icc (0 : ℝ) T) (Icc (-T) T) := by
      intro τ hτ
      exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hLip_neg : LipschitzOnWith K Fneg (closedBall p (a + 1)) := by
      intro x hx y hy
      simpa [Fneg] using hLip hx hy
    have hTaylor_neg :
        ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ base ∈ closedBall p (a + 1),
          ∀ x ∈ closedBall p (a + 1),
            ‖x - base‖ ≤ ρ →
              ‖Fneg x - Fneg base - fderiv ℝ Fneg base (x - base)‖ ≤
                ε * ‖x - base‖ := by
      intro ε hε
      rcases hTaylor ε hε with ⟨ρ, hρ, hrem⟩
      refine ⟨ρ, hρ, ?_⟩
      intro base hbase x hx hxb
      have hfderiv : fderiv ℝ Fneg base = -fderiv ℝ F base := by
        dsimp only [Fneg]
        exact fderiv_neg
      have heq :
          Fneg x - Fneg base - fderiv ℝ Fneg base (x - base) =
            -(F x - F base - fderiv ℝ F base (x - base)) := by
        rw [hfderiv]
        simp only [Fneg, ContinuousLinearMap.neg_apply]
        abel
      rw [heq, norm_neg]
      exact hrem base hbase x hx hxb
    have hbase_der_neg : ∀ τ ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (βneg q) (Fneg (βneg q τ)) (Icc (0 : ℝ) T) τ := by
      intro τ hτ
      convert HasFDerivWithinAt.comp_hasDerivWithinAt τ
        (hbase_der (-τ) (hneg hτ))
        (hasDerivAt_neg τ).hasDerivWithinAt hneg using 1
      all_goals simp [βneg, Fneg]
    have hpert_neg : ∀ᶠ h in 𝓝 (0 : P),
        βneg (q + h) 0 = βneg q 0 + J h ∧
          (∀ τ ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (βneg (q + h)) (Fneg (βneg (q + h) τ))
              (Icc (0 : ℝ) T) τ) ∧
          ∀ τ ∈ Icc (0 : ℝ) T, βneg (q + h) τ ∈ closedBall p a := by
      filter_upwards [hpert] with h hh
      refine ⟨by simpa [βneg] using hh.1, ?_, ?_⟩
      · intro τ hτ
        convert HasFDerivWithinAt.comp_hasDerivWithinAt τ
          (hh.2.1 (-τ) (hneg hτ))
          (hasDerivAt_neg τ).hasDerivWithinAt hneg using 1
        all_goals simp [βneg, Fneg]
      · intro τ hτ
        exact hh.2.2 (-τ) (hneg hτ)
    have hΨD_neg : ∀ᶠ h in 𝓝 (0 : P),
        Ψneg h 0 = J h ∧
          (∀ τ ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (Ψneg h)
              (fderiv ℝ Fneg (βneg q τ) (Ψneg h τ))
              (Icc (0 : ℝ) T) τ) ∧
          Ψneg h u = D h := by
      filter_upwards [hΨD] with h hh
      refine ⟨by simpa [Ψneg] using hh.1, ?_, ?_⟩
      · intro τ hτ
        convert HasFDerivWithinAt.comp_hasDerivWithinAt τ
          (hh.2.1 (-τ) (hneg hτ))
          (hasDerivAt_neg τ).hasDerivWithinAt hneg using 1
        all_goals simp [Ψneg, βneg, Fneg]
      · simpa [Ψneg, u] using hh.2.2
    have hneg_endpoint :
        HasFDerivAt (fun y : P => βneg y u) D q :=
      parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
        (F := Fneg) (β := βneg) (q := q) (J := J) (Ψ := Ψneg) (D := D)
        (T := T) (a := a) (K := K) (p := p) (t := u)
        hT hLip_neg hTaylor_neg hbase_der_neg
        (fun τ hτ => hbase_mem (-τ) (hneg hτ)) hpert_neg hΨD_neg hu
    simpa [βneg, u] using hneg_endpoint

end SymmetricParameterizedFlow

section SymmetricCoordinatePointFlow

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time coordinate of a symmetric autonomous point-flow solution is
`t₀ + s` on the whole symmetric interval. -/
theorem inverseGaugePointFlow_time_eq_symmetric
    (W : ℝ → E → E) {gamma : ℝ → ℝ × E}
    {t₀ T : ℝ} {x₀ : E}
    (hgamma₀ : gamma 0 = (t₀, x₀))
    (hT : 0 ≤ T)
    (hgamma : ∀ s ∈ Icc (-T) T,
      HasDerivWithinAt gamma (inverseGaugePointExtendedField W (gamma s))
        (Icc (-T) T) s) :
    ∀ s ∈ Icc (-T) T, (gamma s).1 = t₀ + s := by
  have hder : ∀ s ∈ Icc (-T) T,
      HasDerivWithinAt (fun r : ℝ => (gamma r).1 - (t₀ + r)) 0
        (Icc (-T) T) s := by
    intro s hs
    have hfst := (hgamma s hs).hasFDerivWithinAt.fst.hasDerivWithinAt
    have hline : HasDerivWithinAt (fun r : ℝ => t₀ + r) 1
        (Icc (-T) T) s :=
      ((hasDerivAt_id s).const_add t₀).hasDerivWithinAt
    simpa [inverseGaugePointExtendedField] using hfst.sub hline
  intro s hs
  have hzero : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hmvt :=
    (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r : ℝ => (gamma r).1 - (t₀ + r))
      (f' := fun _ : ℝ => (0 : ℝ)) (C := (0 : ℝ)) hder
      (fun _ _ => by simp) hzero hs
  have hnorm : ‖(gamma s).1 - (t₀ + s)‖ ≤ 0 := by
    simpa [hgamma₀] using hmvt
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Local symmetric-time inverse-gauge point flow, together with its spatial
variational equation and Frechet derivative in the initial point.

One Picard--Lindelof family `phi` is used on `[-T,T]`; in particular, the
negative and positive trajectories are not independently chosen branches.
-/
theorem exists_local_inverseGaugePointFlow_variationalIdentification_symmetric
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDWcont : ContDiff ℝ 1 (Function.uncurry DW))
    (hDW : ∀ t x, HasFDerivAt (W t) (DW t x) x)
    (t₀ : ℝ) (x₀ : E) :
    ∃ T > (0 : ℝ), ∃ r > (0 : ℝ),
      ∃ phi : E → ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
        (∀ x ∈ closedBall x₀ r,
          phi x 0 = x ∧
            ∀ s ∈ Icc (-T) T,
              HasDerivWithinAt (phi x) (-W (t₀ + s) (phi x s))
                (Icc (-T) T) s) ∧
        D 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ s ∈ Icc (-T) T,
          HasDerivWithinAt D
            (-((DW (t₀ + s) (phi x₀ s)).comp (D s)))
            (Icc (-T) T) s) ∧
        ∀ s ∈ Icc (-T) T,
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
  have hclamp : Continuous clamp :=
    continuous_subtype_val.comp continuous_projIcc
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
  have hsmall : Icc (-T) T ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hTε, hs.1], hs.2.trans hTε⟩
  have hsmallPL : Icc (-T) T ⊆ Icc (0 - ε) (0 + ε) := by
    simpa only [zero_sub, zero_add] using hsmall
  have hsmallD : Icc (-T) T ⊆ Icc (-εD) εD := by
    intro s hs
    exact ⟨by linarith [hTεD, hs.1], hs.2.trans hTεD⟩
  let phi : E → ℝ → E := fun x s => (alpha (t₀, x) s).2
  have hstateMem (x : E) (hx : x ∈ closedBall x₀ (r : ℝ)) :
      (t₀, x) ∈ closedBall z₀ (r : ℝ) := by
    rw [Metric.mem_closedBall]
    change dist (t₀, x) (t₀, x₀) ≤ (r : ℝ)
    simpa [z₀] using hx
  have htime (x : E) (hx : x ∈ closedBall x₀ (r : ℝ)) :
      ∀ s ∈ Icc (-T) T, (alpha (t₀, x) s).1 = t₀ + s := by
    have hax := halpha (t₀, x) (hstateMem x hx)
    exact inverseGaugePointFlow_time_eq_symmetric W hax.1 hT.le
      (fun s hs => (hax.2.1 s (hsmallPL hs)).mono hsmallPL)
  have hphi : ∀ x ∈ closedBall x₀ (r : ℝ),
      phi x 0 = x ∧
        ∀ s ∈ Icc (-T) T,
          HasDerivWithinAt (phi x) (-W (t₀ + s) (phi x s))
            (Icc (-T) T) s := by
    intro x hx
    have hax := halpha (t₀, x) (hstateMem x hx)
    constructor
    · simpa [phi] using congrArg Prod.snd hax.1
    · intro s hs
      have hstate := (hax.2.1 s (hsmallPL hs)).mono hsmallPL
      have hsnd := hstate.hasFDerivWithinAt.snd.hasDerivWithinAt
      simpa [phi, F, inverseGaugePointExtendedField, htime x hx s hs] using hsnd
  have hx₀ : x₀ ∈ closedBall x₀ (r : ℝ) := mem_closedBall_self hr.le
  have hDvar : ∀ s ∈ Icc (-T) T,
      HasDerivWithinAt D
        (-((DW (t₀ + s) (phi x₀ s)).comp (D s)))
        (Icc (-T) T) s := by
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
  have hbaseDer : ∀ s ∈ Icc (-T) T,
      HasDerivWithinAt (beta x₀) (F (beta x₀ s)) (Icc (-T) T) s := by
    intro s hs
    simpa [beta, z₀] using
      (hbase.2.1 s (hsmallPL hs)).mono hsmallPL
  have hbaseMem : ∀ s ∈ Icc (-T) T,
      beta x₀ s ∈ closedBall z₀ (a : ℝ) := by
    intro s hs
    simpa [beta, z₀] using hbase.2.2 s (by simpa using hsmall hs)
  have hpert : ∀ᶠ h in 𝓝 (0 : E),
      beta (x₀ + h) 0 = beta x₀ 0 + J h ∧
        (∀ s ∈ Icc (-T) T,
          HasDerivWithinAt (beta (x₀ + h)) (F (beta (x₀ + h) s))
            (Icc (-T) T) s) ∧
        ∀ s ∈ Icc (-T) T,
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
      simpa [beta] using (hah.2.1 s (hsmallPL hs)).mono hsmallPL
    · intro s hs
      simpa [beta] using hah.2.2 s (by simpa using hsmall hs)
  have hendpoint : ∀ s ∈ Icc (-T) T,
      HasFDerivAt (fun x : E => phi x s) (D s) x₀ := by
    intro s hs
    let Psi : E → ℝ → ℝ × E := fun h tau => (0, D tau h)
    let Dfull : E →L[ℝ] ℝ × E :=
      (ContinuousLinearMap.inr ℝ ℝ E).comp (D s)
    have hPsi : ∀ᶠ h in 𝓝 (0 : E),
        Psi h 0 = J h ∧
          (∀ tau ∈ Icc (-T) T,
            HasDerivWithinAt (Psi h)
              (fderiv ℝ F (beta x₀ tau) (Psi h tau))
              (Icc (-T) T) tau) ∧
          Psi h s = Dfull h := by
      apply Filter.Eventually.of_forall
      intro h
      refine ⟨?_, ?_, ?_⟩
      · simp [Psi, J, hD₀]
      · intro tau htau
        have hdapp : HasDerivWithinAt (fun q => D q h)
            (-((DW (t₀ + tau) (phi x₀ tau)).comp (D tau)) h)
            (Icc (-T) T) tau := by
          have hc : HasDerivWithinAt (fun _ : ℝ => h) 0
              (Icc (-T) T) tau :=
            (hasDerivAt_const tau h).hasDerivWithinAt
          simpa using (hDvar tau htau).clm_apply hc
        have hpair : HasDerivWithinAt (Psi h)
            (0, -((DW (t₀ + tau) (phi x₀ tau)) (D tau h)))
            (Icc (-T) T) tau := by
          simpa [Psi, ContinuousLinearMap.comp_apply] using
            (hasDerivWithinAt_const tau (Icc (-T) T) (0 : ℝ)).prodMk hdapp
        have hfder := fderiv_inverseGaugePointExtendedField_apply_inr
          W DW hW hDW (t₀ + tau) (phi x₀ tau) (D tau h)
        have hbeta_eq : beta x₀ tau = (t₀ + tau, phi x₀ tau) := by
          ext
          · exact htime x₀ hx₀ tau htau
          · rfl
        simpa [F, Psi, hbeta_eq, hfder] using hpair
      · rfl
    have hfull : HasFDerivAt (fun x : E => beta x s) Dfull x₀ :=
      parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually_symmetric
        (F := F) (β := beta) (q := x₀) (J := J)
        (Ψ := Psi) (D := Dfull) (T := T) (a := (a : ℝ))
        (K := K) (p := z₀) (t := s)
        hT hLip hTaylor hbaseDer hbaseMem hpert hPsi hs
    have hproj := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp x₀ hfull
    simpa [phi, beta, Dfull, ContinuousLinearMap.comp_apply] using hproj
  exact ⟨T, hT, (r : ℝ), by exact_mod_cast hr, phi, D,
    hphi, hD₀, hDvar, hendpoint⟩

end SymmetricCoordinatePointFlow

end Poincare
