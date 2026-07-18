import Poincare.Global.DeTurckGaugePullbackDerivative
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Local inverse DeTurck gauge ODE in coordinates

Mathlib provides local Picard--Lindelof existence for autonomous `C¹` fields,
but not a ready smooth-dependence theorem for a time-dependent manifold flow.
This file makes the standard autonomous augmentation explicit.  The state is

    `(time, point, differential)`

and its last two equations are exactly the inverse-gauge equation and its
variational equation.  Thus the differential curve produced here has the
derivative required by `hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci_comp`.
-/

noncomputable section

open Set
open scoped Topology

namespace Poincare

section CoordinateInverseGauge

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Autonomous augmentation of the time-dependent inverse-gauge equation and
its linear variational equation. -/
def inverseGaugeExtendedField
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E) :
    (ℝ × (E × (E →L[ℝ] E))) → (ℝ × (E × (E →L[ℝ] E))) :=
  fun q =>
    (1,
      (-W q.1 q.2.1,
        -((DW q.1 q.2.1).comp q.2.2)))

/-- Joint `C¹` regularity of `W` and `DW` makes the autonomous augmented
inverse-gauge field `C¹`. -/
theorem contDiff_one_inverseGaugeExtendedField
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDW : ContDiff ℝ 1 (Function.uncurry DW)) :
    ContDiff ℝ 1 (inverseGaugeExtendedField W DW) := by
  have htx : ContDiff ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => (q.1, q.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hWq : ContDiff ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => W q.1 q.2.1) := by
    simpa [Function.uncurry] using hW.comp htx
  have hDWq : ContDiff ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => DW q.1 q.2.1) := by
    simpa [Function.uncurry] using hDW.comp htx
  have hcompFamily : ContDiff ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        (ContinuousLinearMap.compL ℝ E E E) (DW q.1 q.2.1)) :=
    (contDiff_const.clm_apply hDWq)
  have hD : ContDiff ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => q.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hcomp : ContDiff ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        (DW q.1 q.2.1).comp q.2.2) := by
    simpa using hcompFamily.clm_apply hD
  simpa [inverseGaugeExtendedField] using
    (contDiff_const.prodMk (hWq.neg.prodMk hcomp.neg))

/-- Pointwise joint `C¹` regularity of `W` and `DW` at the initial
time--point pair makes the autonomous augmented inverse-gauge field `C¹` at
the corresponding extended initial state. -/
theorem contDiffAt_one_inverseGaugeExtendedField
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (t₀ : ℝ) (x₀ : E) (D₀ : E →L[ℝ] E)
    (hW : ContDiffAt ℝ 1 (Function.uncurry W) (t₀, x₀))
    (hDW : ContDiffAt ℝ 1 (Function.uncurry DW) (t₀, x₀)) :
    ContDiffAt ℝ 1 (inverseGaugeExtendedField W DW) (t₀, (x₀, D₀)) := by
  let y₀ : ℝ × (E × (E →L[ℝ] E)) := (t₀, (x₀, D₀))
  have htx : ContDiffAt ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => (q.1, q.2.1)) y₀ :=
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffAt
  have hWq : ContDiffAt ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => W q.1 q.2.1) y₀ := by
    simpa [Function.uncurry, y₀] using hW.comp y₀ htx
  have hDWq : ContDiffAt ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => DW q.1 q.2.1) y₀ := by
    simpa [Function.uncurry, y₀] using hDW.comp y₀ htx
  have hcompFamily : ContDiffAt ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        (ContinuousLinearMap.compL ℝ E E E) (DW q.1 q.2.1)) y₀ :=
    contDiffAt_const.clm_apply hDWq
  have hD : ContDiffAt ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) => q.2.2) y₀ :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have hcomp : ContDiffAt ℝ 1
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        (DW q.1 q.2.1).comp q.2.2) y₀ := by
    simpa using hcompFamily.clm_apply hD
  simpa [inverseGaugeExtendedField, y₀] using
    (contDiffAt_const.prodMk (hWq.neg.prodMk hcomp.neg))

/-- Local uniqueness for the autonomous inverse-gauge/variational system.
Any two solution germs with the same extended initial state agree near the
initial parameter. -/
theorem inverseGaugeExtendedCurve_eventuallyEq
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDW : ContDiff ℝ 1 (Function.uncurry DW))
    {s₀ : ℝ} {y₀ : ℝ × (E × (E →L[ℝ] E))}
    {beta gamma : ℝ → ℝ × (E × (E →L[ℝ] E))}
    (hbeta : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt beta (inverseGaugeExtendedField W DW (beta s)) s)
    (hgamma : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma (inverseGaugeExtendedField W DW (gamma s)) s)
    (hbeta₀ : beta s₀ = y₀) (hgamma₀ : gamma s₀ = y₀) :
    beta =ᶠ[𝓝 s₀] gamma := by
  have hF₀ : ContDiffAt ℝ 1 (inverseGaugeExtendedField W DW) y₀ :=
    (contDiff_one_inverseGaugeExtendedField W DW hW hDW).contDiffAt
  rcases hF₀.exists_lipschitzOnWith with ⟨K, U, hU, hLip⟩
  have hbetaAt := hbeta.self_of_nhds
  have hgammaAt := hgamma.self_of_nhds
  have hbetaMem : ∀ᶠ s in 𝓝 s₀, beta s ∈ U := by
    apply hbetaAt.continuousAt.preimage_mem_nhds
    simpa [hbeta₀] using hU
  have hgammaMem : ∀ᶠ s in 𝓝 s₀, gamma s ∈ U := by
    apply hgammaAt.continuousAt.preimage_mem_nhds
    simpa [hgamma₀] using hU
  apply ODE_solution_unique_of_eventually
    (v := fun _ => inverseGaugeExtendedField W DW)
    (s := fun _ => U) (K := K)
    (.of_forall fun _ => hLip)
    (hbeta.and hbetaMem) (hgamma.and hgammaMem)
  exact hbeta₀.trans hgamma₀.symm

variable [CompleteSpace E]

/-- Point-local existence of an inverse-gauge coordinate trajectory and its
linear variational equation.  Only joint `C¹` regularity at the initial
time--point pair is needed by local Picard--Lindelöf existence. -/
theorem exists_local_inverseGauge_with_variationalEquation_of_contDiffAt
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (t₀ : ℝ) (x₀ : E)
    (hW : ContDiffAt ℝ 1 (Function.uncurry W) (t₀, x₀))
    (hDW : ContDiffAt ℝ 1 (Function.uncurry DW) (t₀, x₀)) :
    ∃ ε > (0 : ℝ), ∃ phi : ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
      phi t₀ = x₀ ∧
        D t₀ = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt phi (-W t (phi t)) t ∧
            HasDerivAt D (-((DW t (phi t)).comp (D t))) t := by
  let y₀ : ℝ × (E × (E →L[ℝ] E)) :=
    (t₀, (x₀, ContinuousLinearMap.id ℝ E))
  let F := inverseGaugeExtendedField W DW
  have hF₀ : ContDiffAt ℝ 1 F y₀ := by
    simpa [F, y₀] using
      contDiffAt_one_inverseGaugeExtendedField W DW t₀ x₀
        (ContinuousLinearMap.id ℝ E) hW hDW
  rcases hF₀.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (t₀ := (0 : ℝ)) with ⟨beta, hbeta₀, ε, hε, hbeta⟩
  have htimeDeriv : ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (fun r : ℝ => (beta r).1) 1 s := by
    intro s hs
    have h := (hbeta s (by simpa using hs)).hasFDerivAt.fst.hasDerivAt
    simpa [F, inverseGaugeExtendedField] using h
  have htime : EqOn (fun s : ℝ => (beta s).1) (fun s => t₀ + s)
      (Ioo (-ε) ε) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ : ℝ => fun _ : ℝ => (1 : ℝ))
      (s := fun _ : ℝ => (Set.univ : Set ℝ)) (K := 0)
      (t₀ := (0 : ℝ))
    · intro _ _
      exact (LipschitzWith.const (1 : ℝ)).lipschitzOnWith
    · simpa using hε
    · intro s hs
      exact ⟨by simpa using htimeDeriv s hs, Set.mem_univ _⟩
    · intro s _
      exact ⟨by simpa using (hasDerivAt_id s).const_add t₀, Set.mem_univ _⟩
    · have hfirst := congrArg Prod.fst hbeta₀
      simpa [y₀] using hfirst
  let phi : ℝ → E := fun t => (beta (t - t₀)).2.1
  let D : ℝ → E →L[ℝ] E := fun t => (beta (t - t₀)).2.2
  refine ⟨ε, hε, phi, D, ?_, ?_, ?_⟩
  · have hsndfst := congrArg (fun q => q.2.1) hbeta₀
    simpa [phi, y₀] using hsndfst
  · have hsndsnd := congrArg (fun q => q.2.2) hbeta₀
    simpa [D, y₀] using hsndsnd
  · intro t ht
    have hs : t - t₀ ∈ Ioo (-ε) ε := by
      constructor <;> linarith [ht.1, ht.2]
    have hb := hbeta (t - t₀) (by simpa using hs)
    have hpair := hb.hasFDerivAt.snd.hasDerivAt
    have hphiShift := hpair.hasFDerivAt.fst.hasDerivAt
    have hDShift := hpair.hasFDerivAt.snd.hasDerivAt
    have hshift : HasDerivAt (fun r : ℝ => r - t₀) 1 t :=
      (hasDerivAt_id t).sub_const t₀
    constructor
    · have hcomp := hphiShift.scomp t hshift
      simpa [phi, F, inverseGaugeExtendedField, htime hs] using hcomp
    · have hcomp := hDShift.scomp t hshift
      simpa [D, phi, F, inverseGaugeExtendedField, htime hs] using hcomp

/--
Local existence of an inverse-gauge coordinate trajectory together with its
linear variational equation.

The returned curves use physical time: they start at `t₀`, and on a genuine
open interval around `t₀` satisfy

* `phi' = -W(t, phi)`, and
* `D' = -(DW(t, phi) ∘ D)`.

The initial differential is the identity.  This is the exact differential
equation consumed by the arbitrary-time pullback cancellation theorem.
-/
theorem exists_local_inverseGauge_with_variationalEquation
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDW : ContDiff ℝ 1 (Function.uncurry DW))
    (t₀ : ℝ) (x₀ : E) :
    ∃ ε > (0 : ℝ), ∃ phi : ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
      phi t₀ = x₀ ∧
        D t₀ = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt phi (-W t (phi t)) t ∧
            HasDerivAt D (-((DW t (phi t)).comp (D t))) t := by
  exact exists_local_inverseGauge_with_variationalEquation_of_contDiffAt
    W DW t₀ x₀ hW.contDiffAt hDW.contDiffAt

/--
Local inverse-gauge existence together with the Ricci pullback derivative.

Besides producing the coordinate trajectory and its differential, this theorem
applies the pullback cancellation theorem at every time of the local interval.
Thus any bilinear-form path whose derivative has the coordinate
Ricci--DeTurck decomposition immediately acquires derivative `-2` times the
Ricci form pulled through the constructed differential.
-/
theorem exists_local_inverseGauge_with_pullbackRicciDerivative
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDW : ContDiff ℝ 1 (Function.uncurry DW))
    (t₀ : ℝ) (x₀ : E) :
    ∃ ε > (0 : ℝ), ∃ phi : ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
      phi t₀ = x₀ ∧
        D t₀ = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt phi (-W t (phi t)) t ∧
            HasDerivAt D (-((DW t (phi t)).comp (D t))) t ∧
            ∀ (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
              (G H adv R : E →L[ℝ] E →L[ℝ] ℝ),
              HasDerivAt A (H - adv) t →
                A t = G →
                (∀ u v : E,
                  H u v =
                    (-2 : ℝ) * R u v + adv u v +
                      G ((DW t (phi t)) u) v +
                        G u ((DW t (phi t)) v)) →
                ∀ u v : E,
                  HasDerivAt (pullbackBilinearApply A D u v)
                    ((-2 : ℝ) * R (D t u) (D t v)) t := by
  rcases exists_local_inverseGauge_with_variationalEquation
      W DW hW hDW t₀ x₀ with
    ⟨ε, hε, phi, D, hphi₀, hD₀, hODE⟩
  refine ⟨ε, hε, phi, D, hphi₀, hD₀, ?_⟩
  intro t ht
  rcases hODE t ht with ⟨hphi, hD⟩
  refine ⟨hphi, hD, ?_⟩
  intro A G H adv R hA hA₀ hDeTurck u v
  exact hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci_comp
    A D G H adv R (DW t (phi t)) hA hD hA₀ hDeTurck u v

end CoordinateInverseGauge

end Poincare
