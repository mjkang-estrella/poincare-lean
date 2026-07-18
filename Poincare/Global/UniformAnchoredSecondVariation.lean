import Poincare.Global.PrescribedLinearODE
import Poincare.Global.ParameterizedFlowDerivative
import Poincare.Global.BasisEndpointAssembly
import Poincare.Global.ExpChartC2
import Poincare.Global.SecondVariationRescale
import Poincare.Global.SecondVariationEndpointGronwall
import Poincare.Global.UniformAnchoredAugmentedFamily

/-!
# Uniform anchored second variation

Scaled basis inputs remove the apparent `T⁻¹` blow-up in the augmented initial
state.  This permits one compact augmented tube, a prescribed short
second-variation Picard--Lindelöf interval, and genuine restricted-parameter
derivatives of the augmented endpoint at every point of a small normal ball.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace UniformAnchoredSecondVariation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "A" => (E × E) × (E × E)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/-- The restricted change of augmented initial state when only `q` varies. -/
def anchoredBaseInitializationCLM (T : ℝ) : E →L[ℝ] A :=
  ((0 : E →L[ℝ] E).prod
      (T⁻¹ • ContinuousLinearMap.id ℝ E)).prod
    (0 : E →L[ℝ] (E × E))

@[simp]
theorem anchoredBaseInitializationCLM_apply (T : ℝ) (h : E) :
    anchoredBaseInitializationCLM T h =
      (((0 : E), T⁻¹ • h), ((0 : E), (0 : E))) := by
  rfl

/--
On one small normal ball, every scaled canonical-basis augmented endpoint is
Frechet differentiable in the anchored base parameter.

The scale is the common endpoint time `T`: the first-variation input is
`T • bᵢ`, so its augmented initial value is the time-independent vector `bᵢ`.
-/
theorem exists_scaled_finBasis_augmented_endpoint_hasFDerivAt
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∃ T > (0 : ℝ),
      ∃ R : ℝ, 0 ≤ R ∧ ∃ β : (E × E) → ℝ → A,
        (∀ q ∈ ball (0 : E) ρ, ∀ w : E,
          (β (q, w) T).2.1 =
            fderiv ℝ
              (expAtChartOpenPartialHomeomorph (g := g) x₀) q w) ∧
        ∀ q ∈ ball (0 : E) ρ,
          ∀ i : Fin (Module.finrank ℝ E),
            ∃ D : E →L[ℝ] A,
              HasFDerivAt
                (fun q' : E =>
                  β (q', T • (Module.finBasis ℝ E) i) T) D q ∧
                ∃ Ξ : E → ℝ → A,
                  (∀ h : E, Ξ h 0 = anchoredBaseInitializationCLM T h) ∧
                    (∀ h : E, ∀ t ∈ Icc (0 : ℝ) T,
                      HasDerivWithinAt (Ξ h)
                        (secondVariationFlowFieldAlong
                          (chartChristoffelField g x₀)
                          (fun s => β (q, T • (Module.finBasis ℝ E) i) s)
                          t (Ξ h t))
                        (Icc (0 : ℝ) T) t) ∧
                    (∀ h : E, Ξ h T = D h) ∧
                β (q, T • (Module.finBasis ℝ E) i) 0 =
                  ((extChartAt I x₀ x₀, T⁻¹ • q),
                    ((0 : E), (Module.finBasis ℝ E) i)) ∧
                (∀ t ∈ Icc (0 : ℝ) T,
                  HasDerivWithinAt
                    (β (q, T • (Module.finBasis ℝ E) i))
                    (augmentedGeodesicFlowField
                      (chartChristoffelField g x₀)
                      (β (q, T • (Module.finBasis ℝ E) i) t))
                    (Icc (0 : ℝ) T) t) ∧
                ∀ t ∈ Icc (0 : ℝ) T,
                  β (q, T • (Module.finBasis ℝ E) i) t ∈
                    closedBall (0 : A) R := by
  classical
  rcases
      UniformAnchoredAugmentedFamily.exists_uniform_anchored_augmented_family_for_all_small_times
        (g := g) (x₀ := x₀) with
    ⟨ε, hε, C₀, hC₀, Kfirst, hfamily⟩
  let B : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E), ‖(Module.finBasis ℝ E) i‖
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  let R : ℝ := C₀ + B * Real.exp ((Kfirst : ℝ) * ε)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  rcases
      exists_chartChristoffel_secondVariationCoefficient_bounds_closedBall
        (g := g) (x₀ := x₀) (0 : A) R with
    ⟨Ksecond, _Lsecond, hsecondOp, _hsecondLip⟩
  let T : ℝ := min (ε / 2) (1 / (4 * ((Ksecond : ℝ) + 1)))
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min (half_pos hε) (by positivity)
  have hTε : T < ε := by
    have hle : T ≤ ε / 2 := by
      dsimp [T]
      exact min_le_left _ _
    linarith
  have hKT : (Ksecond : ℝ) * T ≤ (1 : ℝ) / 2 := by
    have hle : T ≤ 1 / (4 * ((Ksecond : ℝ) + 1)) := by
      dsimp [T]
      exact min_le_right _ _
    have hK : 0 ≤ (Ksecond : ℝ) := Ksecond.2
    calc
      (Ksecond : ℝ) * T ≤
          (Ksecond : ℝ) * (1 / (4 * ((Ksecond : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hle hK
      _ ≤ 1 / 4 := by
        have hden : (Ksecond : ℝ) + 1 ≠ 0 := by positivity
        calc
          (Ksecond : ℝ) * (1 / (4 * ((Ksecond : ℝ) + 1))) =
              ((Ksecond : ℝ) / ((Ksecond : ℝ) + 1)) / 4 := by
            field_simp [hden]
          _ ≤ 1 / 4 := by
            gcongr
            exact (div_le_one (by positivity)).2 (by linarith)
      _ ≤ 1 / 2 := by norm_num
  rcases hfamily T hT hTε with ⟨ρ, hρ, β, hβ⟩
  refine ⟨ρ, hρ, T, hT, R, hR, β, ?_, ?_⟩
  · intro q hq w
    exact (hβ q hq w).2.2.1
  · intro q hq i
    let b : E := (Module.finBasis ℝ E) i
    let w : E := T • b
    rcases hβ q hq w with
      ⟨hβ0, hβder, _hβend, _hExpDer, hβmemRaw⟩
    have hTne : T ≠ 0 := ne_of_gt hT
    have hscaled : T⁻¹ • w = b := by
      simp [w, smul_smul, hTne]
    have hiB : ‖b‖ ≤ B := by
      dsimp [B, b]
      exact Finset.single_le_sum
        (fun j _hj => norm_nonneg ((Module.finBasis ℝ E) j))
        (Finset.mem_univ i)
    have hscaleNorm : |T⁻¹| * ‖w‖ = ‖b‖ := by
      rw [show w = T • b from rfl, norm_smul, Real.norm_eq_abs]
      have hTabs : |T| = T := abs_of_pos hT
      rw [abs_inv, hTabs]
      field_simp [hTne]
    have hexp :
        Real.exp ((Kfirst : ℝ) * T) ≤
          Real.exp ((Kfirst : ℝ) * ε) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hTε.le Kfirst.2
    have hrawRadius :
        C₀ + (|T⁻¹| * ‖w‖) * Real.exp ((Kfirst : ℝ) * T) ≤ R := by
      rw [hscaleNorm]
      calc
        C₀ + ‖b‖ * Real.exp ((Kfirst : ℝ) * T) ≤
            C₀ + ‖b‖ * Real.exp ((Kfirst : ℝ) * ε) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left hexp (norm_nonneg b)) C₀
        _ ≤ C₀ + B * Real.exp ((Kfirst : ℝ) * ε) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right hiB (Real.exp_pos _).le) C₀
        _ = R := rfl
    have hβmem : ∀ t ∈ Icc (0 : ℝ) T,
        β (q, w) t ∈ closedBall (0 : A) R := by
      intro t ht
      exact closedBall_subset_closedBall hrawRadius (hβmemRaw t ht)
    let ζ : ℝ → A := fun t =>
      β (q, w) (Set.projIcc (0 : ℝ) T hT.le t)
    have hβcont : ContinuousOn (β (q, w)) (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn
        (f' := fun t =>
          augmentedGeodesicFlowField
            (chartChristoffelField g x₀) (β (q, w) t)) hβder
    have hζ : Continuous ζ := by
      exact
        (continuousOn_iff_continuous_restrict.mp hβcont).comp
          continuous_projIcc
    let F : A → A :=
      augmentedGeodesicFlowField (chartChristoffelField g x₀)
    let Aop : ℝ → A →L[ℝ] A := fun t => fderiv ℝ F (ζ t)
    rcases
        exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
          (g := g) (x₀ := x₀) (p := (0 : A)) (a := 0) with
      ⟨hFtwo, _hFLip⟩
    have hAopCont : Continuous Aop := by
      simpa [Aop, F] using
        (hFtwo.continuous_fderiv (by norm_num)).comp hζ
    have hζeq : ∀ t ∈ Icc (0 : ℝ) T, ζ t = β (q, w) t := by
      intro t ht
      simp [ζ, Set.projIcc_of_mem hT.le ht]
    have hAopBound : ∀ t ∈ Icc (-T) T, ‖Aop t‖ ≤ (Ksecond : ℝ) := by
      intro t ht
      apply hsecondOp
      have hproj : (Set.projIcc (0 : ℝ) T hT.le t : ℝ) ∈ Icc (0 : ℝ) T :=
        (Set.projIcc (0 : ℝ) T hT.le t).2
      simpa [Aop, F, ζ] using hβmem _ hproj
    have hplA :=
      isPicardLindelof_continuous_linearODE_zero_on_prescribed_Icc
        Aop hAopCont hT.le Ksecond hAopBound hKT
    have hpl : IsPicardLindelof
        (fun t ξ => secondVariationFlowFieldAlong
          (chartChristoffelField g x₀) ζ t ξ)
        (tmin := -T) (tmax := T)
        ⟨(0 : ℝ), by constructor <;> linarith⟩ (0 : A)
        (1 : ℝ≥0) (1 / 2 : ℝ≥0) Ksecond Ksecond := by
      simpa [Aop, F, secondVariationFlowFieldAlong,
        secondVariationFlowOperator] using hplA
    rcases
        SecondVariationRescale.exists_rescaled_hosted_secondVariation_solution_family_linear_of_pl
          (g := g) (x₀ := x₀) hT (by norm_num) hpl with
      ⟨Ξ, hΞ0, hΞder, hΞadd, hΞsmul⟩
    let endpointLinear : A →ₗ[ℝ] A :=
      { toFun := fun η => Ξ η T
        map_add' := fun η η' => hΞadd η η' T ⟨by linarith [hT], le_rfl⟩
        map_smul' := fun c η => hΞsmul c η T ⟨by linarith [hT], le_rfl⟩ }
    let Dfull : A →L[ℝ] A :=
      LinearMap.toContinuousLinearMap endpointLinear
    let J : E →L[ℝ] A := anchoredBaseInitializationCLM T
    let D : E →L[ℝ] A := Dfull.comp J
    let βw : E → ℝ → A := fun q' => β (q', w)
    let Ξparam : E → ℝ → A := fun h => Ξ (J h)
    have hpert : ∀ᶠ h in 𝓝 (0 : E),
        βw (q + h) 0 = βw q 0 + J h ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (βw (q + h))
              (augmentedGeodesicFlowField
                (chartChristoffelField g x₀) (βw (q + h) t))
              (Icc (0 : ℝ) T) t) ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            βw (q + h) t ∈ closedBall (0 : A) R := by
      have htend : Tendsto (fun h : E => q + h) (𝓝 (0 : E)) (𝓝 q) := by
        have hc : ContinuousAt (fun h : E => q + h) 0 :=
          continuousAt_const.add continuousAt_id
        change Tendsto (fun h : E => q + h) (𝓝 (0 : E)) (𝓝 (q + 0)) at hc
        simpa only [add_zero] using hc
      have hevent : ∀ᶠ h in 𝓝 (0 : E), q + h ∈ ball (0 : E) ρ :=
        htend.eventually (Metric.isOpen_ball.mem_nhds hq)
      filter_upwards [hevent] with h hqh
      rcases hβ (q + h) hqh w with
        ⟨hβh0, hβhder, _hβhend, _hExpDer, hβhmemRaw⟩
      have hβhmem : ∀ t ∈ Icc (0 : ℝ) T,
          β (q + h, w) t ∈ closedBall (0 : A) R := by
        intro t ht
        exact closedBall_subset_closedBall hrawRadius (hβhmemRaw t ht)
      refine ⟨?_, hβhder, hβhmem⟩
      rw [show βw (q + h) 0 = β (q + h, w) 0 from rfl,
        show βw q 0 = β (q, w) 0 from rfl, hβh0, hβ0]
      simp [J, anchoredBaseInitializationCLM, smul_add]
    have hΞprops : ∀ h : E,
        Ξparam h 0 = J h ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (Ξparam h)
              (secondVariationFlowFieldAlong
                (chartChristoffelField g x₀) (βw q) t (Ξparam h t))
              (Icc (0 : ℝ) T) t) ∧
          Ξparam h T = D h := by
      intro h
      refine ⟨hΞ0 (J h), ?_, ?_⟩
      · intro t ht
        have hsub : Icc (0 : ℝ) T ⊆ Icc (-T) T := by
          intro s hs
          exact ⟨by linarith [hT, hs.1], hs.2⟩
        have hraw := (hΞder (J h) t (hsub ht)).mono hsub
        change HasDerivWithinAt (Ξ (J h))
          (secondVariationFlowOperator (chartChristoffelField g x₀)
            (ζ t) (Ξ (J h) t)) (Icc (0 : ℝ) T) t at hraw
        rw [hζeq t ht] at hraw
        simpa [Ξparam, βw, secondVariationFlowFieldAlong] using hraw
      · rfl
    have hΞD : ∀ᶠ h in 𝓝 (0 : E),
        Ξparam h 0 = J h ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (Ξparam h)
              (secondVariationFlowFieldAlong
                (chartChristoffelField g x₀) (βw q) t (Ξparam h t))
              (Icc (0 : ℝ) T) t) ∧
          Ξparam h T = D h :=
      Filter.Eventually.of_forall hΞprops
    have hHas : HasFDerivAt (fun q' : E => β (q', w) T) D q :=
      chartChristoffel_parameterizedAugmentedEndpoint_hasFDerivAt_of_secondVariation_eventually
        (g := g) (x₀ := x₀)
        (β := βw) (q := q) (J := J) (Ξ := Ξparam) (D := D)
        (T := T) (a := R) (p := (0 : A)) (t := T)
        hT hβder hβmem hpert hΞD ⟨hT.le, le_rfl⟩
    refine ⟨D, hHas, Ξparam, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hΞ0 (J h)
    · intro h t ht
      exact (hΞprops h).2.1 t ht
    · intro h
      exact (hΞprops h).2.2
    · simpa [w, b, hscaled] using hβ0
    · simpa [w, b] using hβder
    · simpa [w, b] using hβmem

/--
The derivative field of the exponential chart is Frechet differentiable at
every point of one small normal ball.  This is the pointwise `C²` statement;
continuity of the resulting second-derivative field is a separate Gronwall
comparison step.
-/
theorem exists_expAtChart_fderiv_hasFDerivAt_on_smallBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∀ q ∈ ball (0 : E) ρ,
      ∃ D : E →L[ℝ] E →L[ℝ] E,
        HasFDerivAt
          (fun q' : E =>
            fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q')
          D q := by
  rcases exists_scaled_finBasis_augmented_endpoint_hasFDerivAt g x₀ with
    ⟨ρ, hρ, T, hT, _R, _hR, β, hfield, hendpoint⟩
  refine ⟨ρ, hρ, ?_⟩
  intro q hq
  apply EndpointCurry.exists_hasFDerivAt_clm_of_apply_finBasis
  intro i
  rcases hendpoint q hq i with
    ⟨Dfull, hDfull, _hΞ, _hinit, _hder, _hmem⟩
  let P : A →L[ℝ] E :=
    AnchoredEndpointIdentity.augmentedFirstVariationPosition
  let D : E →L[ℝ] E := T⁻¹ • (P.comp Dfull)
  have hprojected : HasFDerivAt
      (fun q' : E => T⁻¹ • P (β (q', T • (Module.finBasis ℝ E) i) T))
      D q := by
    exact (P.hasFDerivAt.comp q hDfull).const_smul T⁻¹
  have hevent : ∀ᶠ q' in 𝓝 q, q' ∈ ball (0 : E) ρ :=
    Metric.isOpen_ball.mem_nhds hq
  have heq :
      (fun q' : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q'
          ((Module.finBasis ℝ E) i)) =ᶠ[𝓝 q]
      (fun q' : E => T⁻¹ •
        P (β (q', T • (Module.finBasis ℝ E) i) T)) := by
    filter_upwards [hevent] with q' hq'
    have hend := hfield q' hq' (T • (Module.finBasis ℝ E) i)
    have hTne : T ≠ 0 := ne_of_gt hT
    rw [show P (β (q', T • (Module.finBasis ℝ E) i) T) =
        (β (q', T • (Module.finBasis ℝ E) i) T).2.1 from rfl,
      hend]
    simp [map_smul, smul_smul, hTne]
  exact ⟨D, hprojected.congr_of_eventuallyEq heq⟩

/--
The exponential-chart derivative field is `C¹` on a small normal ball, hence
the exponential chart is genuinely `C²` there.  Coherence of the second
derivative is obtained from uniqueness plus the pairwise second-variation
endpoint Gronwall estimate; no arbitrary derivative selector remains in the
statement.
-/
theorem exists_expAtChart_fderiv_contDiffAt_one_on_smallBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∀ q ∈ ball (0 : E) ρ,
      ContDiffAt ℝ 1
        (fun q' : E =>
          fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q') q := by
  classical
  rcases exists_scaled_finBasis_augmented_endpoint_hasFDerivAt g x₀ with
    ⟨ρ, hρ, T, hT, R, hR, β, hfield, hendpoint⟩
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_closedBall
        (g := g) (x₀ := x₀) (0 : A) R with
    ⟨_hFone, Kflow, hflowLip⟩
  rcases
      exists_chartChristoffel_secondVariationCoefficient_bounds_closedBall
        (g := g) (x₀ := x₀) (0 : A) R with
    ⟨Ksecond, Lsecond, hsecondOp, hsecondLip⟩
  let J : E →L[ℝ] A := anchoredBaseInitializationCLM T
  let P : A →L[ℝ] E :=
    AnchoredEndpointIdentity.augmentedFirstVariationPosition
  let B : ℝ≥0 :=
    ⟨‖J‖ * Real.exp ((Kflow : ℝ) * T), by positivity⟩
  let Cgr : ℝ := gronwallBound 0 (Ksecond : ℝ) 1 T
  have hCgr : 0 ≤ Cgr := by
    have hmono : Monotone (gronwallBound 0 (Ksecond : ℝ) 1) :=
      gronwallBound_mono (by norm_num) (by norm_num) Ksecond.2
    have h0T := hmono hT.le
    simpa [Cgr, gronwallBound_x0] using h0T
  let C : ℝ≥0 :=
    ⟨‖P‖ * ‖J‖ * ((Lsecond : ℝ) * (B : ℝ)) *
        Real.exp ((Ksecond : ℝ) * T) * Cgr,
      by
        positivity⟩
  refine ⟨ρ, hρ, ?_⟩
  intro q hq
  apply
    EndpointCurry.contDiffAt_one_clm_of_smul_finBasis_pairwise_fderiv_gronwall
      T (ne_of_gt hT) Metric.isOpen_ball hq (fun _ => C)
  intro i q₁ hq₁ q₂ hq₂
  rcases hendpoint q₁ hq₁ i with
    ⟨Dfull₁, hDfull₁, Ξ₁, hΞ₁0, hΞ₁der, hΞ₁end,
      hβ₁0, hβ₁der, hβ₁mem⟩
  rcases hendpoint q₂ hq₂ i with
    ⟨Dfull₂, hDfull₂, Ξ₂, hΞ₂0, hΞ₂der, hΞ₂end,
      hβ₂0, hβ₂der, hβ₂mem⟩
  let w : E := T • (Module.finBasis ℝ E) i
  let βw : E → ℝ → A := fun q' => β (q', w)
  let D₁ : E →L[ℝ] E := P.comp Dfull₁
  let D₂ : E →L[ℝ] E := P.comp Dfull₂
  have hD₁ : HasFDerivAt
      (fun y : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) y w)
      D₁ q₁ := by
    have hraw := P.hasFDerivAt.comp q₁ hDfull₁
    have hevent : ∀ᶠ y in 𝓝 q₁, y ∈ ball (0 : E) ρ :=
      Metric.isOpen_ball.mem_nhds hq₁
    apply hraw.congr_of_eventuallyEq
    filter_upwards [hevent] with y hy
    simpa [w, P] using (hfield y hy w).symm
  have hD₂ : HasFDerivAt
      (fun y : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) y w)
      D₂ q₂ := by
    have hraw := P.hasFDerivAt.comp q₂ hDfull₂
    have hevent : ∀ᶠ y in 𝓝 q₂, y ∈ ball (0 : E) ρ :=
      Metric.isOpen_ball.mem_nhds hq₂
    apply hraw.congr_of_eventuallyEq
    filter_upwards [hevent] with y hy
    simpa [w, P] using (hfield y hy w).symm
  have hinit' : βw q₂ 0 = βw q₁ 0 + J (q₂ - q₁) := by
    rw [show βw q₂ 0 = β (q₂, w) 0 from rfl,
      show βw q₁ 0 = β (q₁, w) 0 from rfl,
      hβ₂0, hβ₁0]
    simp [J, anchoredBaseInitializationCLM, smul_sub]
  have hβdiff : ∀ t ∈ Ico (0 : ℝ) T,
      ‖βw q₂ t - βw q₁ t‖ ≤ (B : ℝ) * dist q₂ q₁ := by
    intro t ht
    have hbound :=
      parameterizedFlow_sub_norm_le_of_initial_clm
        (F := augmentedGeodesicFlowField (chartChristoffelField g x₀))
        (β := βw) (q₁ := q₁) (q₂ := q₂) J
        (T := T) (a := R) (K := Kflow) (p := (0 : A)) (t := t)
        hflowLip hinit' hβ₁der hβ₂der hβ₁mem hβ₂mem
        (Ico_subset_Icc_self ht)
    simpa [B, dist_eq_norm] using hbound
  have hbound :=
    projected_secondVariation_endpoint_clm_lipschitz_of_augmented_base_curves
      (g := g) (x₀ := x₀)
      (ζ₁ := βw q₁) (ζ₂ := βw q₂)
      (Ξ₁ := Ξ₁) (Ξ₂ := Ξ₂) (D₁ := D₁) (D₂ := D₂)
      J P (T := T) (t := T) (δnorm := dist q₂ q₁)
      (K := (Ksecond : ℝ)) (L := Lsecond) (B := B)
      (S := closedBall (0 : A) R)
      hT.le Ksecond.2 dist_nonneg hsecondLip
      (fun t ht => hβ₁mem t (Ico_subset_Icc_self ht))
      (fun t ht => hβ₂mem t (Ico_subset_Icc_self ht))
      hβdiff
      (fun t ht => hsecondOp _ (hβ₁mem t (Ico_subset_Icc_self ht)))
      (fun t ht => hsecondOp _ (hβ₂mem t (Ico_subset_Icc_self ht)))
      (by simpa [J] using hΞ₁0)
      (by simpa [J] using hΞ₂0)
      hΞ₁der hΞ₂der
      (by
        intro h
        simp [D₁]
        rw [← hΞ₁end h])
      (by
        intro h
        simp [D₂]
        rw [← hΞ₂end h])
      ⟨hT.le, le_rfl⟩
  refine ⟨D₁, D₂, hD₁, hD₂, ?_⟩
  simpa [C, Cgr] using hbound

/-- The canonical `fderiv` is the derivative of the exponential chart on a
small normal ball. -/
theorem exists_expAtChart_hasFDerivAt_on_smallBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∀ q ∈ ball (0 : E) ρ,
      HasFDerivAt
        (expAtChartOpenPartialHomeomorph (g := g) x₀)
        (fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q) q := by
  rcases
      UniformAnchoredAugmentedFamily.exists_uniform_anchored_augmented_family
        (g := g) (x₀ := x₀) with
    ⟨ρ, hρ, _T, _hT, β, hβ⟩
  refine ⟨ρ, hρ, ?_⟩
  intro q hq
  rcases hβ q hq (0 : E) with
    ⟨_hβ0, _hβder, _hβend, hExpDer, _R, _hR, _hβmem⟩
  exact hExpDer

/-- The exponential chart is `C²` at every point of one small normal ball. -/
theorem exists_expAtChart_contDiffAt_two_on_smallBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∀ q ∈ ball (0 : E) ρ,
      ContDiffAt ℝ 2
        (expAtChartOpenPartialHomeomorph (g := g) x₀) q := by
  rcases exists_expAtChart_hasFDerivAt_on_smallBall g x₀ with
    ⟨ρ₁, hρ₁, hder⟩
  rcases exists_expAtChart_fderiv_contDiffAt_one_on_smallBall g x₀ with
    ⟨ρ₂, hρ₂, hc1⟩
  let ρ : ℝ := min ρ₁ ρ₂
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρ₁ hρ₂
  refine ⟨ρ, hρ, ?_⟩
  intro q hq
  have hq₁ : q ∈ ball (0 : E) ρ₁ := by
    exact Metric.ball_subset_ball (min_le_left ρ₁ ρ₂) hq
  have hq₂ : q ∈ ball (0 : E) ρ₂ := by
    exact Metric.ball_subset_ball (min_le_right ρ₁ ρ₂) hq
  apply
    (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)
      (f := expAtChartOpenPartialHomeomorph (g := g) x₀) (x := q)).2
  refine
    ⟨fun y : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) y,
      ?_, hc1 q hq₂⟩
  exact
    ⟨ball (0 : E) ρ₁, Metric.isOpen_ball.mem_nhds hq₁,
      fun y hy => hder y hy⟩

/--
Uniform source and round-sphere normal balls provide the `C²` Cartan chart-map
input.  The only remaining pointwise hypothesis is an invertible derivative
of the source exponential chart, exactly as required by the inverse-function
handoff in `ExpChartC2`.
-/
theorem exists_cartanChartMap_contDiffAt_two_on_small_normal_balls
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρs > (0 : ℝ), ∃ ρt > (0 : ℝ),
      ∀ v : E,
        v ∈ ball (0 : E) ρs →
        L v ∈ ball (0 : E) ρt →
        v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source →
        (∃ sourceIso : E ≃L[ℝ] E,
          HasFDerivAt
            (expAtChartOpenPartialHomeomorph (g := g) x₀)
            (sourceIso : E →L[ℝ] E) v) →
        ContDiffAt ℝ 2 (CartanDifferential.cartanChartMap g x₀ p₀ L)
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) := by
  rcases exists_expAtChart_hasFDerivAt_on_smallBall g x₀ with
    ⟨ρsd, hρsd, hsourceDer⟩
  rcases exists_expAtChart_fderiv_contDiffAt_one_on_smallBall g x₀ with
    ⟨ρsc, hρsc, hsourceC1⟩
  rcases
      exists_expAtChart_hasFDerivAt_on_smallBall
        (M := RoundSphere3) roundSphereMetric3 p₀ with
    ⟨ρtd, hρtd, htargetDer⟩
  rcases
      exists_expAtChart_fderiv_contDiffAt_one_on_smallBall
        (M := RoundSphere3) roundSphereMetric3 p₀ with
    ⟨ρtc, hρtc, htargetC1⟩
  let ρs : ℝ := min ρsd ρsc
  let ρt : ℝ := min ρtd ρtc
  have hρs : 0 < ρs := by
    dsimp [ρs]
    exact lt_min hρsd hρsc
  have hρt : 0 < ρt := by
    dsimp [ρt]
    exact lt_min hρtd hρtc
  refine ⟨ρs, hρs, ρt, hρt, ?_⟩
  intro v hv hLv hvsrc hIso
  rcases hIso with ⟨sourceIso, hsourceIso⟩
  have hv_sd : v ∈ ball (0 : E) ρsd :=
    Metric.ball_subset_ball (min_le_left ρsd ρsc) hv
  have hv_sc : v ∈ ball (0 : E) ρsc :=
    Metric.ball_subset_ball (min_le_right ρsd ρsc) hv
  have hLv_td : L v ∈ ball (0 : E) ρtd :=
    Metric.ball_subset_ball (min_le_left ρtd ρtc) hLv
  have hLv_tc : L v ∈ ball (0 : E) ρtc :=
    Metric.ball_subset_ball (min_le_right ρtd ρtc) hLv
  apply
    ExpChartC2.cartanChartMap_contDiffAt_two_of_expChart_derivative_fields
      (g := g) (x0 := x₀) (p0 := p₀) (L := L) (v := v)
      hvsrc
      (sourceD := fun q : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q)
      (targetD := fun q : E =>
        fderiv ℝ
          (expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) q)
      (sourceIso := sourceIso)
  · exact
      ⟨ball (0 : E) ρsd, Metric.isOpen_ball.mem_nhds hv_sd,
        fun q hq => hsourceDer q hq⟩
  · exact hsourceC1 v hv_sc
  · exact hsourceIso
  · exact
      ⟨ball (0 : E) ρtd, Metric.isOpen_ball.mem_nhds hLv_td,
        fun q hq => htargetDer q hq⟩
  · exact htargetC1 (L v) hLv_tc

end UniformAnchoredSecondVariation
end Poincare
