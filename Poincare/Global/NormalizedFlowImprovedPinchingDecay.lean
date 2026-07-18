import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative decay downstream of Hamilton's improved pinching maximum

Hamilton's improved maximum principle controls
`|Ric°|² / R^(2 - delta)`. That control alone is a uniform bound, not a
decay statement. This file records two honest ways to obtain decay without
assuming a limiting metric:

* a positive scalar lower profile tending to infinity forces the
  scale-invariant anisotropy `|Ric°|² / R²` to tend uniformly to zero;
* integrability of the improved spatial maximum, together with its Hamilton
  antitonicity, forces the maximum and every point value to tend to zero.

The first conclusion also makes the ordinary Ricci pinching quotient tend
uniformly to its Einstein value `1 / 3`. No metric convergence, compactness
extraction, or sphere-recognition conclusion is asserted.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

namespace ClosedSmoothRiemannianMetric

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

variable (g : ClosedSmoothRiemannianMetric 3 M)
variable [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]

/-- The scale-invariant squared traceless-Ricci anisotropy `|Ric°|² / R²`. -/
noncomputable def relativeTracelessRicciAt (x : M) : ℝ :=
  g.tracelessRicciNormSqAt x / (g.scalarAt x) ^ 2

/-- The defining formula for the relative traceless-Ricci anisotropy. -/
theorem relativeTracelessRicciAt_eq (x : M) :
    g.relativeTracelessRicciAt x =
      g.tracelessRicciNormSqAt x / (g.scalarAt x) ^ 2 :=
  rfl

/-- Relative traceless-Ricci anisotropy is nonnegative. -/
theorem relativeTracelessRicciAt_nonneg (x : M) :
    0 ≤ g.relativeTracelessRicciAt x := by
  exact div_nonneg
    (g.tracelessRicciNormSqAt_nonneg x (by norm_num))
    (sq_nonneg (g.scalarAt x))

/-- On the positive-scalar domain, removing the improved pinching weight
leaves exactly one factor `R^delta` in the denominator. -/
theorem relativeTracelessRicciAt_eq_tracelessPinchingAt_div_rpow
    (x : M) (delta : ℝ) (hR : 0 < g.scalarAt x) :
    g.relativeTracelessRicciAt x =
      g.tracelessPinchingAt x delta / (g.scalarAt x) ^ delta := by
  have hfactor :
      (g.scalarAt x) ^ (2 - delta) * (g.scalarAt x) ^ delta =
        (g.scalarAt x) ^ 2 := by
    calc
      (g.scalarAt x) ^ (2 - delta) * (g.scalarAt x) ^ delta =
          (g.scalarAt x) ^ ((2 - delta) + delta) :=
        (Real.rpow_add hR (2 - delta) delta).symm
      _ = (g.scalarAt x) ^ (2 : ℝ) := by ring_nf
      _ = (g.scalarAt x) ^ 2 := Real.rpow_two (g.scalarAt x)
  rw [relativeTracelessRicciAt_eq, tracelessPinchingAt_eq, div_div, hfactor]

/-- In dimension three, relative traceless-Ricci anisotropy is exactly the
gap between the ordinary Ricci quotient and its Einstein value `1 / 3`. -/
theorem pinchingQuotientAt_sub_one_third_eq_relativeTracelessRicciAt
    (x : M) (hR : 0 < g.scalarAt x) :
    g.pinchingQuotientAt x - 1 / 3 = g.relativeTracelessRicciAt x := by
  rw [pinchingQuotientAt_eq, relativeTracelessRicciAt_eq,
    tracelessRicciNormSqAt_eq]
  field_simp [hR.ne']
  ring

end ClosedSmoothRiemannianMetric

section MaximumTrackBasics

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/-- A point value lies below the improved spatial maximum track. -/
theorem tracelessPinchingAt_le_tracelessPinchingMaximumTrack
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t0 delta tau : ℝ)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hQTwo : ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).tracelessPinchingAt y delta) x)
    (x : M) :
    (gt (t0 + tau)).tracelessPinchingAt x delta ≤
      tracelessPinchingMaximumTrack gt t0 delta tau := by
  simpa only [tracelessPinchingMaximumTrack] using
    tracelessPinchingAt_le_tracelessPinchingMaximumAt
      (g := gt (t0 + tau)) delta hQTwo x

/-- Positive scalar curvature makes the improved spatial maximum
nonnegative. -/
theorem tracelessPinchingMaximumTrack_nonneg_of_scalar_pos
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t0 delta tau : ℝ)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hRpos : ∀ x : M, 0 < (gt (t0 + tau)).scalarAt x)
    (hQTwo : ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).tracelessPinchingAt y delta) x) :
    0 ≤ tracelessPinchingMaximumTrack gt t0 delta tau := by
  classical
  let x0 : M := Classical.choice (inferInstance : Nonempty M)
  have hpoint :
      0 ≤ (gt (t0 + tau)).tracelessPinchingAt x0 delta :=
    (gt (t0 + tau)).tracelessPinchingAt_nonneg_of_scalarAt_pos
      x0 delta (by norm_num) (hRpos x0)
  exact hpoint.trans
    (tracelessPinchingAt_le_tracelessPinchingMaximumTrack
      gt t0 delta tau hQTwo x0)

end MaximumTrackBasics

section ScalarGrowthConsumer

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/-- Quantitative downstream estimate from an anchored improved-maximum
bound and a positive scalar lower profile.

The right side is explicit: the initial improved maximum divided by the
remaining scalar factor `m(tau)^delta`. -/
theorem relativeTracelessRicciAt_le_initial_improvedMaximum_div_scalarProfile_rpow
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (m : ℝ → ℝ) {t0 delta tau : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hdelta : 0 < delta)
    (htau : tau ∈ Ici (0 : ℝ))
    (hmPos : ∀ s ∈ Ici (0 : ℝ), 0 < m s)
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      m s ≤ (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y delta) x)
    (hMaximumControl : ∀ s ∈ Ici (0 : ℝ),
      tracelessPinchingMaximumTrack gt t0 delta s ≤
        tracelessPinchingMaximumTrack gt t0 delta 0)
    (x : M) :
    (gt (t0 + tau)).relativeTracelessRicciAt x ≤
      tracelessPinchingMaximumTrack gt t0 delta 0 / (m tau) ^ delta := by
  have hm : 0 < m tau := hmPos tau htau
  have hR : 0 < (gt (t0 + tau)).scalarAt x :=
    hm.trans_le (hScalarLower tau htau x)
  have hpointMax :
      (gt (t0 + tau)).tracelessPinchingAt x delta ≤
        tracelessPinchingMaximumTrack gt t0 delta tau :=
    tracelessPinchingAt_le_tracelessPinchingMaximumTrack
      gt t0 delta tau (hQTwo tau htau) x
  have hpointInitial :
      (gt (t0 + tau)).tracelessPinchingAt x delta ≤
        tracelessPinchingMaximumTrack gt t0 delta 0 :=
    hpointMax.trans (hMaximumControl tau htau)
  have hpointNonneg :
      0 ≤ (gt (t0 + tau)).tracelessPinchingAt x delta :=
    (gt (t0 + tau)).tracelessPinchingAt_nonneg_of_scalarAt_pos
      x delta (by norm_num) hR
  have hInitialNonneg :
      0 ≤ tracelessPinchingMaximumTrack gt t0 delta 0 :=
    hpointNonneg.trans hpointInitial
  have hpowLe :
      (m tau) ^ delta ≤ ((gt (t0 + tau)).scalarAt x) ^ delta :=
    Real.rpow_le_rpow hm.le (hScalarLower tau htau x) hdelta.le
  rw [(gt (t0 + tau)).relativeTracelessRicciAt_eq_tracelessPinchingAt_div_rpow
    x delta hR]
  exact
    (div_le_div_of_nonneg_right hpointInitial
      (Real.rpow_pos_of_pos hR delta).le).trans
      (div_le_div_of_nonneg_left hInitialNonneg
        (Real.rpow_pos_of_pos hm delta) hpowLe)

/-- If the positive scalar lower profile tends to infinity, an anchored
Hamilton improved-maximum bound forces uniform pointwise decay of
`|Ric°|² / R²`. -/
theorem relativeTracelessRicciAt_eventually_uniformly_small_of_improvedMaximum_of_scalarProfile_atTop
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (m : ℝ → ℝ) {t0 delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hdelta : 0 < delta)
    (hmPos : ∀ s ∈ Ici (0 : ℝ), 0 < m s)
    (hmAtTop : Tendsto m atTop atTop)
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      m s ≤ (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y delta) x)
    (hMaximumControl : ∀ s ∈ Ici (0 : ℝ),
      tracelessPinchingMaximumTrack gt t0 delta s ≤
        tracelessPinchingMaximumTrack gt t0 delta 0) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ s in atTop, ∀ x : M,
      (gt (t0 + s)).relativeTracelessRicciAt x < eta := by
  intro eta heta
  have hpowAtTop : Tendsto (fun s : ℝ ↦ (m s) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp hmAtTop
  have hboundZero :
      Tendsto
        (fun s : ℝ ↦
          tracelessPinchingMaximumTrack gt t0 delta 0 / (m s) ^ delta)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpowAtTop
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    hboundZero.eventually (Iio_mem_nhds heta)] with s hs hbound
  intro x
  exact
    (relativeTracelessRicciAt_le_initial_improvedMaximum_div_scalarProfile_rpow
      gt m hdelta hs hmPos hScalarLower hQTwo hMaximumControl x).trans_lt hbound

/-- Under the same scalar-growth premise, the ordinary Ricci quotient tends
uniformly to the three-dimensional Einstein value `1 / 3`. -/
theorem pinchingQuotientAt_eventually_uniformly_close_one_third_of_improvedMaximum_of_scalarProfile_atTop
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (m : ℝ → ℝ) {t0 delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hdelta : 0 < delta)
    (hmPos : ∀ s ∈ Ici (0 : ℝ), 0 < m s)
    (hmAtTop : Tendsto m atTop atTop)
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      m s ≤ (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y delta) x)
    (hMaximumControl : ∀ s ∈ Ici (0 : ℝ),
      tracelessPinchingMaximumTrack gt t0 delta s ≤
        tracelessPinchingMaximumTrack gt t0 delta 0) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ s in atTop, ∀ x : M,
      |(gt (t0 + s)).pinchingQuotientAt x - 1 / 3| < eta := by
  intro eta heta
  have hrelative :=
    relativeTracelessRicciAt_eventually_uniformly_small_of_improvedMaximum_of_scalarProfile_atTop
      gt m hdelta hmPos hmAtTop hScalarLower hQTwo hMaximumControl eta heta
  filter_upwards [eventually_ge_atTop (0 : ℝ), hrelative] with s hs hsmall
  intro x
  have hR : 0 < (gt (t0 + s)).scalarAt x :=
    (hmPos s hs).trans_le (hScalarLower s hs x)
  rw [(gt (t0 + s)).pinchingQuotientAt_sub_one_third_eq_relativeTracelessRicciAt
    x hR, abs_of_nonneg ((gt (t0 + s)).relativeTracelessRicciAt_nonneg x)]
  exact hsmall x

end ScalarGrowthConsumer

section IntegrableAntitoneConsumer

/-- A nonnegative antitone function on the forward real ray that is
integrable there must tend to zero. -/
theorem tendsto_zero_of_antitoneOn_Ici_of_nonneg_of_integrableOn
    (D : ℝ → ℝ)
    (hNonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ D t)
    (hAntitone : AntitoneOn D (Ici (0 : ℝ)))
    (hIntegrable : IntegrableOn D (Ici (0 : ℝ))) :
    Tendsto D atTop (nhds 0) := by
  obtain ⟨sample, hsampleAtTop, hsampleZero⟩ :=
    exists_escaping_sample_value_tendsto_zero_of_integrableOn_nonneg
      D hNonneg hIntegrable
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact ha.trans_le (hNonneg t ht)
  · intro b hb
    have hsampleNonneg : ∀ᶠ i in atTop, 0 ≤ sample i :=
      hsampleAtTop.eventually (eventually_ge_atTop (0 : ℝ))
    have hsampleLt : ∀ᶠ i in atTop, D (sample i) < b :=
      hsampleZero.eventually (Iio_mem_nhds hb)
    obtain ⟨i, hiNonneg, hiLt⟩ := (hsampleNonneg.and hsampleLt).exists
    filter_upwards [eventually_ge_atTop (sample i)] with t hit
    exact (hAntitone hiNonneg (hiNonneg.trans hit) hit).trans_lt hiLt

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "TM" => (TangentSpace I : M → Type _)

/-- Global forward Hamilton improvement on every translated finite slab
makes the improved maximum track genuinely antitone on the whole forward
ray. All regularity, evolution, positivity, and eigenvalue-floor premises
remain explicit. -/
theorem tracelessPinchingMaximumTrack_antitoneOn_of_hamilton_forward_improvement
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 epsilon delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hepsilonPos : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hQCont : ∀ s ∈ Ici (0 : ℝ),
      Continuous ↿(fun tau (x : M) ↦
        (gt ((t0 + s) + tau)).tracelessPinchingAt x delta))
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y delta) x)
    (hEvol : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + s) x delta
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hPin : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) epsilon) :
    AntitoneOn (tracelessPinchingMaximumTrack gt t0 delta) (Ici (0 : ℝ)) := by
  intro s hs u hu hsu
  have hLength : 0 ≤ u - s := sub_nonneg.mpr hsu
  have hLocal :=
    hamilton_pinching_improvement
      (gt := gt) (t₀ := t0 + s) (T := u - s)
      (ε := epsilon) (δ := delta)
      rfl hLength hepsilonPos hepsilonLe hdeltaNonneg hdeltaAdm
      (hQCont s hs)
      (fun tau htau x ↦ by
        simpa only [add_assoc] using
          hQTwo (s + tau) (add_nonneg hs htau.1) x)
      (fun tau htau x ↦ by
        simpa only [add_assoc] using
          hEvol (s + tau) (add_nonneg hs htau.1) x)
      (fun tau htau x b mu hEig i ↦ by
        have hEig' : ∀ j : Fin 3,
            (gt (t0 + (s + tau))).ricciEndoAt x (b j) = mu j • b j := by
          simpa only [add_assoc] using hEig
        simpa only [add_assoc] using
          hPin (s + tau) (add_nonneg hs htau.1) x b mu hEig' i)
  have hEndpoint := hLocal (u - s) ⟨hLength, le_rfl⟩
  have htime : (t0 + s) + (u - s) = t0 + u := by ring
  simpa only [tracelessPinchingMaximumTrack, htime, add_zero] using hEndpoint

/-- Antitonicity plus integrability is the exact scalar premise needed to
turn the improved maximum bound into decay of that maximum. -/
theorem tracelessPinchingMaximumTrack_tendsto_zero_of_antitoneOn_of_integrableOn
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y delta) x)
    (hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 delta) (Ici (0 : ℝ)))
    (hIntegrable :
      IntegrableOn (tracelessPinchingMaximumTrack gt t0 delta) (Ici 0)) :
    Tendsto (tracelessPinchingMaximumTrack gt t0 delta) atTop (nhds 0) := by
  apply tendsto_zero_of_antitoneOn_Ici_of_nonneg_of_integrableOn
    (tracelessPinchingMaximumTrack gt t0 delta) _ hAntitone hIntegrable
  intro s hs
  exact tracelessPinchingMaximumTrack_nonneg_of_scalar_pos
    gt t0 delta s (hRpos s hs) (hQTwo s hs)

/-- An integrable antitone improved maximum forces its pointwise pinching
quantity to tend uniformly to zero on the whole forward ray. -/
theorem tracelessPinchingAt_eventually_uniformly_small_of_antitoneMaximum_of_integrableMaximum
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y delta) x)
    (hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 delta) (Ici (0 : ℝ)))
    (hIntegrable :
      IntegrableOn (tracelessPinchingMaximumTrack gt t0 delta) (Ici 0)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ s in atTop, ∀ x : M,
      (gt (t0 + s)).tracelessPinchingAt x delta < eta := by
  intro eta heta
  have hMaximumZero :=
    tracelessPinchingMaximumTrack_tendsto_zero_of_antitoneOn_of_integrableOn
      gt hRpos hQTwo hAntitone hIntegrable
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    hMaximumZero.eventually (Iio_mem_nhds heta)] with s hs hmax
  intro x
  exact (tracelessPinchingAt_le_tracelessPinchingMaximumTrack
    gt t0 delta s (hQTwo s hs) x).trans_lt hmax

/-- Fully downstream analytic consumer: explicit global Hamilton evolution
gives antitonicity; integrability of the resulting maximum gives uniform
pointwise decay. -/
theorem tracelessPinchingAt_eventually_uniformly_small_of_hamilton_forward_improvement_of_integrableMaximum
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 epsilon delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hepsilonPos : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x)
    (hQCont : ∀ s ∈ Ici (0 : ℝ),
      Continuous ↿(fun tau (x : M) ↦
        (gt ((t0 + s) + tau)).tracelessPinchingAt x delta))
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y delta) x)
    (hEvol : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + s) x delta
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hPin : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) epsilon)
    (hIntegrable :
      IntegrableOn (tracelessPinchingMaximumTrack gt t0 delta) (Ici 0)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ s in atTop, ∀ x : M,
      (gt (t0 + s)).tracelessPinchingAt x delta < eta := by
  have hAntitone :=
    tracelessPinchingMaximumTrack_antitoneOn_of_hamilton_forward_improvement
      gt hepsilonPos hepsilonLe hdeltaNonneg hdeltaAdm
        hQCont hQTwo hEvol hPin
  exact
    tracelessPinchingAt_eventually_uniformly_small_of_antitoneMaximum_of_integrableMaximum
      gt hRpos hQTwo hAntitone hIntegrable

end IntegrableAntitoneConsumer

end Poincare
