import Poincare.Global.MetricVariation
import Poincare.Global.Laplacian
import Poincare.Global.RicciNorm
import Poincare.LocalConnectionRegularity
import Poincare.ChartIdentification

/-!
# Scalar curvature variation: first closed-manifold layer

This file records the first reusable closed-manifold facts needed before the
full scalar-variation formula can be ported from the model-space chain in
`ModelLaplacian.lean`.

The main proved step is the finite-dimensional trace decomposition: once the
raised Ricci endomorphism has a genuine time derivative, scalar curvature has
a time derivative and its derivative is the trace of that Ricci-endomorphism
derivative.  This is the closed analogue of the model theorem
`RicciFlow.RicciFlow.hasDerivAt_trace`.

The later Lichnerowicz target is intentionally not encoded here as a fake
placeholder: the closed-manifold double-divergence vocabulary is still missing.
The intended shape is recorded in `harness/reports/M3-scalar-variation_notes.md`
against the model analogues `ricciDeriv_*`,
`lichnerowiczLaplacian_*`, `g_covDeltaGammaDeriv_lichnerowicz`, and
`hamilton_scalar_evolution_of_bianchi`.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

namespace ClosedSmoothRiemannianMetric

omit [T2Space M] in
/--
The blended chart representative of a closed smooth metric is `C³`.

This is the regularity input needed to apply the model contracted Bianchi
identity to the cutoff chart metric.
-/
theorem contDiff_three_blendedChartMetric
    (g : ClosedSmoothRiemannianMetric n M)
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (x₀ : M)
    (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : tsupport χ ⊆ (extChartAt I x₀).target) :
    ContDiff ℝ 3 (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀) := by
  have hthree_le_top : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hthree_add_one_le_top : (3 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (3 : ℕ∞ω) + 1 = ((4 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg3 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 3
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le hthree_le_top
  exact CovariantDerivative.contDiff_blendedChartMetric χ G₀ g.inner x₀
    hthree_add_one_le_top hχ hχsupp hg3

/--
On the cutoff-one chart neighborhood, the transported model Levi-Civita value
is the public closed metric connection `g.leviCivita`.
-/
theorem chartTransportedLeviCivitaValueAt_eq_leviCivita_of_eventually_eq_one
    (g : ClosedSmoothRiemannianMetric n M)
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hbl : Differentiable ℝ (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    {σ : Π y : M, TM y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I x₀ y), χ z' = 1)
    (hσ : MDiffAtTangentField σ y)
    (v : TM y) :
    CovariantDerivative.chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp σ hy v =
      g.leviCivita σ y v := by
  simpa [leviCivita] using
    (LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
      g χ G₀ hG₀pos x₀ hχ0 hχ1 hsupp hbl hG₀symm hy hχone hσ v)

/--
The raised Ricci endomorphism as a continuous-linear map on the tangent fiber.

The underlying geometric object is `g.ricciEndoAt x`; the wrapper lets us use
the existing trace derivative theorem for paths in `E →L[ℝ] E`.
-/
noncomputable def ricciEndoContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : TM x →L[ℝ] TM x :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (g.ricciEndoAt x)

theorem ricciEndoContinuousAt_coe
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    (g.ricciEndoContinuousAt x : TM x →ₗ[ℝ] TM x) = g.ricciEndoAt x := by
  rfl

/-- Scalar curvature is the trace of the continuous-linear Ricci endomorphism. -/
theorem scalarAt_eq_trace_ricciEndoContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    g.scalarAt x =
      LinearMap.trace ℝ (TM x) (g.ricciEndoContinuousAt x : TM x →ₗ[ℝ] TM x) := by
  rw [g.scalarAt_eq_trace_ricciEndoAt]
  rfl

/--
Honest time differentiability hypothesis for the raised Ricci endomorphism.

This is stronger than differentiability of each Ricci component: it asserts a
derivative of the actual endomorphism path on the finite-dimensional tangent
fiber.
-/
def RicciEndoHasDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (A' : TM x →L[ℝ] TM x) : Prop :=
  HasDerivAt (fun t ↦ (gt t).ricciEndoContinuousAt x) A' t₀

/-- The metric index-raising map, packaged as a continuous linear map on the
continuous dual of a fixed tangent fiber. -/
noncomputable def metricRaiseContinuousAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    (TM x →L[ℝ] ℝ) →L[ℝ] TM x :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm.toLinearMap) ∘ₗ
      (LinearMap.toContinuousLinearMap.symm :
        (TM x →L[ℝ] ℝ) ≃ₗ[ℝ] (TM x →ₗ[ℝ] ℝ)).toLinearMap)

/-- Lowering the metric-raised continuous covector recovers the covector. -/
theorem metricRaiseContinuousAt_inner_apply
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (φ : TM x →L[ℝ] ℝ) (v : TM x) :
    (g.inner x ((g.metricRaiseContinuousAt x) φ)) v = φ v := by
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  change g.metricBilinAt x ((g.metricRaiseContinuousAt x) φ) v = φ v
  unfold metricRaiseContinuousAt
  let A := LinearMap.BilinForm.toDual (g.metricBilinAt x)
    (g.metricBilinAt_nondegenerate x)
  let ψ : Module.Dual ℝ (TM x) := LinearMap.toContinuousLinearMap.symm φ
  have h : A (A.symm ψ) = ψ := LinearEquiv.apply_symm_apply A ψ
  have hv : (A (A.symm ψ)) v = ψ v :=
    congrArg (fun η : Module.Dual ℝ (TM x) ↦ η v) h
  change (g.metricBilinAt x) (A.symm ψ) v = φ v
  change (A (A.symm ψ)) v = ψ v
  exact hv

/-- The Ricci tensor as a continuous-linear map into the continuous dual. -/
noncomputable def ricciDualContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : TM x →L[ℝ] (TM x →L[ℝ] ℝ) :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (((LinearMap.toContinuousLinearMap :
        (TM x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TM x →L[ℝ] ℝ)).toLinearMap) ∘ₗ
      CovariantDerivative.ricciDualAt g.leviCivita x)

@[simp] theorem ricciDualContinuousAt_apply
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    g.ricciDualContinuousAt x u w = g.ricciAt x u w :=
  by
    simp [ricciDualContinuousAt, ClosedSmoothRiemannianMetric.ricciAt,
      CovariantDerivative.ricciDualAt]

/-- The existing Ricci endomorphism wrapper is the raised Ricci-dual map. -/
theorem ricciEndoContinuousAt_eq_metricRaise_comp_ricciDualContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    g.ricciEndoContinuousAt x =
      (g.metricRaiseContinuousAt x).comp (g.ricciDualContinuousAt x) := by
  ext u
  simp [ricciEndoContinuousAt, ricciEndoAt, metricRaiseContinuousAt,
    ricciDualContinuousAt]

theorem ricciBilinearDeriv_add_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀)
    (u u' w : TM x) :
    δRic (u + u') w = δRic u w + δRic u' w := by
  have hsum := (hRic u w).add (hRic u' w)
  have htarget := hRic (u + u') w
  have hpath :
      (fun t ↦ (gt t).ricciAt x (u + u') w) =
        fun t ↦ (gt t).ricciAt x u w + (gt t).ricciAt x u' w := by
    funext t
    exact (gt t).ricciAt_add_left x u u' w
  rw [hpath] at htarget
  exact htarget.unique hsum

theorem ricciBilinearDeriv_smul_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀)
    (c : ℝ) (u w : TM x) :
    δRic (c • u) w = c • δRic u w := by
  have hscale := (hRic u w).const_smul c
  have htarget := hRic (c • u) w
  have hpath :
      (fun t ↦ (gt t).ricciAt x (c • u) w) =
        fun t ↦ c • (gt t).ricciAt x u w := by
    funext t
    exact (gt t).ricciAt_smul_left x c u w
  rw [hpath] at htarget
  exact htarget.unique hscale

theorem ricciBilinearDeriv_add_right
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀)
    (u w w' : TM x) :
    δRic u (w + w') = δRic u w + δRic u w' := by
  have hsum := (hRic u w).add (hRic u w')
  have htarget := hRic u (w + w')
  have hpath :
      (fun t ↦ (gt t).ricciAt x u (w + w')) =
        fun t ↦ (gt t).ricciAt x u w + (gt t).ricciAt x u w' := by
    funext t
    exact (gt t).ricciAt_add_right x u w w'
  rw [hpath] at htarget
  exact htarget.unique hsum

theorem ricciBilinearDeriv_smul_right
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀)
    (c : ℝ) (u w : TM x) :
    δRic u (c • w) = c • δRic u w := by
  have hscale := (hRic u w).const_smul c
  have htarget := hRic u (c • w)
  have hpath :
      (fun t ↦ (gt t).ricciAt x u (c • w)) =
        fun t ↦ c • (gt t).ricciAt x u w := by
    funext t
    exact (gt t).ricciAt_smul_right x c u w
  rw [hpath] at htarget
  exact htarget.unique hscale

/-- Package pointwise Ricci-variation components as a continuous-linear
dual-valued map.  Linearity is obtained from the derivative hypotheses by
uniqueness, not assumed separately. -/
noncomputable def ricciDerivativeDualContinuousAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (δRic : TM x → TM x → ℝ)
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀) :
    TM x →L[ℝ] (TM x →L[ℝ] ℝ) :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let δRicDual : TM x →ₗ[ℝ] Module.Dual ℝ (TM x) :=
    { toFun := fun u ↦
        { toFun := fun w ↦ δRic u w
          map_add' := fun w w' ↦ ricciBilinearDeriv_add_right hRic u w w'
          map_smul' := fun c w ↦ ricciBilinearDeriv_smul_right hRic c u w }
      map_add' := by
        intro u u'
        ext w
        exact ricciBilinearDeriv_add_left hRic u u' w
      map_smul' := by
        intro c u
        ext w
        exact ricciBilinearDeriv_smul_left hRic c u w }
  LinearMap.toContinuousLinearMap
    (((LinearMap.toContinuousLinearMap :
        (TM x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TM x →L[ℝ] ℝ)).toLinearMap) ∘ₗ
      δRicDual)

@[simp] theorem ricciDerivativeDualContinuousAt_apply
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀)
    (u w : TM x) :
    ricciDerivativeDualContinuousAt (gt := gt) (t₀ := t₀) (x := x) δRic hRic u w =
      δRic u w :=
  by
    simp [ricciDerivativeDualContinuousAt]

theorem hasDerivAt_ricciDualContinuousAt_of_ricciBilinearHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀) :
    HasDerivAt (fun t ↦ (gt t).ricciDualContinuousAt x)
      (ricciDerivativeDualContinuousAt (gt := gt) (t₀ := t₀) (x := x) δRic hRic)
      t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
  intro u
  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
  intro w
  simpa using hRic u w

/--
Lift pointwise Ricci bilinear derivatives to the raised Ricci endomorphism.

The derivative of the metric raising map is supplied as an explicit honest
hypothesis; the formula is the product rule
`d(raise ∘ RicDual) = d(raise) ∘ RicDual + raise ∘ d(RicDual)`.
-/
theorem ricciEndoHasDerivAt_of_ricciBilinearHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀) :
    RicciEndoHasDerivAt gt t₀ x
      (raise'.comp ((gt t₀).ricciDualContinuousAt x) +
        ((gt t₀).metricRaiseContinuousAt x).comp
          (ricciDerivativeDualContinuousAt
            (gt := gt) (t₀ := t₀) (x := x) δRic hRic)) := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hRicDual :=
    hasDerivAt_ricciDualContinuousAt_of_ricciBilinearHasDerivAt
      (gt := gt) (t₀ := t₀) (x := x) hRic
  have hcomp : HasDerivAt
      (fun t ↦ ((gt t).metricRaiseContinuousAt x).comp
        ((gt t).ricciDualContinuousAt x))
      (raise'.comp ((gt t₀).ricciDualContinuousAt x) +
        ((gt t₀).metricRaiseContinuousAt x).comp
          (ricciDerivativeDualContinuousAt
            (gt := gt) (t₀ := t₀) (x := x) δRic hRic))
      t₀ :=
    @HasDerivAt.clm_comp ℝ _ (TM x →L[ℝ] ℝ) _ _ (TM x) _ _ t₀
      (TM x) _ _
      (fun t ↦ (gt t).metricRaiseContinuousAt x)
      raise'
      (fun t ↦ (gt t).ricciDualContinuousAt x)
      (ricciDerivativeDualContinuousAt
        (gt := gt) (t₀ := t₀) (x := x) δRic hRic)
      hRaise hRicDual
  unfold RicciEndoHasDerivAt
  convert hcomp using 1

/--
The trace decomposition for scalar variation: differentiating the trace of the
raised Ricci endomorphism gives the trace of the endomorphism derivative.
-/
theorem hasDerivAt_trace_ricciEndoContinuousAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    HasDerivAt
      (fun t ↦ LinearMap.trace ℝ (TM x)
        ((gt t).ricciEndoContinuousAt x : TM x →ₗ[ℝ] TM x))
      (LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x)) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact RicciFlow.RicciFlow.hasDerivAt_trace hA

/--
Differentiability layer for scalar curvature from a genuine Ricci-endomorphism
time derivative.
-/
theorem hasDerivAt_scalarAt_of_ricciEndoHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    HasDerivAt (fun t ↦ (gt t).scalarAt x)
      (LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x)) t₀ := by
  have htrace := hasDerivAt_trace_ricciEndoContinuousAt hA
  convert htrace using 1

/-- The `DifferentiableAt` prerequisite for `SatisfiesHamiltonScalarEvolutionAt`. -/
theorem differentiableAt_scalarAt_of_ricciEndoHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    DifferentiableAt ℝ (fun t ↦ (gt t).scalarAt x) t₀ :=
  (hasDerivAt_scalarAt_of_ricciEndoHasDerivAt hA).differentiableAt

/-- Formula for `deriv scalarAt` once the Ricci-endomorphism derivative is known. -/
theorem deriv_scalarAt_eq_trace_of_ricciEndoHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x) :=
  (hasDerivAt_scalarAt_of_ricciEndoHasDerivAt hA).deriv

end ClosedSmoothRiemannianMetric

/-- The metric time derivative, packaged as a continuous bilinear form. -/
noncomputable def timeDerivContinuousAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hgt : TimeDifferentiableAt gt t₀ x) :
    TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (((LinearMap.toContinuousLinearMap :
        (TM x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TM x →L[ℝ] ℝ)).toLinearMap) ∘ₗ
      timeDerivBilinAt gt t₀ x hgt)

omit [T2Space M] in
@[simp] theorem timeDerivContinuousAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hgt : TimeDifferentiableAt gt t₀ x) (v w : TM x) :
    timeDerivContinuousAt gt t₀ x hgt v w = timeDerivAt gt t₀ x v w := by
  simp [timeDerivContinuousAt, timeDerivBilinAt]

omit [T2Space M] in
/-- Pointwise time differentiability of a metric gives a derivative of the
metric tensor as a continuous bilinear form on the fixed tangent fiber. -/
theorem hasDerivAt_inner_of_timeDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    HasDerivAt (fun t ↦ (gt t).inner x)
      (timeDerivContinuousAt gt t₀ x hgt) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
  intro v
  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
  intro w
  simpa [timeDerivAt] using (hgt v w).hasDerivAt

/--
Honest time differentiability hypothesis for canonical connection values on
canonical extended sections.

This is the closed-manifold analogue of the model `christoffelDeriv`
regularity input, but stated directly for the canonical Levi-Civita connection.
-/
def ConnectionValueTimeDifferentiableAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ v w : TM x, DifferentiableAt ℝ
    (fun t ↦ (gt t).leviCivita (extend E w) x v) t₀

/--
The pointwise connection variation `δΓ(v,w)`, defined as the time derivative
of the canonical Levi-Civita connection applied to the canonical extension of
`w` in direction `v`.
-/
noncomputable def deltaGammaAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TM x → TM x → TM x :=
  fun v w ↦
    letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
    deriv (fun t ↦ (gt t).leviCivita (extend E w) x v) t₀

theorem deltaGammaAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v w : TM x) :
    deltaGammaAt gt t₀ x v w =
      deriv (fun t ↦ (gt t).leviCivita (extend E w) x v) t₀ :=
  rfl

/-- If the connection-value path has derivative `Γ'`, `deltaGammaAt` recovers it. -/
theorem deltaGammaAt_eq_of_hasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    {v w : TM x} {Γ' : TM x}
    (hΓ : HasDerivAt (fun t ↦ (gt t).leviCivita (extend E w) x v) Γ' t₀) :
    deltaGammaAt gt t₀ x v w = Γ' := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  exact hΓ.deriv

/-- The canonical extension is additive in its seed tangent vector. -/
theorem extend_tangent_add {x : M} (w w' : TM x) :
    extend E (w + w') = extend E w + extend E w' := by
  funext y
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hcoord :
      (e ⟨x, w + w'⟩).2 = (e ⟨x, w⟩).2 + (e ⟨x, w'⟩).2 := by
    simpa using (e.linear ℝ hx).map_add w w'
  change e.symm y ((e ⟨x, w + w'⟩).2) =
    e.symm y ((e ⟨x, w⟩).2) + e.symm y ((e ⟨x, w'⟩).2)
  rw [hcoord]
  simpa [Trivialization.symmL_apply] using
    (map_add (e.symmL ℝ y) ((e ⟨x, w⟩).2) ((e ⟨x, w'⟩).2))

/-- The canonical extension is homogeneous in its seed tangent vector. -/
theorem extend_tangent_smul {x : M} (c : ℝ) (w : TM x) :
    extend E (c • w) = (fun _ : M ↦ c) • extend E w := by
  funext y
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hcoord :
      (e ⟨x, c • w⟩).2 = c • (e ⟨x, w⟩).2 := by
    simpa using (e.linear ℝ hx).map_smul c w
  change e.symm y ((e ⟨x, c • w⟩).2) = c • e.symm y ((e ⟨x, w⟩).2)
  rw [hcoord]
  change (e.symmL ℝ y) (c • (e ⟨x, w⟩).2) =
    c • (e.symmL ℝ y) ((e ⟨x, w⟩).2)
  exact map_smul (e.symmL ℝ y) c ((e ⟨x, w⟩).2)

omit [T2Space M] in
/--
In the anchor chart, the canonical tangent extension has constant
representative equal to its seed tangent vector.
-/
theorem mfderiv_extChartAt_extend_apply
    {x y : M} (hy : y ∈ (extChartAt I x).source) (p : TM x) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (extend E p y) = p := by
  let e := trivializationAt E (TangentSpace I) x
  have hy_chart : y ∈ (chartAt E x).source := by
    rwa [extChartAt_source] at hy
  have hsymm :
      e.symmL ℝ y =
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm
          (Set.range I) (extChartAt I x y) := by
    simpa [e] using
      (@TangentBundle.symmL_trivializationAt ℝ _ E _ _ E _
        I M _ _ (by infer_instance) x y hy_chart)
  have hpcoord : (e ⟨x, p⟩).2 = p := by
    have hround :
        fderivWithin ℝ ((extChartAt I x) ∘ (extChartAt I x).symm)
            (Set.range I) (extChartAt I x x) p = p := by
      simpa using congrArg (fun L : E →L[ℝ] E => L p)
        (@fderivWithin_extChartAt_comp_extChartAt_symm_range ℝ _
          E _ _ E _ I M _ _ x)
    simpa [e, TangentBundle.trivializationAt_apply,
      ModelWithCorners.range_eq_univ I] using hround
  have hext : extend E p y = e.symmL ℝ y p := by
    simp [FiberBundle.extend, e, hpcoord, Trivialization.symmL_apply]
  rw [hext, hsymm]
  have hcomp :
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y) ∘L
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm
          (Set.range I) (extChartAt I x y)) =
          ContinuousLinearMap.id ℝ E := by
    simpa using
      (@mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' ℝ _
        E _ _ E _ I M _ _ (by infer_instance) x y hy)
  exact congrArg (fun L : E →L[ℝ] E => L p) hcomp

omit [T2Space M] in
/-- The inverse-chart transport of a canonical extension is constant in its anchor chart. -/
theorem chartTransportedLeviCivitaSection_extend_apply_chart
    {x y : M} (hy : y ∈ (extChartAt I x).source) (p : TM x) :
    CovariantDerivative.chartTransportedLeviCivitaSection x
        (extend E p) (extChartAt I x y) = p := by
  rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
    x (extend E p) hy]
  exact mfderiv_extChartAt_extend_apply (x := x) hy p

theorem extDerivFun_extDerivFun_extend_eq_fderiv_fderiv_chart
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v : TM x) :
    extDerivFun (fun y : M ↦ extDerivFun f y (extend E v y)) x v =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm))
        (extChartAt I x x) v v := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  let F : E → ℝ := f ∘ (extChartAt I x).symm
  let A : E → ℝ := fun z ↦
    fderiv ℝ F z
      (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I x).symm (extend E v) z)
  let B : E → ℝ := fun z ↦ fderiv ℝ F z v
  have hchart :=
    _root_.extDerivFun_extDerivFun_chart
      (I' := I) (f := f) (U := extend E v) (x := x)
      hf (by simpa using (mdifferentiableAt_extend (σ₀ := v) ..)) v
  have hAB : A =ᶠ[nhds (extChartAt I x x)] B := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds
      (mem_extChartAt_target x)] with z hzT
    have hy : (extChartAt I x).symm z ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hzT
    have hz_eq : extChartAt I x ((extChartAt I x).symm z) = z :=
      (extChartAt I x).right_inv hzT
    have hpull :=
      mpullback_extChartAt_symm_apply (I' := I) (x := x)
        (y := (extChartAt I x).symm z) hy (extend E v)
    rw [hz_eq] at hpull
    have hconst :=
      mfderiv_extChartAt_extend_apply (x := x)
        (y := (extChartAt I x).symm z) hy v
    simpa [A, B] using
      congrArg (fun w : E ↦ fderiv ℝ F z w) (hpull.trans hconst)
  have hF : ContDiffAt ℝ 2 F (extChartAt I x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [ModelWithCorners.range_eq_univ I, contDiffWithinAt_univ] at h
    have heq : (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I x).symm =
        f ∘ (extChartAt I x).symm := by
      funext z
      simp
    rwa [heq] at h
  have hBderiv :
      fderiv ℝ B (extChartAt I x x) v =
        fderiv ℝ (fderiv ℝ F) (extChartAt I x x) v v := by
    have hdf : DifferentiableAt ℝ (fderiv ℝ F) (extChartAt I x x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hcomp :=
      ((ContinuousLinearMap.apply ℝ ℝ (v : E)).hasFDerivAt.comp
        (extChartAt I x x) hdf.hasFDerivAt).fderiv
    simpa [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using
      congrArg (fun L : E →L[ℝ] ℝ ↦ L (v : E)) hcomp
  calc
    extDerivFun (fun y : M ↦ extDerivFun f y (extend E v y)) x v
        = fderiv ℝ A (extChartAt I x x) v := by
            simpa [A, F] using hchart
    _ = fderiv ℝ B (extChartAt I x x) v := by
            rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hAB]
    _ = fderiv ℝ (fderiv ℝ F) (extChartAt I x x) v v := hBderiv
    _ = fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm))
          (extChartAt I x x) v v := rfl

omit [T2Space M] in
/-- Canonical tangent extensions have zero Lie bracket at their common anchor. -/
theorem mlieBracket_extend_extend_apply_self
    {x : M} (p q : TM x) :
    VectorField.mlieBracket I (extend E p) (extend E q) x = 0 := by
  let Xc : E → E :=
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
      (extend E p) (Set.range I)
  let Yc : E → E :=
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
      (extend E q) (Set.range I)
  have hX : Xc =ᶠ[nhdsWithin (extChartAt I x x) (Set.range I)] fun _ : E => p := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    have hy : (extChartAt I x).symm z ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz
    have hz_eq : extChartAt I x ((extChartAt I x).symm z) = z :=
      (extChartAt I x).right_inv hz
    have hval :=
      chartTransportedLeviCivitaSection_extend_apply_chart (x := x)
        (y := (extChartAt I x).symm z) hy p
    rw [hz_eq] at hval
    simpa [Xc, CovariantDerivative.chartTransportedLeviCivitaSection] using hval
  have hY : Yc =ᶠ[nhdsWithin (extChartAt I x x) (Set.range I)] fun _ : E => q := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    have hy : (extChartAt I x).symm z ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz
    have hz_eq : extChartAt I x ((extChartAt I x).symm z) = z :=
      (extChartAt I x).right_inv hz
    have hval :=
      chartTransportedLeviCivitaSection_extend_apply_chart (x := x)
        (y := (extChartAt I x).symm z) hy q
    rw [hz_eq] at hval
    simpa [Yc, CovariantDerivative.chartTransportedLeviCivitaSection] using hval
  have hbr :
      VectorField.lieBracketWithin ℝ Xc Yc (Set.range I) (extChartAt I x x) =
        VectorField.lieBracketWithin ℝ (fun _ : E => p) (fun _ : E => q)
          (Set.range I) (extChartAt I x x) :=
    Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
      hX hY (Set.mem_range_self _)
  rw [mlieBracket_apply_chart]
  change VectorField.lieBracketWithin ℝ Xc Yc (Set.range I) (extChartAt I x x) = 0
  rw [hbr]
  simp [VectorField.lieBracketWithin]

/-- Additivity of `δΓ` in its direction slot. -/
theorem deltaGammaAt_add_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (v v' w : TM x) :
    deltaGammaAt gt t₀ x (v + v') w =
      deltaGammaAt gt t₀ x v w + deltaGammaAt gt t₀ x v' w := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  have hfun :
      (fun t ↦ (gt t).leviCivita (extend E w) x (v + v')) =
        fun t ↦ (gt t).leviCivita (extend E w) x v +
          (gt t).leviCivita (extend E w) x v' := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_add (hΓ v w) (hΓ v' w)

/-- Homogeneity of `δΓ` in its direction slot. -/
theorem deltaGammaAt_smul_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (c : ℝ) (v w : TM x) :
    deltaGammaAt gt t₀ x (c • v) w = c • deltaGammaAt gt t₀ x v w := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  have hfun :
      (fun t ↦ (gt t).leviCivita (extend E w) x (c • v)) =
        fun t ↦ c • (gt t).leviCivita (extend E w) x v := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_const_smul c (hΓ v w)

/-- Additivity of `δΓ` in its differentiated-section slot. -/
theorem deltaGammaAt_add_right
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (v w w' : TM x) :
    deltaGammaAt gt t₀ x v (w + w') =
      deltaGammaAt gt t₀ x v w + deltaGammaAt gt t₀ x v w' := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  have hfun :
      (fun t ↦ (gt t).leviCivita (extend E (w + w')) x v) =
        fun t ↦ (gt t).leviCivita (extend E w) x v +
          (gt t).leviCivita (extend E w') x v := by
    funext t
    rw [extend_tangent_add (x := x) w w']
    have hadd := (gt t).leviCivita.isCovariantDerivativeOnUniv.add
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E w))
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E w'))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hadd
  rw [hfun]
  exact deriv_fun_add (hΓ v w) (hΓ v w')

/-- Homogeneity of `δΓ` in its differentiated-section slot. -/
theorem deltaGammaAt_smul_right
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (c : ℝ) (v w : TM x) :
    deltaGammaAt gt t₀ x v (c • w) = c • deltaGammaAt gt t₀ x v w := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  have hfun :
      (fun t ↦ (gt t).leviCivita (extend E (c • w)) x v) =
        fun t ↦ c • (gt t).leviCivita (extend E w) x v := by
    funext t
    rw [extend_tangent_smul (x := x) c w]
    have hsmul := (gt t).leviCivita.isCovariantDerivativeOnUniv.smul_const c
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E w))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hsmul
  rw [hfun]
  exact deriv_fun_const_smul c (hΓ v w)

/-- Time-constant families have differentiable connection values. -/
theorem connectionValueTimeDifferentiableAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    ConnectionValueTimeDifferentiableAt (fun _ : ℝ ↦ g) t₀ x :=
  fun v w ↦ differentiableAt_const
    (c := g.leviCivita (extend E w) x v)

/-- The connection variation of a time-constant family vanishes. -/
@[simp] theorem deltaGammaAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v w : TM x) :
    deltaGammaAt (fun _ : ℝ ↦ g) t₀ x v w = 0 := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  rw [deriv_const]

/--
The Ricci tensor is the basis trace of the curvature operator in the first
curvature slot, written in the same explicit contraction form as the model
`coordRicci`.
-/
theorem ricciAt_eq_curvature_contraction
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    g.ricciAt x u w =
      letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (Module.finBasis ℝ (TM x)).coord i
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E ((Module.finBasis ℝ (TM x)) i)) (extend E u)
          (extend E w) x) := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  change g.ricciAt x u w =
    ∑ i, b.coord i
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (b i)) (extend E u) (extend E w) x)
  unfold ClosedSmoothRiemannianMetric.ricciAt
    CovariantDerivative.ricciBilinearAt CovariantDerivative.ricciTraceAt
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change b.coord i
      (CovariantDerivative.curvatureEndAt g.leviCivita
        (CovariantDerivative.derivRegularAt_extend g.leviCivita w) u (b i)) =
    b.coord i
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (b i)) (extend E u) (extend E w) x)
  rw [CovariantDerivative.curvatureEndAt_apply]
  congr 1

/--
Covariant derivative of the connection variation, viewed as a `(1,2)` tensor
and evaluated on canonical extensions of the two tensor slots.
-/
noncomputable def covDeltaGammaDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (a u w : TM x) : TM x :=
  let T : ∀ y : M, TM y :=
    fun y ↦ deltaGammaAt gt t₀ y (extend E u y) (extend E w y)
  (gt t₀).leviCivita T x a
    - deltaGammaAt gt t₀ x ((gt t₀).leviCivita (extend E u) x a) w
    - deltaGammaAt gt t₀ x u ((gt t₀).leviCivita (extend E w) x a)

/--
The curvature variation predicted by the tensorial `δΓ` formula:
`δRm(a,u)w = (∇_a δΓ)(u,w) - (∇_u δΓ)(a,w)`.
-/
noncomputable def curvatureVariationByDeltaGammaAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (a u w : TM x) : TM x :=
  covDeltaGammaDerivAt gt t₀ x a u w
    - covDeltaGammaDerivAt gt t₀ x u a w

/--
The derivative field of the inner connection value
`y ↦ ∂ₜ (∇^t_{extend u} extend w)_y`, written in terms of `δΓ`.
-/
noncomputable def deltaGammaFieldAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    {x : M} (u w : TM x) : ∀ y : M, TM y :=
  fun y ↦ deltaGammaAt gt t₀ y (extend E u y) (extend E w y)

/--
First-order spatial regularity for the vector-valued `δΓ` field in canonical
extension slots.

This is the analytic input needed for the scalar entry product rule: the
field `y ↦ δΓ_y(extend p, extend w)` must be a differentiable tangent section
at the base point.
-/
def DeltaGammaFieldMDifferentiableAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ p w : TM x,
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
      (T% (deltaGammaFieldAt gt t₀ p w)) x

/-- Static metric flows have a zero `δΓ` field, hence satisfy the field regularity class. -/
theorem deltaGammaFieldMDifferentiableAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    DeltaGammaFieldMDifferentiableAt (fun _ : ℝ ↦ g) t₀ x := by
  intro p w
  have hzero :
      deltaGammaFieldAt (fun _ : ℝ ↦ g) t₀ p w =
        fun y : M ↦ (0 : TM y) := by
    funext y
    simp [deltaGammaFieldAt]
  rw [hzero]
  simpa using
    (Bundle.mdifferentiableAt_zeroSection ℝ
      (TangentSpace I : M → Type _) (x := x))

/--
The expected time derivative of an iterated connection value
`∇^t_a (∇^t_u w)` at `t₀`.

The first term is the spatial covariant derivative of the connection
variation; the second is the outer connection's own time variation applied to
the `t₀` inner connection value.
-/
noncomputable def iteratedConnectionDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (a u w : TM x) : TM x :=
  (gt t₀).leviCivita (deltaGammaFieldAt gt t₀ u w) x a
    + deltaGammaAt gt t₀ x a ((gt t₀).leviCivita (extend E w) x u)

/-- Time-dependent metric regularity needed to differentiate closed curvature. -/
structure MetricFlowRegularAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop where
  /-- Pointwise connection values are time differentiable at every base point. -/
  connection :
    ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y
  /--
  The iterated connection values appearing in the closed curvature definition
  are time differentiable.
  -/
  iteratedConnection_timeDifferentiable :
    ∀ a u w : TM x, DifferentiableAt ℝ
      (fun t ↦ (gt t).leviCivita
        (fun y ↦ (gt t).leviCivita (extend E w) y (extend E u y)) x a) t₀
  /--
  Schwarz/mixed-partial obligation: the derivative of
  `t ↦ ∇^t_a(∇^t_u w)` is the covariant spatial derivative of `δΓ(u,w)`,
  plus the outer `δΓ` correction.
  -/
  iteratedConnection_deriv_eq :
    ∀ a u w : TM x,
      deriv
        (fun t ↦ (gt t).leviCivita
          (fun y ↦ (gt t).leviCivita (extend E w) y (extend E u y)) x a) t₀ =
        iteratedConnectionDerivAt gt t₀ x a u w

private theorem leviCivita_zero_section
    (g : ClosedSmoothRiemannianMetric n M) :
    g.leviCivita (0 : ∀ y : M, TM y) = 0 := by
  ext y v
  have hzero :
      g.leviCivita (0 : ∀ y : M, TM y) y = 0 :=
    g.leviCivita.isCovariantDerivativeOnUniv.zero
  exact congrArg (fun L : TM y →L[ℝ] TM y ↦ L v) hzero

@[simp] theorem covDeltaGammaDerivAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (a u w : TM x) :
    covDeltaGammaDerivAt (fun _ : ℝ ↦ g) t₀ x a u w = 0 := by
  unfold covDeltaGammaDerivAt
  have hzero :
      (fun y : M ↦ deltaGammaAt (fun _ : ℝ ↦ g) t₀ y
        (extend E u y) (extend E w y)) = (0 : ∀ y : M, TM y) := by
    funext y
    simp
  change (g.leviCivita
      (fun y : M ↦ deltaGammaAt (fun _ : ℝ ↦ g) t₀ y
        (extend E u y) (extend E w y)) x) a
      - deltaGammaAt (fun _ : ℝ ↦ g) t₀ x
        (g.leviCivita (extend E u) x a) w
      - deltaGammaAt (fun _ : ℝ ↦ g) t₀ x u
        (g.leviCivita (extend E w) x a) = 0
  rw [hzero, leviCivita_zero_section]
  simp

theorem metricFlowRegularAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    MetricFlowRegularAt (fun _ : ℝ ↦ g) t₀ x where
  connection := fun y ↦ connectionValueTimeDifferentiableAt_const g t₀ y
  iteratedConnection_timeDifferentiable := by
    intro a u w
    exact differentiableAt_const
      (c := g.leviCivita
        (fun y ↦ g.leviCivita (extend E w) y (extend E u y)) x a)
      (x := t₀)
  iteratedConnection_deriv_eq := by
    intro a u w
    letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
    change deriv
        (fun _ : ℝ ↦
          g.leviCivita
            (fun y ↦ g.leviCivita (extend E w) y (extend E u y)) x a) t₀ =
        iteratedConnectionDerivAt (fun _ : ℝ ↦ g) t₀ x a u w
    trans 0
    · exact (hasDerivAt_const t₀
        (g.leviCivita
          (fun y ↦ g.leviCivita (extend E w) y (extend E u y)) x a)).deriv
    unfold iteratedConnectionDerivAt deltaGammaFieldAt
    have hzero :
        (fun y : M ↦ deltaGammaAt (fun _ : ℝ ↦ g) t₀ y
          (extend E u y) (extend E w y)) = (0 : ∀ y : M, TM y) := by
      funext y
      simp
    rw [hzero, leviCivita_zero_section]
    simp

theorem MetricFlowRegularAt.iteratedConnection_hasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hreg : MetricFlowRegularAt gt t₀ x) (a u w : TM x) :
    HasDerivAt
      (fun t ↦ (gt t).leviCivita
        (fun y ↦ (gt t).leviCivita (extend E w) y (extend E u y)) x a)
      (iteratedConnectionDerivAt gt t₀ x a u w) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  have h := (hreg.iteratedConnection_timeDifferentiable a u w).hasDerivAt
  rwa [hreg.iteratedConnection_deriv_eq a u w] at h

theorem MetricFlowRegularAt.bracketConnection_hasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hreg : MetricFlowRegularAt gt t₀ x) (a u w : TM x) :
    HasDerivAt
      (fun t ↦ (gt t).leviCivita (extend E w) x
        (VectorField.mlieBracket I (extend E a) (extend E u) x))
      (deltaGammaAt gt t₀ x
        (VectorField.mlieBracket I (extend E a) (extend E u) x) w) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  have h :=
    (hreg.connection x
      (VectorField.mlieBracket I (extend E a) (extend E u) x) w).hasDerivAt
  simpa [deltaGammaAt] using h

theorem deltaGammaAt_sub_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (v v' w : TM x) :
    deltaGammaAt gt t₀ x (v - v') w =
      deltaGammaAt gt t₀ x v w - deltaGammaAt gt t₀ x v' w := by
  rw [sub_eq_add_neg, deltaGammaAt_add_left hΓ v (-v') w]
  have hneg :
      deltaGammaAt gt t₀ x (-v') w = -deltaGammaAt gt t₀ x v' w := by
    simpa using deltaGammaAt_smul_left (gt := gt) (t₀ := t₀) (x := x)
      hΓ (-1 : ℝ) v' w
  rw [hneg]
  abel

theorem deltaGammaAt_mlieBracket_eq_sub
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (a u w : TM x) :
    deltaGammaAt gt t₀ x
        (VectorField.mlieBracket I (extend E a) (extend E u) x) w =
      deltaGammaAt gt t₀ x ((gt t₀).leviCivita (extend E u) x a) w
        - deltaGammaAt gt t₀ x ((gt t₀).leviCivita (extend E a) x u) w := by
  have hbr :
      (gt t₀).leviCivita (extend E u) x a
          - (gt t₀).leviCivita (extend E a) x u =
        VectorField.mlieBracket I (extend E a) (extend E u) x := by
    have htf := (gt t₀).leviCivita_torsionFreeAt x
      (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E a))
      (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E u))
    rwa [extend_apply_self, extend_apply_self] at htf
  rw [← hbr]
  exact deltaGammaAt_sub_left (gt := gt) (t₀ := t₀) (x := x) hΓ
    ((gt t₀).leviCivita (extend E u) x a)
    ((gt t₀).leviCivita (extend E a) x u) w

theorem curvatureVariationByDeltaGammaAt_eq_iteratedConnectionDeriv_sub
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (a u w : TM x) :
    iteratedConnectionDerivAt gt t₀ x a u w
      - iteratedConnectionDerivAt gt t₀ x u a w
      - deltaGammaAt gt t₀ x
        (VectorField.mlieBracket I (extend E a) (extend E u) x) w =
      curvatureVariationByDeltaGammaAt gt t₀ x a u w := by
  rw [deltaGammaAt_mlieBracket_eq_sub (gt := gt) (t₀ := t₀) (x := x)
    hΓ a u w]
  unfold iteratedConnectionDerivAt curvatureVariationByDeltaGammaAt
    covDeltaGammaDerivAt deltaGammaFieldAt
  module

theorem curvatureVariation_hasDerivAt_of_metricFlowRegularAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hreg : MetricFlowRegularAt gt t₀ x) (a u w : TM x) :
    HasDerivAt
      (fun t ↦ CovariantDerivative.curvatureOp (gt t).leviCivita
        (extend E a) (extend E u) (extend E w) x)
      (curvatureVariationByDeltaGammaAt gt t₀ x a u w) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  have hA := hreg.iteratedConnection_hasDerivAt a u w
  have hB := hreg.iteratedConnection_hasDerivAt u a w
  have hC := hreg.bracketConnection_hasDerivAt a u w
  have hraw :
      HasDerivAt
        (fun t ↦
          (gt t).leviCivita
              (fun y ↦ (gt t).leviCivita (extend E w) y
                (extend E u y)) x a
            - (gt t).leviCivita
              (fun y ↦ (gt t).leviCivita (extend E w) y
                (extend E a y)) x u
            - (gt t).leviCivita (extend E w) x
              (VectorField.mlieBracket I (extend E a) (extend E u) x))
        (iteratedConnectionDerivAt gt t₀ x a u w
          - iteratedConnectionDerivAt gt t₀ x u a w
          - deltaGammaAt gt t₀ x
            (VectorField.mlieBracket I (extend E a) (extend E u) x) w)
        t₀ := by
    simpa using (hA.sub hB).sub hC
  have hraw' :
      HasDerivAt
        (fun t ↦
          (gt t).leviCivita
              (fun y ↦ (gt t).leviCivita (extend E w) y
                (extend E u y)) x a
            - (gt t).leviCivita
              (fun y ↦ (gt t).leviCivita (extend E w) y
                (extend E a y)) x u
            - (gt t).leviCivita (extend E w) x
              (VectorField.mlieBracket I (extend E a) (extend E u) x))
        (curvatureVariationByDeltaGammaAt gt t₀ x a u w) t₀ := by
    simpa [curvatureVariationByDeltaGammaAt_eq_iteratedConnectionDeriv_sub
      (gt := gt) (t₀ := t₀) (x := x) (hreg.connection x) a u w] using hraw
  have hpath :
      (fun t ↦ CovariantDerivative.curvatureOp (gt t).leviCivita
        (extend E a) (extend E u) (extend E w) x) =
        fun t ↦
          (gt t).leviCivita
              (fun y ↦ (gt t).leviCivita (extend E w) y
                (extend E u y)) x a
            - (gt t).leviCivita
              (fun y ↦ (gt t).leviCivita (extend E w) y
                (extend E a y)) x u
            - (gt t).leviCivita (extend E w) x
              (VectorField.mlieBracket I (extend E a) (extend E u) x) := by
    funext t
    rw [CovariantDerivative.curvatureOp_apply]
    rw [extend_apply_self, extend_apply_self]
  rw [hpath]
  exact hraw'

/-- The divergence contraction `Σᵢ eⁱ((∇_{eᵢ} δΓ)(u,w))`. -/
noncomputable def deltaGammaDivergenceAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, (Module.finBasis ℝ (TM x)).coord i
    (covDeltaGammaDerivAt gt t₀ x ((Module.finBasis ℝ (TM x)) i) u w)

/-- The trace-derivative contraction `Σᵢ eⁱ((∇_u δΓ)(eᵢ,w))`. -/
noncomputable def deltaGammaContractionDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, (Module.finBasis ℝ (TM x)).coord i
    (covDeltaGammaDerivAt gt t₀ x u ((Module.finBasis ℝ (TM x)) i) w)

@[simp] theorem deltaGammaDivergenceAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u w : TM x) :
    deltaGammaDivergenceAt (fun _ : ℝ ↦ g) t₀ x u w = 0 := by
  unfold deltaGammaDivergenceAt
  simp

@[simp] theorem deltaGammaContractionDerivAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u w : TM x) :
    deltaGammaContractionDerivAt (fun _ : ℝ ↦ g) t₀ x u w = 0 := by
  unfold deltaGammaContractionDerivAt
  simp

/-- The Ricci variation candidate obtained by contracting covariant `δΓ`. -/
noncomputable def deltaRicciAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u w : TM x) : ℝ :=
  deltaGammaDivergenceAt gt t₀ x u w
    - deltaGammaContractionDerivAt gt t₀ x u w

/-- `deltaRicciAt` as the basis trace of the predicted curvature variation. -/
theorem deltaRicciAt_eq_curvatureVariation_contraction
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u w : TM x) :
    deltaRicciAt gt t₀ x u w =
      letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (Module.finBasis ℝ (TM x)).coord i
        (curvatureVariationByDeltaGammaAt gt t₀ x
          ((Module.finBasis ℝ (TM x)) i) u w) := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  change deltaRicciAt gt t₀ x u w =
    ∑ i, b.coord i
      (curvatureVariationByDeltaGammaAt gt t₀ x (b i) u w)
  unfold deltaRicciAt deltaGammaDivergenceAt deltaGammaContractionDerivAt
    curvatureVariationByDeltaGammaAt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sub]

/--
Trace-through-time form of the Ricci variation formula.  The hypothesis is the
remaining curvature-variation bridge: the time derivative of the curvature
operator is the antisymmetrized covariant derivative of `deltaGammaAt`.
-/
theorem ricciVariation_eq_deltaGamma_contractions
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (u w : TM x)
    (hCurv : ∀ a : TM x,
      HasDerivAt
        (fun t ↦ CovariantDerivative.curvatureOp (gt t).leviCivita
          (extend E a) (extend E u) (extend E w) x)
        (curvatureVariationByDeltaGammaAt gt t₀ x a u w) t₀) :
    HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
      (deltaRicciAt gt t₀ x u w) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  have hpath :
      (fun t ↦ (gt t).ricciAt x u w) =
        fun t ↦ ∑ i, b.coord i
          (CovariantDerivative.curvatureOp (gt t).leviCivita
            (extend E (b i)) (extend E u) (extend E w) x) := by
    funext t
    simpa [b] using
      (ricciAt_eq_curvature_contraction (g := gt t) x u w)
  have hdelta :
      deltaRicciAt gt t₀ x u w =
        ∑ i, b.coord i
          (curvatureVariationByDeltaGammaAt gt t₀ x (b i) u w) := by
    simpa [b] using
      (deltaRicciAt_eq_curvatureVariation_contraction gt t₀ x u w)
  rw [hpath, hdelta]
  apply HasDerivAt.fun_sum
  intro i _
  exact (LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp_hasDerivAt
    t₀ (hCurv (b i))

theorem ricciVariation_eq_deltaGamma_contractions'
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x) (u w : TM x) :
    HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
      (deltaRicciAt gt t₀ x u w) t₀ :=
  ricciVariation_eq_deltaGamma_contractions (gt := gt) (t₀ := t₀) (x := x)
    u w (fun a ↦ curvatureVariation_hasDerivAt_of_metricFlowRegularAt hreg a u w)

theorem deriv_scalarAt_eq_trace_deltaRicciAt_of_metricFlowRegularAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀) :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      let hRic : ∀ u w : TM x,
          HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
            (deltaRicciAt gt t₀ x u w) t₀ :=
        fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
      LinearMap.trace ℝ (TM x)
        (((raise'.comp ((gt t₀).ricciDualContinuousAt x) +
            ((gt t₀).metricRaiseContinuousAt x).comp
              (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                (gt := gt) (t₀ := t₀) (x := x)
                (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x) := by
  let hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciAt gt t₀ x u w) t₀ :=
    fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
  have hA :=
    ClosedSmoothRiemannianMetric.ricciEndoHasDerivAt_of_ricciBilinearHasDerivAt
      (gt := gt) (t₀ := t₀) (x := x)
      (δRic := deltaRicciAt gt t₀ x) (raise' := raise')
      hRaise hRic
  simpa [hRic] using
    (ClosedSmoothRiemannianMetric.deriv_scalarAt_eq_trace_of_ricciEndoHasDerivAt
      (gt := gt) (t₀ := t₀) (x := x) hA)

/-- Raise a cotangent vector with the metric at a fixed point. -/
noncomputable def metricDualVectorAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (φ : Module.Dual ℝ (TM x)) : TM x :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  (LinearMap.BilinForm.toDual (g.metricBilinAt x)
    (g.metricBilinAt_nondegenerate x)).symm φ

/--
The metric trace of a raw metric variation `h`: `tr_g h`.

This is the closed-manifold analogue of the model `tensorMetricTrace`, written
with the tangent-space basis and metric-dual raised basis covectors.
-/
noncomputable def traceMetricVariationAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, h x ((Module.finBasis ℝ (TM x)) i)
    (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))

theorem traceMetricVariationAt_add
    (g : ClosedSmoothRiemannianMetric n M)
    (h k : ∀ y : M, TM y → TM y → ℝ) (x : M) :
    traceMetricVariationAt g (fun y v w ↦ h y v w + k y v w) x =
      traceMetricVariationAt g h x + traceMetricVariationAt g k x := by
  unfold traceMetricVariationAt
  rw [Finset.sum_add_distrib]

theorem traceMetricVariationAt_smul
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (c : ℝ) (x : M) :
    traceMetricVariationAt g (fun y v w ↦ c * h y v w) x =
      c * traceMetricVariationAt g h x := by
  unfold traceMetricVariationAt
  rw [Finset.mul_sum]

@[simp] theorem traceMetricVariationAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    traceMetricVariationAt g (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x = 0 := by
  unfold traceMetricVariationAt
  simp

/--
The metric pairing `⟨h, Ric⟩_g = h^{ij} Ric_{ij}` for a raw metric variation.

Both slots of `h` are raised by `g`, then paired with the Ricci tensor in the
chosen finite-dimensional tangent basis.
-/
noncomputable def metricVariationRicciPairingAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ j, ∑ i,
    h x
      (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord j))
      (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) *
        g.ricciAt x ((Module.finBasis ℝ (TM x)) i)
          ((Module.finBasis ℝ (TM x)) j)

theorem metricVariationRicciPairingAt_add
    (g : ClosedSmoothRiemannianMetric n M)
    (h k : ∀ y : M, TM y → TM y → ℝ) (x : M) :
    metricVariationRicciPairingAt g (fun y v w ↦ h y v w + k y v w) x =
      metricVariationRicciPairingAt g h x +
        metricVariationRicciPairingAt g k x := by
  unfold metricVariationRicciPairingAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem metricVariationRicciPairingAt_smul
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (c : ℝ) (x : M) :
    metricVariationRicciPairingAt g (fun y v w ↦ c * h y v w) x =
      c * metricVariationRicciPairingAt g h x := by
  unfold metricVariationRicciPairingAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

@[simp] theorem metricVariationRicciPairingAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    metricVariationRicciPairingAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x = 0 := by
  unfold metricVariationRicciPairingAt
  simp

/-- Lowering the raised algebraic covector recovers the covector. -/
theorem metricDualVectorAt_inner_apply
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (φ : Module.Dual ℝ (TM x)) (v : TM x) :
    (g.inner x (metricDualVectorAt g x φ)) v = φ v := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  change g.metricBilinAt x (metricDualVectorAt g x φ) v = φ v
  unfold metricDualVectorAt
  exact LinearMap.BilinForm.apply_toDual_symm_apply
    (B := g.metricBilinAt x) (hB := g.metricBilinAt_nondegenerate x) φ v

/-- The algebraic raised dual vector is the continuous metric-raise map applied
to the same covector. -/
theorem metricDualVectorAt_eq_metricRaiseContinuousAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (φ : TM x →L[ℝ] ℝ) :
    metricDualVectorAt g x (φ : Module.Dual ℝ (TM x)) =
      g.metricRaiseContinuousAt x φ := by
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  refine sub_eq_zero.mp (LeviCivitaExistence.metric_nondegenerate g x
    (metricDualVectorAt g x (φ : Module.Dual ℝ (TM x)) -
      g.metricRaiseContinuousAt x φ) ?_)
  intro v
  rw [map_sub]
  simp only [ContinuousLinearMap.sub_apply]
  rw [metricDualVectorAt_inner_apply g x (φ : Module.Dual ℝ (TM x)) v,
    ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  simp

omit [T2Space M] [IsManifold I ∞ M] in
/--
Finite-dimensional reconstruction for manifold-domain CLM fields.

This is the closed-manifold analogue of the model-space
`differentiableAt_clm_of_apply`: differentiability after applying every fixed
model vector determines differentiability of the CLM-valued field.
-/
theorem mdifferentiableAt_clm_of_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : M → E →L[ℝ] F} {x : M}
    (h : ∀ w : E, MDifferentiableAt I 𝓘(ℝ, F) (fun y : M ↦ Φ y w) x) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] F) Φ x := by
  let bE := Module.finBasis ℝ E
  let coordC : Fin (Module.finrank ℝ E) → (E →L[ℝ] ℝ) :=
    fun i ↦ LinearMap.toContinuousLinearMap (bE.coord i)
  have hrepr : ∀ ρ : E →L[ℝ] F,
      ρ = ∑ i, (coordC i).smulRight (ρ (bE i)) := by
    intro ρ
    ext w
    have hw := bE.sum_repr w
    conv_lhs => rw [← hw]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, map_smul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show coordC i w = bE.coord i w from rfl, Module.Basis.coord_apply]
  have hfun : Φ = fun y : M ↦ ∑ i, (coordC i).smulRight (Φ y (bE i)) := by
    funext y
    exact hrepr (Φ y)
  rw [hfun]
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] F)
        (fun y : M ↦ (coordC i).smulRight (Φ y (bE i))) x := by
    intro i
    exact (ContinuousLinearMap.smulRightL ℝ E F (coordC i)).differentiableAt
      |>.comp_mdifferentiableAt (h (bE i))
  refine Finset.induction_on (Finset.univ) ?base ?step
  · simpa using (mdifferentiableAt_const (c := (0 : E →L[ℝ] F)) (x := x))
  · intro a s ha ih
    simpa [Finset.sum_insert ha] using (hsummand a).add ih

omit [T2Space M] [IsManifold I ∞ M] in
/--
Dual-valued specialization of `mdifferentiableAt_clm_of_apply`.
-/
theorem mdifferentiableAt_clm_dual_of_apply
    {f : M → E →L[ℝ] ℝ} {x : M}
    (h : ∀ w : E, MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ f y w) x) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ) f x := by
  exact mdifferentiableAt_clm_of_apply (F := ℝ) h

/--
Scalar metric entries are differentiable for canonical extension sections.

This is the verified scalar-entry fact currently available without moving raw
model vectors through the preferred-chart tangent coordinates.
-/
theorem metric_pairing_extend_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M) {x : M} (p q : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ g.inner y (extend E p y) (extend E q y)) x := by
  exact g.metric_pairing_mdiffAt
    (mdifferentiableAt_extend I E p)
    (mdifferentiableAt_extend I E q)

/--
Gram matrix of the metric in the canonical extension frame seeded at `x` and
evaluated at `y`.
-/
noncomputable def gramMatrix
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) :
    Matrix (Fin (Module.finrank ℝ (TM x))) (Fin (Module.finrank ℝ (TM x))) ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  fun i j ↦ g.inner y (extend E (b i) y) (extend E (b j) y)

/-- At the seed point, the canonical-extension Gram matrix is the metric matrix
in the finite basis of `TM x`. -/
theorem gramMatrix_at_base
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    gramMatrix g x x =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E);
      LinearMap.toMatrix₂ (Module.finBasis ℝ (TM x))
        (Module.finBasis ℝ (TM x)) (g.metricBilinAt x)) := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ext i j
  simp [gramMatrix, LinearMap.toMatrix₂_apply, g.metricBilinAt_apply]

/-- The base Gram determinant is nonzero by metric nondegeneracy. -/
theorem gramMatrix_at_base_det_ne_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    (gramMatrix g x x).det ≠ 0 := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  rw [gramMatrix_at_base]
  exact (LinearMap.nondegenerate_iff_det_ne_zero
    (b := Module.finBasis ℝ (TM x))).mp (g.metricBilinAt_nondegenerate x)

/-- The base Gram matrix is a unit. -/
theorem gramMatrix_at_base_isUnit
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    IsUnit (gramMatrix g x x) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (gramMatrix_at_base_det_ne_zero (g := g) (x := x))

/-- Each canonical-extension Gram entry is differentiable at the seed point. -/
theorem gramMatrix_entry_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ gramMatrix g x y i j) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  simpa [gramMatrix, b] using
    (metric_pairing_extend_mdiffAt (g := g) (x := x) (b i) (b j))

omit [T2Space M] [IsManifold I ∞ M] in
/-- Determinants of finite matrix fields are differentiable when all entries are. -/
theorem mdifferentiableAt_matrix_det_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : M → Matrix ι ι ℝ} {x : M}
    (hA : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ A y i j) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ (A y).det) x := by
  classical
  rw [show (fun y : M ↦ (A y).det) =
      fun y : M ↦ ∑ σ : Equiv.Perm ι,
        ((↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A y (σ i) i) by
    funext y
    rw [Matrix.det_apply']]
  have hsum : MDifferentiableAt I 𝓘(ℝ)
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
        fun y : M ↦ (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A y (σ i) i) x := by
    refine MDifferentiableAt.sum (t := (Finset.univ : Finset (Equiv.Perm ι))) ?_
    intro σ _hσ
    have hprod : MDifferentiableAt I 𝓘(ℝ)
        (∏ i ∈ (Finset.univ : Finset ι), fun y : M ↦ A y (σ i) i) x := by
      refine MDifferentiableAt.prod (t := (Finset.univ : Finset ι)) ?_
      intro i _hi
      exact hA (σ i) i
    have hprod' : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ ∏ i, A y (σ i) i) x :=
      hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by simp)
    have hconst : MDifferentiableAt I 𝓘(ℝ)
        (fun _ : M ↦ (↑↑(Equiv.Perm.sign σ) : ℝ)) x := mdifferentiableAt_const
    simpa using hconst.mul hprod'
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by simp)

/-- The canonical-extension Gram determinant is differentiable at the seed point. -/
theorem gramMatrix_det_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ (gramMatrix g x y).det) x := by
  exact mdifferentiableAt_matrix_det_of_entries
    (A := fun y : M ↦ gramMatrix g x y)
    (fun i j ↦ gramMatrix_entry_mdiffAt (g := g) x i j)

/-- The canonical-extension Gram matrix is invertible eventually near the seed point. -/
theorem gramMatrix_eventually_isUnit
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∀ᶠ y in nhds x, IsUnit (gramMatrix g x y) := by
  have hdetCont :
      ContinuousAt (fun y : M ↦ (gramMatrix g x y).det) x :=
    (gramMatrix_det_mdiffAt (g := g) x).continuousAt
  have hdet_ne :
      (fun y : M ↦ (gramMatrix g x y).det) x ≠ 0 :=
    gramMatrix_at_base_det_ne_zero (g := g) (x := x)
  exact (hdetCont.eventually_ne hdet_ne).mono fun y hy ↦ by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hy

/-- Adjugate entries of the canonical-extension Gram matrix are differentiable
at the seed point. -/
theorem gramMatrix_adjugate_entry_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ (gramMatrix g x y).adjugate i j) x := by
  let row : Fin (Module.finrank ℝ (TM x)) → ℝ := Pi.single i (1 : ℝ)
  let A : M → Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
    fun y : M ↦ (gramMatrix g x y).updateRow j row
  have hentries : ∀ a b,
      MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ A y a b) x := by
    intro a b
    by_cases ha : a = j
    · subst a
      simpa [A, Matrix.updateRow] using
        (mdifferentiableAt_const (c := row b) (x := x))
    · simpa [A, Matrix.updateRow, ha] using
        (gramMatrix_entry_mdiffAt (g := g) x a b)
  have hdet : MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ (A y).det) x :=
    mdifferentiableAt_matrix_det_of_entries (A := A) hentries
  exact hdet.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
    simp [A, row, Matrix.adjugate_apply])

/-- Inverse Gram entries are differentiable at the seed point. -/
theorem gramMatrix_inv_entry_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x := by
  have hdetInv : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ ((gramMatrix g x y).det)⁻¹) x :=
    (gramMatrix_det_mdiffAt (g := g) x).inv
      (gramMatrix_at_base_det_ne_zero (g := g) (x := x))
  have hadj : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ (gramMatrix g x y).adjugate i j) x :=
    gramMatrix_adjugate_entry_mdiffAt (g := g) x i j
  exact (hdetInv.mul hadj).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ by simp [Matrix.inv_def])

omit [T2Space M] in
/-- The canonical extension frame seeded at `x` and evaluated in the fiber over `y`. -/
noncomputable def gramFrame (x y : M) :
    Fin (Module.finrank ℝ (TM x)) → TM y :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  fun i ↦ extend E ((Module.finBasis ℝ (TM x)) i) y

omit [T2Space M] in
/-- If its Gram matrix is invertible, the canonical extension frame is linearly independent. -/
theorem gramFrame_linearIndependent_of_isUnit
    (g : ClosedSmoothRiemannianMetric n M) {x y : M}
    (hG : IsUnit (gramMatrix g x y)) :
    LinearIndependent ℝ (gramFrame (n := n) (M := M) x y) := by
  classical
  letI : NormedAddCommGroup (TM y) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM y) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let e : Fin (Module.finrank ℝ (TM x)) → TM y := fun i ↦ extend E (b i) y
  change LinearIndependent ℝ e
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc i
  have hvec : Matrix.vecMul c (gramMatrix g x y) = 0 := by
    ext j
    let φ : TM y →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (e j)).comp (g.inner y)
    have hφ := congrArg φ hc
    change φ (∑ i, c i • e i) = φ 0 at hφ
    simp [φ, e, b, smul_eq_mul] at hφ
    simpa [Matrix.vecMul, dotProduct] using hφ
  have hinj : Function.Injective (fun v ↦ Matrix.vecMul v (gramMatrix g x y)) :=
    Matrix.vecMul_injective_iff_isUnit.mpr hG
  have hc0 : c = 0 := hinj (by simpa using hvec)
  simpa using congrFun hc0 i

/-- The canonical extension frame as a basis whenever its Gram matrix is invertible. -/
noncomputable def gramFrameBasis
    (g : ClosedSmoothRiemannianMetric n M) (x y : M)
    (hG : IsUnit (gramMatrix g x y)) :
    Module.Basis (Fin (Module.finrank ℝ (TM x))) ℝ (TM y) :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  basisOfLinearIndependentOfCardEqFinrank'
    (gramFrame (n := n) (M := M) x y)
    (gramFrame_linearIndependent_of_isUnit (g := g) hG)
    (by
      rw [show Module.finrank ℝ (TM x) = Module.finrank ℝ E from rfl,
        show Module.finrank ℝ (TM y) = Module.finrank ℝ E from rfl]
      simp)

omit [T2Space M] in
@[simp] theorem gramFrameBasis_apply
    (g : ClosedSmoothRiemannianMetric n M) (x y : M)
    (hG : IsUnit (gramMatrix g x y))
    (i : Fin (Module.finrank ℝ (TM x))) :
    gramFrameBasis (n := n) (M := M) g x y hG i =
      gramFrame (n := n) (M := M) x y i := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold gramFrameBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']

/--
The metric-raised dual coframe of the canonical Gram frame is obtained by the
rows of the inverse Gram matrix.
-/
theorem metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv
    (g : ClosedSmoothRiemannianMetric n M) {x y : M}
    (hG : IsUnit (gramMatrix g x y))
    (i : Fin (Module.finrank ℝ (TM x))) :
    metricDualVectorAt g y ((gramFrameBasis g x y hG).coord i) =
      ∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j := by
  classical
  letI : NormedAddCommGroup (TM y) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM y) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let B := gramFrameBasis g x y hG
  let G := gramMatrix g x y
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  apply (LinearMap.BilinForm.toDual (g.metricBilinAt y)
    (g.metricBilinAt_nondegenerate y)).injective
  apply B.ext
  intro k
  have hmatrix : ∑ j, G⁻¹ i j * G j k = if i = k then 1 else 0 := by
    have hmul := congrArg (fun A : Matrix (Fin (Module.finrank ℝ (TM x)))
        (Fin (Module.finrank ℝ (TM x))) ℝ ↦ A i k)
      (Matrix.nonsing_inv_mul G hdet)
    simpa [Matrix.mul_apply, G] using hmul
  calc
    ((LinearMap.BilinForm.toDual (g.metricBilinAt y)
        (g.metricBilinAt_nondegenerate y))
        (metricDualVectorAt g y (B.coord i))) (B k)
        = B.coord i (B k) := by
          simp [metricDualVectorAt, B]
    _ = if i = k then 1 else 0 := by
          rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
          by_cases hik : i = k <;> simp [hik, eq_comm]
    _ = ∑ j, G⁻¹ i j * G j k := hmatrix.symm
    _ = ((LinearMap.BilinForm.toDual (g.metricBilinAt y)
        (g.metricBilinAt_nondegenerate y))
        (∑ j, G⁻¹ i j • gramFrame x y j)) (B k) := by
          simp [LinearMap.BilinForm.toDual_def,
            ClosedSmoothRiemannianMetric.metricBilinAt_apply,
            G, B, gramMatrix, gramFrame, smul_eq_mul]

/-- At the seed point, inverse Gram rows expand the raised dual finite basis. -/
theorem metricDualVectorAt_finBasis_coord_eq_sum_gram_inv
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (i : Fin (Module.finrank ℝ (TM x))) :
    metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i) =
      ∑ j, (gramMatrix g x x)⁻¹ i j • (Module.finBasis ℝ (TM x)) j := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let G := gramMatrix g x x
  have hdet : IsUnit G.det := by
    simpa [G] using
      (Matrix.isUnit_iff_isUnit_det (gramMatrix g x x)).mp
        (gramMatrix_at_base_isUnit (g := g) (x := x))
  apply (LinearMap.BilinForm.toDual (g.metricBilinAt x)
    (g.metricBilinAt_nondegenerate x)).injective
  apply b.ext
  intro k
  have hmatrix : ∑ j, G⁻¹ i j * G j k = if i = k then 1 else 0 := by
    have hmul := congrArg (fun A : Matrix (Fin (Module.finrank ℝ (TM x)))
        (Fin (Module.finrank ℝ (TM x))) ℝ ↦ A i k)
      (Matrix.nonsing_inv_mul G hdet)
    simpa [Matrix.mul_apply, G] using hmul
  calc
    ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x))
        (metricDualVectorAt g x (b.coord i))) (b k)
        = b.coord i (b k) := by
          simp [metricDualVectorAt, b]
    _ = if i = k then 1 else 0 := by
          rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
          by_cases hik : i = k <;> simp [hik, eq_comm]
    _ = ∑ j, G⁻¹ i j * G j k := hmatrix.symm
    _ = ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x))
        (∑ j, G⁻¹ i j • b j)) (b k) := by
          simp [LinearMap.BilinForm.toDual_def,
            ClosedSmoothRiemannianMetric.metricBilinAt_apply,
            G, b, gramMatrix, smul_eq_mul]

/--
The metric trace of a fiberwise bilinear form, computed in an arbitrary finite
basis and paired with the `g`-raised dual coframe of that basis.
-/
noncomputable def metricTraceInBasisAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (B : LinearMap.BilinForm ℝ (TM x))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) : ℝ :=
  ∑ i, B (b i) (metricDualVectorAt g x (b.coord i))

/-- The endomorphism obtained by raising one index of a fiberwise bilinear form. -/
noncomputable def metricTraceEndomorphismAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (B : LinearMap.BilinForm ℝ (TM x)) : TM x →ₗ[ℝ] TM x :=
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
      (g.metricBilinAt_nondegenerate x)).symm.toLinearMap) ∘ₗ B

/-- Coordinates in any basis are metric pairings with the raised dual vector. -/
theorem coord_eq_inner_metricDualVectorAt_of_basis
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) (i : ι) (v : TM x) :
    b.coord i v =
      (g.inner x v (metricDualVectorAt g x (b.coord i))) := by
  rw [g.inner_symm x v (metricDualVectorAt g x (b.coord i))]
  exact (metricDualVectorAt_inner_apply g x (b.coord i) v).symm

/--
The raised dual vector of any basis coordinate covector is the continuous
metric-raise map applied to the same coordinate covector.
-/
theorem metricDualVectorAt_basisCoord_eq_metricRaiseContinuousAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [T2Space (TM x)] [FiniteDimensional ℝ (TM x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    metricDualVectorAt g x (b.coord i) =
      g.metricRaiseContinuousAt x (LinearMap.toContinuousLinearMap (b.coord i)) := by
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  simpa using
    (metricDualVectorAt_eq_metricRaiseContinuousAt
      (g := g) (x := x)
      (φ := LinearMap.toContinuousLinearMap (b.coord i)))

/--
The arbitrary-basis metric trace is the trace of the raised endomorphism, hence
is basis-free.
-/
theorem metricTraceInBasisAt_eq_linearMap_trace
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (B : LinearMap.BilinForm ℝ (TM x))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) :
    metricTraceInBasisAt g x B b =
      LinearMap.trace ℝ (TM x) (metricTraceEndomorphismAt g x B) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  unfold metricTraceInBasisAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change B (b i) (metricDualVectorAt g x (b.coord i)) =
    b.coord i ((metricTraceEndomorphismAt g x B) (b i))
  rw [coord_eq_inner_metricDualVectorAt_of_basis (g := g) (x := x) (b := b)]
  unfold metricTraceEndomorphismAt
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  change B (b i) (metricDualVectorAt g x (b.coord i)) =
    g.metricBilinAt x
      ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm (B (b i)))
      (metricDualVectorAt g x (b.coord i))
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]

/-- Computing the same fiberwise metric trace in two finite bases gives the same scalar. -/
theorem metricTraceInBasisAt_eq_metricTraceInBasisAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (B : LinearMap.BilinForm ℝ (TM x))
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ (TM x)) (c : Module.Basis κ ℝ (TM x)) :
    metricTraceInBasisAt g x B b = metricTraceInBasisAt g x B c := by
  rw [metricTraceInBasisAt_eq_linearMap_trace (g := g) (x := x) (B := B) (b := b),
    metricTraceInBasisAt_eq_linearMap_trace (g := g) (x := x) (B := B) (b := c)]

/--
For the canonical finite basis, the arbitrary-basis bilinear trace agrees with
the existing raw-field trace definition.
-/
theorem metricTraceInBasisAt_finBasis_eq_traceMetricVariationAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (B : LinearMap.BilinForm ℝ (TM x))
    (hB : ∀ p q : TM x, B p q = h x p q) :
    metricTraceInBasisAt g x B (Module.finBasis ℝ (TM x)) =
      traceMetricVariationAt g h x := by
  unfold metricTraceInBasisAt traceMetricVariationAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hB]

/--
Basis-invariant bridge from the existing `traceMetricVariationAt` definition to
an arbitrary finite basis, once the fiber value of `h` is packaged as a genuine
bilinear form.
-/
theorem traceMetricVariationAt_eq_metricTraceInBasisAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (B : LinearMap.BilinForm ℝ (TM x))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x))
    (hB : ∀ p q : TM x, B p q = h x p q) :
    traceMetricVariationAt g h x = metricTraceInBasisAt g x B b := by
  calc
    traceMetricVariationAt g h x =
        metricTraceInBasisAt g x B (Module.finBasis ℝ (TM x)) :=
          (metricTraceInBasisAt_finBasis_eq_traceMetricVariationAt
            (g := g) (h := h) (x := x) (B := B) hB).symm
    _ = metricTraceInBasisAt g x B b :=
          metricTraceInBasisAt_eq_metricTraceInBasisAt
            (g := g) (x := x) (B := B)
            (b := Module.finBasis ℝ (TM x)) (c := b)

theorem laplacianAt_eq_sum_hessianAt
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) :
    g.laplacianAt f x =
      (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
        ∑ i, g.hessianAt f x ((Module.finBasis ℝ (TM x)) i)
          (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  have htrace :=
    metricTraceInBasisAt_eq_linearMap_trace
      (g := g) (x := x) (B := g.hessianDualAt f x) (b := b)
  change g.laplacianAt f x =
    ∑ i, g.hessianAt f x (b i) (metricDualVectorAt g x (b.coord i))
  simpa [ClosedSmoothRiemannianMetric.laplacianAt, metricTraceEndomorphismAt,
    metricTraceInBasisAt, b] using htrace.symm

/--
Gram-inverse form of the metric trace in the canonical extension frame.  The
fiber value of `h` is supplied as a bilinear form, matching the existing
basis-invariant trace bridge.
-/
theorem traceMetricVariationAt_eq_sum_gram_inv
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x y : M)
    (hG : IsUnit (gramMatrix g x y))
    (B : LinearMap.BilinForm ℝ (TM y))
    (hB : ∀ p q : TM y, B p q = h y p q) :
    traceMetricVariationAt g h y =
      ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
        h y (gramFrame x y i) (gramFrame x y j) := by
  classical
  letI : NormedAddCommGroup (TM y) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM y) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := gramFrameBasis g x y hG
  calc
    traceMetricVariationAt g h y = metricTraceInBasisAt g y B b := by
      exact traceMetricVariationAt_eq_metricTraceInBasisAt
        (g := g) (h := h) (x := y) (B := B) (b := b) hB
    _ = ∑ i, B (b i) (metricDualVectorAt g y (b.coord i)) := rfl
    _ = ∑ i, B (gramFrame x y i)
        (∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [b, metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv]
    _ = ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
        h y (gramFrame x y i) (gramFrame x y j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        B (gramFrame x y i)
            (∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j) =
            ∑ j, B (gramFrame x y i)
              ((gramMatrix g x y)⁻¹ i j • gramFrame x y j) := by
          rw [map_sum]
        _ = ∑ j, (gramMatrix g x y)⁻¹ i j *
              B (gramFrame x y i) (gramFrame x y j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [smul_eq_mul]
        _ = ∑ j, (gramMatrix g x y)⁻¹ i j *
              h y (gramFrame x y i) (gramFrame x y j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [hB]

/--
Basis-free trace form of `traceMetricVariationAt`: once the fiber value of
`h` is packaged as a bilinear form, the metric trace is the linear trace of the
endomorphism obtained by raising one index.
-/
theorem traceMetricVariationAt_eq_linearMap_trace
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (B : LinearMap.BilinForm ℝ (TM x))
    (hB : ∀ p q : TM x, B p q = h x p q) :
    traceMetricVariationAt g h x =
      LinearMap.trace ℝ (TM x) (metricTraceEndomorphismAt g x B) := by
  rw [traceMetricVariationAt_eq_metricTraceInBasisAt
    (g := g) (h := h) (x := x) (B := B)
    (b := Module.finBasis ℝ (TM x)) hB]
  exact metricTraceInBasisAt_eq_linearMap_trace
    (g := g) (x := x) (B := B) (b := Module.finBasis ℝ (TM x))

/-- Continuous-linear version of `metricTraceEndomorphismAt`. -/
noncomputable def metricTraceEndomorphismContinuousAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (B : LinearMap.BilinForm ℝ (TM x)) : TM x →L[ℝ] TM x :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (metricTraceEndomorphismAt g x B)

@[simp] theorem metricTraceEndomorphismContinuousAt_coe
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (B : LinearMap.BilinForm ℝ (TM x)) :
    (metricTraceEndomorphismContinuousAt g x B : TM x →ₗ[ℝ] TM x) =
      metricTraceEndomorphismAt g x B := by
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  rfl

/-- `traceMetricVariationAt` as trace of the continuous raised endomorphism. -/
theorem traceMetricVariationAt_eq_trace_metricTraceEndomorphismContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (B : LinearMap.BilinForm ℝ (TM x))
    (hB : ∀ p q : TM x, B p q = h x p q) :
    traceMetricVariationAt g h x =
      LinearMap.trace ℝ (TM x)
        (metricTraceEndomorphismContinuousAt g x B : TM x →ₗ[ℝ] TM x) := by
  rw [metricTraceEndomorphismContinuousAt_coe]
  exact traceMetricVariationAt_eq_linearMap_trace
    (g := g) (h := h) (x := x) (B := B) hB

/-- Specialization of the basis-free trace bridge to the metric time derivative. -/
theorem traceMetricVariationAt_timeDeriv_eq_linearMap_trace
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x =
      LinearMap.trace ℝ (TM x)
        (metricTraceEndomorphismAt (gt t₀) x
          (timeDerivBilinAt gt t₀ x hgt)) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact traceMetricVariationAt_eq_linearMap_trace
    (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
    (B := timeDerivBilinAt gt t₀ x hgt)
    (by intro p q; rfl)

/--
The finite-dimensional trace as a continuous linear functional on the fixed
endomorphism space of a closed tangent fiber.
-/
noncomputable def endomorphismTraceContinuousAt (x : M) :
    (TM x →L[ℝ] TM x) →L[ℝ] ℝ :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (TM x)) ∘ₗ
      (ContinuousLinearMap.coeLM ℝ :
        (TM x →L[ℝ] TM x) →ₗ[ℝ] (TM x →ₗ[ℝ] TM x)))

omit [T2Space M] [IsManifold I ∞ M] in
@[simp] theorem endomorphismTraceContinuousAt_apply
    (x : M) (A : TM x →L[ℝ] TM x) :
    endomorphismTraceContinuousAt (n := n) (M := M) x A =
      LinearMap.trace ℝ (TM x) (A : TM x →ₗ[ℝ] TM x) := by
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  rfl

omit [T2Space M] [IsManifold I ∞ M] in
/-- Differentiating a finite-dimensional trace is applying trace to the derivative. -/
theorem hasDerivAt_trace_endomorphismContinuousAt
    {x : M} {A : ℝ → TM x →L[ℝ] TM x} {A' : TM x →L[ℝ] TM x} {t₀ : ℝ}
    (hA : HasDerivAt A A' t₀) :
    HasDerivAt
      (fun t ↦ LinearMap.trace ℝ (TM x) (A t : TM x →ₗ[ℝ] TM x))
      (LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x)) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  simpa using
    ((endomorphismTraceContinuousAt (n := n) (M := M) x).hasFDerivAt.comp_hasDerivAt
      t₀ hA)

/--
The chart frame at a chart target point: transport the fixed model finite basis
through the derivative of the inverse chart.
-/
noncomputable def chartTangentBasisAt
    (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TM ((extChartAt I x₀).symm z)) :=
  let hInv := isInvertible_mfderivWithin_extChartAt_symm (x := x₀) hz
  (Module.finBasis ℝ E).map (Classical.choose hInv).toLinearEquiv

/-- The chart-frame basis vectors are exactly the inverse-chart derivative of the model basis. -/
theorem chartTangentBasisAt_apply
    (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (i : Fin (Module.finrank ℝ E)) :
    chartTangentBasisAt (n := n) (M := M) x₀ hz i =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (Set.range I) z
        ((Module.finBasis ℝ E) i) := by
  let hInv := isInvertible_mfderivWithin_extChartAt_symm (x := x₀) hz
  have hchoose :
      ((Classical.choose hInv :
          E ≃L[ℝ] TM ((extChartAt I x₀).symm z)) : E →L[ℝ]
            TM ((extChartAt I x₀).symm z)) =
        mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (Set.range I) z :=
    Classical.choose_spec hInv
  unfold chartTangentBasisAt
  rw [Module.Basis.map_apply]
  simpa [hInv] using
    congrArg
      (fun L : E →L[ℝ] TM ((extChartAt I x₀).symm z) =>
        L ((Module.finBasis ℝ E) i)) hchoose

/--
Specialization of the basis-invariant trace bridge to the chart frame on the
target of `extChartAt`.
-/
theorem traceMetricVariationAt_eq_chartTangentBasisAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x₀ : M)
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (B : LinearMap.BilinForm ℝ (TM ((extChartAt I x₀).symm z)))
    (hB : ∀ p q : TM ((extChartAt I x₀).symm z),
      B p q = h ((extChartAt I x₀).symm z) p q) :
    traceMetricVariationAt g h ((extChartAt I x₀).symm z) =
      metricTraceInBasisAt g ((extChartAt I x₀).symm z) B
        (chartTangentBasisAt (n := n) (M := M) x₀ hz) := by
  letI : FiniteDimensional ℝ (TM ((extChartAt I x₀).symm z)) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  exact traceMetricVariationAt_eq_metricTraceInBasisAt
    (g := g) (h := h) (x := (extChartAt I x₀).symm z)
    (B := B) (b := chartTangentBasisAt (n := n) (M := M) x₀ hz) hB

/-- The chart-frame specialization unfolded as the finite frame/coframe sum. -/
theorem traceMetricVariationAt_eq_chartTangentBasisAt_sum
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x₀ : M)
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (B : LinearMap.BilinForm ℝ (TM ((extChartAt I x₀).symm z)))
    (hB : ∀ p q : TM ((extChartAt I x₀).symm z),
      B p q = h ((extChartAt I x₀).symm z) p q) :
    traceMetricVariationAt g h ((extChartAt I x₀).symm z) =
      ∑ i, B (chartTangentBasisAt (n := n) (M := M) x₀ hz i)
        (metricDualVectorAt g ((extChartAt I x₀).symm z)
          ((chartTangentBasisAt (n := n) (M := M) x₀ hz).coord i)) := by
  rw [traceMetricVariationAt_eq_chartTangentBasisAt
    (g := g) (h := h) (x₀ := x₀) (hz := hz) (B := B) hB]
  rfl

/-- The chart-frame raised coframe rewritten through the continuous raise map. -/
theorem metricDualVectorAt_chartTangentBasisAt_coord_eq_metricRaiseContinuousAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    [T2Space (TM ((extChartAt I x₀).symm z))]
    [FiniteDimensional ℝ (TM ((extChartAt I x₀).symm z))]
    (i : Fin (Module.finrank ℝ E)) :
    metricDualVectorAt g ((extChartAt I x₀).symm z)
        ((chartTangentBasisAt (n := n) (M := M) x₀ hz).coord i) =
      g.metricRaiseContinuousAt ((extChartAt I x₀).symm z)
        (LinearMap.toContinuousLinearMap
          ((chartTangentBasisAt (n := n) (M := M) x₀ hz).coord i)) := by
  letI : FiniteDimensional ℝ (TM ((extChartAt I x₀).symm z)) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  exact metricDualVectorAt_basisCoord_eq_metricRaiseContinuousAt
    (g := g) (x := (extChartAt I x₀).symm z)
    (b := chartTangentBasisAt (n := n) (M := M) x₀ hz) i

/--
The chart-frame trace sum with the raised dual coframe expressed via
`metricRaiseContinuousAt`.
-/
theorem traceMetricVariationAt_eq_chartTangentBasisAt_continuousRaise_sum
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x₀ : M)
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    [T2Space (TM ((extChartAt I x₀).symm z))]
    [FiniteDimensional ℝ (TM ((extChartAt I x₀).symm z))]
    (B : LinearMap.BilinForm ℝ (TM ((extChartAt I x₀).symm z)))
    (hB : ∀ p q : TM ((extChartAt I x₀).symm z),
      B p q = h ((extChartAt I x₀).symm z) p q) :
    traceMetricVariationAt g h ((extChartAt I x₀).symm z) =
      ∑ i, B (chartTangentBasisAt (n := n) (M := M) x₀ hz i)
        (g.metricRaiseContinuousAt ((extChartAt I x₀).symm z)
          (LinearMap.toContinuousLinearMap
            ((chartTangentBasisAt (n := n) (M := M) x₀ hz).coord i))) := by
  rw [traceMetricVariationAt_eq_chartTangentBasisAt_sum
    (g := g) (h := h) (x₀ := x₀) (hz := hz) (B := B) hB]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [metricDualVectorAt_chartTangentBasisAt_coord_eq_metricRaiseContinuousAt
    (g := g) (x₀ := x₀) (hz := hz) (i := i)]

/-- Coordinates are metric pairings with the corresponding raised dual basis vector. -/
theorem coord_eq_inner_metricDualVectorAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (i : Fin (Module.finrank ℝ (TM x))) (v : TM x) :
    (Module.finBasis ℝ (TM x)).coord i v =
      (g.inner x v
        (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))) := by
  rw [g.inner_symm x v
    (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))]
  exact (metricDualVectorAt_inner_apply g x
    ((Module.finBasis ℝ (TM x)).coord i) v).symm

/-- The raised-coordinate matrix of the metric dual basis is symmetric. -/
theorem metricDualVectorAt_coord_symm
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (i j : Fin (Module.finrank ℝ (TM x))) :
    (Module.finBasis ℝ (TM x)).coord i
      (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord j)) =
    (Module.finBasis ℝ (TM x)).coord j
      (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) := by
  rw [coord_eq_inner_metricDualVectorAt g x i,
    coord_eq_inner_metricDualVectorAt g x j]
  exact g.inner_symm x _ _

/-- The Ricci tensor as a raw `(0,2)` variation field for a fixed metric. -/
noncomputable def ricciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] :
    ∀ y : M, TM y → TM y → ℝ :=
  fun y v w ↦ g.ricciAt y v w

/-- The raw metric variation field `-2 Ric`. -/
noncomputable def negTwoRicciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] :
    ∀ y : M, TM y → TM y → ℝ :=
  fun y v w ↦ -2 * g.ricciAt y v w

/-- The metric trace of the Ricci variation field is scalar curvature. -/
theorem traceMetricVariationAt_ricci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    traceMetricVariationAt g (ricciVariationField g) x = g.scalarAt x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  rw [g.scalarAt_eq_trace_ricciEndoAt]
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  unfold traceMetricVariationAt ricciVariationField
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change g.ricciAt x (b i) (metricDualVectorAt g x (b.coord i)) =
    b.coord i (g.ricciEndoAt x (b i))
  rw [coord_eq_inner_metricDualVectorAt]
  rw [g.inner_ricciEndoAt]

theorem extDerivFun_traceMetricVariationAt_ricci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (w : TM x) :
    extDerivFun
        (fun y : M ↦ traceMetricVariationAt g (ricciVariationField g) y)
        x w =
      extDerivFun (fun y : M ↦ g.scalarAt y) x w := by
  have hfun :
      (fun y : M ↦ traceMetricVariationAt g (ricciVariationField g) y) =
        fun y : M ↦ g.scalarAt y := by
    funext y
    exact traceMetricVariationAt_ricci g y
  rw [hfun]

/-- Tracing `-2 Ric` gives `-2 R`. -/
theorem traceMetricVariationAt_negTwoRicci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    traceMetricVariationAt g (negTwoRicciVariationField g) x =
      -2 * g.scalarAt x := by
  unfold negTwoRicciVariationField
  rw [traceMetricVariationAt_smul]
  simpa [ricciVariationField] using
    congrArg (fun r : ℝ ↦ -2 * r) (traceMetricVariationAt_ricci g x)

/-- Contracting coordinates against the metric reconstructs the metric pairing. -/
theorem sum_coord_inner_eq_inner
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)] (u v : TM x) :
    (∑ i, (Module.finBasis ℝ (TM x)).coord i u *
      g.inner x ((Module.finBasis ℝ (TM x)) i) v) = g.inner x u v := by
  let b := Module.finBasis ℝ (TM x)
  have hrepr : u = ∑ i, b.coord i u • b i := (b.sum_repr u).symm
  calc
    (∑ i, b.coord i u * g.inner x (b i) v) =
        ∑ i, g.inner x (b.coord i u • b i) v := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp [smul_eq_mul]
    _ = g.inner x (∑ i, b.coord i u • b i) v := by
          have hmap :=
            congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
              (map_sum (g.inner x) (fun i ↦ b.coord i u • b i) Finset.univ)
          simpa using hmap.symm
    _ = g.inner x u v := by
          rw [← hrepr]

/-- The Ricci/Ricci metric-variation pairing is the squared Ricci norm. -/
theorem metricVariationRicciPairingAt_ricci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    metricVariationRicciPairingAt g (ricciVariationField g) x =
      g.ricciNormSqAt x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  rw [g.ricciNormSqAt_eq_trace]
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  unfold metricVariationRicciPairingAt ricciVariationField
  change (∑ j, ∑ i, g.ricciAt x (sharp j) (sharp i) *
      g.ricciAt x (b i) (b j)) =
    ∑ j, ((LinearMap.toMatrix b b)
      (g.ricciEndoAt x ∘ₗ g.ricciEndoAt x)).diag j
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (∑ i, g.ricciAt x (sharp j) (sharp i) *
      g.ricciAt x (b i) (b j)) =
    b.coord j ((g.ricciEndoAt x ∘ₗ g.ricciEndoAt x) (b j))
  rw [LinearMap.comp_apply, coord_eq_inner_metricDualVectorAt]
  have hcoord : ∀ i,
      g.ricciAt x (sharp j) (sharp i) =
        b.coord i (g.ricciEndoAt x (sharp j)) := by
    intro i
    rw [coord_eq_inner_metricDualVectorAt]
    rw [g.inner_ricciEndoAt]
  have hslot : ∀ i,
      g.ricciAt x (b i) (b j) =
        g.inner x (b i) (g.ricciEndoAt x (b j)) := by
    intro i
    calc
      g.ricciAt x (b i) (b j) = g.ricciAt x (b j) (b i) := g.ricciAt_symm x (b i) (b j)
      _ = g.inner x (g.ricciEndoAt x (b j)) (b i) := by
            rw [g.inner_ricciEndoAt]
      _ = g.inner x (b i) (g.ricciEndoAt x (b j)) := g.inner_symm x _ _
  calc
    (∑ i, g.ricciAt x (sharp j) (sharp i) *
        g.ricciAt x (b i) (b j)) =
        ∑ i, b.coord i (g.ricciEndoAt x (sharp j)) *
          g.inner x (b i) (g.ricciEndoAt x (b j)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hcoord i, hslot i]
    _ = g.inner x (g.ricciEndoAt x (sharp j))
        (g.ricciEndoAt x (b j)) := by
          exact sum_coord_inner_eq_inner g x
            (g.ricciEndoAt x (sharp j)) (g.ricciEndoAt x (b j))
    _ = g.inner x (sharp j) (g.ricciEndoAt x (g.ricciEndoAt x (b j))) := by
          exact g.ricciEndoAt_selfAdjoint x (sharp j)
            (g.ricciEndoAt x (b j))
    _ = g.inner x (g.ricciEndoAt x (g.ricciEndoAt x (b j))) (sharp j) := by
          rw [g.inner_symm]

/-- Pairing `-2 Ric` with Ricci gives `-2 |Ric|²`. -/
theorem metricVariationRicciPairingAt_negTwoRicci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    metricVariationRicciPairingAt g (negTwoRicciVariationField g) x =
      -2 * g.ricciNormSqAt x := by
  unfold negTwoRicciVariationField
  rw [metricVariationRicciPairingAt_smul]
  simpa [ricciVariationField] using
    congrArg (fun r : ℝ ↦ -2 * r) (metricVariationRicciPairingAt_ricci g x)

/-- Pointwise equality at `x` is enough to identify metric traces at `x`. -/
theorem traceMetricVariationAt_congr_at
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hEq : ∀ v w : TM x, h x v w = k x v w) :
    traceMetricVariationAt g h x = traceMetricVariationAt g k x := by
  unfold traceMetricVariationAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact hEq _ _

/-- Pointwise equality at `x` is enough to identify Ricci pairings at `x`. -/
theorem metricVariationRicciPairingAt_congr_at
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hEq : ∀ v w : TM x, h x v w = k x v w) :
    metricVariationRicciPairingAt g h x =
      metricVariationRicciPairingAt g k x := by
  unfold metricVariationRicciPairingAt
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hEq]

/-- Under pointwise `h = -2 Ric`, the metric trace is `-2 R`. -/
theorem traceMetricVariationAt_timeDeriv_eq_negTwoRicci
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hEq : ∀ v w : TM x,
      timeDerivAt gt t₀ x v w = -2 * (gt t₀).ricciAt x v w) :
    traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x =
      -2 * (gt t₀).scalarAt x := by
  calc
    traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x =
        traceMetricVariationAt (gt t₀) (negTwoRicciVariationField (gt t₀)) x := by
          apply traceMetricVariationAt_congr_at
          intro v w
          simpa [negTwoRicciVariationField] using hEq v w
    _ = -2 * (gt t₀).scalarAt x :=
          traceMetricVariationAt_negTwoRicci (gt t₀) x

/-- Under pointwise `h = -2 Ric`, the Ricci pairing is `-2 |Ric|²`. -/
theorem metricVariationRicciPairingAt_timeDeriv_eq_negTwoRicci
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hEq : ∀ v w : TM x,
      timeDerivAt gt t₀ x v w = -2 * (gt t₀).ricciAt x v w) :
    metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
      -2 * (gt t₀).ricciNormSqAt x := by
  calc
    metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
        metricVariationRicciPairingAt (gt t₀) (negTwoRicciVariationField (gt t₀)) x := by
          apply metricVariationRicciPairingAt_congr_at
          intro v w
          simpa [negTwoRicciVariationField] using hEq v w
    _ = -2 * (gt t₀).ricciNormSqAt x :=
          metricVariationRicciPairingAt_negTwoRicci (gt t₀) x

/--
Raised-dual-basis contraction swap on one closed tangent fiber.

For any scalar form linear in both slots, contracting the metric-dual raised
basis in the first slot is the same as contracting it in the second slot.
-/
theorem sum_metricDualVectorAt_contraction_swap
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (F : TM x → TM x → ℝ)
    (hadd1 : ∀ p₁ p₂ q, F (p₁ + p₂) q = F p₁ q + F p₂ q)
    (hsmul1 : ∀ (c : ℝ) p q, F (c • p) q = c • F p q)
    (hadd2 : ∀ p q₁ q₂, F p (q₁ + q₂) = F p q₁ + F p q₂)
    (hsmul2 : ∀ (c : ℝ) p q, F p (c • q) = c • F p q) :
    ∑ k, F (metricDualVectorAt g x
        ((Module.finBasis ℝ (TM x)).coord k)) ((Module.finBasis ℝ (TM x)) k)
      = ∑ k, F ((Module.finBasis ℝ (TM x)) k)
          (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord k)) := by
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun k ↦ metricDualVectorAt g x (b.coord k)
  have hrepr : ∀ k, sharp k = ∑ i, b.coord i (sharp k) • b i := by
    intro k
    exact (b.sum_repr (sharp k)).symm
  have hexp1 : ∀ k, F (sharp k) (b k)
      = ∑ i, b.coord i (sharp k) • F (b i) (b k) := by
    intro k
    conv_lhs => rw [hrepr k]
    set L : TM x →ₗ[ℝ] ℝ :=
      IsLinearMap.mk' (fun p ↦ F p (b k))
        ⟨fun p₁ p₂ ↦ hadd1 p₁ p₂ (b k),
         fun c p ↦ hsmul1 c p (b k)⟩ with hL
    have hmap := map_sum L (fun i ↦ b.coord i (sharp k) • b i) Finset.univ
    simp only [map_smul] at hmap
    exact hmap
  have hexp2 : ∀ k, F (b k) (sharp k)
      = ∑ i, b.coord i (sharp k) • F (b k) (b i) := by
    intro k
    conv_lhs => rw [hrepr k]
    set L : TM x →ₗ[ℝ] ℝ :=
      IsLinearMap.mk' (fun q ↦ F (b k) q)
        ⟨fun q₁ q₂ ↦ hadd2 (b k) q₁ q₂,
         fun c q ↦ hsmul2 c (b k) q⟩ with hL
    have hmap := map_sum L (fun i ↦ b.coord i (sharp k) • b i) Finset.univ
    simp only [map_smul] at hmap
    exact hmap
  change (∑ k, F (sharp k) (b k)) = ∑ k, F (b k) (sharp k)
  rw [Finset.sum_congr rfl (fun k _ ↦ hexp1 k),
    Finset.sum_congr rfl (fun k _ ↦ hexp2 k), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [metricDualVectorAt_coord_symm g x i k]

/-- Coordinates of the raised Ricci covector are Ricci evaluated on the raised dual basis. -/
theorem coord_metricRaiseContinuousAt_ricciDualContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) [FiniteDimensional ℝ (TM x)]
    (i j : Fin (Module.finrank ℝ (TM x))) :
    (Module.finBasis ℝ (TM x)).coord i
      (g.metricRaiseContinuousAt x
        (g.ricciDualContinuousAt x ((Module.finBasis ℝ (TM x)) j))) =
      g.ricciAt x ((Module.finBasis ℝ (TM x)) j)
        (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) := by
  rw [coord_eq_inner_metricDualVectorAt]
  rw [ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  simp

/--
The double raised-basis definition of `⟨h,Ric⟩` is the same contraction as
`Σⱼ h(♯Ric(eⱼ), ♯eʲ)`.
-/
theorem metricVariationRicciPairingAt_eq_raise_ricci_sum
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : TimeDifferentiableAt gt t₀ x) :
    metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
      letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ j, timeDerivAt gt t₀ x
        ((gt t₀).metricRaiseContinuousAt x
          ((gt t₀).ricciDualContinuousAt x ((Module.finBasis ℝ (TM x)) j)))
        (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  let ricSharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ g.metricRaiseContinuousAt x (g.ricciDualContinuousAt x (b j))
  have hH_expand : ∀ j k : Fin (Module.finrank ℝ (TM x)),
      timeDerivAt gt t₀ x (sharp j) (sharp k) =
        ∑ i, b.coord i (sharp k) * timeDerivAt gt t₀ x (sharp j) (b i) := by
    intro j k
    have hrepr : sharp k = ∑ i, b.coord i (sharp k) • b i := by
      conv_lhs => rw [(b.sum_repr (sharp k)).symm]
      simp [Module.Basis.coord_apply]
    calc
      timeDerivAt gt t₀ x (sharp j) (sharp k) =
          (timeDerivContinuousAt gt t₀ x hgt (sharp j)) (sharp k) := by
            simp
      _ = (timeDerivContinuousAt gt t₀ x hgt (sharp j))
          (∑ i, b.coord i (sharp k) • b i) :=
            congrArg (fun u ↦ (timeDerivContinuousAt gt t₀ x hgt (sharp j)) u)
              hrepr
      _ = ∑ i, b.coord i (sharp k) * timeDerivAt gt t₀ x (sharp j) (b i) := by
            rw [map_sum]
            simp [timeDerivContinuousAt_apply]
  have hRic_expand : ∀ j i : Fin (Module.finrank ℝ (TM x)),
      g.ricciAt x (b j) (sharp i) =
        ∑ k, b.coord k (sharp i) * g.ricciAt x (b j) (b k) := by
    intro j i
    have hrepr : sharp i = ∑ k, b.coord k (sharp i) • b k := by
      conv_lhs => rw [(b.sum_repr (sharp i)).symm]
      simp [Module.Basis.coord_apply]
    calc
      g.ricciAt x (b j) (sharp i) = (g.ricciDualContinuousAt x (b j)) (sharp i) := by
        simp
      _ = (g.ricciDualContinuousAt x (b j)) (∑ k, b.coord k (sharp i) • b k) :=
            congrArg (fun u ↦ (g.ricciDualContinuousAt x (b j)) u) hrepr
      _ = ∑ k, b.coord k (sharp i) * g.ricciAt x (b j) (b k) := by
            rw [map_sum]
            simp
  have htrace_expand : ∀ j : Fin (Module.finrank ℝ (TM x)),
      timeDerivAt gt t₀ x (ricSharp j) (sharp j) =
        ∑ i, ∑ k,
          b.coord k (sharp i) * g.ricciAt x (b j) (b k) *
            timeDerivAt gt t₀ x (b i) (sharp j) := by
    intro j
    have hfirst : timeDerivAt gt t₀ x (ricSharp j) (sharp j) =
        ∑ i, b.coord i (ricSharp j) * timeDerivAt gt t₀ x (b i) (sharp j) := by
      have hrepr : ricSharp j = ∑ i, b.coord i (ricSharp j) • b i := by
        conv_lhs => rw [(b.sum_repr (ricSharp j)).symm]
        simp [Module.Basis.coord_apply]
      calc
        timeDerivAt gt t₀ x (ricSharp j) (sharp j) =
            (timeDerivContinuousAt gt t₀ x hgt (ricSharp j)) (sharp j) := by
              simp
        _ = (timeDerivContinuousAt gt t₀ x hgt
              (∑ i, b.coord i (ricSharp j) • b i)) (sharp j) :=
              congrArg (fun u ↦ (timeDerivContinuousAt gt t₀ x hgt u) (sharp j))
                hrepr
        _ = ∑ i, b.coord i (ricSharp j) * timeDerivAt gt t₀ x (b i) (sharp j) := by
              rw [map_sum]
              simp [timeDerivContinuousAt_apply]
    rw [hfirst]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coord_metricRaiseContinuousAt_ricciDualContinuousAt]
    rw [hRic_expand j i]
    rw [Finset.sum_mul]
  calc
    metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x
        = ∑ j, ∑ k, timeDerivAt gt t₀ x (sharp j) (sharp k) *
            g.ricciAt x (b k) (b j) := by
            simp [metricVariationRicciPairingAt, g, b, sharp]
    _ = ∑ j, ∑ k, (∑ i, b.coord i (sharp k) *
          timeDerivAt gt t₀ x (sharp j) (b i)) * g.ricciAt x (b k) (b j) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [hH_expand]
    _ = ∑ j, ∑ k, ∑ i,
          b.coord i (sharp k) * timeDerivAt gt t₀ x (sharp j) (b i) *
            g.ricciAt x (b k) (b j) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, ∑ k,
          b.coord k (sharp i) * g.ricciAt x (b j) (b k) *
            timeDerivAt gt t₀ x (b i) (sharp j) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [metricDualVectorAt_coord_symm]
            rw [ClosedSmoothRiemannianMetric.ricciAt_symm]
            rw [timeDerivAt_symm gt t₀ x (sharp j) (b i)]
            ring
    _ = ∑ j, timeDerivAt gt t₀ x (ricSharp j) (sharp j) := by
            refine (Finset.sum_congr rfl fun j _ ↦ ?_).symm
            exact htrace_expand j
    _ = (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ j, timeDerivAt gt t₀ x
        ((gt t₀).metricRaiseContinuousAt x
          ((gt t₀).ricciDualContinuousAt x ((Module.finBasis ℝ (TM x)) j)))
        (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j))) := by
            rfl

/-- The derivative of the metric index-raising map is `-♯ ∘ h^♭ ∘ ♯`. -/
noncomputable def metricRaiseDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hgt : TimeDifferentiableAt gt t₀ x) :
    (TM x →L[ℝ] ℝ) →L[ℝ] TM x :=
  -(((gt t₀).metricRaiseContinuousAt x).comp
      ((timeDerivContinuousAt gt t₀ x hgt).comp
        ((gt t₀).metricRaiseContinuousAt x)))

/-- Pairing the explicit raise-map derivative with the metric lowers it to `-h`. -/
theorem metricRaiseDerivAt_inner_apply
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (φ : TM x →L[ℝ] ℝ) (v : TM x) :
    (gt t₀).inner x (metricRaiseDerivAt gt t₀ x hgt φ) v =
      -timeDerivAt gt t₀ x ((gt t₀).metricRaiseContinuousAt x φ) v := by
  unfold metricRaiseDerivAt
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, map_neg]
  rw [ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  simp

/-- Any derivative of the metric raise map is the explicit inverse-metric derivative. -/
theorem metricRaise_deriv_eq_of_hasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀) :
    raise' = metricRaiseDerivAt gt t₀ x hgt := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  ext φ
  apply sub_eq_zero.mp
  refine LeviCivitaExistence.metric_nondegenerate (gt t₀) x
    (raise' φ - metricRaiseDerivAt gt t₀ x hgt φ) ?_
  intro v
  have hφ : HasDerivAt (fun _ : ℝ ↦ φ) 0 t₀ := hasDerivAt_const t₀ φ
  have hraiseφ : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x φ)
      (raise' φ) t₀ := by
    simpa using hRaise.clm_apply hφ
  have hinner :=
    hasDerivAt_inner_of_timeDifferentiableAt (gt := gt) (t₀ := t₀) (x := x) hgt
  have hpairCLM : HasDerivAt
      (fun t ↦ (gt t).inner x ((gt t).metricRaiseContinuousAt x φ))
      (timeDerivContinuousAt gt t₀ x hgt ((gt t₀).metricRaiseContinuousAt x φ) +
        (gt t₀).inner x (raise' φ)) t₀ := by
    simpa using hinner.clm_apply hraiseφ
  have hv : HasDerivAt (fun _ : ℝ ↦ v) 0 t₀ := hasDerivAt_const t₀ v
  have hpair : HasDerivAt
      (fun t ↦ (gt t).inner x ((gt t).metricRaiseContinuousAt x φ) v)
      (timeDerivAt gt t₀ x ((gt t₀).metricRaiseContinuousAt x φ) v +
        (gt t₀).inner x (raise' φ) v) t₀ := by
    simpa using hpairCLM.clm_apply hv
  have hconst : HasDerivAt
      (fun t ↦ (gt t).inner x ((gt t).metricRaiseContinuousAt x φ) v)
      0 t₀ := by
    have hid :
        (fun t ↦ (gt t).inner x ((gt t).metricRaiseContinuousAt x φ) v) =
          fun _ : ℝ ↦ φ v := by
      funext t
      exact ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply
        (gt t) x φ v
    simpa [hid] using (hasDerivAt_const t₀ (φ v))
  have hzero :
      timeDerivAt gt t₀ x ((gt t₀).metricRaiseContinuousAt x φ) v +
        (gt t₀).inner x (raise' φ) v = 0 :=
    hpair.unique hconst
  rw [map_sub]
  simp only [ContinuousLinearMap.sub_apply]
  rw [metricRaiseDerivAt_inner_apply hgt]
  linarith

/-- The explicit raise-map derivative contributes `-⟨h,Ric⟩` to scalar variation. -/
theorem metricRaiseDeriv_trace_ricciDualContinuousAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : TimeDifferentiableAt gt t₀ x) :
    LinearMap.trace ℝ (TM x)
      (((metricRaiseDerivAt gt t₀ x hgt).comp
          ((gt t₀).ricciDualContinuousAt x) : TM x →L[ℝ] TM x) :
        TM x →ₗ[ℝ] TM x)
      = -metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hpair := metricVariationRicciPairingAt_eq_raise_ricci_sum
    (gt := gt) (t₀ := t₀) (x := x) hgt
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  have hdiag :
      (∑ i,
        ((LinearMap.toMatrix b b)
          ↑((metricRaiseDerivAt gt t₀ x hgt).comp
            ((gt t₀).ricciDualContinuousAt x))).diag i) =
        ∑ j, b.coord j
          ((metricRaiseDerivAt gt t₀ x hgt)
            (g.ricciDualContinuousAt x (b j))) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [hdiag]
  change (∑ j, b.coord j
      ((metricRaiseDerivAt gt t₀ x hgt)
        (g.ricciDualContinuousAt x (b j)))) =
    -metricVariationRicciPairingAt g (timeDerivAt gt t₀) x
  rw [hpair]
  calc
    (∑ j, b.coord j
      ((metricRaiseDerivAt gt t₀ x hgt)
        (g.ricciDualContinuousAt x (b j)))) =
        ∑ j, -timeDerivAt gt t₀ x
          (g.metricRaiseContinuousAt x (g.ricciDualContinuousAt x (b j)))
          (sharp j) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [coord_eq_inner_metricDualVectorAt]
            rw [metricRaiseDerivAt_inner_apply hgt]
    _ = -∑ j, timeDerivAt gt t₀ x
          (g.metricRaiseContinuousAt x (g.ricciDualContinuousAt x (b j)))
          (sharp j) := by
            rw [Finset.sum_neg_distrib]

/-- The actual derivative of the raise-map has the `-⟨h,Ric⟩` trace. -/
theorem metricRaise_trace_ricciDualContinuousAt_eq_neg
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀) :
    LinearMap.trace ℝ (TM x)
      ((raise'.comp ((gt t₀).ricciDualContinuousAt x) : TM x →L[ℝ] TM x) :
        TM x →ₗ[ℝ] TM x)
      = -metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x := by
  rw [metricRaise_deriv_eq_of_hasDerivAt hgt hRaise]
  exact metricRaiseDeriv_trace_ricciDualContinuousAt
    (gt := gt) (t₀ := t₀) (x := x) hgt

theorem trace_metricRaise_ricciDerivativeDualContinuousAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀) :
    LinearMap.trace ℝ (TM x)
      (((((gt t₀).metricRaiseContinuousAt x).comp
          (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
            (gt := gt) (t₀ := t₀) (x := x) δRic hRic)) : TM x →L[ℝ] TM x) :
        TM x →ₗ[ℝ] TM x)
      =
        letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
        ∑ j, δRic ((Module.finBasis ℝ (TM x)) j)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)) := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  have hdiag :
      (∑ j,
        ((LinearMap.toMatrix b b)
          ↑((((gt t₀).metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x) δRic hRic)))).diag j) =
        ∑ j, b.coord j
          (((gt t₀).metricRaiseContinuousAt x)
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x) δRic hRic (b j))) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [hdiag]
  change (∑ j, b.coord j
      (g.metricRaiseContinuousAt x
        (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
          (gt := gt) (t₀ := t₀) (x := x) δRic hRic (b j)))) =
    ∑ j, δRic (b j) (sharp j)
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coord_eq_inner_metricDualVectorAt]
  rw [ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  simp [g, b, sharp]

theorem trace_metricRaise_deltaRicciAt_eq_sum
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x) :
    LinearMap.trace ℝ (TM x)
        (((((gt t₀).metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x)
              (deltaRicciAt gt t₀ x)
              (fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w))) :
            TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
      =
        letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
        ∑ j, deltaRicciAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)) := by
  let hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciAt gt t₀ x u w) t₀ :=
    fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
  simpa [hRic] using
    (trace_metricRaise_ricciDerivativeDualContinuousAt
      (gt := gt) (t₀ := t₀) (x := x)
      (δRic := deltaRicciAt gt t₀ x) hRic)

theorem deltaRicciAt_raised_trace_eq_deltaGamma_contractions
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ j, deltaRicciAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
        (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
      =
        (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
          ∑ j, deltaGammaDivergenceAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
            (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
        -
        (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
          ∑ j, deltaGammaContractionDerivAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
            (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j))) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  unfold deltaRicciAt
  rw [Finset.sum_sub_distrib]

omit [T2Space M] [IsManifold I ∞ M] in
private theorem extDerivFun_zero_at (x : M) :
    (extDerivFun (fun _ : M ↦ (0 : ℝ)) x : TM x →L[ℝ] ℝ) = 0 := by
  unfold extDerivFun
  simp

omit [T2Space M] in
private theorem extDerivFun_const_smul_at {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (c : ℝ) :
    (extDerivFun (c • f) x : TM x →L[ℝ] ℝ) =
      c • (extDerivFun f x : TM x →L[ℝ] ℝ) := by
  ext v
  have hmul := CovariantDerivative.extDerivFun_mul
    (p := fun _ : M ↦ c) (q := f) (x := x) mdifferentiableAt_const hf v
  simp [Pi.smul_apply, smul_eq_mul] at hmul ⊢
  exact hmul

omit [T2Space M] in
private theorem extDerivFun_add_sub_at {f g h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hh : MDifferentiableAt I 𝓘(ℝ) h x)
    (v : TM x) :
    extDerivFun (fun y : M ↦ f y + g y - h y) x v =
      extDerivFun f x v + extDerivFun g x v - extDerivFun h x v := by
  have hfg : MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ f y + g y) x :=
    hf.add hg
  have hneg : MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ -h y) x := by
    simpa using hh.neg
  have hsum := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
    (extDerivFun_add hfg hneg)
  have hfg' := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
    (extDerivFun_add hf hg)
  have hsum' :
      extDerivFun ((fun y : M ↦ f y + g y) + fun y : M ↦ -h y) x v =
        extDerivFun (fun y : M ↦ f y + g y) x v +
          extDerivFun (fun y : M ↦ -h y) x v := by
    simpa using hsum
  have hfg'' :
      extDerivFun (fun y : M ↦ f y + g y) x v =
        extDerivFun f x v + extDerivFun g x v := by
    simpa using hfg'
  have hnegFun : (fun y : M ↦ -h y) = (-1 : ℝ) • h := by
    funext y
    simp
  have hneg' : extDerivFun (fun y : M ↦ -h y) x v =
      -extDerivFun h x v := by
    rw [hnegFun]
    have h := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
      (extDerivFun_const_smul_at (n := n) (M := M) hh (-1 : ℝ))
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have hfun :
      (fun y : M ↦ f y + g y - h y) =
        (fun y : M ↦ f y + g y) + fun y : M ↦ -h y := by
    funext y
    simp [sub_eq_add_neg]
  rw [hfun]
  rw [hsum', hfg'', hneg']
  ring

omit [T2Space M] in
private theorem extDerivFun_sum_at {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → M → ℝ) {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x)
    (v : TM x) :
    extDerivFun (∑ i ∈ s, f i) x v =
      ∑ i ∈ s, extDerivFun (f i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
        (extDerivFun_zero_at (n := n) (M := M) (x := x))
  | insert a s ha ih =>
      have haDiff : MDifferentiableAt I 𝓘(ℝ) (f a) x :=
        hf a (Finset.mem_insert_self a s)
      have hsDiff : MDifferentiableAt I 𝓘(ℝ)
          (∑ i ∈ s, f i) x := by
        exact @MDifferentiableAt.sum ℝ _ E _ _ E _ I M _ _ ℝ _ _ x ι s f
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      have hAdd := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
        (extDerivFun_add haDiff hsDiff)
      calc
        extDerivFun (∑ i ∈ insert a s, f i) x v =
            extDerivFun (f a + ∑ i ∈ s, f i) x v := by
              rw [Finset.sum_insert ha]
        _ = extDerivFun (f a) x v
              + extDerivFun (∑ i ∈ s, f i) x v := by
              simpa using hAdd
        _ = extDerivFun (f a) x v
              + ∑ i ∈ s, extDerivFun (f i) x v := by
              rw [ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))]
        _ = ∑ i ∈ insert a s, extDerivFun (f i) x v := by
              simp [Finset.sum_insert, ha]

set_option maxHeartbeats 5000000 in
private theorem gramMatrix_inv_extDerivFun_mul_self_eq_neg
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (w : TM x)
    (i l : Fin (Module.finrank ℝ (TM x))) :
    ∑ k,
        extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i k) x w *
          gramMatrix g x x k l
      =
        -∑ k,
          (gramMatrix g x x)⁻¹ i k *
            extDerivFun (fun y : M ↦ gramMatrix g x y k l) x w := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let term : Fin (Module.finrank ℝ (TM x)) → M → ℝ :=
    fun k y ↦ (gramMatrix g x y)⁻¹ i k * gramMatrix g x y k l
  have htermDiff : ∀ k,
      MDifferentiableAt I 𝓘(ℝ) (term k) x := by
    intro k
    exact (gramMatrix_inv_entry_mdiffAt (g := g) x i k).mul
      (gramMatrix_entry_mdiffAt (g := g) x k l)
  have hsum := extDerivFun_sum_at
    (n := n) (M := M)
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
    (f := term) (x := x)
    (fun k _hk ↦ htermDiff k) w
  have heq :
      (∑ k, term k) =ᶠ[nhds x]
        fun _ : M ↦ if i = l then (1 : ℝ) else 0 := by
    exact (gramMatrix_eventually_isUnit (g := g) x).mono fun y hy ↦ by
      have hdet : IsUnit (gramMatrix g x y).det :=
        (Matrix.isUnit_iff_isUnit_det (gramMatrix g x y)).mp hy
      have hmul := congrArg
        (fun A : Matrix (Fin (Module.finrank ℝ (TM x)))
            (Fin (Module.finrank ℝ (TM x))) ℝ ↦ A i l)
        (Matrix.nonsing_inv_mul (gramMatrix g x y) hdet)
      simpa [term, Matrix.mul_apply] using hmul
  have hcongr := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L w)
    (CovariantDerivative.extDerivFun_congr heq)
  change extDerivFun (∑ k, term k) x w =
    extDerivFun (fun _ : M ↦ if i = l then (1 : ℝ) else 0) x w at hcongr
  rw [hsum] at hcongr
  have hprod : ∀ k,
      extDerivFun (term k) x w =
        (gramMatrix g x x)⁻¹ i k *
            extDerivFun (fun y : M ↦ gramMatrix g x y k l) x w
          + extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i k) x w *
            gramMatrix g x x k l := by
    intro k
    have hinv : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ (gramMatrix g x y)⁻¹ i k) x :=
      gramMatrix_inv_entry_mdiffAt (g := g) x i k
    have hentry : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ gramMatrix g x y k l) x :=
      gramMatrix_entry_mdiffAt (g := g) x k l
    simpa [term] using
      (CovariantDerivative.extDerivFun_mul
        (p := fun y : M ↦ (gramMatrix g x y)⁻¹ i k)
        (q := fun y : M ↦ gramMatrix g x y k l)
        (x := x) hinv hentry w)
  have hzero :
      (∑ k,
          ((gramMatrix g x x)⁻¹ i k *
              extDerivFun (fun y : M ↦ gramMatrix g x y k l) x w
            + extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i k) x w *
              gramMatrix g x x k l))
        = 0 := by
    rw [Finset.sum_congr rfl (fun k _hk ↦ hprod k)] at hcongr
    simpa using hcongr
  rw [Finset.sum_add_distrib] at hzero
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_comm] using hzero

private theorem gramMatrix_inv_extDerivFun_matrix_eq_neg
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (w : TM x) :
    let Dinv : Matrix (Fin (Module.finrank ℝ (TM x)))
        (Fin (Module.finrank ℝ (TM x))) ℝ :=
      fun i j ↦ extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w
    let Dgram : Matrix (Fin (Module.finrank ℝ (TM x)))
        (Fin (Module.finrank ℝ (TM x))) ℝ :=
      fun i j ↦ extDerivFun (fun y : M ↦ gramMatrix g x y i j) x w
    Dinv =
      -((gramMatrix g x x)⁻¹ * Dgram * (gramMatrix g x x)⁻¹) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let G : Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ := gramMatrix g x x
  let Dinv : Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
    fun i j ↦ extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w
  let Dgram : Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
    fun i j ↦ extDerivFun (fun y : M ↦ gramMatrix g x y i j) x w
  have hmul : Dinv * G = -(G⁻¹ * Dgram) := by
    ext i l
    simpa [Dinv, Dgram, G, Matrix.mul_apply] using
      gramMatrix_inv_extDerivFun_mul_self_eq_neg
        (g := g) (x := x) (w := w) i l
  have hdet : IsUnit G.det := by
    simpa [G] using
      (Matrix.isUnit_iff_isUnit_det (gramMatrix g x x)).mp
        (gramMatrix_at_base_isUnit (g := g) (x := x))
  have hright : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  calc
    Dinv = Dinv * 1 := by rw [Matrix.mul_one]
    _ = Dinv * (G * G⁻¹) := by rw [hright]
    _ = (Dinv * G) * G⁻¹ := by rw [Matrix.mul_assoc]
    _ = (-(G⁻¹ * Dgram)) * G⁻¹ := by rw [hmul]
    _ = -(G⁻¹ * Dgram * G⁻¹) := by
          simp [Matrix.mul_assoc]

theorem gramMatrix_inv_extDerivFun_eq_neg_sum
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (w : TM x)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w =
      -∑ k, ∑ l,
        (gramMatrix g x x)⁻¹ i k *
          extDerivFun (fun y : M ↦ gramMatrix g x y k l) x w *
          (gramMatrix g x x)⁻¹ l j := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let G : Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ := gramMatrix g x x
  let Dgram : Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
    fun i j ↦ extDerivFun (fun y : M ↦ gramMatrix g x y i j) x w
  have hmat := gramMatrix_inv_extDerivFun_matrix_eq_neg
    (g := g) (x := x) (w := w)
  have hij := congrArg
    (fun A : Matrix (Fin (Module.finrank ℝ (TM x)))
        (Fin (Module.finrank ℝ (TM x))) ℝ ↦ A i j) hmat
  calc
    extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w =
        (-(G⁻¹ * Dgram * G⁻¹)) i j := by
          simpa [G, Dgram] using hij
    _ = -∑ k, ∑ l,
        (gramMatrix g x x)⁻¹ i k *
          extDerivFun (fun y : M ↦ gramMatrix g x y k l) x w *
          (gramMatrix g x x)⁻¹ l j := by
          simp [G, Dgram, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

def Tensor2AddLeft
    (h : ∀ y : M, TM y → TM y → ℝ) : Prop :=
  ∀ y : M, ∀ p₁ p₂ q : TM y,
    h y (p₁ + p₂) q = h y p₁ q + h y p₂ q

def Tensor2SMulLeft
    (h : ∀ y : M, TM y → TM y → ℝ) : Prop :=
  ∀ y : M, ∀ (c : ℝ) (p q : TM y),
    h y (c • p) q = c * h y p q

def Tensor2AddRight
    (h : ∀ y : M, TM y → TM y → ℝ) : Prop :=
  ∀ y : M, ∀ p q₁ q₂ : TM y,
    h y p (q₁ + q₂) = h y p q₁ + h y p q₂

def Tensor2SMulRight
    (h : ∀ y : M, TM y → TM y → ℝ) : Prop :=
  ∀ y : M, ∀ (c : ℝ) (p q : TM y),
    h y p (c • q) = c * h y p q

theorem tensor2AddLeft_ricciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] :
    Tensor2AddLeft (ricciVariationField g) := by
  intro y p₁ p₂ q
  simpa [ricciVariationField] using g.ricciAt_add_left y p₁ p₂ q

theorem tensor2SMulLeft_ricciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] :
    Tensor2SMulLeft (ricciVariationField g) := by
  intro y c p q
  simpa [ricciVariationField, smul_eq_mul] using g.ricciAt_smul_left y c p q

theorem tensor2AddRight_ricciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] :
    Tensor2AddRight (ricciVariationField g) := by
  intro y p q₁ q₂
  simpa [ricciVariationField] using g.ricciAt_add_right y p q₁ q₂

theorem tensor2SMulRight_ricciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] :
    Tensor2SMulRight (ricciVariationField g) := by
  intro y c p q
  simpa [ricciVariationField, smul_eq_mul] using g.ricciAt_smul_right y c p q

/-- The closed Ricci tensor packaged as a bilinear form for Gram-trace lemmas. -/
noncomputable def ricciVariationBilinForm
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (y : M) : LinearMap.BilinForm ℝ (TM y) :=
  LinearMap.mk₂ ℝ (fun p q ↦ ricciVariationField g y p q)
    (fun p p' q ↦ tensor2AddLeft_ricciVariationField g y p p' q)
    (fun c p q ↦ tensor2SMulLeft_ricciVariationField g y c p q)
    (fun p q q' ↦ tensor2AddRight_ricciVariationField g y p q q')
    (fun c p q ↦ tensor2SMulRight_ricciVariationField g y c p q)

private theorem tensor2_sum_left
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {h : ∀ y : M, TM y → TM y → ℝ}
    (hAddL : Tensor2AddLeft h) (hSMulL : Tensor2SMulLeft h)
    (x : M) (c : ι → ℝ) (p : ι → TM x) (q : TM x) :
    h x (∑ i, c i • p i) q = ∑ i, c i * h x (p i) q := by
  set L : TM x →ₗ[ℝ] ℝ :=
    IsLinearMap.mk' (fun p ↦ h x p q)
      ⟨fun p₁ p₂ ↦ hAddL x p₁ p₂ q,
       fun c p ↦ by simpa [smul_eq_mul] using hSMulL x c p q⟩ with hL
  change L (∑ i, c i • p i) = ∑ i, c i * L (p i)
  have hmap := map_sum L (fun i ↦ c i • p i) Finset.univ
  simpa [smul_eq_mul] using hmap

private theorem tensor2_sum_right
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {h : ∀ y : M, TM y → TM y → ℝ}
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h)
    (x : M) (p : TM x) (c : ι → ℝ) (q : ι → TM x) :
    h x p (∑ i, c i • q i) = ∑ i, c i * h x p (q i) := by
  set L : TM x →ₗ[ℝ] ℝ :=
    IsLinearMap.mk' (fun q ↦ h x p q)
      ⟨fun q₁ q₂ ↦ hAddR x p q₁ q₂,
       fun c q ↦ by simpa [smul_eq_mul] using hSMulR x c p q⟩ with hL
  change L (∑ i, c i • q i) = ∑ i, c i * L (q i)
  have hmap := map_sum L (fun i ↦ c i • q i) Finset.univ
  simpa [smul_eq_mul] using hmap

/-- A vector reconstructed from pairings with the finite basis and the raised dual coframe. -/
theorem sum_inner_basis_smul_metricDualVectorAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)] (v : TM x) :
    (∑ i, g.inner x v ((Module.finBasis ℝ (TM x)) i) •
      metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) = v := by
  classical
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  apply sub_eq_zero.mp
  refine LeviCivitaExistence.metric_nondegenerate g x
    ((∑ i, g.inner x v (b i) • sharp i) - v) ?_
  intro z
  rw [map_sub]
  simp only [ContinuousLinearMap.sub_apply]
  have hpair :
      g.inner x (∑ i, g.inner x v (b i) • sharp i) z =
        g.inner x v z := by
    have hsum :
        g.inner x (∑ i, g.inner x v (b i) • sharp i) z =
          ∑ i, g.inner x v (b i) * g.inner x (sharp i) z := by
      have hmap := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L z)
        (map_sum (g.inner x) (fun i ↦ g.inner x v (b i) • sharp i) Finset.univ)
      simpa [sharp, smul_eq_mul] using hmap
    calc
      g.inner x (∑ i, g.inner x v (b i) • sharp i) z =
          ∑ i, g.inner x v (b i) * g.inner x (sharp i) z := hsum
      _ = ∑ i, b.coord i z * g.inner x (b i) v := by
            refine Finset.sum_congr rfl fun i _hi ↦ ?_
            rw [metricDualVectorAt_inner_apply]
            rw [g.inner_symm x v (b i)]
            ring
      _ = g.inner x z v :=
            sum_coord_inner_eq_inner (g := g) (x := x) z v
      _ = g.inner x v z := g.inner_symm x z v
  rw [hpair]
  simp

private theorem tensor2_basis_expansion_left
    {h : ∀ y : M, TM y → TM y → ℝ}
    (g : ClosedSmoothRiemannianMetric n M)
    (hAddL : Tensor2AddLeft h) (hSMulL : Tensor2SMulLeft h)
    (x : M) [FiniteDimensional ℝ (TM x)] (v q : TM x) :
    h x v q =
      ∑ i, g.inner x v (metricDualVectorAt g x
          ((Module.finBasis ℝ (TM x)).coord i)) *
        h x ((Module.finBasis ℝ (TM x)) i) q := by
  classical
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hrepr : v = ∑ i, b.coord i v • b i := (b.sum_repr v).symm
  calc
    h x v q = h x (∑ i, b.coord i v • b i) q :=
          congrArg (fun u ↦ h x u q) hrepr
    _ = ∑ i, b.coord i v * h x (b i) q := by
          exact tensor2_sum_left (h := h) hAddL hSMulL x (fun i ↦ b.coord i v) b q
    _ = ∑ i, g.inner x v (sharp i) * h x (b i) q := by
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          rw [coord_eq_inner_metricDualVectorAt]

private theorem tensor2_metricDual_expansion_right
    {h : ∀ y : M, TM y → TM y → ℝ}
    (g : ClosedSmoothRiemannianMetric n M)
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h)
    (x : M) [FiniteDimensional ℝ (TM x)] (p v : TM x) :
    h x p v =
      ∑ i, g.inner x v ((Module.finBasis ℝ (TM x)) i) *
        h x p (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) := by
  classical
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hrepr :
      (∑ i, g.inner x v (b i) • sharp i) = v :=
    sum_inner_basis_smul_metricDualVectorAt (g := g) (x := x) v
  calc
    h x p v = h x p (∑ i, g.inner x v (b i) • sharp i) :=
          congrArg (fun u ↦ h x p u) hrepr.symm
    _ = ∑ i, g.inner x v (b i) * h x p (sharp i) := by
          exact tensor2_sum_right (h := h) hAddR hSMulR x p
            (fun i ↦ g.inner x v (b i)) sharp

def CovTensor2ExtDifferentiableAt
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ p q : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ h y (extend E p y) (extend E q y)) x

/--
Second-order scalar-entry regularity for a raw `(0,2)` variation tensor in the
canonical extension frame.

This is the C² analogue of `CovTensor2ExtDifferentiableAt`: after taking one
exterior derivative of each scalar entry, the resulting scalar field is still
differentiable in every canonical extension direction.
-/
def CovTensor2ExtSecondDifferentiableAt
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ p q v : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        extDerivFun
          (fun z : M ↦ h z (extend E p z) (extend E q z)) y
          (extend E v y)) x

/-- Second-order scalar-entry regularity for the metric Gram entries. -/
def MetricExtSecondDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) : Prop :=
  ∀ p q v : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        extDerivFun
          (fun z : M ↦ g.inner z (extend E p z) (extend E q z)) y
          (extend E v y)) x

/--
Neighborhood-form scalar-entry regularity for a raw `(0,2)` tensor in the
canonical extension frame.

Unlike `CovTensor2ExtSecondDifferentiableAt`, this asks the scalar entries
themselves to be `C^k` at `x`.  At `k = 2` this is the honest local hypothesis
needed to apply product, inverse, and second exterior-derivative rules near the
base point.
-/
def CovTensor2ExtContMDiffAt
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) (k : ℕ∞) : Prop :=
  ∀ p q : TM x,
    ContMDiffAt I 𝓘(ℝ) k
      (fun y : M ↦ h y (extend E p y) (extend E q y)) x

/-- Neighborhood-form scalar-entry regularity for metric Gram entries. -/
def MetricExtContMDiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (k : ℕ∞) : Prop :=
  ∀ p q : TM x,
    ContMDiffAt I 𝓘(ℝ) k
      (fun y : M ↦ g.inner y (extend E p y) (extend E q y)) x

/--
Neighborhood-form scalar-entry regularity for the metric time-variation tensor.
For `h = timeDerivAt gt t₀`, this is the natural spatial part of a jointly
smooth metric-flow hypothesis.
-/
def TimeVariationExtContMDiffAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (k : ℕ∞) : Prop :=
  CovTensor2ExtContMDiffAt (timeDerivAt gt t₀) x k

/-- Combined Cᵏ vocabulary for the trace Gram route. -/
def TraceMetricVariationEntriesExtContMDiffAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) (k : ℕ∞) : Prop :=
  CovTensor2ExtContMDiffAt h x k ∧ MetricExtContMDiffAt g x k

/-- Combined Cᵏ vocabulary specialized to a metric flow at `t₀`. -/
def TimeVariationTraceEntriesExtContMDiffAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (k : ℕ∞) : Prop :=
  TraceMetricVariationEntriesExtContMDiffAt
    (gt t₀) (timeDerivAt gt t₀) x k

/-- A `C²` canonical-entry tensor is pointwise differentiable in the old sense. -/
theorem covTensor2ExtDifferentiableAt_of_contMDiffAt_two
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hC2 : CovTensor2ExtContMDiffAt h x 2) :
    CovTensor2ExtDifferentiableAt h x := by
  intro p q
  exact (hC2 p q).mdifferentiableAt two_ne_zero

/--
A `C²` canonical-entry tensor has the old second-differentiability field
predicate.
-/
theorem covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hC2 : CovTensor2ExtContMDiffAt h x 2) :
    CovTensor2ExtSecondDifferentiableAt h x := by
  intro p q v
  have hv : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E v)) x := by
    simpa using (mdifferentiableAt_extend I E v)
  exact CovariantDerivative.mdiffAt_extDerivFun_apply (hC2 p q) hv

/-- A `C²` metric-entry class has the old metric second-differentiability predicate. -/
theorem metricExtSecondDifferentiableAt_of_contMDiffAt_two
    {g : ClosedSmoothRiemannianMetric n M} {x : M}
    (hC2 : MetricExtContMDiffAt g x 2) :
    MetricExtSecondDifferentiableAt g x := by
  intro p q v
  have hv : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E v)) x := by
    simpa using (mdifferentiableAt_extend I E v)
  exact CovariantDerivative.mdiffAt_extDerivFun_apply (hC2 p q) hv

/-- The combined C² vocabulary implies all older point-at-`x` entry classes. -/
theorem traceMetricVariationEntriesExtContMDiffAt_two_old_regularities
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hC2 : TraceMetricVariationEntriesExtContMDiffAt g h x 2) :
    CovTensor2ExtDifferentiableAt h x ∧
      CovTensor2ExtSecondDifferentiableAt h x ∧
      MetricExtSecondDifferentiableAt g x := by
  rcases hC2 with ⟨hh, hg⟩
  exact ⟨covTensor2ExtDifferentiableAt_of_contMDiffAt_two hh,
    covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two hh,
    metricExtSecondDifferentiableAt_of_contMDiffAt_two hg⟩

/-- The zero tensor satisfies the neighborhood scalar-entry vocabulary. -/
theorem covTensor2ExtContMDiffAt_zero (x : M) (k : ℕ∞) :
    CovTensor2ExtContMDiffAt
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x k := by
  intro p q
  simpa using
    (contMDiffAt_const :
      ContMDiffAt I 𝓘(ℝ) k (fun _ : M ↦ (0 : ℝ)) x)

/-- Smooth metrics satisfy the metric-entry C² vocabulary. -/
theorem metricExtContMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    MetricExtContMDiffAt g x 2 := by
  intro p q
  exact g.metric_pairing_contMDiffAt_two
    (FiberBundle.contMDiffAt_extend' (k := 2) I E p)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E q)

/-- Zero variation plus a smooth metric satisfies the combined trace-entry C² vocabulary. -/
theorem traceMetricVariationEntriesExtContMDiffAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    TraceMetricVariationEntriesExtContMDiffAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x 2 :=
  ⟨covTensor2ExtContMDiffAt_zero x 2,
    metricExtContMDiffAt_two g x⟩

/-- C² scalar-entry regularity for the metric time-variation tensor. -/
def TimeVariationExtSecondDifferentiableAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  CovTensor2ExtSecondDifferentiableAt (timeDerivAt gt t₀) x

/-- The time-variation C² vocabulary implies the older time-variation entry classes. -/
theorem timeVariationTraceEntriesExtContMDiffAt_two_old_regularities
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hC2 : TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2) :
    CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x ∧
      TimeVariationExtSecondDifferentiableAt gt t₀ x ∧
      MetricExtSecondDifferentiableAt (gt t₀) x := by
  simpa [TimeVariationExtSecondDifferentiableAt,
    TimeVariationTraceEntriesExtContMDiffAt]
    using
      traceMetricVariationEntriesExtContMDiffAt_two_old_regularities
        (g := gt t₀) (h := timeDerivAt gt t₀) (x := x) hC2

omit [T2Space M] in
/-- Static metric flows have zero time-variation entries, hence satisfy the Cᵏ vocabulary. -/
theorem timeVariationExtContMDiffAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) (k : ℕ∞) :
    TimeVariationExtContMDiffAt (fun _ : ℝ ↦ g) t₀ x k := by
  intro p q
  have hzero :
      (fun y : M ↦
        timeDerivAt (fun _ : ℝ ↦ g) t₀ y (extend E p y) (extend E q y)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    simp
  rw [hzero]
  exact contMDiffAt_const

/-- Static metric flows satisfy the combined trace-entry C² vocabulary. -/
theorem timeVariationTraceEntriesExtContMDiffAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TimeVariationTraceEntriesExtContMDiffAt (fun _ : ℝ ↦ g) t₀ x 2 := by
  exact
    ⟨timeVariationExtContMDiffAt_const (n := n) (M := M) g t₀ x 2,
      metricExtContMDiffAt_two g x⟩

/--
Second-order regularity of the scalar metric trace itself.

This is the scalar consequence the Gram route must ultimately derive from
`CovTensor2ExtSecondDifferentiableAt` and `MetricExtSecondDifferentiableAt`:
the directional derivative field of `tr_g h` along every canonical extension
is differentiable at the base point.
-/
def TraceMetricVariationExtSecondDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ w : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        extDerivFun (fun z : M ↦ traceMetricVariationAt g h z) y
          (extend E w y)) x

/--
Scalar `C²` regularity of the metric trace is enough for the closed
second-exterior-derivative predicate.
-/
theorem traceMetricVariationExtSecondDifferentiableAt_of_contMDiffAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hTrace :
      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ traceMetricVariationAt g h y) x) :
    TraceMetricVariationExtSecondDifferentiableAt g h x := by
  intro w
  have hW : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E w)) x := by
    simpa using (mdifferentiableAt_extend I E w)
  exact CovariantDerivative.mdiffAt_extDerivFun_apply hTrace hW

/-- Finite products of real-valued `C²` scalar fields are `C²`. -/
theorem contMDiffAt_two_finset_prod_real
    {ι : Type} [DecidableEq ι] {t : Finset ι}
    {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ t, ContMDiffAt I 𝓘(ℝ) 2 (f i) x) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ ∏ i ∈ t, f i y) x := by
  classical
  revert hf
  refine Finset.induction_on t ?base ?step
  · intro _hf
    simpa using
      (contMDiffAt_const :
        ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ (1 : ℝ)) x)
  · intro a s ha ih hf
    have hfa : ContMDiffAt I 𝓘(ℝ) 2 (f a) x :=
      hf a (Finset.mem_insert_self a s)
    have hs : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ ∏ i ∈ s, f i y) x :=
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hmul := hfa.smul hs
    simpa [Finset.prod_insert ha, smul_eq_mul] using hmul

/-- Finite sums of real-valued `C²` scalar fields are `C²`. -/
theorem contMDiffAt_two_finset_sum_real
    {ι : Type} [DecidableEq ι] {t : Finset ι}
    {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ t, ContMDiffAt I 𝓘(ℝ) 2 (f i) x) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ ∑ i ∈ t, f i y) x := by
  classical
  revert hf
  refine Finset.induction_on t ?base ?step
  · intro _hf
    simpa using
      (contMDiffAt_const :
        ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) x)
  · intro a s ha ih hf
    have hfa : ContMDiffAt I 𝓘(ℝ) 2 (f a) x :=
      hf a (Finset.mem_insert_self a s)
    have hs : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ ∑ i ∈ s, f i y) x :=
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hadd := hfa.add hs
    simpa [Finset.sum_insert ha] using hadd

/-- Determinants of finite matrix fields are `C²` when all entries are `C²`. -/
theorem contMDiffAt_two_matrix_det_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : M → Matrix ι ι ℝ} {x : M}
    (hA : ∀ i j, ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ A y i j) x) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (A y).det) x := by
  classical
  rw [show (fun y : M ↦ (A y).det) =
      fun y : M ↦ ∑ σ : Equiv.Perm ι,
        ((↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A y (σ i) i) by
    funext y
    rw [Matrix.det_apply']]
  have hsum : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ ∑ σ : Equiv.Perm ι,
        (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A y (σ i) i) x := by
    refine contMDiffAt_two_finset_sum_real (n := n) (M := M)
      (t := (Finset.univ : Finset (Equiv.Perm ι))) ?_
    intro σ _hσ
    have hprod : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ ∏ i, A y (σ i) i) x := by
      simpa using
        (contMDiffAt_two_finset_prod_real (n := n) (M := M)
        (t := (Finset.univ : Finset ι))
        (f := fun i y ↦ A y (σ i) i)
        (fun i _hi ↦ hA (σ i) i))
    have hconst : ContMDiffAt I 𝓘(ℝ) 2
        (fun _ : M ↦ (↑↑(Equiv.Perm.sign σ) : ℝ)) x := contMDiffAt_const
    simpa [smul_eq_mul] using hconst.smul hprod
  exact hsum

/-- Canonical Gram entries are `C²` under the metric-entry neighborhood class. -/
theorem gramMatrix_entry_contMDiffAt_two_of_metricExtContMDiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (hMetric : MetricExtContMDiffAt g x 2)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ gramMatrix g x y i j) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  simpa [gramMatrix, b] using hMetric (b i) (b j)

/-- The canonical Gram determinant is `C²` under the metric-entry neighborhood class. -/
theorem gramMatrix_det_contMDiffAt_two_of_metricExtContMDiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (hMetric : MetricExtContMDiffAt g x 2) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gramMatrix g x y).det) x :=
  contMDiffAt_two_matrix_det_of_entries
    (A := fun y : M ↦ gramMatrix g x y)
    (fun i j ↦
      gramMatrix_entry_contMDiffAt_two_of_metricExtContMDiffAt
        (g := g) (x := x) hMetric i j)

/-- Adjugate Gram entries are `C²` under the metric-entry neighborhood class. -/
theorem gramMatrix_adjugate_entry_contMDiffAt_two_of_metricExtContMDiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (hMetric : MetricExtContMDiffAt g x 2)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gramMatrix g x y).adjugate i j) x := by
  let row : Fin (Module.finrank ℝ (TM x)) → ℝ := Pi.single i (1 : ℝ)
  let A : M → Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
    fun y : M ↦ (gramMatrix g x y).updateRow j row
  have hentries : ∀ a b,
      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ A y a b) x := by
    intro a b
    by_cases ha : a = j
    · subst a
      simpa [A, Matrix.updateRow] using
        (contMDiffAt_const :
          ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ row b) x)
    · simpa [A, Matrix.updateRow, ha] using
        (gramMatrix_entry_contMDiffAt_two_of_metricExtContMDiffAt
          (g := g) (x := x) hMetric a b)
  have hdet : ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (A y).det) x :=
    contMDiffAt_two_matrix_det_of_entries (A := A) hentries
  exact hdet.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
    simp [A, row, Matrix.adjugate_apply])

/-- Inverse Gram entries are `C²` under the metric-entry neighborhood class. -/
theorem gramMatrix_inv_entry_contMDiffAt_two_of_metricExtContMDiffAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (hMetric : MetricExtContMDiffAt g x 2)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x := by
  have hdetInv : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ ((gramMatrix g x y).det)⁻¹) x :=
    (gramMatrix_det_contMDiffAt_two_of_metricExtContMDiffAt
      (g := g) (x := x) hMetric).inv₀
      (gramMatrix_at_base_det_ne_zero (g := g) (x := x))
  have hadj : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gramMatrix g x y).adjugate i j) x :=
    gramMatrix_adjugate_entry_contMDiffAt_two_of_metricExtContMDiffAt
      (g := g) (x := x) hMetric i j
  exact (hdetInv.smul hadj).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ by simp [Matrix.inv_def])

/--
The Gram-inverse trace formula gives scalar `C²` regularity of `tr_g h` from
neighborhood `C²` regularity of the canonical tensor and metric entries.
-/
theorem traceMetricVariationAt_contMDiffAt_two_of_entries
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hEntries : TraceMetricVariationEntriesExtContMDiffAt g h x 2)
    (B : ∀ y : M, LinearMap.BilinForm ℝ (TM y))
    (hB : ∀ y : M, ∀ p q : TM y, B y p q = h y p q) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ traceMetricVariationAt g h y) x := by
  classical
  rcases hEntries with ⟨hCov, hMetric⟩
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let rhs : M → ℝ := fun y : M ↦
    ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
      h y (gramFrame x y i) (gramFrame x y j)
  have hsum : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
          h y (gramFrame x y i) (gramFrame x y j)) x := by
    refine contMDiffAt_two_finset_sum_real (n := n) (M := M)
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
    intro i _hi
    have hinner : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ ∑ j, (gramMatrix g x y)⁻¹ i j *
          h y (gramFrame x y i) (gramFrame x y j)) x := by
      refine contMDiffAt_two_finset_sum_real (n := n) (M := M)
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
      intro j _hj
      have hinv : ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x :=
        gramMatrix_inv_entry_contMDiffAt_two_of_metricExtContMDiffAt
          (g := g) (x := x) hMetric i j
      have hh : ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x := by
        simpa [gramFrame, b, CovTensor2ExtContMDiffAt] using hCov (b i) (b j)
      simpa [smul_eq_mul] using hinv.smul hh
    exact hinner
  have hrhs : ContMDiffAt I 𝓘(ℝ) 2 rhs x :=
    by simpa [rhs] using hsum
  have heq : (fun y : M ↦ traceMetricVariationAt g h y) =ᶠ[nhds x] rhs := by
    exact (gramMatrix_eventually_isUnit (g := g) x).mono fun y hy ↦ by
      simpa [rhs] using
        (traceMetricVariationAt_eq_sum_gram_inv
          (g := g) (h := h) (x := x) (y := y) (hG := hy)
          (B := B y) (hB := hB y))
  exact hrhs.congr_of_eventuallyEq heq

/--
Trace second-differentiability follows from the strengthened neighborhood
entry vocabulary.
-/
theorem traceMetricVariationExtSecondDifferentiableAt_of_entries_contMDiffAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hEntries : TraceMetricVariationEntriesExtContMDiffAt g h x 2)
    (B : ∀ y : M, LinearMap.BilinForm ℝ (TM y))
    (hB : ∀ y : M, ∀ p q : TM y, B y p q = h y p q) :
    TraceMetricVariationExtSecondDifferentiableAt g h x :=
  traceMetricVariationExtSecondDifferentiableAt_of_contMDiffAt
    (g := g) (h := h) (x := x)
    (traceMetricVariationAt_contMDiffAt_two_of_entries
      (g := g) (h := h) (x := x) hEntries B hB)

/-- Time-variation specialization of the trace C² discharge. -/
theorem traceMetricVariationExtSecondDifferentiableAt_timeDeriv_of_entries_contMDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hEntries : TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2) :
    TraceMetricVariationExtSecondDifferentiableAt
      (gt t₀) (timeDerivAt gt t₀) x :=
  traceMetricVariationExtSecondDifferentiableAt_of_entries_contMDiffAt
    (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
    hEntries
    (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
    (by
      intro y p q
      rfl)

/-- First-slot trace form of `δΓ`, evaluated fiberwise. -/
noncomputable def deltaGammaFirstSlotTraceFieldAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (w : TM y) : ℝ :=
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, (Module.finBasis ℝ (TM y)).coord i
    (deltaGammaAt gt t₀ y ((Module.finBasis ℝ (TM y)) i) w)

/-- The first-slot `δΓ` endomorphism whose trace is
`deltaGammaFirstSlotTraceFieldAt`. -/
noncomputable def deltaGammaFirstSlotEndomorphismAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ y)
    (w : TM y) : TM y →ₗ[ℝ] TM y :=
  IsLinearMap.mk' (fun v ↦ deltaGammaAt gt t₀ y v w)
    ⟨(fun p q ↦ deltaGammaAt_add_left
        (gt := gt) (t₀ := t₀) (x := y) hΓ p q w),
      (fun c p ↦ deltaGammaAt_smul_left
        (gt := gt) (t₀ := t₀) (x := y) hΓ c p w)⟩

@[simp] theorem deltaGammaFirstSlotEndomorphismAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ y)
    (w v : TM y) :
    deltaGammaFirstSlotEndomorphismAt gt t₀ y hΓ w v =
      deltaGammaAt gt t₀ y v w := rfl

/-- The first-slot `δΓ` field is the ordinary trace of its first-slot
endomorphism. -/
theorem deltaGammaFirstSlotTraceFieldAt_eq_linearMap_trace
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ y)
    (w : TM y) :
    deltaGammaFirstSlotTraceFieldAt gt t₀ y w =
      LinearMap.trace ℝ (TM y)
        (deltaGammaFirstSlotEndomorphismAt gt t₀ y hΓ w) := by
  classical
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM y)
  unfold deltaGammaFirstSlotTraceFieldAt
  change (∑ i, b.coord i (deltaGammaAt gt t₀ y (b i) w)) =
    LinearMap.trace ℝ (TM y)
      (deltaGammaFirstSlotEndomorphismAt gt t₀ y hΓ w)
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rfl

/-- The first-slot `δΓ` trace can be computed in any finite basis. -/
theorem deltaGammaFirstSlotTraceFieldAt_eq_trace_in_basis
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ y)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM y)) (w : TM y) :
    deltaGammaFirstSlotTraceFieldAt gt t₀ y w =
      ∑ i, b.coord i (deltaGammaAt gt t₀ y (b i) w) := by
  classical
  rw [deltaGammaFirstSlotTraceFieldAt_eq_linearMap_trace
    (gt := gt) (t₀ := t₀) (y := y) hΓ w]
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rfl

/-- Trace-cyclicity cancellation for the closed first-slot `δΓ` trace. -/
theorem deltaGammaFirstSlotTrace_leviCivita_slot_cancel
    (g : ClosedSmoothRiemannianMetric n M)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (u w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      ∑ i, b.coord i
        (g.leviCivita
          (extend E (deltaGammaAt gt t₀ x (b i) w)) x u))
      =
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      ∑ i, b.coord i
        (deltaGammaAt gt t₀ x
          (g.leviCivita (extend E (b i)) x u) w)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let Γ : TM x → TM x := fun p ↦ g.leviCivita (extend E p) x u
  let Δ : TM x →ₗ[ℝ] TM x :=
    deltaGammaFirstSlotEndomorphismAt gt t₀ x hΓ w
  set Γlin : TM x →ₗ[ℝ] TM x :=
    IsLinearMap.mk' Γ
      ⟨(by
          intro p q
          change g.leviCivita (extend E (p + q)) x u =
            g.leviCivita (extend E p) x u +
              g.leviCivita (extend E q) x u
          rw [extend_tangent_add (x := x) p q]
          have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E p))
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E q))
          simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hadd),
        (by
          intro c p
          change g.leviCivita (extend E (c • p)) x u =
            c • g.leviCivita (extend E p) x u
          rw [extend_tangent_smul (x := x) c p]
          have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E p))
          simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hsmul)⟩
      with hΓlin
  change (∑ i, b.coord i (Γ (Δ (b i)))) =
    ∑ i, b.coord i (Δ (Γ (b i)))
  calc
    (∑ i, b.coord i (Γ (Δ (b i)))) =
        LinearMap.trace ℝ (TM x) (Γlin.comp Δ) := by
          rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
          rfl
    _ = LinearMap.trace ℝ (TM x) (Δ.comp Γlin) :=
          (LinearMap.trace_comp_comm' Γlin Δ).symm
    _ = ∑ i, b.coord i (Δ (Γ (b i))) := by
          rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
          rfl

/-- Anchored Gram-inverse form of the first-slot `δΓ` trace field.  This is
the moving-field analogue of `traceMetricVariationAt_eq_sum_gram_inv`. -/
theorem deltaGammaFirstSlotTraceFieldAt_eq_sum_gram_inv
    (g : ClosedSmoothRiemannianMetric n M)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    {x y : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ y)
    (hG : IsUnit (gramMatrix g x y))
    (w : TM y) :
    deltaGammaFirstSlotTraceFieldAt gt t₀ y w =
      ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
        g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i) w)
          (gramFrame x y j) := by
  classical
  letI : NormedAddCommGroup (TM y) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM y) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := gramFrameBasis g x y hG
  calc
    deltaGammaFirstSlotTraceFieldAt gt t₀ y w =
        ∑ i, b.coord i (deltaGammaAt gt t₀ y (b i) w) := by
          exact deltaGammaFirstSlotTraceFieldAt_eq_trace_in_basis
            (gt := gt) (t₀ := t₀) (y := y) hΓ b w
    _ = ∑ i,
        g.inner y (deltaGammaAt gt t₀ y (b i) w)
          (metricDualVectorAt g y (b.coord i)) := by
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          rw [coord_eq_inner_metricDualVectorAt_of_basis
            (g := g) (x := y) (b := b)]
    _ = ∑ i,
        g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i) w)
          (∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j) := by
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          simp [b, metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv]
    _ = ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
        g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i) w)
          (gramFrame x y j) := by
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          have hmap := map_sum
            (g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i) w))
            (fun j ↦ (gramMatrix g x y)⁻¹ i j • gramFrame x y j)
            Finset.univ
          simpa [smul_eq_mul] using hmap

/-- Lower-slot inner trace form of `δΓ`, evaluated fiberwise. -/
noncomputable def deltaGammaInnerTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (w : TM y) : ℝ :=
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM y)
  ∑ i, g.inner y
    (deltaGammaAt gt t₀ y (b i) (metricDualVectorAt g y (b.coord i))) w

/-- The lower-slot inner `δΓ` trace can be computed in any finite basis. -/
theorem deltaGammaInnerTraceFieldAt_eq_trace_in_basis
    (g : ClosedSmoothRiemannianMetric n M)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ y)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM y)) (w : TM y) :
    deltaGammaInnerTraceFieldAt g gt t₀ y w =
      ∑ i, g.inner y
        (deltaGammaAt gt t₀ y (b i)
          (metricDualVectorAt g y (b.coord i))) w := by
  classical
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let B : LinearMap.BilinForm ℝ (TM y) :=
    LinearMap.mk₂ ℝ (fun p q ↦ g.inner y (deltaGammaAt gt t₀ y p q) w)
      (fun p p' q ↦ by
        dsimp
        rw [deltaGammaAt_add_left
          (gt := gt) (t₀ := t₀) (x := y) hΓ p p' q]
        exact (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
          (map_add (g.inner y)
            (deltaGammaAt gt t₀ y p q)
            (deltaGammaAt gt t₀ y p' q)) : _))
      (fun c p q ↦ by
        dsimp
        rw [deltaGammaAt_smul_left
          (gt := gt) (t₀ := t₀) (x := y) hΓ c p q]
        simpa [smul_eq_mul] using
          (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
            (map_smul (g.inner y) c (deltaGammaAt gt t₀ y p q)) : _))
      (fun p q q' ↦ by
        dsimp
        rw [deltaGammaAt_add_right
          (gt := gt) (t₀ := t₀) (x := y) hΓ p q q']
        exact (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
          (map_add (g.inner y)
            (deltaGammaAt gt t₀ y p q)
            (deltaGammaAt gt t₀ y p q')) : _))
      (fun c p q ↦ by
        dsimp
        rw [deltaGammaAt_smul_right
          (gt := gt) (t₀ := t₀) (x := y) hΓ c p q]
        simpa [smul_eq_mul] using
          (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
            (map_smul (g.inner y) c (deltaGammaAt gt t₀ y p q)) : _))
  calc
    deltaGammaInnerTraceFieldAt g gt t₀ y w =
        metricTraceInBasisAt g y B (Module.finBasis ℝ (TM y)) := by
          unfold deltaGammaInnerTraceFieldAt metricTraceInBasisAt
          simp [B]
    _ = metricTraceInBasisAt g y B b := by
          exact metricTraceInBasisAt_eq_metricTraceInBasisAt
            (g := g) (x := y) (B := B)
            (b := Module.finBasis ℝ (TM y)) (c := b)
    _ = ∑ i, g.inner y
        (deltaGammaAt gt t₀ y (b i)
          (metricDualVectorAt g y (b.coord i))) w := by
          unfold metricTraceInBasisAt
          simp [B]

/-- Anchored Gram-inverse form of the lower-slot inner `δΓ` trace field. -/
theorem deltaGammaInnerTraceFieldAt_eq_sum_gram_inv
    (g : ClosedSmoothRiemannianMetric n M)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    {x y : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ y)
    (hG : IsUnit (gramMatrix g x y))
    (w : TM y) :
    deltaGammaInnerTraceFieldAt g gt t₀ y w =
      ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
        g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i)
          (gramFrame x y j)) w := by
  classical
  letI : NormedAddCommGroup (TM y) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM y) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := gramFrameBasis g x y hG
  calc
    deltaGammaInnerTraceFieldAt g gt t₀ y w =
        ∑ i, g.inner y
          (deltaGammaAt gt t₀ y (b i)
            (metricDualVectorAt g y (b.coord i))) w := by
          exact deltaGammaInnerTraceFieldAt_eq_trace_in_basis
            (g := g) (gt := gt) (t₀ := t₀) (y := y) hΓ b w
    _ = ∑ i, g.inner y
          (deltaGammaAt gt t₀ y (gramFrame x y i)
            (∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j)) w := by
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          simp [b, metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv]
    _ = ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
        g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i)
          (gramFrame x y j)) w := by
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          let L : TM y →ₗ[ℝ] ℝ :=
            IsLinearMap.mk'
              (fun q ↦ g.inner y
                (deltaGammaAt gt t₀ y (gramFrame x y i) q) w)
              ⟨(by
                  intro q q'
                  rw [deltaGammaAt_add_right
                    (gt := gt) (t₀ := t₀) (x := y) hΓ
                    (gramFrame x y i) q q']
                  exact (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
                    (map_add (g.inner y)
                      (deltaGammaAt gt t₀ y (gramFrame x y i) q)
                      (deltaGammaAt gt t₀ y (gramFrame x y i) q')) : _)),
                (by
                  intro c q
                  rw [deltaGammaAt_smul_right
                    (gt := gt) (t₀ := t₀) (x := y) hΓ c
                    (gramFrame x y i) q]
                  simpa [smul_eq_mul] using
                    (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
                      (map_smul (g.inner y) c
                        (deltaGammaAt gt t₀ y (gramFrame x y i) q)) : _))⟩
          change L (∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j) =
            ∑ j, (gramMatrix g x y)⁻¹ i j *
              L (gramFrame x y j)
          have hmap :=
            map_sum L
              (fun j ↦ (gramMatrix g x y)⁻¹ i j • gramFrame x y j)
              Finset.univ
          simpa [smul_eq_mul] using hmap

/-- Differentiability of the closed first-slot `δΓ` trace-form field. -/
def DeltaGammaFirstSlotTraceFieldDifferentiableAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ w : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y)) x

/-- Differentiability of the closed inner `δΓ` trace-form field. -/
def DeltaGammaInnerTraceFieldDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ w : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ deltaGammaInnerTraceFieldAt g gt t₀ y (extend E w y)) x

/--
Derivative identification for the first-slot `δΓ` trace-form field.

It says that the covariant derivative of the one-form field obtained by tracing
the first `δΓ` slot is represented by `deltaGammaContractionDerivAt`.
-/
def DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  ∀ u w : TM x,
    deltaGammaContractionDerivAt gt t₀ x u w =
      extDerivFun
          (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
          x u
        - deltaGammaFirstSlotTraceFieldAt gt t₀ x
          (g.leviCivita (extend E w) x u)

/--
Scalar-entry derivative bridge for the first-slot `δΓ` trace route.

For fixed base vectors `p`, `q`, and `w`, it identifies the exterior derivative
of the scalar pairing
`y ↦ g(δΓ_y(extend p, extend w), extend q)` with the covariant derivative
`covDeltaGammaDerivAt` plus the three Levi-Civita slot corrections.
-/
structure DeltaGammaEntryDerivativeBridgeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop where
  mdifferentiable :
    ∀ p q w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          (gt t₀).inner y
            (deltaGammaAt gt t₀ y (extend E p y) (extend E w y))
            (extend E q y)) x
  extDeriv_eq :
    ∀ u p q w : TM x,
      extDerivFun
        (fun y : M ↦
          (gt t₀).inner y
            (deltaGammaAt gt t₀ y (extend E p y) (extend E w y))
            (extend E q y)) x u
      =
        (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u p w) q
        + (gt t₀).inner x
            (deltaGammaAt gt t₀ x ((gt t₀).leviCivita (extend E p) x u) w) q
        + (gt t₀).inner x
            (deltaGammaAt gt t₀ x p ((gt t₀).leviCivita (extend E w) x u)) q
        + (gt t₀).inner x
            (deltaGammaAt gt t₀ x p w)
            ((gt t₀).leviCivita (extend E q) x u)

/-- Static sanity witness for the `δΓ` scalar-entry derivative bridge. -/
theorem deltaGammaEntryDerivativeBridgeAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    DeltaGammaEntryDerivativeBridgeAt (fun _ : ℝ ↦ g) t₀ x where
  mdifferentiable := by
    intro p q w
    have hzero :
        (fun y : M ↦
          g.inner y
            (deltaGammaAt (fun _ : ℝ ↦ g) t₀ y (extend E p y) (extend E w y))
            (extend E q y)) = fun _ : M ↦ (0 : ℝ) := by
      funext y
      simp
    rw [hzero]
    exact mdifferentiableAt_const
  extDeriv_eq := by
    intro u p q w
    have hzero :
        (fun y : M ↦
          g.inner y
            (deltaGammaAt (fun _ : ℝ ↦ g) t₀ y (extend E p y) (extend E w y))
            (extend E q y)) = fun _ : M ↦ (0 : ℝ) := by
      funext y
      simp
    rw [hzero]
    simp [extDerivFun_zero_at]

/--
Triple product-rule bridge for scalar `δΓ` entries.

The only analytic input is differentiability of the vector-valued
`δΓ(extend p, extend w)` field. Metric compatibility differentiates the
pairing, and the definition of `covDeltaGammaDerivAt` supplies the two
extension-slot corrections.
-/
theorem deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hδ : DeltaGammaFieldMDifferentiableAt gt t₀ x) :
    DeltaGammaEntryDerivativeBridgeAt gt t₀ x where
  mdifferentiable := by
    intro p q w
    exact (gt t₀).metric_pairing_mdiffAt
      (hδ p w)
      (mdifferentiableAt_extend I E q)
  extDeriv_eq := by
    intro u p q w
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let A : ∀ y : M, TM y := deltaGammaFieldAt gt t₀ p w
    let B : ∀ y : M, TM y := extend E q
    have hA :
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% A) x := by
      simpa [A] using hδ p w
    have hB :
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% B) x := by
      simpa [B] using (mdifferentiableAt_extend I E q)
    have hcompat :=
      g.leviCivita_metricCompatibleAt x
        (Y := A) (Z := B)
        (by simpa [MDiffAtTangentField] using hA)
        (by simpa [MDiffAtTangentField] using hB)
        u
    have hcov :
        g.leviCivita A x u =
          covDeltaGammaDerivAt gt t₀ x u p w
            + deltaGammaAt gt t₀ x
                (g.leviCivita (extend E p) x u) w
            + deltaGammaAt gt t₀ x p
                (g.leviCivita (extend E w) x u) := by
      unfold covDeltaGammaDerivAt
      change g.leviCivita A x u =
        (g.leviCivita A x u
          - deltaGammaAt gt t₀ x (g.leviCivita (extend E p) x u) w
          - deltaGammaAt gt t₀ x p (g.leviCivita (extend E w) x u))
        + deltaGammaAt gt t₀ x (g.leviCivita (extend E p) x u) w
        + deltaGammaAt gt t₀ x p (g.leviCivita (extend E w) x u)
      abel
    change
      extDerivFun (fun y : M ↦ g.inner y (A y) (B y)) x u =
        g.inner x (covDeltaGammaDerivAt gt t₀ x u p w) q
        + g.inner x
            (deltaGammaAt gt t₀ x (g.leviCivita (extend E p) x u) w) q
        + g.inner x
            (deltaGammaAt gt t₀ x p (g.leviCivita (extend E w) x u)) q
        + g.inner x (deltaGammaAt gt t₀ x p w)
            (g.leviCivita (extend E q) x u)
    rw [hcompat, hcov]
    simp [A, B, g, deltaGammaFieldAt, extend_apply_self]

/--
The inner-trace route uses the same scalar `δΓ` entries as the first-slot
route, with the paired output vector occupying the bridge's `q` slot.
-/
theorem deltaGammaInnerTraceEntry_mdiffAt_of_entryBridge
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (p q w : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        (gt t₀).inner y
          (deltaGammaAt gt t₀ y (extend E p y) (extend E q y))
          (extend E w y)) x := by
  simpa using hBridge.mdifferentiable p w q

/--
Exterior-derivative form of the reused scalar-entry bridge for the
inner-trace route.
-/
theorem deltaGammaInnerTraceEntry_extDeriv_eq_of_entryBridge
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (u p q w : TM x) :
    extDerivFun
      (fun y : M ↦
        (gt t₀).inner y
          (deltaGammaAt gt t₀ y (extend E p y) (extend E q y))
          (extend E w y)) x u
      =
        (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u p q) w
        + (gt t₀).inner x
            (deltaGammaAt gt t₀ x
              ((gt t₀).leviCivita (extend E p) x u) q) w
        + (gt t₀).inner x
            (deltaGammaAt gt t₀ x p
              ((gt t₀).leviCivita (extend E q) x u)) w
        + (gt t₀).inner x
            (deltaGammaAt gt t₀ x p q)
            ((gt t₀).leviCivita (extend E w) x u) := by
  simpa using hBridge.extDeriv_eq u p w q

/-- Static sanity witness for the first-slot trace-field covariant derivative. -/
theorem deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt
      (fun _ : ℝ ↦ g) t₀ x := by
  intro u w
  have hfield :
      (fun y : M ↦
        deltaGammaFirstSlotTraceFieldAt (fun _ : ℝ ↦ g) t₀ y (extend E w y)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    simp [deltaGammaFirstSlotTraceFieldAt]
  have hpoint :
      deltaGammaFirstSlotTraceFieldAt (fun _ : ℝ ↦ g) t₀ x
        (g.leviCivita (extend E w) x u) = 0 := by
    simp [deltaGammaFirstSlotTraceFieldAt]
  change deltaGammaContractionDerivAt (fun _ : ℝ ↦ g) t₀ x u w =
    extDerivFun
        (fun y : M ↦
          deltaGammaFirstSlotTraceFieldAt (fun _ : ℝ ↦ g) t₀ y (extend E w y))
        x u
      - deltaGammaFirstSlotTraceFieldAt (fun _ : ℝ ↦ g) t₀ x
        (g.leviCivita (extend E w) x u)
  rw [deltaGammaContractionDerivAt_const, hfield, hpoint]
  simp [extDerivFun_zero_at]

/--
Hessian identification for the covariant derivative of the first-slot `δΓ`
trace-form field.
-/
def DeltaGammaFirstSlotTraceFieldHessianAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  ∀ u w : TM x,
      extDerivFun
          (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
          x u
        - deltaGammaFirstSlotTraceFieldAt gt t₀ x
          (g.leviCivita (extend E w) x u)
      =
        (1 / 2 : ℝ) * g.hessianAt f x u w

/--
The Gram-inverse scalar trace formula gives an honest differentiability proof
for `tr_g h` from canonical-extension scalar regularity.  The fiber value of
`h` is supplied as bilinear witnesses so the basis-invariant trace identity can
be used near `x`.
-/
theorem traceMetricVariationAt_mdiffAt_of_covTensor2ExtDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (B : ∀ y : M, LinearMap.BilinForm ℝ (TM y))
    (hB : ∀ y : M, ∀ p q : TM y, B y p q = h y p q) :
    MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ traceMetricVariationAt g h y) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let rhs : M → ℝ := fun y : M ↦
    ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
      h y (gramFrame x y i) (gramFrame x y j)
  have hsum : MDifferentiableAt I 𝓘(ℝ)
      (∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))),
        fun y : M ↦ ∑ j, (gramMatrix g x y)⁻¹ i j *
          h y (gramFrame x y i) (gramFrame x y j)) x := by
    refine MDifferentiableAt.sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
    intro i _hi
    have hinner : MDifferentiableAt I 𝓘(ℝ)
        (∑ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))),
          fun y : M ↦ (gramMatrix g x y)⁻¹ i j *
            h y (gramFrame x y i) (gramFrame x y j)) x := by
      refine MDifferentiableAt.sum
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
      intro j _hj
      have hinv : MDifferentiableAt I 𝓘(ℝ)
          (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x :=
        gramMatrix_inv_entry_mdiffAt (g := g) x i j
      have hh : MDifferentiableAt I 𝓘(ℝ)
          (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x := by
        simpa [gramFrame, b, CovTensor2ExtDifferentiableAt] using hDiff (b i) (b j)
      exact hinv.mul hh
    exact hinner.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by simp)
  have hrhs : MDifferentiableAt I 𝓘(ℝ) rhs x :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by simp [rhs])
  have heq : (fun y : M ↦ traceMetricVariationAt g h y) =ᶠ[nhds x] rhs := by
    exact (gramMatrix_eventually_isUnit (g := g) x).mono fun y hy ↦ by
      simpa [rhs] using
        (traceMetricVariationAt_eq_sum_gram_inv
          (g := g) (h := h) (x := x) (y := y) (hG := hy)
          (B := B y) (hB := hB y))
  exact hrhs.congr_of_eventuallyEq heq

/--
Exterior-derivative bridge for the Gram-inverse scalar trace formula.  Near
`x`, `tr_g h` is the scalar Gram RHS, so their exterior derivatives at `x`
agree.
-/
theorem traceMetricVariationAt_extDerivFun_eq_gram_rhs
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (B : ∀ y : M, LinearMap.BilinForm ℝ (TM y))
    (hB : ∀ y : M, ∀ p q : TM y, B y p q = h y p q)
    (w : TM x) :
    extDerivFun (fun y : M ↦ traceMetricVariationAt g h y) x w =
      extDerivFun
        (fun y : M ↦ ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
          h y (gramFrame x y i) (gramFrame x y j)) x w := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let rhs : M → ℝ := fun y : M ↦
    ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
      h y (gramFrame x y i) (gramFrame x y j)
  have heq : (fun y : M ↦ traceMetricVariationAt g h y) =ᶠ[nhds x] rhs := by
    exact (gramMatrix_eventually_isUnit (g := g) x).mono fun y hy ↦ by
      simpa [rhs] using
        (traceMetricVariationAt_eq_sum_gram_inv
          (g := g) (h := h) (x := x) (y := y) (hG := hy)
          (B := B y) (hB := hB y))
  exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L w)
    (CovariantDerivative.extDerivFun_congr heq)

/-- Product-rule expansion of the differentiated canonical Gram RHS. -/
theorem gram_rhs_extDerivFun_eq_sum_product
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (w : TM x) :
    extDerivFun
        (fun y : M ↦ ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
          h y (gramFrame x y i) (gramFrame x y j)) x w =
      ∑ i, ∑ j,
        ((gramMatrix g x x)⁻¹ i j *
          extDerivFun
            (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w
         + extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
            h x (gramFrame x x i) (gramFrame x x j)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let term : Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) → M → ℝ :=
    fun i j y ↦ (gramMatrix g x y)⁻¹ i j *
      h y (gramFrame x y i) (gramFrame x y j)
  have htermDiff : ∀ i j,
      MDifferentiableAt I 𝓘(ℝ) (term i j) x := by
    intro i j
    have hinv : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x :=
      gramMatrix_inv_entry_mdiffAt (g := g) x i j
    have hh : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x := by
      simpa [gramFrame, b, CovTensor2ExtDifferentiableAt] using hDiff (b i) (b j)
    exact hinv.mul hh
  have hinnerDiff : ∀ i,
      MDifferentiableAt I 𝓘(ℝ) (∑ j, term i j) x := by
    intro i
    exact MDifferentiableAt.sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
      (fun j _hj ↦ htermDiff i j)
  have houter := extDerivFun_sum_at
    (n := n) (M := M)
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
    (f := fun i ↦ ∑ j, term i j)
    (x := x)
    (fun i _hi ↦ hinnerDiff i) w
  have hfun :
      (fun y : M ↦ ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
        h y (gramFrame x y i) (gramFrame x y j)) =
        (∑ i, ∑ j, term i j) := by
    funext y
    simp [term]
  rw [hfun]
  change extDerivFun (∑ i, ∑ j, term i j) x w =
    ∑ i, ∑ j,
      ((gramMatrix g x x)⁻¹ i j *
        extDerivFun
          (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w
       + extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
          h x (gramFrame x x i) (gramFrame x x j))
  rw [houter]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  have hinner := extDerivFun_sum_at
    (n := n) (M := M)
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
    (f := fun j ↦ term i j)
    (x := x)
    (fun j _hj ↦ htermDiff i j) w
  rw [hinner]
  refine Finset.sum_congr rfl fun j _hj ↦ ?_
  have hinv : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x :=
    gramMatrix_inv_entry_mdiffAt (g := g) x i j
  have hh : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x := by
    simpa [gramFrame, b, CovTensor2ExtDifferentiableAt] using hDiff (b i) (b j)
  have hmul := CovariantDerivative.extDerivFun_mul
    (p := fun y : M ↦ (gramMatrix g x y)⁻¹ i j)
    (q := fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j))
    (x := x) hinv hh w
  simpa [term] using hmul

/--
Fixed-vector spatial differentiability for a raw `(0,2)` variation tensor.

Unlike `TraceMetricVariationDerivAt`, this says only that every scalar
component `y ↦ h_y(p,q)` with fixed model vectors `p q : E` is
manifold-differentiable at `x`; it contains no covariant-derivative or trace
identity.
-/
def VariationSpatiallyDifferentiableAt
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ p q : E,
    MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ h y p q) x

/--
Honest regularity class for time-variation tensors whose fixed-vector
components are spatially differentiable.
-/
def TimeVariationSpatiallyDifferentiableAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ p q : E,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ timeDerivAt gt t₀ y p q) x

omit [T2Space M] in
theorem variationSpatiallyDifferentiableAt_timeDeriv_of_regular
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hreg : TimeVariationSpatiallyDifferentiableAt gt t₀ x) :
    VariationSpatiallyDifferentiableAt (timeDerivAt gt t₀) x := by
  intro p q
  exact hreg p q

omit [T2Space M] [IsManifold I ∞ M] in
theorem variationSpatiallyDifferentiableAt_static
    (H : E → E → ℝ) (x : M) :
    VariationSpatiallyDifferentiableAt
      (fun y : M ↦ fun p q : TM y ↦ H p q) x := by
  intro p q
  simpa [VariationSpatiallyDifferentiableAt] using
    (mdifferentiableAt_const (c := H p q) (x := x))

omit [T2Space M] [IsManifold I ∞ M] in
theorem variationSpatiallyDifferentiableAt_zero (x : M) :
    VariationSpatiallyDifferentiableAt
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x := by
  simpa using
    (variationSpatiallyDifferentiableAt_static
      (n := n) (M := M) (fun _ _ : E ↦ (0 : ℝ)) x)

omit [T2Space M] in
theorem timeVariationSpatiallyDifferentiableAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TimeVariationSpatiallyDifferentiableAt (fun _ : ℝ ↦ g) t₀ x := by
  intro p q
  have hfun :
      (fun y : M ↦ timeDerivAt (fun _ : ℝ ↦ g) t₀ y p q) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    exact timeDerivAt_const g t₀ y p q
  rw [hfun]
  exact mdifferentiableAt_const

omit [T2Space M] in
theorem variationSpatiallyDifferentiableAt_const_timeDeriv
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    VariationSpatiallyDifferentiableAt (timeDerivAt (fun _ : ℝ ↦ g) t₀) x :=
  variationSpatiallyDifferentiableAt_timeDeriv_of_regular
    (timeVariationSpatiallyDifferentiableAt_const (n := n) (M := M) g t₀ x)

/--
Spatial derivative of the metric pairing in the closed vocabulary, evaluated on
canonical extensions of two fixed tangent vectors.
-/
noncomputable def spatialMetricDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v p q : TM x) : ℝ :=
  extDerivFun (fun y : M ↦ g.inner y (extend E p y) (extend E q y)) x v

/--
Metric compatibility for the closed spatial metric derivative, unwrapped on
canonical extensions.
-/
theorem spatialMetricDerivAt_eq_leviCivita
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v p q : TM x) :
    spatialMetricDerivAt g x v p q =
      g.inner x (g.leviCivita (extend E p) x v) q +
        g.inner x p (g.leviCivita (extend E q) x v) := by
  unfold spatialMetricDerivAt
  have h := g.leviCivita_metricCompatibleAt x
    (Y := extend E p) (Z := extend E q)
    (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E p))
    (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E q))
    v
  simpa using h

/-- The exterior derivative of a canonical Gram entry is the closed spatial
metric derivative of the seeded basis vectors. -/
theorem gramMatrix_extDerivFun_eq_spatialMetricDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v : TM x) (i j : Fin (Module.finrank ℝ (TM x))) :
    extDerivFun (fun y : M ↦ gramMatrix g x y i j) x v =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E);
      spatialMetricDerivAt g x v ((Module.finBasis ℝ (TM x)) i)
        ((Module.finBasis ℝ (TM x)) j)) := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  simp [gramMatrix, spatialMetricDerivAt]

/-- Gram-entry derivative in Levi-Civita correction form. -/
theorem gramMatrix_extDerivFun_eq_leviCivita
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v : TM x) (i j : Fin (Module.finrank ℝ (TM x))) :
    extDerivFun (fun y : M ↦ gramMatrix g x y i j) x v =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E);
      g.inner x
        (g.leviCivita (extend E ((Module.finBasis ℝ (TM x)) i)) x v)
        ((Module.finBasis ℝ (TM x)) j)
        +
      g.inner x ((Module.finBasis ℝ (TM x)) i)
        (g.leviCivita (extend E ((Module.finBasis ℝ (TM x)) j)) x v)) := by
  rw [gramMatrix_extDerivFun_eq_spatialMetricDerivAt,
    spatialMetricDerivAt_eq_leviCivita]

/-- The covector `q ↦ g(p, ∇ᵥ q)` in the closed canonical-extension vocabulary. -/
noncomputable def leviCivitaRightCovectorLinearAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v p : TM x) : TM x →ₗ[ℝ] ℝ where
  toFun := fun q : TM x ↦ g.inner x p (g.leviCivita (extend E q) x v)
  map_add' := by
    intro q₁ q₂
    have hΓ :
        g.leviCivita (extend E (q₁ + q₂)) x v =
          g.leviCivita (extend E q₁) x v +
            g.leviCivita (extend E q₂) x v := by
      rw [extend_tangent_add (x := x) q₁ q₂]
      have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
        (by simpa [MDiffAtTangentField] using
          (mdifferentiableAt_extend I E q₁))
        (by simpa [MDiffAtTangentField] using
          (mdifferentiableAt_extend I E q₂))
      simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hadd
    rw [hΓ]
    exact map_add (g.inner x p) _ _
  map_smul' := by
    intro c q
    have hΓ :
        g.leviCivita (extend E (c • q)) x v =
          c • g.leviCivita (extend E q) x v := by
      rw [extend_tangent_smul (x := x) c q]
      have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
        (by simpa [MDiffAtTangentField] using
          (mdifferentiableAt_extend I E q))
      simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hsmul
    rw [hΓ]
    exact map_smul (g.inner x p) c _

/-- Continuous-linear packaging of `q ↦ g(p, ∇ᵥ q)`. -/
noncomputable def leviCivitaRightCovectorAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v p : TM x) : TM x →L[ℝ] ℝ :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (leviCivitaRightCovectorLinearAt g x v p)

/--
Closed algebraic candidate for the spatial derivative of a raised fixed
covector.  The two terms are the two metric-compatibility corrections.
-/
noncomputable def spatialMetricDualVectorDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (v : TM x)
    (φ : TM x →L[ℝ] ℝ) : TM x :=
  let p : TM x := g.metricRaiseContinuousAt x φ;
  let ψ : Module.Dual ℝ (TM x) := leviCivitaRightCovectorAt g x v p;
  -g.leviCivita (extend E p) x v - metricDualVectorAt g x ψ

/--
Pairing the closed spatial raised-covector derivative candidate with `g`
recovers `-∂ᵥ g(♯φ, -)`.
-/
theorem spatialMetricDualVectorDerivAt_inner_apply
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (v : TM x)
    (φ : TM x →L[ℝ] ℝ) (z : TM x) :
    g.inner x (spatialMetricDualVectorDerivAt g x v φ) z =
      -spatialMetricDerivAt g x v (g.metricRaiseContinuousAt x φ) z := by
  let p : TM x := g.metricRaiseContinuousAt x φ
  let ψ : Module.Dual ℝ (TM x) := leviCivitaRightCovectorAt g x v p
  have hψ : g.inner x (metricDualVectorAt g x ψ) z = ψ z :=
    metricDualVectorAt_inner_apply g x ψ z
  unfold spatialMetricDualVectorDerivAt
  simp only [map_sub, map_neg]
  change -g.inner x (g.leviCivita (extend E p) x v) z -
      g.inner x (metricDualVectorAt g x ψ) z =
    -spatialMetricDerivAt g x v p z
  rw [hψ]
  change -g.inner x (g.leviCivita (extend E p) x v) z -
      g.inner x p (g.leviCivita (extend E z) x v) =
    -spatialMetricDerivAt g x v p z
  rw [spatialMetricDerivAt_eq_leviCivita]
  ring

omit [T2Space M] [IsManifold I ∞ M] in
theorem tensor2AddLeft_zero :
    Tensor2AddLeft (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
  intro y p₁ p₂ q
  simp

omit [T2Space M] [IsManifold I ∞ M] in
theorem tensor2SMulLeft_zero :
    Tensor2SMulLeft (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
  intro y c p q
  simp

omit [T2Space M] [IsManifold I ∞ M] in
theorem tensor2AddRight_zero :
    Tensor2AddRight (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
  intro y p q₁ q₂
  simp

omit [T2Space M] [IsManifold I ∞ M] in
theorem tensor2SMulRight_zero :
    Tensor2SMulRight (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
  intro y c p q
  simp

omit [T2Space M] in
theorem covTensor2ExtDifferentiableAt_zero (x : M) :
    CovTensor2ExtDifferentiableAt
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x := by
  intro p q
  simpa [CovTensor2ExtDifferentiableAt] using
    (mdifferentiableAt_const (c := (0 : ℝ)) (x := x))

omit [T2Space M] in
theorem covTensor2ExtSecondDifferentiableAt_zero (x : M) :
    CovTensor2ExtSecondDifferentiableAt
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x := by
  intro p q v
  have hfun :
      (fun y : M ↦
        extDerivFun
          (fun z : M ↦ (0 : ℝ)) y (extend E v y)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    simp [extDerivFun_zero_at]
  rw [hfun]
  exact mdifferentiableAt_const

omit [T2Space M] in
theorem timeVariationExtSecondDifferentiableAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TimeVariationExtSecondDifferentiableAt (fun _ : ℝ ↦ g) t₀ x := by
  intro p q v
  have hfun :
      (fun y : M ↦
        extDerivFun
          (fun z : M ↦
            timeDerivAt (fun _ : ℝ ↦ g) t₀ z (extend E p z) (extend E q z))
          y (extend E v y)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    have hzero :
        (fun z : M ↦
          timeDerivAt (fun _ : ℝ ↦ g) t₀ z (extend E p z) (extend E q z)) =
          fun _ : M ↦ (0 : ℝ) := by
      funext z
      simp
    rw [hzero]
    simp [extDerivFun_zero_at]
  rw [hfun]
  exact mdifferentiableAt_const

omit [T2Space M] in
theorem tensor2AddLeft_timeDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y) :
    Tensor2AddLeft (timeDerivAt gt t₀) := by
  intro y p₁ p₂ q
  exact timeDerivAt_add_left (hgt y) p₁ p₂ q

omit [T2Space M] in
theorem tensor2SMulLeft_timeDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y) :
    Tensor2SMulLeft (timeDerivAt gt t₀) := by
  intro y c p q
  exact timeDerivAt_smul_left (hgt y) c p q

omit [T2Space M] in
theorem tensor2AddRight_timeDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y) :
    Tensor2AddRight (timeDerivAt gt t₀) := by
  intro y p q₁ q₂
  exact timeDerivAt_add_right (hgt y) p q₁ q₂

omit [T2Space M] in
theorem tensor2SMulRight_timeDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y) :
    Tensor2SMulRight (timeDerivAt gt t₀) := by
  intro y c p q
  exact timeDerivAt_smul_right (hgt y) c p q

/--
Covariant derivative of a raw `(0,2)` variation tensor:
`(∇_v h)(p,q) = D_v(h(p,q)) - h(∇_v p,q) - h(p,∇_v q)`.

The tensor slots are evaluated on canonical extensions, matching the rest of
this closed-manifold scalar-variation layer.
-/
noncomputable def covTensor2DerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (v p q : TM x) : ℝ :=
  extDerivFun (fun y : M ↦ h y (extend E p y) (extend E q y)) x v
    - h x ((g.leviCivita (extend E p) x v)) q
    - h x p ((g.leviCivita (extend E q) x v))

/-- Unfolding bridge from the flat derivative of `h` on canonical extension
slots to its covariant derivative and the two Levi-Civita slot corrections. -/
theorem extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (v p q : TM x) :
    extDerivFun (fun y : M ↦ h y (extend E p y) (extend E q y)) x v =
      covTensor2DerivAt g h x v p q
        + h x ((g.leviCivita (extend E p) x v)) q
        + h x p ((g.leviCivita (extend E q) x v)) := by
  unfold covTensor2DerivAt
  ring

theorem covTensor2DerivAt_timeDeriv_symm
    (g : ClosedSmoothRiemannianMetric n M)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v p q : TM x) :
    covTensor2DerivAt g (timeDerivAt gt t₀) x v p q =
      covTensor2DerivAt g (timeDerivAt gt t₀) x v q p := by
  unfold covTensor2DerivAt
  have hfun :
      (fun y : M ↦ timeDerivAt gt t₀ y (extend E p y) (extend E q y)) =
        fun y : M ↦ timeDerivAt gt t₀ y (extend E q y) (extend E p y) := by
    funext y
    exact timeDerivAt_symm gt t₀ y (extend E p y) (extend E q y)
  rw [hfun]
  rw [timeDerivAt_symm gt t₀ x (g.leviCivita (extend E p) x v) q]
  rw [timeDerivAt_symm gt t₀ x p (g.leviCivita (extend E q) x v)]
  ring

theorem covTensor2DerivAt_ricciVariationField_symm
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v p q : TM x) :
    covTensor2DerivAt g (ricciVariationField g) x v p q =
      covTensor2DerivAt g (ricciVariationField g) x v q p := by
  unfold covTensor2DerivAt ricciVariationField
  have hfun :
      (fun y : M ↦ g.ricciAt y (extend E p y) (extend E q y)) =
        fun y : M ↦ g.ricciAt y (extend E q y) (extend E p y) := by
    funext y
    exact g.ricciAt_symm y (extend E p y) (extend E q y)
  rw [hfun]
  rw [g.ricciAt_symm x (g.leviCivita (extend E p) x v) q]
  rw [g.ricciAt_symm x p (g.leviCivita (extend E q) x v)]
  ring

/--
Covariant derivative of the closed curvature operator in anchored
extend-frame slots.

This is the intrinsic closed analogue of the model-space `covCurvDeriv`.
The remaining native Bianchi work is to identify this expression with the
extend-frame derivative expansion and prove its cyclic second-Bianchi sum.
-/
noncomputable def closedCurvatureCovDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w z : TM x) : TM x :=
  let R : ∀ y : M, TM y :=
    fun y ↦
      CovariantDerivative.curvatureOp g.leviCivita
        (extend E u) (extend E w) (extend E z) y
  g.leviCivita R x v
    - CovariantDerivative.curvatureOp g.leviCivita
        (extend E (g.leviCivita (extend E u) x v))
        (extend E w) (extend E z) x
    - CovariantDerivative.curvatureOp g.leviCivita
        (extend E u)
        (extend E (g.leviCivita (extend E w) x v))
        (extend E z) x
    - CovariantDerivative.curvatureOp g.leviCivita
        (extend E u) (extend E w)
        (extend E (g.leviCivita (extend E z) x v)) x

omit [T2Space M] in
theorem curvatureOp_congr_fst_of_value_eq
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x : M} {X X' Y Z : ∀ y : M, TM y}
    (hreg : CovariantDerivative.DerivRegularAt cov Z x)
    (hX : MDiffAtTangentField X x) (hX' : MDiffAtTangentField X' x)
    (hY : MDiffAtTangentField Y x) (hXX' : X x = X' x) :
    CovariantDerivative.curvatureOp cov X Y Z x =
      CovariantDerivative.curvatureOp cov X' Y Z x := by
  rw [← CovariantDerivative.curvatureTensorAt_apply (cov := cov) (hreg := hreg)
      (X := X) (Y := Y)
      (by simpa [MDiffAtTangentField] using hX)
      (by simpa [MDiffAtTangentField] using hY),
    ← CovariantDerivative.curvatureTensorAt_apply (cov := cov) (hreg := hreg)
      (X := X') (Y := Y)
      (by simpa [MDiffAtTangentField] using hX')
      (by simpa [MDiffAtTangentField] using hY)]
  rw [hXX']

omit [T2Space M] in
theorem curvatureOp_congr_snd_of_value_eq
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x : M} {X Y Y' Z : ∀ y : M, TM y}
    (hreg : CovariantDerivative.DerivRegularAt cov Z x)
    (hX : MDiffAtTangentField X x)
    (hY : MDiffAtTangentField Y x) (hY' : MDiffAtTangentField Y' x)
    (hYY' : Y x = Y' x) :
    CovariantDerivative.curvatureOp cov X Y Z x =
      CovariantDerivative.curvatureOp cov X Y' Z x := by
  rw [← CovariantDerivative.curvatureTensorAt_apply (cov := cov) (hreg := hreg)
      (X := X) (Y := Y)
      (by simpa [MDiffAtTangentField] using hX)
      (by simpa [MDiffAtTangentField] using hY),
    ← CovariantDerivative.curvatureTensorAt_apply (cov := cov) (hreg := hreg)
      (X := X) (Y := Y')
      (by simpa [MDiffAtTangentField] using hX)
      (by simpa [MDiffAtTangentField] using hY')]
  rw [hYY']

/--
The canonical closed curvature derivative agrees with the abstract covariant
derivative of the curvature operator in actual field slots.  This replaces
the constant extensions of the three connection-slot values by the
corresponding covariant-derivative vector fields using curvature tensoriality.
-/
theorem closedCurvatureCovDerivAt_eq_field_slots
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w z : TM x) :
    let X : ∀ y : M, TM y := extend E v
    let U : ∀ y : M, TM y := extend E u
    let W : ∀ y : M, TM y := extend E w
    let Z : ∀ y : M, TM y := extend E z
    let Γu : ∀ y : M, TM y := fun y ↦ g.leviCivita U y (X y)
    let Γw : ∀ y : M, TM y := fun y ↦ g.leviCivita W y (X y)
    let Γz : ∀ y : M, TM y := fun y ↦ g.leviCivita Z y (X y)
    closedCurvatureCovDerivAt g x v u w z =
      g.leviCivita (CovariantDerivative.curvatureOp g.leviCivita U W Z) x v
        - CovariantDerivative.curvatureOp g.leviCivita Γu W Z x
        - CovariantDerivative.curvatureOp g.leviCivita U Γw Z x
        - CovariantDerivative.curvatureOp g.leviCivita U W Γz x := by
  intro X U W Z Γu Γw Γz
  have hX : MDiffAtTangentField X x := by
    simpa [MDiffAtTangentField, X] using (mdifferentiableAt_extend I E v)
  have hU : MDiffAtTangentField U x := by
    simpa [MDiffAtTangentField, U] using (mdifferentiableAt_extend I E u)
  have hW : MDiffAtTangentField W x := by
    simpa [MDiffAtTangentField, W] using (mdifferentiableAt_extend I E w)
  have hΓu : MDiffAtTangentField Γu x := by
    have hU2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% U) x := by
      simpa [U] using (FiberBundle.contMDiffAt_extend' (k := 2) I E u)
    simpa [MDiffAtTangentField, Γu] using
      (CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
        (cov := g.leviCivita) hU2 (by simpa [MDiffAtTangentField] using hX))
  have hΓw : MDiffAtTangentField Γw x := by
    have hW2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% W) x := by
      simpa [W] using (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
    simpa [MDiffAtTangentField, Γw] using
      (CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
        (cov := g.leviCivita) hW2 (by simpa [MDiffAtTangentField] using hX))
  have hΓz₂ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Γz) x := by
    haveI : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 2 :=
      ClosedSmoothRiemannianMetric.leviCivita_contMDiff₂ g
    have hZ3 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% Z) x := by
      simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 3) I E z)
    have hX2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% X) x := by
      simpa [X] using (FiberBundle.contMDiffAt_extend' (k := 2) I E v)
    simpa [Γz] using
      (CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
        (cov := g.leviCivita) hZ3 hX2)
  have hΓz : MDiffAtTangentField Γz x := by
    exact hΓz₂.mdifferentiableAt two_ne_zero
  have hregZ : CovariantDerivative.DerivRegularAt g.leviCivita Z x := by
    simpa [Z] using
      (CovariantDerivative.derivRegularAt_extend (cov := g.leviCivita) z)
  have hfirst :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E (g.leviCivita U x v)) W Z x =
        CovariantDerivative.curvatureOp g.leviCivita Γu W Z x := by
    refine curvatureOp_congr_fst_of_value_eq
      (cov := g.leviCivita) (x := x) (Y := W) (Z := Z)
      hregZ ?_ hΓu hW ?_
    · simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E (g.leviCivita U x v))
    · simp [Γu, X]
  have hsecond :
      CovariantDerivative.curvatureOp g.leviCivita U
          (extend E (g.leviCivita W x v)) Z x =
        CovariantDerivative.curvatureOp g.leviCivita U Γw Z x := by
    refine curvatureOp_congr_snd_of_value_eq
      (cov := g.leviCivita) (x := x) (X := U) (Z := Z)
      hregZ hU ?_ hΓw ?_
    · simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E (g.leviCivita W x v))
    · simp [Γw, X]
  have hthird :
      CovariantDerivative.curvatureOp g.leviCivita U W
          (extend E (g.leviCivita Z x v)) x =
        CovariantDerivative.curvatureOp g.leviCivita U W Γz x := by
    refine CovariantDerivative.curvatureOp_congr_of_value_eq
      (cov := g.leviCivita)
      (X := U) (Y := W)
      (Z := extend E (g.leviCivita Z x v)) (Z' := Γz)
      ?_ hΓz₂ ?_ ?_ ?_
    · simpa using
        (FiberBundle.contMDiffAt_extend' (k := 2) I E (g.leviCivita Z x v))
    · simp [Γz, X]
    · simpa [MDiffAtTangentField] using hU
    · simpa [MDiffAtTangentField] using hW
  unfold closedCurvatureCovDerivAt
  change g.leviCivita (CovariantDerivative.curvatureOp g.leviCivita U W Z) x v
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E (g.leviCivita U x v)) W Z x
      - CovariantDerivative.curvatureOp g.leviCivita U
          (extend E (g.leviCivita W x v)) Z x
      - CovariantDerivative.curvatureOp g.leviCivita U W
          (extend E (g.leviCivita Z x v)) x =
    g.leviCivita (CovariantDerivative.curvatureOp g.leviCivita U W Z) x v
      - CovariantDerivative.curvatureOp g.leviCivita Γu W Z x
      - CovariantDerivative.curvatureOp g.leviCivita U Γw Z x
      - CovariantDerivative.curvatureOp g.leviCivita U W Γz x
  rw [hfirst, hsecond, hthird]

/-- Closed curvature operator field in canonical extension slots. -/
noncomputable def closedCurvatureFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w z : TM x) : ∀ y : M, TM y :=
  fun y ↦
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E u) (extend E w) (extend E z) y

/--
Differentiability of the closed curvature fields in anchored extension slots.

This is the non-vacuous regularity atom needed to differentiate scalar
curvature entries.  The derivative bridge below uses it only to invoke metric
compatibility on the vector-valued curvature field.
-/
def ClosedCurvatureFieldMDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ u w z : TM x,
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
      (T% (closedCurvatureFieldAt g u w z)) x

/--
The canonical Levi-Civita curvature fields in anchored extension slots are
differentiable.  This is the fixed-metric witness supplied by the `C²`
regularity of the closed Levi-Civita connection.
-/
theorem closedCurvatureFieldMDifferentiableAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ClosedCurvatureFieldMDifferentiableAt g x := by
  intro u w z
  let X : Π y : M, TM y := extend E u
  let Y : Π y : M, TM y := extend E w
  let Z : Π y : M, TM y := extend E z
  have hX2 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% X) x := by
    simpa [X] using (FiberBundle.contMDiffAt_extend' (k := 2) I E u)
  have hY2 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Y) x := by
    simpa [Y] using (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
  have hZ2 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Z) x := by
    simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 2) I E z)
  have hZ3 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% Z) x := by
    simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 3) I E z)
  have hXdiff :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% X) x :=
    hX2.mdifferentiableAt two_ne_zero
  have hYdiff :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Y) x :=
    hY2.mdifferentiableAt two_ne_zero
  haveI : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 2 :=
    ClosedSmoothRiemannianMetric.leviCivita_contMDiff₂ g
  have hInnerY :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
        (T% (fun y : M ↦ g.leviCivita Z y (Y y))) x :=
    CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
      (cov := g.leviCivita) hZ3 hY2
  have hInnerX :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
        (T% (fun y : M ↦ g.leviCivita Z y (X y))) x :=
    CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
      (cov := g.leviCivita) hZ3 hX2
  have hTermXY :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦
          g.leviCivita (fun p : M ↦ g.leviCivita Z p (Y p)) y (X y))) x :=
    CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
      (cov := g.leviCivita) hInnerY hXdiff
  have hTermYX :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦
          g.leviCivita (fun p : M ↦ g.leviCivita Z p (X p)) y (Y y))) x :=
    CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
      (cov := g.leviCivita) hInnerX hYdiff
  haveI : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by
    rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    exact_mod_cast (inferInstance : IsManifold I 3 M)
  have hbr :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (VectorField.mlieBracket I X Y)) x := by
    have h2 : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ ((2 : ℕ∞) : ℕ∞ω) := by
      simp
      norm_num
    exact (ContMDiffAt.mlieBracket_vectorField (m := 1) (n := 2)
      hX2 hY2 h2).mdifferentiableAt one_ne_zero
  have hTermBracket :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦
          g.leviCivita Z y (VectorField.mlieBracket I X Y y))) x :=
    CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
      (cov := g.leviCivita) hZ2 hbr
  have hcurv :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦
          g.leviCivita (fun p : M ↦ g.leviCivita Z p (Y p)) y (X y)
            - g.leviCivita (fun p : M ↦ g.leviCivita Z p (X p)) y (Y y)
            - g.leviCivita Z y (VectorField.mlieBracket I X Y y))) x :=
    mdifferentiableAt_sub_section
      (mdifferentiableAt_sub_section hTermXY hTermYX) hTermBracket
  simpa [closedCurvatureFieldAt, CovariantDerivative.curvatureOp, X, Y, Z] using hcurv

/--
Scalar-entry derivative bridge for closed curvature values.

For fixed base vectors `a`, `u`, `w`, and `q`, it identifies the exterior
derivative of
`y ↦ g(R_y(extend a, extend u) extend w, extend q)` with the covariant
curvature derivative and the three curvature-slot plus output-slot
Levi-Civita corrections.
-/
structure ClosedCurvatureEntryDerivativeBridgeAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop where
  mdifferentiable :
    ∀ a u w q : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          g.inner y
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u) (extend E w) y)
            (extend E q y)) x
  extDeriv_eq :
    ∀ v a u w q : TM x,
      extDerivFun
        (fun y : M ↦
          g.inner y
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u) (extend E w) y)
            (extend E q y)) x v
      =
        g.inner x (closedCurvatureCovDerivAt g x v a u w) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E (g.leviCivita (extend E a) x v))
              (extend E u) (extend E w) x) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a)
              (extend E (g.leviCivita (extend E u) x v))
              (extend E w) x) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u)
              (extend E (g.leviCivita (extend E w) x v)) x) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u) (extend E w) x)
            (g.leviCivita (extend E q) x v)

/--
Triple product-rule bridge for scalar closed-curvature entries.

This is the curvature analogue of
`deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt`:
metric compatibility differentiates the pairing, while the definition of
`closedCurvatureCovDerivAt` supplies the three curvature-slot corrections.
-/
theorem closedCurvatureEntryDerivativeBridgeAt_of_curvatureFieldMDifferentiableAt
    {g : ClosedSmoothRiemannianMetric n M}
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M}
    (hR : ClosedCurvatureFieldMDifferentiableAt g x) :
    ClosedCurvatureEntryDerivativeBridgeAt g x where
  mdifferentiable := by
    intro a u w q
    exact g.metric_pairing_mdiffAt
      (hR a u w)
      (mdifferentiableAt_extend I E q)
  extDeriv_eq := by
    intro v a u w q
    let R : ∀ y : M, TM y := closedCurvatureFieldAt g a u w
    let Q : ∀ y : M, TM y := extend E q
    have hRdiff :
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% R) x := by
      simpa [R] using hR a u w
    have hQdiff :
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Q) x := by
      simpa [Q] using (mdifferentiableAt_extend I E q)
    have hcompat :=
      g.leviCivita_metricCompatibleAt x
        (Y := R) (Z := Q)
        (by simpa [MDiffAtTangentField] using hRdiff)
        (by simpa [MDiffAtTangentField] using hQdiff)
        v
    have hcov :
        g.leviCivita R x v =
          closedCurvatureCovDerivAt g x v a u w
            + CovariantDerivative.curvatureOp g.leviCivita
              (extend E (g.leviCivita (extend E a) x v))
              (extend E u) (extend E w) x
            + CovariantDerivative.curvatureOp g.leviCivita
              (extend E a)
              (extend E (g.leviCivita (extend E u) x v))
              (extend E w) x
            + CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u)
              (extend E (g.leviCivita (extend E w) x v)) x := by
      unfold closedCurvatureCovDerivAt
      change g.leviCivita R x v =
        (g.leviCivita R x v
          - CovariantDerivative.curvatureOp g.leviCivita
              (extend E (g.leviCivita (extend E a) x v))
              (extend E u) (extend E w) x
          - CovariantDerivative.curvatureOp g.leviCivita
              (extend E a)
              (extend E (g.leviCivita (extend E u) x v))
              (extend E w) x
          - CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u)
              (extend E (g.leviCivita (extend E w) x v)) x)
        + CovariantDerivative.curvatureOp g.leviCivita
              (extend E (g.leviCivita (extend E a) x v))
              (extend E u) (extend E w) x
        + CovariantDerivative.curvatureOp g.leviCivita
              (extend E a)
              (extend E (g.leviCivita (extend E u) x v))
              (extend E w) x
        + CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u)
              (extend E (g.leviCivita (extend E w) x v)) x
      abel
    change
      extDerivFun (fun y : M ↦ g.inner y (R y) (Q y)) x v =
        g.inner x (closedCurvatureCovDerivAt g x v a u w) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E (g.leviCivita (extend E a) x v))
              (extend E u) (extend E w) x) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a)
              (extend E (g.leviCivita (extend E u) x v))
              (extend E w) x) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u)
              (extend E (g.leviCivita (extend E w) x v)) x) q
        + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E a) (extend E u) (extend E w) x)
            (g.leviCivita (extend E q) x v)
    rw [hcompat, hcov]
    simp [R, Q, closedCurvatureFieldAt, extend_apply_self]

/-- Canonical scalar-entry derivative bridge for closed curvature values. -/
theorem closedCurvatureEntryDerivativeBridgeAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ClosedCurvatureEntryDerivativeBridgeAt g x :=
  closedCurvatureEntryDerivativeBridgeAt_of_curvatureFieldMDifferentiableAt
    (closedCurvatureFieldMDifferentiableAt_canonical g x)

/-- Flat exterior derivative of a scalar closed-curvature entry. -/
noncomputable def closedCurvatureEntryDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) : ℝ :=
  extDerivFun
    (fun y : M ↦
      g.inner y
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) y)
        (extend E q y)) x v

/--
The four Christoffel-slot corrections in the scalar-entry derivative bridge
for `closedCurvatureCovDerivAt`.
-/
noncomputable def closedCurvatureCovDerivAtCorrectionAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) : ℝ :=
  g.inner x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (g.leviCivita (extend E a) x v))
        (extend E u) (extend E w) x) q
    + g.inner x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E a)
        (extend E (g.leviCivita (extend E u) x v))
        (extend E w) x) q
    + g.inner x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E a) (extend E u)
        (extend E (g.leviCivita (extend E w) x v)) x) q
    + g.inner x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E a) (extend E u) (extend E w) x)
      (g.leviCivita (extend E q) x v)

/--
Scalar-paired expansion of `closedCurvatureCovDerivAt` through the canonical
curvature-entry derivative bridge.
-/
theorem closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v a u w) q =
      closedCurvatureEntryDerivAt g x v a u w q
        - closedCurvatureCovDerivAtCorrectionAt g x v a u w q := by
  unfold closedCurvatureEntryDerivAt closedCurvatureCovDerivAtCorrectionAt
  have h :=
    (closedCurvatureEntryDerivativeBridgeAt_canonical g x).extDeriv_eq
      v a u w q
  linarith

/--
Cyclic scalar-paired expansion of the closed second-Bianchi expression.  The
remaining intrinsic second-Bianchi atom is exactly the cancellation of the
three flat entry derivatives against these cyclic Christoffel corrections.
-/
theorem closedCurvatureCovDerivAt_cyclic_inner_expansion
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v u w z) q
      + g.inner x (closedCurvatureCovDerivAt g x u w v z) q
      + g.inner x (closedCurvatureCovDerivAt g x w v u z) q =
        closedCurvatureEntryDerivAt g x v u w z q
          + closedCurvatureEntryDerivAt g x u w v z q
          + closedCurvatureEntryDerivAt g x w v u z q
          - (closedCurvatureCovDerivAtCorrectionAt g x v u w z q
            + closedCurvatureCovDerivAtCorrectionAt g x u w v z q
            + closedCurvatureCovDerivAtCorrectionAt g x w v u z q) := by
  rw [closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := v) (a := u) (u := w) (w := z) (q := q),
    closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := u) (a := w) (u := v) (w := z) (q := q),
    closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := w) (a := v) (u := u) (w := z) (q := q)]
  ring

/--
Scalar-paired cyclic cancellation implies the vector-valued closed cyclic
second-Bianchi identity at a point.
-/
theorem closed_cyclic_second_bianchi_at_of_inner_sum
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hScalar : ∀ u v w z q : TM x,
      g.inner x (closedCurvatureCovDerivAt g x v u w z) q
        + g.inner x (closedCurvatureCovDerivAt g x u w v z) q
        + g.inner x (closedCurvatureCovDerivAt g x w v u z) q = 0) :
    ∀ u v w z : TM x,
      closedCurvatureCovDerivAt g x v u w z
        + closedCurvatureCovDerivAt g x u w v z
        + closedCurvatureCovDerivAt g x w v u z = 0 := by
  intro u v w z
  refine LeviCivitaExistence.metric_nondegenerate g x _ ?_
  intro q
  have hq := hScalar u v w z q
  simpa [map_add] using hq

/--
Neighborhood version of `closed_cyclic_second_bianchi_at_of_inner_sum`, in
the exact vector-valued shape consumed by the twice-contracted Bianchi bridge.
-/
theorem eventually_closed_cyclic_second_bianchi_of_inner_sum
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hScalar : ∀ᶠ y in nhds x, ∀ u v w z q : TM y,
      g.inner y (closedCurvatureCovDerivAt g y v u w z) q
        + g.inner y (closedCurvatureCovDerivAt g y u w v z) q
        + g.inner y (closedCurvatureCovDerivAt g y w v u z) q = 0) :
    ∀ᶠ y in nhds x, ∀ u v w z : TM y,
      closedCurvatureCovDerivAt g y v u w z
        + closedCurvatureCovDerivAt g y u w v z
        + closedCurvatureCovDerivAt g y w v u z = 0 := by
  filter_upwards [hScalar] with y hy
  exact closed_cyclic_second_bianchi_at_of_inner_sum (g := g) (x := y) hy

/--
Scalar field for an iterated closed connection value:
`g(∇_p (∇_u w), q)` with `u`, `w` transported by canonical extensions.
-/
noncomputable def closedIteratedConnectionEntryFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} (u w : TM x) : ∀ y : M, TM y → TM y → ℝ :=
  fun y p q ↦
    g.inner y
      (g.leviCivita
        (fun r : M ↦ g.leviCivita (extend E w) r (extend E u r))
        y p) q

/--
Scalar field for the bracket connection value in the defining curvature
identity: `g(∇_[a,u] w, q)`.
-/
noncomputable def closedBracketConnectionEntryFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} (a u w : TM x) : ∀ y : M, TM y → ℝ :=
  fun y q ↦
    g.inner y
      (g.leviCivita (extend E w) y
        (VectorField.mlieBracket I (extend E a) (extend E u) y)) q

/--
The four Christoffel-slot corrections expanded through the same defining
curvature-entry vocabulary as `closedCurvatureDefExpansionResidueAt`.
-/
theorem closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u z q : TM x) :
    closedCurvatureCovDerivAtCorrectionAt g x v a u z q =
      (closedIteratedConnectionEntryFieldAt g u z x
          (g.leviCivita (extend E a) x v) q
        - closedIteratedConnectionEntryFieldAt g
          (g.leviCivita (extend E a) x v) z x u q
        - closedBracketConnectionEntryFieldAt g
          (g.leviCivita (extend E a) x v) u z x q)
      + (closedIteratedConnectionEntryFieldAt g
          (g.leviCivita (extend E u) x v) z x a q
        - closedIteratedConnectionEntryFieldAt g a z x
          (g.leviCivita (extend E u) x v) q
        - closedBracketConnectionEntryFieldAt g a
          (g.leviCivita (extend E u) x v) z x q)
      + (closedIteratedConnectionEntryFieldAt g u
          (g.leviCivita (extend E z) x v) x a q
        - closedIteratedConnectionEntryFieldAt g a
          (g.leviCivita (extend E z) x v) x u q
        - closedBracketConnectionEntryFieldAt g a u
          (g.leviCivita (extend E z) x v) x q)
      + (closedIteratedConnectionEntryFieldAt g u z x a
          (g.leviCivita (extend E q) x v)
        - closedIteratedConnectionEntryFieldAt g a z x u
          (g.leviCivita (extend E q) x v)
        - closedBracketConnectionEntryFieldAt g a u z x
          (g.leviCivita (extend E q) x v)) := by
  simp only [closedCurvatureCovDerivAtCorrectionAt,
    CovariantDerivative.curvatureOp_apply,
    closedIteratedConnectionEntryFieldAt,
    closedBracketConnectionEntryFieldAt,
    extend_apply_self,
    map_sub,
    ContinuousLinearMap.sub_apply]

/--
Covariant derivative of the scalar bracket-connection entry in the output
slot.  The raw exterior derivative is recovered by adding the output
Levi-Civita correction.
-/
noncomputable def closedBracketConnectionEntryDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (v a u w q : TM x) : ℝ :=
  extDerivFun
      (fun y : M ↦
        closedBracketConnectionEntryFieldAt g a u w y (extend E q y)) x v
    - closedBracketConnectionEntryFieldAt g a u w x
        (g.leviCivita (extend E q) x v)

/--
Closed curvature defining expansion after differentiating the three scalar
terms.  The first two terms are second connection-entry derivatives, and the
remaining summands are the connection-product corrections from transported
slots.
-/
noncomputable def closedCurvatureDefExpansionAt
    (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (v a u w q : TM x) : ℝ :=
  covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g u w) x v a q
    - covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g a w) x v u q
    - closedBracketConnectionEntryDerivAt g x v a u w q
    + closedIteratedConnectionEntryFieldAt g u w x
        (g.leviCivita (extend E a) x v) q
    - closedIteratedConnectionEntryFieldAt g a w x
        (g.leviCivita (extend E u) x v) q
    + closedIteratedConnectionEntryFieldAt g u w x a
        (g.leviCivita (extend E q) x v)
    - closedIteratedConnectionEntryFieldAt g a w x u
        (g.leviCivita (extend E q) x v)
    - closedBracketConnectionEntryFieldAt g a u w x
        (g.leviCivita (extend E q) x v)

theorem closedIteratedConnectionEntry_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (a u w q : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        closedIteratedConnectionEntryFieldAt g u w y
          (extend E a y) (extend E q y)) x := by
  let X : Π y : M, TM y := extend E a
  let Y : Π y : M, TM y := extend E u
  let Z : Π y : M, TM y := extend E w
  let Q : Π y : M, TM y := extend E q
  have hXdiff :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% X) x := by
    simpa [X] using (mdifferentiableAt_extend I E a)
  have hQdiff :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Q) x := by
    simpa [Q] using (mdifferentiableAt_extend I E q)
  have hY2 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Y) x := by
    simpa [Y] using (FiberBundle.contMDiffAt_extend' (k := 2) I E u)
  have hZ3 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% Z) x := by
    simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 3) I E w)
  haveI : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 2 :=
    ClosedSmoothRiemannianMetric.leviCivita_contMDiff₂ g
  have hInner :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
        (T% (fun y : M ↦ g.leviCivita Z y (Y y))) x :=
    CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
      (cov := g.leviCivita) hZ3 hY2
  have hTerm :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦
          g.leviCivita (fun r : M ↦ g.leviCivita Z r (Y r)) y (X y))) x :=
    CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
      (cov := g.leviCivita) hInner hXdiff
  exact g.metric_pairing_mdiffAt
    (by simpa [closedIteratedConnectionEntryFieldAt, X, Y, Z] using hTerm)
    hQdiff

theorem closedBracketConnectionEntry_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (a u w q : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        closedBracketConnectionEntryFieldAt g a u w y
          (extend E q y)) x := by
  let X : Π y : M, TM y := extend E a
  let Y : Π y : M, TM y := extend E u
  let Z : Π y : M, TM y := extend E w
  let Q : Π y : M, TM y := extend E q
  have hZ2 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Z) x := by
    simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
  have hX2 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% X) x := by
    simpa [X] using (FiberBundle.contMDiffAt_extend' (k := 2) I E a)
  have hY2 :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Y) x := by
    simpa [Y] using (FiberBundle.contMDiffAt_extend' (k := 2) I E u)
  haveI : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 2 :=
    ClosedSmoothRiemannianMetric.leviCivita_contMDiff₂ g
  haveI : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by
    rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    exact_mod_cast (inferInstance : IsManifold I 3 M)
  have hbr :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (VectorField.mlieBracket I X Y)) x := by
    have h2 : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ ((2 : ℕ∞) : ℕ∞ω) := by
      simp
      norm_num
    exact (ContMDiffAt.mlieBracket_vectorField (m := 1) (n := 2)
      hX2 hY2 h2).mdifferentiableAt one_ne_zero
  have hTerm :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦
          g.leviCivita Z y (VectorField.mlieBracket I X Y y))) x :=
    CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
      (cov := g.leviCivita) hZ2 hbr
  have hQdiff :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Q) x := by
    simpa [Q] using (mdifferentiableAt_extend I E q)
  exact g.metric_pairing_mdiffAt
    (by simpa [closedBracketConnectionEntryFieldAt, X, Y, Z] using hTerm)
    hQdiff

/--
Neighborhood form of the curvature defining identity in canonical extension
slots.
-/
theorem curvature_def_eventually
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (a u w q : TM x) :
    (fun y : M ↦
      g.inner y
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) y)
        (extend E q y))
      =ᶠ[nhds x]
    (fun y : M ↦
      closedIteratedConnectionEntryFieldAt g u w y
          (extend E a y) (extend E q y)
        - closedIteratedConnectionEntryFieldAt g a w y
          (extend E u y) (extend E q y)
        - closedBracketConnectionEntryFieldAt g a u w y
          (extend E q y)) := by
  exact Filter.Eventually.of_forall fun y ↦ by
    simp [closedIteratedConnectionEntryFieldAt,
      closedBracketConnectionEntryFieldAt, CovariantDerivative.curvatureOp]

/--
Exterior-derivative form of the curvature defining identity, split into the
two iterated-connection terms and the bracket term.
-/
theorem curvature_def_extDerivFun
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    closedCurvatureEntryDerivAt g x v a u w q =
      extDerivFun
          (fun y : M ↦
            closedIteratedConnectionEntryFieldAt g u w y
              (extend E a y) (extend E q y)) x v
        - extDerivFun
          (fun y : M ↦
            closedIteratedConnectionEntryFieldAt g a w y
              (extend E u y) (extend E q y)) x v
        - extDerivFun
          (fun y : M ↦
            closedBracketConnectionEntryFieldAt g a u w y
              (extend E q y)) x v := by
  let A : M → ℝ := fun y : M ↦
    closedIteratedConnectionEntryFieldAt g u w y
      (extend E a y) (extend E q y)
  let B : M → ℝ := fun y : M ↦
    closedIteratedConnectionEntryFieldAt g a w y
      (extend E u y) (extend E q y)
  let C : M → ℝ := fun y : M ↦
    closedBracketConnectionEntryFieldAt g a u w y
      (extend E q y)
  let L : M → ℝ := fun y : M ↦
    g.inner y
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E a) (extend E u) (extend E w) y)
      (extend E q y)
  have hevent :
      L =ᶠ[nhds x] fun y : M ↦ A y - B y - C y := by
    simpa [L, A, B, C] using
      curvature_def_eventually (g := g) (x := x) a u w q
  have hderiv :
      extDerivFun L x v =
        extDerivFun (fun y : M ↦ A y - B y - C y) x v := by
    exact congrArg (fun L' : TM x →L[ℝ] ℝ ↦ L' v)
      (CovariantDerivative.extDerivFun_congr hevent)
  have hA : MDifferentiableAt I 𝓘(ℝ) A x := by
    simpa [A] using closedIteratedConnectionEntry_mdiffAt
      (g := g) (a := a) (u := u) (w := w) (q := q)
  have hB : MDifferentiableAt I 𝓘(ℝ) B x := by
    simpa [B] using closedIteratedConnectionEntry_mdiffAt
      (g := g) (a := u) (u := a) (w := w) (q := q)
  have hC : MDifferentiableAt I 𝓘(ℝ) C x := by
    simpa [C] using closedBracketConnectionEntry_mdiffAt
      (g := g) (a := a) (u := u) (w := w) (q := q)
  have hsplit :
      extDerivFun (fun y : M ↦ A y - B y - C y) x v =
        extDerivFun A x v - extDerivFun B x v - extDerivFun C x v := by
    have hnegB : MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ -B y) x := hB.neg
    have hraw := extDerivFun_add_sub_at
      (n := n) (M := M)
      (f := A) (g := fun y : M ↦ -B y) (h := C) (x := x)
      hA hnegB hC v
    have hneg :
        extDerivFun (fun y : M ↦ -B y) x v = -extDerivFun B x v := by
      have hfun : (fun y : M ↦ -B y) = (-1 : ℝ) • B := by
        funext y
        simp
      rw [hfun]
      have h := congrArg (fun L' : TM x →L[ℝ] ℝ ↦ L' v)
        (extDerivFun_const_smul_at
          (n := n) (M := M) (f := B) (x := x) hB (-1 : ℝ))
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hfun :
        (fun y : M ↦ A y - B y - C y) =
          fun y : M ↦ A y + (-B y) - C y := by
      funext y
      ring
    rw [hfun, hraw, hneg]
    ring
  unfold closedCurvatureEntryDerivAt
  calc
    extDerivFun L x v =
        extDerivFun (fun y : M ↦ A y - B y - C y) x v := hderiv
    _ = extDerivFun A x v - extDerivFun B x v - extDerivFun C x v := hsplit

theorem closedIteratedConnectionEntry_extDerivFun_eq
    (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (v a u w q : TM x) :
    extDerivFun
        (fun y : M ↦
          closedIteratedConnectionEntryFieldAt g u w y
            (extend E a y) (extend E q y)) x v =
      covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g u w) x v a q
        + closedIteratedConnectionEntryFieldAt g u w x
          (g.leviCivita (extend E a) x v) q
        + closedIteratedConnectionEntryFieldAt g u w x a
          (g.leviCivita (extend E q) x v) := by
  unfold covTensor2DerivAt
  ring

theorem closedBracketConnectionEntry_extDerivFun_eq
    (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (v a u w q : TM x) :
    extDerivFun
        (fun y : M ↦
          closedBracketConnectionEntryFieldAt g a u w y
            (extend E q y)) x v =
      closedBracketConnectionEntryDerivAt g x v a u w q
        + closedBracketConnectionEntryFieldAt g a u w x
          (g.leviCivita (extend E q) x v) := by
  unfold closedBracketConnectionEntryDerivAt
  ring

/--
Closed curvature Koszul expansion: the flat derivative of the scalar
curvature entry is the differentiated defining identity, i.e. second
connection-entry derivatives plus the transported-slot connection products.
-/
theorem closedCurvature_koszul
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    closedCurvatureEntryDerivAt g x v a u w q =
      closedCurvatureDefExpansionAt g x v a u w q := by
  rw [curvature_def_extDerivFun (g := g) (x := x)
    (v := v) (a := a) (u := u) (w := w) (q := q)]
  rw [closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := v) (a := a) (u := u) (w := w) (q := q),
    closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := v) (a := u) (u := a) (w := w) (q := q),
    closedBracketConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := v) (a := a) (u := u) (w := w) (q := q)]
  unfold closedCurvatureDefExpansionAt
  ring

/--
Single-entry scalar-paired closed curvature derivative after substituting the
closed Koszul expansion.
-/
theorem closedCurvatureCovDerivAt_inner_koszul_expansion
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v a u w) q =
      closedCurvatureDefExpansionAt g x v a u w q
        - closedCurvatureCovDerivAtCorrectionAt g x v a u w q := by
  rw [closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := v) (a := a) (u := u) (w := w) (q := q),
    closedCurvature_koszul
      (g := g) (x := x) (v := v) (a := a) (u := u) (w := w) (q := q)]

/--
Cyclic scalar-paired second-Bianchi expansion after substituting the closed
curvature Koszul formula in each entry derivative.
-/
theorem closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v u w z) q
      + g.inner x (closedCurvatureCovDerivAt g x u w v z) q
      + g.inner x (closedCurvatureCovDerivAt g x w v u z) q =
        closedCurvatureDefExpansionAt g x v u w z q
          + closedCurvatureDefExpansionAt g x u w v z q
          + closedCurvatureDefExpansionAt g x w v u z q
          - (closedCurvatureCovDerivAtCorrectionAt g x v u w z q
            + closedCurvatureCovDerivAtCorrectionAt g x u w v z q
            + closedCurvatureCovDerivAtCorrectionAt g x w v u z q) := by
  rw [closedCurvatureCovDerivAt_cyclic_inner_expansion
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q),
    closedCurvature_koszul (g := g) (x := x)
      (v := v) (a := u) (u := w) (w := z) (q := q),
    closedCurvature_koszul (g := g) (x := x)
      (v := u) (a := w) (u := v) (w := z) (q := q),
    closedCurvature_koszul (g := g) (x := x)
      (v := w) (a := v) (u := u) (w := z) (q := q)]

/-- Flat sanity check for the closed curvature Koszul expansion. -/
theorem closedCurvature_koszul_flat
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x)
    (hflat : CovariantDerivative.IsFlat g.leviCivita) :
    closedCurvatureDefExpansionAt g x v a u w q = 0 := by
  rw [← closedCurvature_koszul (g := g) (x := x)
    (v := v) (a := a) (u := u) (w := w) (q := q)]
  unfold closedCurvatureEntryDerivAt
  have hzero :
      (fun y : M ↦
        g.inner y
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E a) (extend E u) (extend E w) y)
          (extend E q y)) = fun _ : M ↦ (0 : ℝ) := by
    funext y
    have hfield :
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) y = 0 :=
      congrArg (fun R : ∀ y : M, TM y ↦ R y)
        (hflat (extend E a) (extend E u) (extend E w))
    simp [hfield]
  rw [hzero]
  simp [extDerivFun_zero_at]

private theorem eventually_contMDiffAt_two_extend
    {x : M} (v : TM x) :
    ∀ᶠ y in nhds x,
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% (extend E v)) y := by
  obtain ⟨s, hs, hscont⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp
      (FiberBundle.contMDiffAt_extend' (k := 2) I E v)
  filter_upwards [interior_mem_nhds.mpr hs] with y hy
  exact ((hscont.mono interior_subset) y hy).contMDiffAt
    (isOpen_interior.mem_nhds hy)

/--
On the anchor-chart neighborhood, canonical extensions have locally constant
chart representatives, so their manifold Lie bracket vanishes near the
anchor.
-/
theorem mlieBracket_extend_extend_eventually_eq_zero
    {x : M} (p q : TM x) :
    (fun y : M => VectorField.mlieBracket I (extend E p) (extend E q) y)
      =ᶠ[nhds x] fun _ : M => (0 : E) := by
  have hp := eventually_contMDiffAt_two_extend (n := n) (M := M) p
  have hq := eventually_contMDiffAt_two_extend (n := n) (M := M) q
  have hsrc : (extChartAt I x).source ∈ nhds x :=
    extChartAt_source_mem_nhds x
  filter_upwards [hsrc, hp, hq] with y hy hp2 hq2
  let z : E := extChartAt I x y
  let Xc : E → E := CovariantDerivative.chartTransportedLeviCivitaSection
    x (extend E p)
  let Yc : E → E := CovariantDerivative.chartTransportedLeviCivitaSection
    x (extend E q)
  have hXc : Xc =ᶠ[nhds z] fun _ : E => p := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds
      ((extChartAt I x).map_source hy)] with z' hz'
    have hy' : (extChartAt I x).symm z' ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz'
    have hz_eq : extChartAt I x ((extChartAt I x).symm z') = z' :=
      (extChartAt I x).right_inv hz'
    have hval :=
      chartTransportedLeviCivitaSection_extend_apply_chart (x := x)
        (y := (extChartAt I x).symm z') hy' p
    rw [hz_eq] at hval
    simpa [Xc, z] using hval
  have hYc : Yc =ᶠ[nhds z] fun _ : E => q := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds
      ((extChartAt I x).map_source hy)] with z' hz'
    have hy' : (extChartAt I x).symm z' ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz'
    have hz_eq : extChartAt I x ((extChartAt I x).symm z') = z' :=
      (extChartAt I x).right_inv hz'
    have hval :=
      chartTransportedLeviCivitaSection_extend_apply_chart (x := x)
        (y := (extChartAt I x).symm z') hy' q
    rw [hz_eq] at hval
    simpa [Yc, z] using hval
  have hmodel :
      VectorField.mlieBracket 𝓘(ℝ, E) Xc Yc z = 0 := by
    have hconst :
        VectorField.mlieBracket 𝓘(ℝ, E) Xc Yc z =
          VectorField.mlieBracket 𝓘(ℝ, E)
            (fun _ : E => p) (fun _ : E => q) z := by
      exact hXc.mlieBracket_vectorField_eq hYc
    rw [hconst, mlieBracket_vectorSpace_eq]
    simp [VectorField.lieBracket]
    rfl
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hchart :=
    CovariantDerivative.chartTransportedLeviCivitaSection_mlieBracket_apply_chart
      x (X := extend E p) (Y := extend E q) hy
      (hp2.mdifferentiableAt two_ne_zero)
      (hq2.mdifferentiableAt two_ne_zero)
  have hpush :
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) y
          (VectorField.mlieBracket I (extend E p) (extend E q) y) = 0 := by
    rw [hmodel] at hchart
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        x (VectorField.mlieBracket I (extend E p) (extend E q)) hy] at hchart
    simpa [Xc, Yc, z] using hchart
  have hround :=
    CovariantDerivative.chartTransportedLeviCivita_direction_roundtrip
      x hy (VectorField.mlieBracket I (extend E p) (extend E q) y)
  rw [hpush] at hround
  rw [map_zero] at hround
  simpa using hround.symm

/--
The scalar bracket-entry field appearing in the cyclic residue is eventually
zero at its own canonical-extension anchor.
-/
theorem closedBracketConnectionEntryFieldAt_extend_eventually_eq_zero
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} (a u w q : TM x) :
    (fun y : M => closedBracketConnectionEntryFieldAt g a u w y (extend E q y))
      =ᶠ[nhds x] fun _ : M => (0 : ℝ) := by
  filter_upwards [mlieBracket_extend_extend_eventually_eq_zero
      (n := n) (M := M) (x := x) a u] with y hbr
  simp only [closedBracketConnectionEntryFieldAt, hbr]
  change g.inner y (g.leviCivita (extend E w) y 0) (extend E q y) = 0
  simp

/--
Consequently the exterior derivative of the bracket-entry field in the
cyclic residue vanishes at the anchor.
-/
theorem closedBracketConnectionEntryFieldAt_extend_extDerivFun_eq_zero
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} (v a u w q : TM x) :
    extDerivFun
        (fun y : M =>
          closedBracketConnectionEntryFieldAt g a u w y (extend E q y)) x v = 0 := by
  have hzero :=
    closedBracketConnectionEntryFieldAt_extend_eventually_eq_zero
      (g := g) (x := x) a u w q
  have h :=
    congrArg (fun L : TM x →L[ℝ] ℝ => L v)
      (CovariantDerivative.extDerivFun_congr hzero)
  simpa [extDerivFun_zero_at] using h

/-- At its anchor, every canonical-extension bracket connection entry vanishes. -/
theorem closedBracketConnectionEntryFieldAt_apply_self_eq_zero
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} (a u w q : TM x) :
    closedBracketConnectionEntryFieldAt g a u w x q = 0 := by
  have hbr := mlieBracket_extend_extend_apply_self (n := n) (M := M)
    (x := x) a u
  simp only [closedBracketConnectionEntryFieldAt, hbr]
  change g.inner x (g.leviCivita (extend E w) x 0) q = 0
  simp

/--
Auxiliary `(0,2)` curvature field whose metric trace is the moving Ricci entry
`Ric_y(extend u, extend w)`.
-/
noncomputable def closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) :
    ∀ y : M, TM y → TM y → ℝ :=
  fun y p q ↦
    g.inner y
      (CovariantDerivative.curvatureTensorAt g.leviCivita
        (CovariantDerivative.derivRegularAt_extend g.leviCivita (extend E w y))
        p (extend E u y)) q

theorem traceMetricVariationAt_closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) (y : M) :
    traceMetricVariationAt g (closedRicciTraceFieldAt g u w) y =
      g.ricciAt y (extend E u y) (extend E w y) := by
  classical
  letI : FiniteDimensional ℝ (TM y) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM y)
  let sharp : Fin (Module.finrank ℝ (TM y)) → TM y :=
    fun i ↦ metricDualVectorAt g y (b.coord i)
  let hreg :=
    CovariantDerivative.derivRegularAt_extend g.leviCivita (extend E w y)
  calc
    traceMetricVariationAt g (closedRicciTraceFieldAt g u w) y =
        ∑ i, g.inner y
          (CovariantDerivative.curvatureTensorAt g.leviCivita hreg
            (b i) (extend E u y)) (sharp i) := by
          simp [traceMetricVariationAt, closedRicciTraceFieldAt, b, sharp]
    _ = ∑ i, b.coord i
          (CovariantDerivative.curvatureTensorAt g.leviCivita hreg
            (b i) (extend E u y)) := by
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          rw [coord_eq_inner_metricDualVectorAt_of_basis
            (g := g) (x := y) (b := b)]
    _ = LinearMap.trace ℝ (TM y)
          (CovariantDerivative.curvatureEndAt g.leviCivita hreg
            (extend E u y)) := by
          rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
          refine Finset.sum_congr rfl fun i _hi ↦ ?_
          rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
          rfl
    _ = g.ricciAt y (extend E u y) (extend E w y) := by
          unfold ClosedSmoothRiemannianMetric.ricciAt
            CovariantDerivative.ricciBilinearAt CovariantDerivative.ricciTraceAt
          rfl

theorem eventually_closedRicciTraceFieldAt_entry_eq_curvature_entry
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w p q : TM x) :
    ∀ᶠ y in nhds x,
      closedRicciTraceFieldAt g u w y (extend E p y) (extend E q y) =
        g.inner y
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E p) (extend E u) (extend E w) y)
          (extend E q y) := by
  have hP := eventually_contMDiffAt_two_extend (n := n) (M := M) p
  have hU := eventually_contMDiffAt_two_extend (n := n) (M := M) u
  have hW := eventually_contMDiffAt_two_extend (n := n) (M := M) w
  filter_upwards [hP, hU, hW] with y hP2 hU2 hW2
  let hreg :=
    CovariantDerivative.derivRegularAt_extend g.leviCivita (extend E w y)
  have hTensor :
      CovariantDerivative.curvatureTensorAt g.leviCivita hreg
          (extend E p y) (extend E u y) =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E p) (extend E u) (extend E (extend E w y)) y := by
    simpa [hreg] using
      (CovariantDerivative.curvatureTensorAt_apply
        (cov := g.leviCivita) (hreg := hreg)
        (X := extend E p) (Y := extend E u)
        (hP2.mdifferentiableAt two_ne_zero)
        (hU2.mdifferentiableAt two_ne_zero))
  have hThird :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E p) (extend E u) (extend E (extend E w y)) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E p) (extend E u) (extend E w) y := by
    exact CovariantDerivative.curvatureOp_congr_of_value_eq
      (cov := g.leviCivita)
      (Z := extend E (extend E w y)) (Z' := extend E w)
      (X := extend E p) (Y := extend E u)
      (FiberBundle.contMDiffAt_extend' (k := 2) I E (extend E w y))
      hW2
      (by simp [extend_apply_self])
      (hP2.mdifferentiableAt two_ne_zero)
      (hU2.mdifferentiableAt two_ne_zero)
  simpa [closedRicciTraceFieldAt, hreg] using
    congrArg (fun z : TM y ↦ g.inner y z (extend E q y))
      (hTensor.trans hThird)

theorem closedRicciTraceFieldAt_apply_eq_curvature_entry
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w p q : TM x) :
    closedRicciTraceFieldAt g u w x p q =
      g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E p) (extend E u) (extend E w) x) q := by
  simpa [extend_apply_self] using
    (eventually_closedRicciTraceFieldAt_entry_eq_curvature_entry
      (g := g) (u := u) (w := w) (p := p) (q := q)).self_of_nhds

theorem tensor2AddLeft_closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) :
    Tensor2AddLeft (closedRicciTraceFieldAt g u w) := by
  intro y p₁ p₂ q
  simp [closedRicciTraceFieldAt]

theorem tensor2SMulLeft_closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) :
    Tensor2SMulLeft (closedRicciTraceFieldAt g u w) := by
  intro y c p q
  simp [closedRicciTraceFieldAt, smul_eq_mul]

theorem tensor2AddRight_closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) :
    Tensor2AddRight (closedRicciTraceFieldAt g u w) := by
  intro y p q₁ q₂
  simp [closedRicciTraceFieldAt]

theorem tensor2SMulRight_closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) :
    Tensor2SMulRight (closedRicciTraceFieldAt g u w) := by
  intro y c p q
  simp [closedRicciTraceFieldAt, smul_eq_mul]

noncomputable def closedRicciTraceBilinFormAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) (y : M) :
    LinearMap.BilinForm ℝ (TM y) :=
  LinearMap.mk₂ ℝ (fun p q ↦ closedRicciTraceFieldAt g u w y p q)
    (fun p p' q ↦ tensor2AddLeft_closedRicciTraceFieldAt g u w y p p' q)
    (fun c p q ↦ tensor2SMulLeft_closedRicciTraceFieldAt g u w y c p q)
    (fun p q q' ↦ tensor2AddRight_closedRicciTraceFieldAt g u w y p q q')
    (fun c p q ↦ tensor2SMulRight_closedRicciTraceFieldAt g u w y c p q)

theorem covTensor2ExtDifferentiableAt_closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (u w : TM x) :
    CovTensor2ExtDifferentiableAt (closedRicciTraceFieldAt g u w) x := by
  intro p q
  have hEntry :
      (fun y : M ↦ closedRicciTraceFieldAt g u w y (extend E p y) (extend E q y))
        =ᶠ[nhds x]
      (fun y : M ↦
        g.inner y
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E p) (extend E u) (extend E w) y)
          (extend E q y)) :=
    eventually_closedRicciTraceFieldAt_entry_eq_curvature_entry
      (g := g) (u := u) (w := w) (p := p) (q := q)
  exact ((closedCurvatureEntryDerivativeBridgeAt_canonical g x).mdifferentiable
    p u w q).congr_of_eventuallyEq hEntry

theorem covTensor2DerivAt_closedRicciTraceFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w p q : TM x) :
    covTensor2DerivAt g (closedRicciTraceFieldAt g u w) x v p q =
      g.inner x (closedCurvatureCovDerivAt g x v p u w) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E p)
            (extend E (g.leviCivita (extend E u) x v))
            (extend E w) x) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E p) (extend E u)
            (extend E (g.leviCivita (extend E w) x v)) x) q := by
  let F : M → ℝ :=
    fun y ↦ closedRicciTraceFieldAt g u w y (extend E p y) (extend E q y)
  let C : M → ℝ :=
    fun y ↦
      g.inner y
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E p) (extend E u) (extend E w) y)
        (extend E q y)
  have hEntry : F =ᶠ[nhds x] C :=
    (eventually_closedRicciTraceFieldAt_entry_eq_curvature_entry
      (g := g) (u := u) (w := w) (p := p) (q := q)).mono
      fun y hy ↦ by simpa [F, C] using hy
  have hDeriv : extDerivFun F x v = extDerivFun C x v := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
      (CovariantDerivative.extDerivFun_congr hEntry)
  have hBridge :=
    (closedCurvatureEntryDerivativeBridgeAt_canonical g x).extDeriv_eq
      v p u w q
  have hP :
      closedRicciTraceFieldAt g u w x (g.leviCivita (extend E p) x v) q =
        g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E (g.leviCivita (extend E p) x v))
            (extend E u) (extend E w) x) q :=
    closedRicciTraceFieldAt_apply_eq_curvature_entry
      (g := g) (u := u) (w := w)
      (p := g.leviCivita (extend E p) x v) (q := q)
  have hQ :
      closedRicciTraceFieldAt g u w x p (g.leviCivita (extend E q) x v) =
        g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E p) (extend E u) (extend E w) x)
          (g.leviCivita (extend E q) x v) :=
    closedRicciTraceFieldAt_apply_eq_curvature_entry
      (g := g) (u := u) (w := w)
      (p := p) (q := g.leviCivita (extend E q) x v)
  unfold covTensor2DerivAt
  change extDerivFun F x v
      - closedRicciTraceFieldAt g u w x (g.leviCivita (extend E p) x v) q
      - closedRicciTraceFieldAt g u w x p (g.leviCivita (extend E q) x v) =
    g.inner x (closedCurvatureCovDerivAt g x v p u w) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E p)
          (extend E (g.leviCivita (extend E u) x v))
          (extend E w) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E p) (extend E u)
          (extend E (g.leviCivita (extend E w) x v)) x) q
  rw [hDeriv, hBridge, hP, hQ]
  ring

/-- Trace of the closed curvature covariant derivative giving `∇ Ric`. -/
noncomputable def closedCovRicciDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, (Module.finBasis ℝ (TM x)).coord i
    (closedCurvatureCovDerivAt g x v
      ((Module.finBasis ℝ (TM x)) i) u w)

theorem closedCovRicciDerivAt_eq_inner_contraction
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w : TM x) :
    closedCovRicciDerivAt g x v u w =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun i ↦ metricDualVectorAt g x (b.coord i)
      ∑ i, g.inner x (closedCurvatureCovDerivAt g x v (b i) u w) (sharp i)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  unfold closedCovRicciDerivAt
  change (∑ i, b.coord i (closedCurvatureCovDerivAt g x v (b i) u w)) =
    ∑ i, g.inner x (closedCurvatureCovDerivAt g x v (b i) u w) (sharp i)
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coord_eq_inner_metricDualVectorAt_of_basis (g := g) (x := x) (b := b)]

theorem ricciAt_eq_curvature_inner_contraction
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    g.ricciAt x u w =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun i ↦ metricDualVectorAt g x (b.coord i)
      ∑ i, g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E (b i)) (extend E u) (extend E w) x) (sharp i)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  rw [ricciAt_eq_curvature_contraction (g := g) x u w]
  change (∑ i, b.coord i
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (b i)) (extend E u) (extend E w) x)) =
    ∑ i, g.inner x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (b i)) (extend E u) (extend E w) x) (sharp i)
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coord_eq_inner_metricDualVectorAt_of_basis (g := g) (x := x) (b := b)]

/-- Divergence trace of the closed curvature covariant derivative. -/
noncomputable def closedCurvatureDivergenceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w z : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, (Module.finBasis ℝ (TM x)).coord i
    (closedCurvatureCovDerivAt g x
      ((Module.finBasis ℝ (TM x)) i) u w z)

theorem closedCurvatureCovDerivAt_antisymm
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w z : TM x) :
    closedCurvatureCovDerivAt g x v u w z =
      -closedCurvatureCovDerivAt g x v w u z := by
  let Ruw : ∀ y : M, TM y := closedCurvatureFieldAt g u w z
  let Rwu : ∀ y : M, TM y := closedCurvatureFieldAt g w u z
  have hRuw : MDiffAtTangentField Ruw x := by
    simpa [MDiffAtTangentField, Ruw] using
      (closedCurvatureFieldMDifferentiableAt_canonical g x u w z)
  have hfield : Rwu = (-1 : ℝ) • Ruw := by
    funext y
    change
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E u) (extend E z) y =
        (-1 : ℝ) •
          CovariantDerivative.curvatureOp g.leviCivita
            (extend E u) (extend E w) (extend E z) y
    rw [CovariantDerivative.curvatureOp_antisymm_apply]
    simp
  have hcov_neg :
      g.leviCivita Rwu x v = -g.leviCivita Ruw x v := by
    have hsmul :=
      g.leviCivita.isCovariantDerivativeOnUniv.smul_const
        (-1 : ℝ) hRuw
    rw [hfield]
    have happ := congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hsmul
    simpa using happ
  let Γu : TM x := g.leviCivita (extend E u) x v
  let Γw : TM x := g.leviCivita (extend E w) x v
  let Γz : TM x := g.leviCivita (extend E z) x v
  have hΓu :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E Γu) (extend E z) x =
        -CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γu) (extend E w) (extend E z) x := by
    simpa [Γu] using
      CovariantDerivative.curvatureOp_antisymm_apply
        (cov := g.leviCivita)
        (extend E w) (extend E Γu) (extend E z) x
  have hΓw :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γw) (extend E u) (extend E z) x =
        -CovariantDerivative.curvatureOp g.leviCivita
          (extend E u) (extend E Γw) (extend E z) x := by
    simpa [Γw] using
      CovariantDerivative.curvatureOp_antisymm_apply
        (cov := g.leviCivita)
        (extend E Γw) (extend E u) (extend E z) x
  have hΓz :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E u) (extend E Γz) x =
        -CovariantDerivative.curvatureOp g.leviCivita
          (extend E u) (extend E w) (extend E Γz) x := by
    simpa [Γz] using
      CovariantDerivative.curvatureOp_antisymm_apply
        (cov := g.leviCivita)
        (extend E w) (extend E u) (extend E Γz) x
  unfold closedCurvatureCovDerivAt
  change g.leviCivita Ruw x v
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γu) (extend E w) (extend E z) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E u) (extend E Γw) (extend E z) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E u) (extend E w) (extend E Γz) x =
    -(g.leviCivita Rwu x v
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γw) (extend E u) (extend E z) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E Γu) (extend E z) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E u) (extend E Γz) x)
  rw [hcov_neg, hΓu, hΓw, hΓz]
  module

theorem closed_first_contracted_bianchi_of_second_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hSecond :
      ∀ u v w z : TM x,
        closedCurvatureCovDerivAt g x v u w z
          + closedCurvatureCovDerivAt g x u w v z
          + closedCurvatureCovDerivAt g x w v u z = 0)
    (v w z : TM x) :
    closedCovRicciDerivAt g x v w z
      + closedCurvatureDivergenceAt g x w v z
      - closedCovRicciDerivAt g x w v z = 0 := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  unfold closedCovRicciDerivAt closedCurvatureDivergenceAt
  change
      (∑ i, b.coord i (closedCurvatureCovDerivAt g x v (b i) w z))
        + (∑ i, b.coord i (closedCurvatureCovDerivAt g x (b i) w v z))
        - (∑ i, b.coord i (closedCurvatureCovDerivAt g x w (b i) v z)) = 0
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have hcyc := hSecond (b i) v w z
  have hanti :
      closedCurvatureCovDerivAt g x w v (b i) z =
        -closedCurvatureCovDerivAt g x w (b i) v z :=
    closedCurvatureCovDerivAt_antisymm (g := g) (x := x) w v (b i) z
  rw [hanti] at hcyc
  have happ := congrArg (fun m : TM x ↦ b.coord i m) hcyc
  simpa [map_add, map_neg] using happ

/-- Model-shaped Ricci divergence trace, using raised dual basis vectors. -/
noncomputable def closedRicciDivergenceTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  ∑ i, closedCovRicciDerivAt g x
    (metricDualVectorAt g x (b.coord i)) w (b i)

/-- Model-shaped derivative of the scalar Ricci trace. -/
noncomputable def closedScalarContractionDerivTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  ∑ i, closedCovRicciDerivAt g x w
    (metricDualVectorAt g x (b.coord i)) (b i)

/--
Moving-point Ricci derivative expansion in canonical extension slots.

This is the closed analogue of the model trace-derivative computation feeding
`covRicciDeriv_eq_tensor_deriv`: the exterior derivative of the Ricci entries
is the curvature-level covariant Ricci derivative plus the two tensor-slot
Levi-Civita corrections.
-/
def ClosedRicciDerivativeExpansionAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ v u w : TM x,
    extDerivFun
        (fun y : M ↦ g.ricciAt y (extend E u y) (extend E w y)) x v =
      closedCovRicciDerivAt g x v u w
        + g.ricciAt x (g.leviCivita (extend E u) x v) w
        + g.ricciAt x u (g.leviCivita (extend E w) x v)

theorem covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : ClosedRicciDerivativeExpansionAt g x)
    (v u w : TM x) :
    covTensor2DerivAt g (ricciVariationField g) x v u w =
      closedCovRicciDerivAt g x v u w := by
  unfold covTensor2DerivAt ricciVariationField
  rw [hRic v u w]
  ring

/--
Raw double contraction of the closed first-contracted Bianchi identity.
This is the closed analogue of `coord_twice_contracted_bianchi_raw`; the
native second-Bianchi proof supplies `hFirst`, and the raised contraction
machinery supplies the middle-term identification.
-/
theorem closed_twice_contracted_bianchi_raw_of_first_contracted
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hFirst :
      ∀ v w z : TM x,
        closedCovRicciDerivAt g x v w z
          + closedCurvatureDivergenceAt g x w v z
          - closedCovRicciDerivAt g x w v z = 0)
    (w : TM x) :
    closedRicciDivergenceTraceAt g x w
      + (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        let b := Module.finBasis ℝ (TM x)
        ∑ i, closedCurvatureDivergenceAt g x w
          (metricDualVectorAt g x (b.coord i)) (b i))
      = closedScalarContractionDerivTraceAt g x w := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  unfold closedRicciDivergenceTraceAt closedScalarContractionDerivTraceAt
  change (∑ i, closedCovRicciDerivAt g x (sharp i) w (b i))
      + (∑ i, closedCurvatureDivergenceAt g x w (sharp i) (b i)) =
    ∑ i, closedCovRicciDerivAt g x w (sharp i) (b i)
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have h := hFirst (sharp i) w (b i)
  linarith

theorem closed_twice_contracted_bianchi_trace_of_raw
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRaw :
      ∀ w : TM x,
        closedRicciDivergenceTraceAt g x w
          + (letI : FiniteDimensional ℝ (TM x) :=
              inferInstanceAs (FiniteDimensional ℝ E)
            let b := Module.finBasis ℝ (TM x)
            ∑ i, closedCurvatureDivergenceAt g x w
              (metricDualVectorAt g x (b.coord i)) (b i))
          = closedScalarContractionDerivTraceAt g x w)
    (hMiddle :
      ∀ w : TM x,
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          let b := Module.finBasis ℝ (TM x)
          ∑ i, closedCurvatureDivergenceAt g x w
            (metricDualVectorAt g x (b.coord i)) (b i))
          = closedRicciDivergenceTraceAt g x w)
    (w : TM x) :
    2 * closedRicciDivergenceTraceAt g x w =
      closedScalarContractionDerivTraceAt g x w := by
  have h := hRaw w
  rw [hMiddle w] at h
  linarith

theorem closed_twice_contracted_bianchi_raw_of_second_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hSecond :
      ∀ u v w z : TM x,
        closedCurvatureCovDerivAt g x v u w z
          + closedCurvatureCovDerivAt g x u w v z
          + closedCurvatureCovDerivAt g x w v u z = 0)
    (w : TM x) :
    closedRicciDivergenceTraceAt g x w
      + (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        let b := Module.finBasis ℝ (TM x)
        ∑ i, closedCurvatureDivergenceAt g x w
          (metricDualVectorAt g x (b.coord i)) (b i))
      = closedScalarContractionDerivTraceAt g x w :=
  closed_twice_contracted_bianchi_raw_of_first_contracted
    (g := g) (x := x)
    (closed_first_contracted_bianchi_of_second_bianchi
      (g := g) (x := x) hSecond)
    w

theorem closed_twice_contracted_bianchi_trace_of_second_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hSecond :
      ∀ u v w z : TM x,
        closedCurvatureCovDerivAt g x v u w z
          + closedCurvatureCovDerivAt g x u w v z
          + closedCurvatureCovDerivAt g x w v u z = 0)
    (hMiddle :
      ∀ w : TM x,
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          let b := Module.finBasis ℝ (TM x)
          ∑ i, closedCurvatureDivergenceAt g x w
            (metricDualVectorAt g x (b.coord i)) (b i))
          = closedRicciDivergenceTraceAt g x w)
    (w : TM x) :
    2 * closedRicciDivergenceTraceAt g x w =
      closedScalarContractionDerivTraceAt g x w :=
  closed_twice_contracted_bianchi_trace_of_raw
    (g := g) (x := x)
    (closed_twice_contracted_bianchi_raw_of_second_bianchi
      (g := g) (x := x) hSecond)
    hMiddle w

theorem eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hSecond :
      ∀ᶠ y in nhds x, ∀ u v w z : TM y,
        closedCurvatureCovDerivAt g y v u w z
          + closedCurvatureCovDerivAt g y u w v z
          + closedCurvatureCovDerivAt g y w v u z = 0)
    (hMiddle :
      ∀ᶠ y in nhds x, ∀ w : TM y,
        (letI : FiniteDimensional ℝ (TM y) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          let b := Module.finBasis ℝ (TM y)
          ∑ i, closedCurvatureDivergenceAt g y w
            (metricDualVectorAt g y (b.coord i)) (b i))
          = closedRicciDivergenceTraceAt g y w) :
    ∀ᶠ y in nhds x, ∀ w : TM y,
      2 * closedRicciDivergenceTraceAt g y w =
        closedScalarContractionDerivTraceAt g y w := by
  filter_upwards [hSecond, hMiddle] with y hySecond hyMiddle
  intro w
  exact closed_twice_contracted_bianchi_trace_of_second_bianchi
    (g := g) (x := y) hySecond hyMiddle w

set_option maxHeartbeats 5000000 in
/-- The inverse-Gram derivative contraction cancels the two Levi-Civita slot corrections. -/
theorem gram_inv_deriv_contraction_eq_leviCivita_corrections
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hAddL : Tensor2AddLeft h) (hSMulL : Tensor2SMulLeft h)
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, ∑ j,
        extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
          h x (gramFrame x x i) (gramFrame x x j))
      =
      (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E);
      let b := Module.finBasis ℝ (TM x);
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun i ↦ metricDualVectorAt g x (b.coord i);
      -∑ i, h x (g.leviCivita (extend E (b i)) x w) (sharp i)
        - ∑ i, h x (b i) (g.leviCivita (extend E (sharp i)) x w)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let G : Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ := gramMatrix g x x
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  let Γ : TM x → TM x := fun p ↦ g.leviCivita (extend E p) x w
  let dG : Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k l ↦ extDerivFun (fun y : M ↦ gramMatrix g x y k l) x w
  have hsharp : ∀ i, sharp i = ∑ j, G⁻¹ i j • b j := by
    intro i
    simpa [sharp, b, G] using
      metricDualVectorAt_finBasis_coord_eq_sum_gram_inv (g := g) (x := x) i
  have hHsharp : ∀ i l,
      h x (b i) (sharp l) =
        ∑ j, G⁻¹ l j * h x (b i) (b j) := by
    intro i l
    rw [hsharp l]
    exact tensor2_sum_right (h := h) hAddR hSMulR x (b i)
      (fun j ↦ G⁻¹ l j) b
  set Γlin : TM x →ₗ[ℝ] TM x :=
    IsLinearMap.mk' Γ
      ⟨(by
          intro p q
          change g.leviCivita (extend E (p + q)) x w =
            g.leviCivita (extend E p) x w + g.leviCivita (extend E q) x w
          rw [extend_tangent_add (x := x) p q]
          have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E p))
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E q))
          simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L w) hadd),
        (by
          intro c p
          change g.leviCivita (extend E (c • p)) x w =
            c • g.leviCivita (extend E p) x w
          rw [extend_tangent_smul (x := x) c p]
          have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E p))
          simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L w) hsmul)⟩ with hΓlin
  have hΓsharp : ∀ i, Γ (sharp i) = ∑ k, G⁻¹ i k • Γ (b k) := by
    intro i
    change Γlin (sharp i) = ∑ k, G⁻¹ i k • Γlin (b k)
    rw [hsharp i]
    simpa using map_sum Γlin (fun k ↦ G⁻¹ i k • b k) Finset.univ
  have hRightΓ : ∀ i k,
      h x (b i) (Γ (b k)) =
        ∑ l, g.inner x (Γ (b k)) (b l) * h x (b i) (sharp l) := by
    intro i k
    simpa [b, sharp, Γ] using
      tensor2_metricDual_expansion_right
        (g := g) (h := h) hAddR hSMulR x (b i) (Γ (b k))
  have hLeftΓ : ∀ l,
      h x (Γ (b l)) (sharp l) =
        ∑ i, g.inner x (Γ (b l)) (sharp i) * h x (b i) (sharp l) := by
    intro l
    simpa [b, sharp, Γ] using
      tensor2_basis_expansion_left
        (g := g) (h := h) hAddL hSMulL x (Γ (b l)) (sharp l)
  have hΓsharp_h : ∀ i,
      h x (b i) (Γ (sharp i)) =
        ∑ k, G⁻¹ i k * h x (b i) (Γ (b k)) := by
    intro i
    rw [hΓsharp i]
    exact tensor2_sum_right (h := h) hAddR hSMulR x (b i)
      (fun k ↦ G⁻¹ i k) (fun k ↦ Γ (b k))
  have hFirst :
      (∑ i, ∑ k, ∑ l,
          G⁻¹ i k * g.inner x (Γ (b k)) (b l) * h x (b i) (sharp l))
        =
      ∑ i, h x (b i) (Γ (sharp i)) := by
    calc
      (∑ i, ∑ k, ∑ l,
          G⁻¹ i k * g.inner x (Γ (b k)) (b l) * h x (b i) (sharp l))
          = ∑ i, ∑ k, G⁻¹ i k * h x (b i) (Γ (b k)) := by
            refine Finset.sum_congr rfl fun i _hi ↦ ?_
            refine Finset.sum_congr rfl fun k _hk ↦ ?_
            rw [hRightΓ i k]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            ring
      _ = ∑ i, h x (b i) (Γ (sharp i)) := by
            refine (Finset.sum_congr rfl fun i _hi ↦ ?_).symm
            exact hΓsharp_h i
  have hSecond :
      (∑ i, ∑ k, ∑ l,
          G⁻¹ i k * g.inner x (b k) (Γ (b l)) * h x (b i) (sharp l))
        =
      ∑ l, h x (Γ (b l)) (sharp l) := by
    calc
      (∑ i, ∑ k, ∑ l,
          G⁻¹ i k * g.inner x (b k) (Γ (b l)) * h x (b i) (sharp l))
          = ∑ l, ∑ i,
              (∑ k, G⁻¹ i k * g.inner x (Γ (b l)) (b k)) *
                h x (b i) (sharp l) := by
            calc
              (∑ i, ∑ k, ∑ l,
                  G⁻¹ i k * g.inner x (b k) (Γ (b l)) * h x (b i) (sharp l))
                  = ∑ i, ∑ l, ∑ k,
                      G⁻¹ i k * g.inner x (b k) (Γ (b l)) *
                        h x (b i) (sharp l) := by
                    refine Finset.sum_congr rfl fun i _hi ↦ ?_
                    rw [Finset.sum_comm]
              _ = ∑ l, ∑ i, ∑ k,
                    G⁻¹ i k * g.inner x (b k) (Γ (b l)) *
                      h x (b i) (sharp l) := by
                    rw [Finset.sum_comm]
              _ = ∑ l, ∑ i,
                    (∑ k, G⁻¹ i k * g.inner x (Γ (b l)) (b k)) *
                      h x (b i) (sharp l) := by
                    refine Finset.sum_congr rfl fun l _hl ↦ ?_
                    refine Finset.sum_congr rfl fun i _hi ↦ ?_
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun k _hk ↦ ?_
                    rw [g.inner_symm x (b k) (Γ (b l))]
      _ = ∑ l, ∑ i,
            g.inner x (Γ (b l)) (sharp i) * h x (b i) (sharp l) := by
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            refine Finset.sum_congr rfl fun i _hi ↦ ?_
            have hpair : g.inner x (Γ (b l)) (sharp i) =
                ∑ k, G⁻¹ i k * g.inner x (Γ (b l)) (b k) := by
              calc
                g.inner x (Γ (b l)) (sharp i) =
                    g.inner x (sharp i) (Γ (b l)) := g.inner_symm x (Γ (b l)) (sharp i)
                _ = g.inner x (∑ k, G⁻¹ i k • b k) (Γ (b l)) := by
                      rw [hsharp i]
                _ = ∑ k, G⁻¹ i k * g.inner x (b k) (Γ (b l)) := by
                      have hmap := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L (Γ (b l)))
                        (map_sum (g.inner x) (fun k ↦ G⁻¹ i k • b k) Finset.univ)
                      simpa [smul_eq_mul] using hmap
                _ = ∑ k, G⁻¹ i k * g.inner x (Γ (b l)) (b k) := by
                      refine Finset.sum_congr rfl fun k _hk ↦ ?_
                      rw [g.inner_symm x (b k) (Γ (b l))]
            rw [hpair]
      _ = ∑ l, h x (Γ (b l)) (sharp l) := by
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            exact (hLeftΓ l).symm
  have hcontract :
      (∑ i, ∑ j,
        extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
          h x (b i) (b j))
        =
      -∑ i, h x (Γ (b i)) (sharp i)
        - ∑ i, h x (b i) (Γ (sharp i)) := by
    calc
      (∑ i, ∑ j,
        extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
          h x (b i) (b j))
          = -∑ i, ∑ k, ∑ l,
              G⁻¹ i k * dG k l *
                (∑ j, G⁻¹ l j * h x (b i) (b j)) := by
            simp_rw [gramMatrix_inv_extDerivFun_eq_neg_sum (g := g) (x := x) (w := w)]
            change
              (∑ i, ∑ j,
                (-(∑ k, ∑ l, G⁻¹ i k * dG k l * G⁻¹ l j)) *
                  h x (b i) (b j))
                =
              -∑ i, ∑ k, ∑ l,
                G⁻¹ i k * dG k l *
                  (∑ j, G⁻¹ l j * h x (b i) (b j))
            calc
              (∑ i, ∑ j,
                (-(∑ k, ∑ l, G⁻¹ i k * dG k l * G⁻¹ l j)) *
                  h x (b i) (b j))
                  = -∑ i, ∑ j, ∑ k, ∑ l,
                      G⁻¹ i k * dG k l * G⁻¹ l j * h x (b i) (b j) := by
                    simp [Finset.sum_neg_distrib, Finset.sum_mul, neg_mul, mul_assoc]
              _ = -∑ i, ∑ k, ∑ l, ∑ j,
                      G⁻¹ i k * dG k l * G⁻¹ l j * h x (b i) (b j) := by
                    congr 1
                    refine Finset.sum_congr rfl fun i _hi ↦ ?_
                    calc
                      (∑ j, ∑ k, ∑ l,
                          G⁻¹ i k * dG k l * G⁻¹ l j * h x (b i) (b j))
                          = ∑ k, ∑ j, ∑ l,
                              G⁻¹ i k * dG k l * G⁻¹ l j * h x (b i) (b j) := by
                            rw [Finset.sum_comm]
                      _ = ∑ k, ∑ l, ∑ j,
                              G⁻¹ i k * dG k l * G⁻¹ l j * h x (b i) (b j) := by
                            refine Finset.sum_congr rfl fun k _hk ↦ ?_
                            rw [Finset.sum_comm]
              _ = -∑ i, ∑ k, ∑ l,
                    G⁻¹ i k * dG k l *
                      (∑ j, G⁻¹ l j * h x (b i) (b j)) := by
                    congr 1
                    refine Finset.sum_congr rfl fun i _hi ↦ ?_
                    refine Finset.sum_congr rfl fun k _hk ↦ ?_
                    refine Finset.sum_congr rfl fun l _hl ↦ ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun j _hj ↦ ?_
                    ring
      _ = -∑ i, ∑ k, ∑ l,
              G⁻¹ i k * dG k l * h x (b i) (sharp l) := by
            refine congrArg Neg.neg ?_
            refine Finset.sum_congr rfl fun i _hi ↦ ?_
            refine Finset.sum_congr rfl fun k _hk ↦ ?_
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            rw [hHsharp]
      _ = -∑ i, ∑ k, ∑ l,
              G⁻¹ i k *
                (g.inner x (Γ (b k)) (b l) +
                  g.inner x (b k) (Γ (b l))) *
                h x (b i) (sharp l) := by
            refine congrArg Neg.neg ?_
            refine Finset.sum_congr rfl fun i _hi ↦ ?_
            refine Finset.sum_congr rfl fun k _hk ↦ ?_
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            change G⁻¹ i k *
                extDerivFun (fun y : M ↦ gramMatrix g x y k l) x w *
                h x (b i) (sharp l) =
              G⁻¹ i k *
                (g.inner x (Γ (b k)) (b l) +
                  g.inner x (b k) (Γ (b l))) *
                h x (b i) (sharp l)
            rw [gramMatrix_extDerivFun_eq_leviCivita (g := g) (x := x) (v := w) k l]
      _ = -((∑ i, ∑ k, ∑ l,
              G⁻¹ i k * g.inner x (Γ (b k)) (b l) * h x (b i) (sharp l))
            + (∑ i, ∑ k, ∑ l,
              G⁻¹ i k * g.inner x (b k) (Γ (b l)) * h x (b i) (sharp l))) := by
            congr 1
            simp_rw [mul_add, add_mul]
            simp [Finset.sum_add_distrib, mul_assoc]
      _ = -((∑ i, h x (b i) (Γ (sharp i))) +
            (∑ i, h x (Γ (b i)) (sharp i))) := by
            rw [hFirst, hSecond]
      _ = -∑ i, h x (Γ (b i)) (sharp i)
          - ∑ i, h x (b i) (Γ (sharp i)) := by
            ring
  simpa [gramFrame, b, sharp, Γ] using hcontract

@[simp] theorem covTensor2DerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v p q : TM x) :
    covTensor2DerivAt g (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x v p q = 0 := by
  simp [covTensor2DerivAt, extDerivFun_zero_at]

/--
Spatial differentiability of the covariant derivative of a raw `(0,2)` tensor
when all three tensor slots are transported by canonical extensions.
-/
def CovTensor2DerivExtDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ v p q : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ covTensor2DerivAt g h y
        (extend E v y) (extend E p y) (extend E q y)) x

/--
The closed second covariant derivative of a raw `(0,2)` tensor, obtained by
differentiating `covTensor2DerivAt` and subtracting the three transported-slot
Levi-Civita corrections.
-/
noncomputable def covTensor2SecondDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u v p q : TM x) : ℝ :=
  extDerivFun
      (fun y : M ↦ covTensor2DerivAt g h y
        (extend E v y) (extend E p y) (extend E q y)) x u
    - covTensor2DerivAt g h x (g.leviCivita (extend E v) x u) p q
    - covTensor2DerivAt g h x v (g.leviCivita (extend E p) x u) q
    - covTensor2DerivAt g h x v p (g.leviCivita (extend E q) x u)

/-- The expanded right-hand side of differentiating a `covTensor2DerivAt` entry. -/
noncomputable def covTensor2SecondDerivExpansionAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u v p q : TM x) : ℝ :=
  covTensor2SecondDerivAt g h x u v p q
    + covTensor2DerivAt g h x (g.leviCivita (extend E v) x u) p q
    + covTensor2DerivAt g h x v (g.leviCivita (extend E p) x u) q
    + covTensor2DerivAt g h x v p (g.leviCivita (extend E q) x u)

/-- Unfolding bridge from the raw derivative of `∇h` to `∇²h` plus corrections. -/
theorem extDerivFun_covTensor2DerivAt_extend_eq_secondDerivExpansion
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u v p q : TM x) :
    extDerivFun
        (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q y)) x u =
      covTensor2SecondDerivExpansionAt g h x u v p q := by
  unfold covTensor2SecondDerivExpansionAt covTensor2SecondDerivAt
  ring

theorem covTensor2DerivExtDifferentiableAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    CovTensor2DerivExtDifferentiableAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x := by
  intro v p q
  have hzero :
      (fun y : M ↦ covTensor2DerivAt g
        (fun z : M ↦ fun _ _ : TM z ↦ (0 : ℝ)) y
        (extend E v y) (extend E p y) (extend E q y)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    simp
  rw [hzero]
  exact mdifferentiableAt_const

@[simp] theorem covTensor2SecondDerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u v p q : TM x) :
    covTensor2SecondDerivAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x u v p q = 0 := by
  unfold covTensor2SecondDerivAt
  have hzero :
      (fun y : M ↦ covTensor2DerivAt g
        (fun z : M ↦ fun _ _ : TM z ↦ (0 : ℝ)) y
        (extend E v y) (extend E p y) (extend E q y)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    simp
  rw [hzero]
  simp [extDerivFun_zero_at]

@[simp] theorem covTensor2SecondDerivExpansionAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u v p q : TM x) :
    covTensor2SecondDerivExpansionAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x u v p q = 0 := by
  simp [covTensor2SecondDerivExpansionAt]

theorem covTensor2DerivAt_add_deriv
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hAddL : Tensor2AddLeft h) (hAddR : Tensor2AddRight h)
    (v₁ v₂ p q : TM x) :
    covTensor2DerivAt g h x (v₁ + v₂) p q =
      covTensor2DerivAt g h x v₁ p q + covTensor2DerivAt g h x v₂ p q := by
  unfold covTensor2DerivAt
  rw [map_add]
  simp only [ContinuousLinearMap.map_add]
  rw [hAddL x ((g.leviCivita (extend E p) x v₁))
      ((g.leviCivita (extend E p) x v₂)) q]
  rw [hAddR x p ((g.leviCivita (extend E q) x v₁))
      ((g.leviCivita (extend E q) x v₂))]
  ring

theorem covTensor2DerivAt_smul_deriv
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSMulL : Tensor2SMulLeft h) (hSMulR : Tensor2SMulRight h)
    (c : ℝ) (v p q : TM x) :
    covTensor2DerivAt g h x (c • v) p q =
      c • covTensor2DerivAt g h x v p q := by
  unfold covTensor2DerivAt
  rw [map_smul]
  simp only [ContinuousLinearMap.map_smul]
  rw [hSMulL x c ((g.leviCivita (extend E p) x v)) q]
  rw [hSMulR x c p ((g.leviCivita (extend E q) x v))]
  ring

theorem covTensor2DerivAt_add_left
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hAddL : Tensor2AddLeft h)
    (v p₁ p₂ q : TM x) :
    covTensor2DerivAt g h x v (p₁ + p₂) q =
      covTensor2DerivAt g h x v p₁ q + covTensor2DerivAt g h x v p₂ q := by
  unfold covTensor2DerivAt
  have hfun :
      (fun y : M ↦ h y (extend E (p₁ + p₂) y) (extend E q y)) =
        (fun y : M ↦ h y (extend E p₁ y) (extend E q y)) +
          fun y : M ↦ h y (extend E p₂ y) (extend E q y) := by
    funext y
    rw [extend_tangent_add (x := x) p₁ p₂]
    exact hAddL y (extend E p₁ y) (extend E p₂ y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_add (hDiff p₁ q) (hDiff p₂ q)]
  have hΓ :
      g.leviCivita (extend E (p₁ + p₂)) x v =
        g.leviCivita (extend E p₁) x v + g.leviCivita (extend E p₂) x v := by
    rw [extend_tangent_add (x := x) p₁ p₂]
    have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E p₁))
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E p₂))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hadd
  rw [hΓ]
  rw [hAddL x ((g.leviCivita (extend E p₁) x v))
    ((g.leviCivita (extend E p₂) x v)) q]
  rw [hAddL x p₁ p₂ ((g.leviCivita (extend E q) x v))]
  simp only [ContinuousLinearMap.add_apply]
  ring_nf

theorem covTensor2DerivAt_smul_left
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hSMulL : Tensor2SMulLeft h)
    (c : ℝ) (v p q : TM x) :
    covTensor2DerivAt g h x v (c • p) q =
      c • covTensor2DerivAt g h x v p q := by
  unfold covTensor2DerivAt
  have hfun :
      (fun y : M ↦ h y (extend E (c • p) y) (extend E q y)) =
        c • (fun y : M ↦ h y (extend E p y) (extend E q y)) := by
    funext y
    rw [extend_tangent_smul (x := x) c p]
    exact hSMulL y c (extend E p y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_const_smul_at (hDiff p q) c]
  have hΓ :
      g.leviCivita (extend E (c • p)) x v =
        c • g.leviCivita (extend E p) x v := by
    rw [extend_tangent_smul (x := x) c p]
    have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E p))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hsmul
  rw [hΓ]
  rw [hSMulL x c ((g.leviCivita (extend E p) x v)) q]
  rw [hSMulL x c p ((g.leviCivita (extend E q) x v))]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring_nf

theorem covTensor2DerivAt_add_right
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hAddR : Tensor2AddRight h)
    (v p q₁ q₂ : TM x) :
    covTensor2DerivAt g h x v p (q₁ + q₂) =
      covTensor2DerivAt g h x v p q₁ + covTensor2DerivAt g h x v p q₂ := by
  unfold covTensor2DerivAt
  have hfun :
      (fun y : M ↦ h y (extend E p y) (extend E (q₁ + q₂) y)) =
        (fun y : M ↦ h y (extend E p y) (extend E q₁ y)) +
          fun y : M ↦ h y (extend E p y) (extend E q₂ y) := by
    funext y
    rw [extend_tangent_add (x := x) q₁ q₂]
    exact hAddR y (extend E p y) (extend E q₁ y) (extend E q₂ y)
  rw [hfun]
  rw [extDerivFun_add (hDiff p q₁) (hDiff p q₂)]
  have hΓ :
      g.leviCivita (extend E (q₁ + q₂)) x v =
        g.leviCivita (extend E q₁) x v + g.leviCivita (extend E q₂) x v := by
    rw [extend_tangent_add (x := x) q₁ q₂]
    have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E q₁))
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E q₂))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hadd
  rw [hΓ]
  rw [hAddR x ((g.leviCivita (extend E p) x v)) q₁ q₂]
  rw [hAddR x p ((g.leviCivita (extend E q₁) x v))
    ((g.leviCivita (extend E q₂) x v))]
  simp only [ContinuousLinearMap.add_apply]
  ring_nf

theorem covTensor2DerivAt_smul_right
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hSMulR : Tensor2SMulRight h)
    (c : ℝ) (v p q : TM x) :
    covTensor2DerivAt g h x v p (c • q) =
      c • covTensor2DerivAt g h x v p q := by
  unfold covTensor2DerivAt
  have hfun :
      (fun y : M ↦ h y (extend E p y) (extend E (c • q) y)) =
        c • (fun y : M ↦ h y (extend E p y) (extend E q y)) := by
    funext y
    rw [extend_tangent_smul (x := x) c q]
    exact hSMulR y c (extend E p y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_const_smul_at (hDiff p q) c]
  have hΓ :
      g.leviCivita (extend E (c • q)) x v =
        c • g.leviCivita (extend E q) x v := by
    rw [extend_tangent_smul (x := x) c q]
    have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E q))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) hsmul
  rw [hΓ]
  rw [hSMulR x c ((g.leviCivita (extend E p) x v)) q]
  rw [hSMulR x c p ((g.leviCivita (extend E q) x v))]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring_nf

theorem covTensor2SecondDerivAt_add_outer
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hAddL : Tensor2AddLeft h) (hAddR : Tensor2AddRight h)
    (u₁ u₂ v p q : TM x) :
    covTensor2SecondDerivAt g h x (u₁ + u₂) v p q =
      covTensor2SecondDerivAt g h x u₁ v p q
        + covTensor2SecondDerivAt g h x u₂ v p q := by
  unfold covTensor2SecondDerivAt
  simp only [ContinuousLinearMap.map_add]
  rw [covTensor2DerivAt_add_deriv
      (g := g) (h := h) (x := x) hAddL hAddR
      (g.leviCivita (extend E v) x u₁)
      (g.leviCivita (extend E v) x u₂) p q]
  rw [covTensor2DerivAt_add_left
      (g := g) (h := h) (x := x) hDiff hAddL
      v (g.leviCivita (extend E p) x u₁)
      (g.leviCivita (extend E p) x u₂) q]
  rw [covTensor2DerivAt_add_right
      (g := g) (h := h) (x := x) hDiff hAddR
      v p (g.leviCivita (extend E q) x u₁)
      (g.leviCivita (extend E q) x u₂)]
  ring

theorem covTensor2SecondDerivAt_smul_outer
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hSMulL : Tensor2SMulLeft h) (hSMulR : Tensor2SMulRight h)
    (c : ℝ) (u v p q : TM x) :
    covTensor2SecondDerivAt g h x (c • u) v p q =
      c • covTensor2SecondDerivAt g h x u v p q := by
  unfold covTensor2SecondDerivAt
  simp only [ContinuousLinearMap.map_smul]
  rw [covTensor2DerivAt_smul_deriv
      (g := g) (h := h) (x := x) hSMulL hSMulR c
      (g.leviCivita (extend E v) x u) p q]
  rw [covTensor2DerivAt_smul_left
      (g := g) (h := h) (x := x) hDiff hSMulL c
      v (g.leviCivita (extend E p) x u) q]
  rw [covTensor2DerivAt_smul_right
      (g := g) (h := h) (x := x) hDiff hSMulR c
      v p (g.leviCivita (extend E q) x u)]
  simp only [smul_eq_mul]
  ring

theorem covTensor2SecondDerivAt_add_inner
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSecond : CovTensor2DerivExtDifferentiableAt g h x)
    (hAddL : Tensor2AddLeft h) (hAddR : Tensor2AddRight h)
    (u v₁ v₂ p q : TM x) :
    covTensor2SecondDerivAt g h x u (v₁ + v₂) p q =
      covTensor2SecondDerivAt g h x u v₁ p q
        + covTensor2SecondDerivAt g h x u v₂ p q := by
  unfold covTensor2SecondDerivAt
  have hfun :
      (fun y : M ↦ covTensor2DerivAt g h y
          (extend E (v₁ + v₂) y) (extend E p y) (extend E q y)) =
        (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v₁ y) (extend E p y) (extend E q y)) +
        fun y : M ↦ covTensor2DerivAt g h y
          (extend E v₂ y) (extend E p y) (extend E q y) := by
    funext y
    rw [extend_tangent_add (x := x) v₁ v₂]
    exact covTensor2DerivAt_add_deriv
      (g := g) (h := h) (x := y) hAddL hAddR
      (extend E v₁ y) (extend E v₂ y) (extend E p y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_add (hSecond v₁ p q) (hSecond v₂ p q)]
  have hΓv :
      g.leviCivita (extend E (v₁ + v₂)) x u =
        g.leviCivita (extend E v₁) x u
          + g.leviCivita (extend E v₂) x u := by
    rw [extend_tangent_add (x := x) v₁ v₂]
    have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E v₁))
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E v₂))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hadd
  rw [hΓv]
  rw [covTensor2DerivAt_add_deriv
      (g := g) (h := h) (x := x) hAddL hAddR
      (g.leviCivita (extend E v₁) x u)
      (g.leviCivita (extend E v₂) x u) p q]
  rw [covTensor2DerivAt_add_deriv
      (g := g) (h := h) (x := x) hAddL hAddR
      v₁ v₂ (g.leviCivita (extend E p) x u) q]
  rw [covTensor2DerivAt_add_deriv
      (g := g) (h := h) (x := x) hAddL hAddR
      v₁ v₂ p (g.leviCivita (extend E q) x u)]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem covTensor2SecondDerivAt_smul_inner
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSecond : CovTensor2DerivExtDifferentiableAt g h x)
    (hSMulL : Tensor2SMulLeft h) (hSMulR : Tensor2SMulRight h)
    (c : ℝ) (u v p q : TM x) :
    covTensor2SecondDerivAt g h x u (c • v) p q =
      c • covTensor2SecondDerivAt g h x u v p q := by
  unfold covTensor2SecondDerivAt
  have hfun :
      (fun y : M ↦ covTensor2DerivAt g h y
          (extend E (c • v) y) (extend E p y) (extend E q y)) =
        c • (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q y)) := by
    funext y
    rw [extend_tangent_smul (x := x) c v]
    exact covTensor2DerivAt_smul_deriv
      (g := g) (h := h) (x := y) hSMulL hSMulR
      c (extend E v y) (extend E p y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_const_smul_at (hSecond v p q) c]
  have hΓv :
      g.leviCivita (extend E (c • v)) x u =
        c • g.leviCivita (extend E v) x u := by
    rw [extend_tangent_smul (x := x) c v]
    have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E v))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hsmul
  rw [hΓv]
  rw [covTensor2DerivAt_smul_deriv
      (g := g) (h := h) (x := x) hSMulL hSMulR c
      (g.leviCivita (extend E v) x u) p q]
  rw [covTensor2DerivAt_smul_deriv
      (g := g) (h := h) (x := x) hSMulL hSMulR c
      v (g.leviCivita (extend E p) x u) q]
  rw [covTensor2DerivAt_smul_deriv
      (g := g) (h := h) (x := x) hSMulL hSMulR c
      v p (g.leviCivita (extend E q) x u)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem covTensor2SecondDerivAt_add_left
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSecond : CovTensor2DerivExtDifferentiableAt g h x)
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hAddL : Tensor2AddLeft h)
    (u v p₁ p₂ q : TM x) :
    covTensor2SecondDerivAt g h x u v (p₁ + p₂) q =
      covTensor2SecondDerivAt g h x u v p₁ q
        + covTensor2SecondDerivAt g h x u v p₂ q := by
  unfold covTensor2SecondDerivAt
  have hfun :
      (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E (p₁ + p₂) y) (extend E q y)) =
        (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p₁ y) (extend E q y)) +
        fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p₂ y) (extend E q y) := by
    funext y
    rw [extend_tangent_add (x := x) p₁ p₂]
    exact covTensor2DerivAt_add_left
      (g := g) (h := h) (x := y) (hDiff y) hAddL
      (extend E v y) (extend E p₁ y) (extend E p₂ y)
      (extend E q y)
  rw [hfun]
  rw [extDerivFun_add (hSecond v p₁ q) (hSecond v p₂ q)]
  have hΓp :
      g.leviCivita (extend E (p₁ + p₂)) x u =
        g.leviCivita (extend E p₁) x u
          + g.leviCivita (extend E p₂) x u := by
    rw [extend_tangent_add (x := x) p₁ p₂]
    have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E p₁))
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E p₂))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hadd
  rw [hΓp]
  rw [covTensor2DerivAt_add_left
      (g := g) (h := h) (x := x) (hDiff x) hAddL
      (g.leviCivita (extend E v) x u) p₁ p₂ q]
  rw [covTensor2DerivAt_add_left
      (g := g) (h := h) (x := x) (hDiff x) hAddL
      v (g.leviCivita (extend E p₁) x u)
      (g.leviCivita (extend E p₂) x u) q]
  rw [covTensor2DerivAt_add_left
      (g := g) (h := h) (x := x) (hDiff x) hAddL
      v p₁ p₂ (g.leviCivita (extend E q) x u)]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem covTensor2SecondDerivAt_smul_left
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSecond : CovTensor2DerivExtDifferentiableAt g h x)
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hSMulL : Tensor2SMulLeft h)
    (c : ℝ) (u v p q : TM x) :
    covTensor2SecondDerivAt g h x u v (c • p) q =
      c • covTensor2SecondDerivAt g h x u v p q := by
  unfold covTensor2SecondDerivAt
  have hfun :
      (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E (c • p) y) (extend E q y)) =
        c • (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q y)) := by
    funext y
    rw [extend_tangent_smul (x := x) c p]
    exact covTensor2DerivAt_smul_left
      (g := g) (h := h) (x := y) (hDiff y) hSMulL
      c (extend E v y) (extend E p y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_const_smul_at (hSecond v p q) c]
  have hΓp :
      g.leviCivita (extend E (c • p)) x u =
        c • g.leviCivita (extend E p) x u := by
    rw [extend_tangent_smul (x := x) c p]
    have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E p))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hsmul
  rw [hΓp]
  rw [covTensor2DerivAt_smul_left
      (g := g) (h := h) (x := x) (hDiff x) hSMulL
      c (g.leviCivita (extend E v) x u) p q]
  rw [covTensor2DerivAt_smul_left
      (g := g) (h := h) (x := x) (hDiff x) hSMulL
      c v (g.leviCivita (extend E p) x u) q]
  rw [covTensor2DerivAt_smul_left
      (g := g) (h := h) (x := x) (hDiff x) hSMulL
      c v p (g.leviCivita (extend E q) x u)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem covTensor2SecondDerivAt_add_right
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSecond : CovTensor2DerivExtDifferentiableAt g h x)
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hAddR : Tensor2AddRight h)
    (u v p q₁ q₂ : TM x) :
    covTensor2SecondDerivAt g h x u v p (q₁ + q₂) =
      covTensor2SecondDerivAt g h x u v p q₁
        + covTensor2SecondDerivAt g h x u v p q₂ := by
  unfold covTensor2SecondDerivAt
  have hfun :
      (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E (q₁ + q₂) y)) =
        (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q₁ y)) +
        fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q₂ y) := by
    funext y
    rw [extend_tangent_add (x := x) q₁ q₂]
    exact covTensor2DerivAt_add_right
      (g := g) (h := h) (x := y) (hDiff y) hAddR
      (extend E v y) (extend E p y) (extend E q₁ y) (extend E q₂ y)
  rw [hfun]
  rw [extDerivFun_add (hSecond v p q₁) (hSecond v p q₂)]
  have hΓq :
      g.leviCivita (extend E (q₁ + q₂)) x u =
        g.leviCivita (extend E q₁) x u
          + g.leviCivita (extend E q₂) x u := by
    rw [extend_tangent_add (x := x) q₁ q₂]
    have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E q₁))
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E q₂))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hadd
  rw [hΓq]
  rw [covTensor2DerivAt_add_right
      (g := g) (h := h) (x := x) (hDiff x) hAddR
      (g.leviCivita (extend E v) x u) p q₁ q₂]
  rw [covTensor2DerivAt_add_right
      (g := g) (h := h) (x := x) (hDiff x) hAddR
      v (g.leviCivita (extend E p) x u) q₁ q₂]
  rw [covTensor2DerivAt_add_right
      (g := g) (h := h) (x := x) (hDiff x) hAddR
      v p (g.leviCivita (extend E q₁) x u)
      (g.leviCivita (extend E q₂) x u)]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem covTensor2SecondDerivAt_smul_right
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSecond : CovTensor2DerivExtDifferentiableAt g h x)
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hSMulR : Tensor2SMulRight h)
    (c : ℝ) (u v p q : TM x) :
    covTensor2SecondDerivAt g h x u v p (c • q) =
      c • covTensor2SecondDerivAt g h x u v p q := by
  unfold covTensor2SecondDerivAt
  have hfun :
      (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E (c • q) y)) =
        c • (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q y)) := by
    funext y
    rw [extend_tangent_smul (x := x) c q]
    exact covTensor2DerivAt_smul_right
      (g := g) (h := h) (x := y) (hDiff y) hSMulR
      c (extend E v y) (extend E p y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_const_smul_at (hSecond v p q) c]
  have hΓq :
      g.leviCivita (extend E (c • q)) x u =
        c • g.leviCivita (extend E q) x u := by
    rw [extend_tangent_smul (x := x) c q]
    have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
      (by simpa [MDiffAtTangentField] using
        (mdifferentiableAt_extend I E q))
    simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hsmul
  rw [hΓq]
  rw [covTensor2DerivAt_smul_right
      (g := g) (h := h) (x := x) (hDiff x) hSMulR
      c (g.leviCivita (extend E v) x u) p q]
  rw [covTensor2DerivAt_smul_right
      (g := g) (h := h) (x := x) (hDiff x) hSMulR
      c v (g.leviCivita (extend E p) x u) q]
  rw [covTensor2DerivAt_smul_right
      (g := g) (h := h) (x := x) (hDiff x) hSMulR
      c v p (g.leviCivita (extend E q) x u)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem covTensor2DerivAt_sum_right
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {g : ClosedSmoothRiemannianMetric n M}
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h)
    (v p : TM x) (c : ι → ℝ) (q : ι → TM x) :
    covTensor2DerivAt g h x v p (∑ i, c i • q i) =
      ∑ i, c i * covTensor2DerivAt g h x v p (q i) := by
  set L : TM x →ₗ[ℝ] ℝ :=
    IsLinearMap.mk' (fun q ↦ covTensor2DerivAt g h x v p q)
      ⟨fun q₁ q₂ ↦ covTensor2DerivAt_add_right
          (g := g) (h := h) (x := x) hDiff hAddR v p q₁ q₂,
       fun c q ↦ by
          simpa [smul_eq_mul] using
            covTensor2DerivAt_smul_right
              (g := g) (h := h) (x := x) hDiff hSMulR c v p q⟩ with hL
  change L (∑ i, c i • q i) = ∑ i, c i * L (q i)
  have hmap := map_sum L (fun i ↦ c i • q i) Finset.univ
  simpa [smul_eq_mul] using hmap

set_option maxHeartbeats 5000000 in
/-- The fixed-frame product-rule part contracts to the covariant trace plus the
two Levi-Civita slot corrections. -/
theorem gram_h_extDerivFun_contraction_eq_covTensor2DerivAt_add_corrections
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, ∑ j,
        (gramMatrix g x x)⁻¹ i j *
          extDerivFun
            (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w)
      =
      (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E);
      let b := Module.finBasis ℝ (TM x);
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun i ↦ metricDualVectorAt g x (b.coord i);
      let Γ : TM x → TM x := fun p ↦ g.leviCivita (extend E p) x w;
      ∑ i, covTensor2DerivAt g h x w (b i) (sharp i)
        + ∑ i, h x (Γ (b i)) (sharp i)
        + ∑ i, h x (b i) (Γ (sharp i))) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let G : Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ := gramMatrix g x x
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  let Γ : TM x → TM x := fun p ↦ g.leviCivita (extend E p) x w
  have hsharp : ∀ i, sharp i = ∑ j, G⁻¹ i j • b j := by
    intro i
    simpa [sharp, b, G] using
      metricDualVectorAt_finBasis_coord_eq_sum_gram_inv (g := g) (x := x) i
  set Γlin : TM x →ₗ[ℝ] TM x :=
    IsLinearMap.mk' Γ
      ⟨(by
          intro p q
          change g.leviCivita (extend E (p + q)) x w =
            g.leviCivita (extend E p) x w + g.leviCivita (extend E q) x w
          rw [extend_tangent_add (x := x) p q]
          have hadd := g.leviCivita.isCovariantDerivativeOnUniv.add
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E p))
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E q))
          simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L w) hadd),
        (by
          intro c p
          change g.leviCivita (extend E (c • p)) x w =
            c • g.leviCivita (extend E p) x w
          rw [extend_tangent_smul (x := x) c p]
          have hsmul := g.leviCivita.isCovariantDerivativeOnUniv.smul_const c
            (by simpa [MDiffAtTangentField] using
              (mdifferentiableAt_extend I E p))
          simpa using congrArg (fun L : TM x →L[ℝ] TM x ↦ L w) hsmul)⟩ with hΓlin
  have hΓsharp : ∀ i, Γ (sharp i) = ∑ j, G⁻¹ i j • Γ (b j) := by
    intro i
    change Γlin (sharp i) = ∑ j, G⁻¹ i j • Γlin (b j)
    rw [hsharp i]
    simpa using map_sum Γlin (fun j ↦ G⁻¹ i j • b j) Finset.univ
  have hcovSharp : ∀ i,
      covTensor2DerivAt g h x w (b i) (sharp i) =
        ∑ j, G⁻¹ i j * covTensor2DerivAt g h x w (b i) (b j) := by
    intro i
    rw [hsharp i]
    exact covTensor2DerivAt_sum_right
      (g := g) (h := h) (x := x) hDiff hAddR hSMulR w (b i)
      (fun j ↦ G⁻¹ i j) b
  have hΓLeftSharp : ∀ i,
      h x (Γ (b i)) (sharp i) =
        ∑ j, G⁻¹ i j * h x (Γ (b i)) (b j) := by
    intro i
    rw [hsharp i]
    exact tensor2_sum_right (h := h) hAddR hSMulR x (Γ (b i))
      (fun j ↦ G⁻¹ i j) b
  have hΓRightSharp : ∀ i,
      h x (b i) (Γ (sharp i)) =
        ∑ j, G⁻¹ i j * h x (b i) (Γ (b j)) := by
    intro i
    rw [hΓsharp i]
    exact tensor2_sum_right (h := h) hAddR hSMulR x (b i)
      (fun j ↦ G⁻¹ i j) (fun j ↦ Γ (b j))
  have hrow : ∀ i,
      (∑ j,
          G⁻¹ i j *
            extDerivFun
              (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w)
        =
        covTensor2DerivAt g h x w (b i) (sharp i)
          + h x (Γ (b i)) (sharp i)
          + h x (b i) (Γ (sharp i)) := by
    intro i
    calc
      (∑ j,
          G⁻¹ i j *
            extDerivFun
              (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w)
          =
          ∑ j,
            G⁻¹ i j *
              (covTensor2DerivAt g h x w (b i) (b j)
                + h x (Γ (b i)) (b j)
                + h x (b i) (Γ (b j))) := by
            refine Finset.sum_congr rfl fun j _hj ↦ ?_
            have hentry := extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections
              (g := g) (h := h) (x := x) (v := w) (p := b i) (q := b j)
            simpa [gramFrame, b, Γ] using congrArg (fun t ↦ G⁻¹ i j * t) hentry
      _ =
          (∑ j, G⁻¹ i j * covTensor2DerivAt g h x w (b i) (b j))
            + (∑ j, G⁻¹ i j * h x (Γ (b i)) (b j))
            + (∑ j, G⁻¹ i j * h x (b i) (Γ (b j))) := by
            simp_rw [mul_add]
            simp [Finset.sum_add_distrib]
      _ =
          covTensor2DerivAt g h x w (b i) (sharp i)
            + h x (Γ (b i)) (sharp i)
            + h x (b i) (Γ (sharp i)) := by
            rw [← hcovSharp i, ← hΓLeftSharp i, ← hΓRightSharp i]
  calc
    (∑ i, ∑ j,
      (gramMatrix g x x)⁻¹ i j *
        extDerivFun
          (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w)
      =
        ∑ i,
          (covTensor2DerivAt g h x w (b i) (sharp i)
            + h x (Γ (b i)) (sharp i)
            + h x (b i) (Γ (sharp i))) := by
          simpa [G] using Finset.sum_congr rfl fun i _hi ↦ hrow i
    _ =
        ∑ i, covTensor2DerivAt g h x w (b i) (sharp i)
          + ∑ i, h x (Γ (b i)) (sharp i)
          + ∑ i, h x (b i) (Γ (sharp i)) := by
          simp [Finset.sum_add_distrib]

/--
The closed Koszul master identity for the connection variation.

The two extra hypotheses are the honest analytic product rules not implied by
pointwise `TimeDifferentiableAt` alone: differentiating the spatial
`extDerivFun` terms through the time parameter, and differentiating the
metric pairing of the time-varying connection value.  The conclusion is the
coordinate-free variation formula
`2 g(δΓ(v,w),z) = (∇_v h)(w,z)+(∇_w h)(v,z)-(∇_z h)(v,w)`.
-/
theorem deltaGamma_koszul
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (v w z : TM x) :
    2 * (gt t₀).inner x (deltaGammaAt gt t₀ x v w) z =
      covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x v w z
        + covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x w v z
        - covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x z v w := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  let X : ∀ y : M, TM y := extend E v
  let Y : ∀ y : M, TM y := extend E w
  let Z : ∀ y : M, TM y := extend E z
  let Γvw : TM x := (gt t₀).leviCivita Y x v
  let δΓvw : TM x := deltaGammaAt gt t₀ x v w
  have hΓ : HasDerivAt (fun t ↦ (gt t).leviCivita Y x v) δΓvw t₀ := by
    have h := (hreg.connection x v w).hasDerivAt
    simpa [Y, δΓvw, deltaGammaAt] using h
  have hinner := hasDerivAt_inner_of_timeDifferentiableAt (hgt x)
  have hpairCLM :
      HasDerivAt (fun t ↦ (gt t).inner x ((gt t).leviCivita Y x v))
        (timeDerivContinuousAt gt t₀ x (hgt x) Γvw +
          (gt t₀).inner x δΓvw) t₀ := by
    simpa [Γvw, δΓvw] using hinner.clm_apply hΓ
  have hpair :
      HasDerivAt
        (fun t ↦ (gt t).inner x ((gt t).leviCivita Y x v) z)
        (timeDerivAt gt t₀ x Γvw z + (gt t₀).inner x δΓvw z) t₀ := by
    have hz : HasDerivAt (fun _ : ℝ ↦ z) 0 t₀ := hasDerivAt_const t₀ z
    simpa [Γvw] using hpairCLM.clm_apply hz
  have hleft :
      HasDerivAt
        (fun t ↦ 2 * (gt t).inner x ((gt t).leviCivita Y x v) z)
        (2 * (timeDerivAt gt t₀ x Γvw z + (gt t₀).inner x δΓvw z)) t₀ :=
    hpair.const_mul 2
  let Bvw : TM x := VectorField.mlieBracket I X Y x
  let Bvz : TM x := VectorField.mlieBracket I X Z x
  let Bwz : TM x := VectorField.mlieBracket I Y Z x
  let rhs : ℝ → ℝ := fun t ↦
    extDerivFun (fun y : M ↦ (gt t).inner y (Y y) (Z y)) x v
      + extDerivFun (fun y : M ↦ (gt t).inner y (X y) (Z y)) x w
      - extDerivFun (fun y : M ↦ (gt t).inner y (X y) (Y y)) x z
      + (gt t).inner x Bvw z
      - (gt t).inner x Bvz w
      - (gt t).inner x Bwz v
  let rhs' : ℝ :=
    extDerivFun (fun y : M ↦ timeDerivAt gt t₀ y (Y y) (Z y)) x v
      + extDerivFun (fun y : M ↦ timeDerivAt gt t₀ y (X y) (Z y)) x w
      - extDerivFun (fun y : M ↦ timeDerivAt gt t₀ y (X y) (Y y)) x z
      + timeDerivAt gt t₀ x Bvw z
      - timeDerivAt gt t₀ x Bvz w
      - timeDerivAt gt t₀ x Bwz v
  have hright : HasDerivAt rhs rhs' t₀ := by
    have h1 := hExt v w z
    have h2 := hExt w v z
    have h3 := hExt z v w
    have h4 : HasDerivAt (fun t ↦ (gt t).inner x Bvw z)
        (timeDerivAt gt t₀ x Bvw z) t₀ := by
      simpa [timeDerivAt] using (hgt x Bvw z).hasDerivAt
    have h5 : HasDerivAt (fun t ↦ (gt t).inner x Bvz w)
        (timeDerivAt gt t₀ x Bvz w) t₀ := by
      simpa [timeDerivAt] using (hgt x Bvz w).hasDerivAt
    have h6 : HasDerivAt (fun t ↦ (gt t).inner x Bwz v)
        (timeDerivAt gt t₀ x Bwz v) t₀ := by
      simpa [timeDerivAt] using (hgt x Bwz v).hasDerivAt
    simpa [rhs, rhs', X, Y, Z, Bvw, Bvz, Bwz] using
      (((h1.add h2).sub h3).add h4).sub h5 |>.sub h6
  have hkoszul_fun :
      (fun t ↦ 2 * (gt t).inner x ((gt t).leviCivita Y x v) z) = rhs := by
    funext t
    have hK := CovariantDerivative.koszul_formula
      (g := (gt t).inner) (cov := (gt t).leviCivita) (x := x)
      ((gt t).inner_symm x)
      ((gt t).leviCivita_metricCompatibleAt x)
      ((gt t).leviCivita_torsionFreeAt x)
      (X := X) (Y := Y) (Z := Z)
      (by simpa [X] using (mdifferentiableAt_extend ..))
      (by simpa [Y] using (mdifferentiableAt_extend ..))
      (by simpa [Z] using (mdifferentiableAt_extend ..))
    simpa [rhs, X, Y, Z] using hK
  have hleft_on_rhs : HasDerivAt rhs
      (2 * (timeDerivAt gt t₀ x Γvw z + (gt t₀).inner x δΓvw z)) t₀ := by
    simpa [hkoszul_fun] using hleft
  have hderiv :
      2 * (timeDerivAt gt t₀ x Γvw z + (gt t₀).inner x δΓvw z) = rhs' :=
    hleft_on_rhs.unique hright
  have hBvw :
      Bvw = Γvw - (gt t₀).leviCivita X x w := by
    have ht := (gt t₀).leviCivita_torsionFreeAt x
      (X := X) (Y := Y)
      (by simpa [X] using (mdifferentiableAt_extend ..))
      (by simpa [Y] using (mdifferentiableAt_extend ..))
    simpa [Bvw, Γvw, X, Y] using ht.symm
  have hBvz :
      Bvz = (gt t₀).leviCivita Z x v - (gt t₀).leviCivita X x z := by
    have ht := (gt t₀).leviCivita_torsionFreeAt x
      (X := X) (Y := Z)
      (by simpa [X] using (mdifferentiableAt_extend ..))
      (by simpa [Z] using (mdifferentiableAt_extend ..))
    simpa [Bvz, X, Z] using ht.symm
  have hBwz :
      Bwz = (gt t₀).leviCivita Z x w - (gt t₀).leviCivita Y x z := by
    have ht := (gt t₀).leviCivita_torsionFreeAt x
      (X := Y) (Y := Z)
      (by simpa [Y] using (mdifferentiableAt_extend ..))
      (by simpa [Z] using (mdifferentiableAt_extend ..))
    simpa [Bwz, Y, Z] using ht.symm
  have hcov :
      covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x v w z
        + covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x w v z
        - covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x z v w =
          rhs' - 2 * timeDerivAt gt t₀ x Γvw z := by
    have hsub_left : ∀ a b c : TM x,
        timeDerivAt gt t₀ x (a - b) c =
          timeDerivAt gt t₀ x a c - timeDerivAt gt t₀ x b c := by
      intro a b c
      have hneg :
          timeDerivAt gt t₀ x (-b) c = -timeDerivAt gt t₀ x b c := by
        simpa using (timeDerivAt_smul_left (hgt x) (-1 : ℝ) b c)
      rw [sub_eq_add_neg, timeDerivAt_add_left (hgt x)]
      rw [hneg]
      ring
    simp only [covTensor2DerivAt, rhs', X, Y, Z, Γvw]
    rw [hBvw, hBvz, hBwz]
    rw [hsub_left Γvw ((gt t₀).leviCivita X x w) z]
    rw [hsub_left ((gt t₀).leviCivita Z x v) ((gt t₀).leviCivita X x z) w]
    rw [hsub_left ((gt t₀).leviCivita Z x w) ((gt t₀).leviCivita Y x z) v]
    rw [timeDerivAt_symm gt t₀ x w ((gt t₀).leviCivita Z x v)]
    rw [timeDerivAt_symm gt t₀ x v ((gt t₀).leviCivita Z x w)]
    rw [timeDerivAt_symm gt t₀ x v ((gt t₀).leviCivita Y x z)]
    simp only [X, Y, Z, Γvw]
    ring_nf
  rw [hcov]
  nlinarith

/--
Neighborhood form of the closed `δΓ` Koszul identity, with all tensor slots
transported by canonical extensions from the anchor point.
-/
theorem deltaGamma_koszul_eventually
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (v w z : TM x) :
    (fun y : M ↦
      2 * (gt t₀).inner y
        (deltaGammaAt gt t₀ y (extend E v y) (extend E w y))
        (extend E z y))
      =ᶠ[nhds x]
    (fun y : M ↦
      covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) y
          (extend E v y) (extend E w y) (extend E z y)
        + covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) y
          (extend E w y) (extend E v y) (extend E z y)
        - covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) y
          (extend E z y) (extend E v y) (extend E w y)) := by
  exact hNear.mono fun y hy ↦ by
    rcases hy with ⟨hreg, hExt⟩
    exact deltaGamma_koszul
      (gt := gt) (t₀ := t₀) (x := y)
      hreg hgt hExt (extend E v y) (extend E w y) (extend E z y)

/--
Exterior-derivative form of the neighborhood `δΓ` Koszul identity.

The left side is still the product-rule output
`2 * (g(∇δΓ,z) + δΓ-slot corrections)`.  The right side has each raw
derivative of `∇h` rewritten as `∇²h` plus the three first-order slot
corrections.
-/
theorem deltaGamma_koszul_extDerivFun
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (u v w z : TM x) :
    2 *
      ((gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u v w) z
        + (gt t₀).inner x
          (deltaGammaAt gt t₀ x
            ((gt t₀).leviCivita (extend E v) x u) w) z
        + (gt t₀).inner x
          (deltaGammaAt gt t₀ x v
            ((gt t₀).leviCivita (extend E w) x u)) z
        + (gt t₀).inner x
          (deltaGammaAt gt t₀ x v w)
          ((gt t₀).leviCivita (extend E z) x u))
      =
        covTensor2SecondDerivExpansionAt
            (gt t₀) (timeDerivAt gt t₀) x u v w z
          + covTensor2SecondDerivExpansionAt
            (gt t₀) (timeDerivAt gt t₀) x u w v z
          - covTensor2SecondDerivExpansionAt
            (gt t₀) (timeDerivAt gt t₀) x u z v w := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let S : M → ℝ := fun y : M ↦
    g.inner y
      (deltaGammaAt gt t₀ y (extend E v y) (extend E w y))
      (extend E z y)
  let A : M → ℝ := fun y : M ↦
    covTensor2DerivAt g H y (extend E v y) (extend E w y) (extend E z y)
  let B : M → ℝ := fun y : M ↦
    covTensor2DerivAt g H y (extend E w y) (extend E v y) (extend E z y)
  let C : M → ℝ := fun y : M ↦
    covTensor2DerivAt g H y (extend E z y) (extend E v y) (extend E w y)
  have hevent := deltaGamma_koszul_eventually
    (gt := gt) (t₀ := t₀) (x := x) hgt hNear v w z
  have hderiv :
      extDerivFun (fun y : M ↦ 2 * S y) x u =
        extDerivFun (fun y : M ↦ A y + B y - C y) x u := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L u)
      (CovariantDerivative.extDerivFun_congr (by
        simpa [S, A, B, C, g, H] using hevent))
  have hscale :
      extDerivFun (fun y : M ↦ 2 * S y) x u =
        2 * extDerivFun S x u := by
    have h := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L u)
      (extDerivFun_const_smul_at
        (n := n) (M := M) (f := S) (x := x)
        (by simpa [S, g] using hBridge.mdifferentiable v z w)
        (2 : ℝ))
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have hentry :
      extDerivFun S x u =
        g.inner x (covDeltaGammaDerivAt gt t₀ x u v w) z
        + g.inner x
          (deltaGammaAt gt t₀ x (g.leviCivita (extend E v) x u) w) z
        + g.inner x
          (deltaGammaAt gt t₀ x v (g.leviCivita (extend E w) x u)) z
        + g.inner x (deltaGammaAt gt t₀ x v w)
          (g.leviCivita (extend E z) x u) := by
    simpa [S, g] using hBridge.extDeriv_eq u v z w
  have hleft :
      extDerivFun (fun y : M ↦ 2 * S y) x u =
        2 *
          (g.inner x (covDeltaGammaDerivAt gt t₀ x u v w) z
            + g.inner x
              (deltaGammaAt gt t₀ x (g.leviCivita (extend E v) x u) w) z
            + g.inner x
              (deltaGammaAt gt t₀ x v (g.leviCivita (extend E w) x u)) z
            + g.inner x (deltaGammaAt gt t₀ x v w)
              (g.leviCivita (extend E z) x u)) := by
    rw [hscale, hentry]
  have hright :
      extDerivFun (fun y : M ↦ A y + B y - C y) x u =
        covTensor2SecondDerivExpansionAt g H x u v w z
          + covTensor2SecondDerivExpansionAt g H x u w v z
          - covTensor2SecondDerivExpansionAt g H x u z v w := by
    rw [extDerivFun_add_sub_at
      (n := n) (M := M)
      (f := A) (g := B) (h := C) (x := x)
      (by simpa [A, g, H] using hSecond v w z)
      (by simpa [B, g, H] using hSecond w v z)
      (by simpa [C, g, H] using hSecond z v w) u]
    rw [extDerivFun_covTensor2DerivAt_extend_eq_secondDerivExpansion
      (g := g) (h := H) (x := x) (u := u) (v := v) (p := w) (q := z)]
    rw [extDerivFun_covTensor2DerivAt_extend_eq_secondDerivExpansion
      (g := g) (h := H) (x := x) (u := u) (v := w) (p := v) (q := z)]
    rw [extDerivFun_covTensor2DerivAt_extend_eq_secondDerivExpansion
      (g := g) (h := H) (x := x) (u := u) (v := z) (p := v) (q := w)]
  calc
    2 *
      (g.inner x (covDeltaGammaDerivAt gt t₀ x u v w) z
        + g.inner x
          (deltaGammaAt gt t₀ x (g.leviCivita (extend E v) x u) w) z
        + g.inner x
          (deltaGammaAt gt t₀ x v (g.leviCivita (extend E w) x u)) z
        + g.inner x (deltaGammaAt gt t₀ x v w)
          (g.leviCivita (extend E z) x u))
        = extDerivFun (fun y : M ↦ 2 * S y) x u := hleft.symm
    _ = extDerivFun (fun y : M ↦ A y + B y - C y) x u := hderiv
    _ = covTensor2SecondDerivExpansionAt g H x u v w z
          + covTensor2SecondDerivExpansionAt g H x u w v z
          - covTensor2SecondDerivExpansionAt g H x u z v w := hright

/--
Closed Koszul formula for the covariant derivative of the connection
variation.

This is the differentiated `deltaGamma_koszul` identity solved for
`2 * g((∇_u δΓ)(v,w), z)`.  The right side is the three-term second-derivative
Koszul form, with the first-order slot corrections from differentiating the
metric-paired `δΓ` entry subtracted explicitly.
-/
theorem covDeltaGamma_koszul
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (u v w z : TM x) :
    2 * (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u v w) z =
        covTensor2SecondDerivExpansionAt
            (gt t₀) (timeDerivAt gt t₀) x u v w z
          + covTensor2SecondDerivExpansionAt
            (gt t₀) (timeDerivAt gt t₀) x u w v z
          - covTensor2SecondDerivExpansionAt
            (gt t₀) (timeDerivAt gt t₀) x u z v w
          - 2 *
            ((gt t₀).inner x
              (deltaGammaAt gt t₀ x
                ((gt t₀).leviCivita (extend E v) x u) w) z
            + (gt t₀).inner x
              (deltaGammaAt gt t₀ x v
                ((gt t₀).leviCivita (extend E w) x u)) z
            + (gt t₀).inner x
              (deltaGammaAt gt t₀ x v w)
              ((gt t₀).leviCivita (extend E z) x u)) := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let main : ℝ := g.inner x (covDeltaGammaDerivAt gt t₀ x u v w) z
  let c₁ : ℝ :=
    g.inner x (deltaGammaAt gt t₀ x (g.leviCivita (extend E v) x u) w) z
  let c₂ : ℝ :=
    g.inner x (deltaGammaAt gt t₀ x v (g.leviCivita (extend E w) x u)) z
  let c₃ : ℝ :=
    g.inner x (deltaGammaAt gt t₀ x v w)
      (g.leviCivita (extend E z) x u)
  let corr : ℝ := c₁ + c₂ + c₃
  let rhs : ℝ :=
    covTensor2SecondDerivExpansionAt g H x u v w z
      + covTensor2SecondDerivExpansionAt g H x u w v z
      - covTensor2SecondDerivExpansionAt g H x u z v w
  have hdiff :
      2 * (main + corr) = rhs := by
    have hraw :
        2 * (main + c₁ + c₂ + c₃) = rhs := by
      simpa [main, c₁, c₂, c₃, rhs, g, H] using
        deltaGamma_koszul_extDerivFun
          (gt := gt) (t₀ := t₀) (x := x)
          hgt hNear hBridge hSecond u v w z
    change 2 * (main + (c₁ + c₂ + c₃)) = rhs
    linarith
  have hfinal : 2 * main = rhs - 2 * corr := by
    linarith
  simpa [main, corr, c₁, c₂, c₃, rhs, g, H] using hfinal

/-- Static sanity witness: the covariant `δΓ` Koszul formula is zero for a
time-constant metric family. -/
theorem covDeltaGamma_koszul_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u v w z : TM x) :
    2 * g.inner x (covDeltaGammaDerivAt (fun _ : ℝ ↦ g) t₀ x u v w) z =
        covTensor2SecondDerivExpansionAt
            g (timeDerivAt (fun _ : ℝ ↦ g) t₀) x u v w z
          + covTensor2SecondDerivExpansionAt
            g (timeDerivAt (fun _ : ℝ ↦ g) t₀) x u w v z
          - covTensor2SecondDerivExpansionAt
            g (timeDerivAt (fun _ : ℝ ↦ g) t₀) x u z v w
          - 2 *
            (g.inner x
              (deltaGammaAt (fun _ : ℝ ↦ g) t₀ x
                (g.leviCivita (extend E v) x u) w) z
            + g.inner x
              (deltaGammaAt (fun _ : ℝ ↦ g) t₀ x v
                (g.leviCivita (extend E w) x u)) z
            + g.inner x
              (deltaGammaAt (fun _ : ℝ ↦ g) t₀ x v w)
              (g.leviCivita (extend E z) x u)) := by
  have hH :
      timeDerivAt (fun _ : ℝ ↦ g) t₀ =
        (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
    funext y p q
    simp
  simp [hH]

set_option maxHeartbeats 5000000 in
/--
Closed differentiated-Koszul cancellation for one summand of the divergence
trace.

Substituting the first-order `deltaGamma_koszul` formula into the three
connection-correction terms of `covDeltaGamma_koszul` cancels exactly the
first-order corrections inside `covTensor2SecondDerivExpansionAt`.  The result
is the pure three-term `∇²h` summand used by the summed keystone.
-/
theorem covDeltaGamma_koszul_secondDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (u v w z : TM x) :
    2 * (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u v w) z =
      covTensor2SecondDerivAt
          (gt t₀) (timeDerivAt gt t₀) x u v w z
        + covTensor2SecondDerivAt
          (gt t₀) (timeDerivAt gt t₀) x u w v z
        - covTensor2SecondDerivAt
          (gt t₀) (timeDerivAt gt t₀) x u z v w := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let Γv : TM x := g.leviCivita (extend E v) x u
  let Γw : TM x := g.leviCivita (extend E w) x u
  let Γz : TM x := g.leviCivita (extend E z) x u
  have hcov :
      2 * g.inner x (covDeltaGammaDerivAt gt t₀ x u v w) z =
        covTensor2SecondDerivExpansionAt g H x u v w z
          + covTensor2SecondDerivExpansionAt g H x u w v z
          - covTensor2SecondDerivExpansionAt g H x u z v w
          - 2 *
            (g.inner x (deltaGammaAt gt t₀ x Γv w) z
            + g.inner x (deltaGammaAt gt t₀ x v Γw) z
            + g.inner x (deltaGammaAt gt t₀ x v w) Γz) := by
    simpa [g, H, Γv, Γw, Γz] using
      covDeltaGamma_koszul
        (gt := gt) (t₀ := t₀) (x := x)
        hgt hNear hBridge hSecond u v w z
  have hδv :
      2 * g.inner x (deltaGammaAt gt t₀ x Γv w) z =
        covTensor2DerivAt g H x Γv w z
          + covTensor2DerivAt g H x w Γv z
          - covTensor2DerivAt g H x z Γv w := by
    simpa [g, H, Γv] using
      deltaGamma_koszul
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt Γv w z
  have hδw :
      2 * g.inner x (deltaGammaAt gt t₀ x v Γw) z =
        covTensor2DerivAt g H x v Γw z
          + covTensor2DerivAt g H x Γw v z
          - covTensor2DerivAt g H x z v Γw := by
    simpa [g, H, Γw] using
      deltaGamma_koszul
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt v Γw z
  have hδz :
      2 * g.inner x (deltaGammaAt gt t₀ x v w) Γz =
        covTensor2DerivAt g H x v w Γz
          + covTensor2DerivAt g H x w v Γz
          - covTensor2DerivAt g H x Γz v w := by
    simpa [g, H, Γz] using
      deltaGamma_koszul
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt v w Γz
  unfold covTensor2SecondDerivExpansionAt at hcov
  change 2 * g.inner x (covDeltaGammaDerivAt gt t₀ x u v w) z =
      covTensor2SecondDerivAt g H x u v w z
        + covTensor2SecondDerivAt g H x u w v z
        - covTensor2SecondDerivAt g H x u z v w
  nlinarith [hcov, hδv, hδw, hδz]

set_option maxHeartbeats 5000000 in
/--
Summed divergence trace in pure second-covariant-derivative form.

This is the closed-manifold analogue of the model
`deltaGammaDivergenceTrace_sndDeriv`, with the actual frozen closed trace
orientation `Σⱼ deltaGammaDivergenceAt(bⱼ, ♯eʲ)`.
-/
theorem deltaGammaDivergenceTrace_sndDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j))
    =
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j, ∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
          + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)
          - covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j))) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  change (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
    ∑ j, ∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
        + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)
        - covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j))
  refine Finset.sum_congr rfl fun j _hj ↦ ?_
  have hdiv :
      deltaGammaDivergenceAt gt t₀ x (b j) (sharp j) =
        ∑ i, g.inner x
          (covDeltaGammaDerivAt gt t₀ x (b i) (b j) (sharp j)) (sharp i) := by
    unfold deltaGammaDivergenceAt
    change (∑ i, b.coord i
        (covDeltaGammaDerivAt gt t₀ x (b i) (b j) (sharp j))) =
      ∑ i, g.inner x
        (covDeltaGammaDerivAt gt t₀ x (b i) (b j) (sharp j)) (sharp i)
    refine Finset.sum_congr rfl fun i _hi ↦ ?_
    simpa [g, b, sharp] using
      coord_eq_inner_metricDualVectorAt (g := g) (x := x) i
        (covDeltaGammaDerivAt gt t₀ x (b i) (b j) (sharp j))
  rw [hdiv]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  have hk :=
    covDeltaGamma_koszul_secondDerivAt
      (gt := gt) (t₀ := t₀) (x := x)
      hreg hgt hExt hNear hBridge hSecond
      (b i) (b j) (sharp j) (sharp i)
  change
    2 * g.inner x
      (covDeltaGammaDerivAt gt t₀ x (b i) (b j) (sharp j)) (sharp i)
      =
        covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
          + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)
          - covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j) at hk
  nlinarith

/--
The positive `T1 + T2` block in the summed divergence-trace second-derivative
formula.
-/
noncomputable def deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  ∑ j, ∑ i, (1 / 2 : ℝ) *
    (covTensor2SecondDerivAt g h x (b i) (b j) (sharp j) (sharp i)
      + covTensor2SecondDerivAt g h x (b i) (sharp j) (b j) (sharp i))

/--
The negative `T3` block in the summed divergence-trace second-derivative
formula.
-/
noncomputable def deltaGammaDivergenceTraceSecondDerivTraceBlockAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  ∑ j, ∑ i,
    covTensor2SecondDerivAt g h x (b i) (sharp i) (b j) (sharp j)

set_option maxHeartbeats 5000000 in
/-- Split form of `deltaGammaDivergenceTrace_sndDerivAt` into the two keystone
double-trace groups. -/
theorem deltaGammaDivergenceTrace_sndDerivAt_blocks
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j))
    =
      deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
        (gt t₀) (timeDerivAt gt t₀) x
        - (1 / 2 : ℝ) *
          deltaGammaDivergenceTraceSecondDerivTraceBlockAt
            (gt t₀) (timeDerivAt gt t₀) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hsnd :=
    deltaGammaDivergenceTrace_sndDerivAt
      (gt := gt) (t₀ := t₀) (x := x)
      hreg hgt hExt hNear hBridge hSecond
  change (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
      deltaGammaDivergenceTraceSecondDerivPositiveBlockAt g H x
        - (1 / 2 : ℝ) *
          deltaGammaDivergenceTraceSecondDerivTraceBlockAt g H x
  rw [hsnd]
  simp only [deltaGammaDivergenceTraceSecondDerivPositiveBlockAt,
    deltaGammaDivergenceTraceSecondDerivTraceBlockAt, g, H]
  have hsplit :
      (∑ j, ∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
          + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)
          - covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j))) =
        (∑ j, ∑ i, (1 / 2 : ℝ) *
          (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
            + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)))
          - (1 / 2 : ℝ) *
            (∑ j, ∑ i,
              covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j)) := by
    calc
      (∑ j, ∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
          + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)
          - covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j)))
          =
          ∑ j,
            ((∑ i, (1 / 2 : ℝ) *
              (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
                + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)))
              - (1 / 2 : ℝ) *
                (∑ i,
                  covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j))) := by
            refine Finset.sum_congr rfl fun j _hj ↦ ?_
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _hi ↦ ?_
            ring
      _ =
          (∑ j, ∑ i, (1 / 2 : ℝ) *
            (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
              + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)))
            - (1 / 2 : ℝ) *
              (∑ j, ∑ i,
                covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j)) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  exact hsplit

/--
The divergence one-form of a raw metric variation:
`(div h)(w) = Σᵢ (∇_{♯eⁱ}h)(eᵢ,w)`.
-/
noncomputable def tensorDivergenceOneFormAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) (w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, covTensor2DerivAt g h x
    (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))
    ((Module.finBasis ℝ (TM x)) i) w

theorem tensorDivergenceOneFormAt_ricciVariationField_swap
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (w : TM x) :
    tensorDivergenceOneFormAt g (ricciVariationField g) x w =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, covTensor2DerivAt g (ricciVariationField g) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))
        w ((Module.finBasis ℝ (TM x)) i)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold tensorDivergenceOneFormAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact covTensor2DerivAt_ricciVariationField_symm
    (g := g) (x := x)
    (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))
    ((Module.finBasis ℝ (TM x)) i) w

theorem tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : ClosedRicciDerivativeExpansionAt g x)
    (w : TM x) :
    tensorDivergenceOneFormAt g (ricciVariationField g) x w =
      closedRicciDivergenceTraceAt g x w := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  rw [tensorDivergenceOneFormAt_ricciVariationField_swap (g := g) (x := x) w]
  unfold closedRicciDivergenceTraceAt
  change (∑ i, covTensor2DerivAt g (ricciVariationField g) x (sharp i) w (b i)) =
    ∑ i, closedCovRicciDerivAt g x (sharp i) w (b i)
  exact Finset.sum_congr rfl fun i _ ↦
    covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt
      (g := g) (x := x) hRic (sharp i) w (b i)

theorem eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : ∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y) :
    ∀ᶠ y in nhds x, ∀ w : TM y,
      tensorDivergenceOneFormAt g (ricciVariationField g) y w =
        closedRicciDivergenceTraceAt g y w :=
  hRic.mono fun y hy w ↦
    tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt
      (g := g) (x := y) hy w

/--
Derivative identification for the inner `δΓ` trace-form field after the already
proved first-order reduction to `div h - 1/2 d(tr h)`.
-/
def DeltaGammaInnerTraceFieldCovariantDerivativeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  ∀ u w : TM x,
    deltaGammaDivergenceAt gt t₀ x w u =
      (extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E w y))
          x u
        - tensorDivergenceOneFormAt g H x
          (g.leviCivita (extend E w) x u))
      - (1 / 2 : ℝ) * g.hessianAt f x w u

@[simp] theorem tensorDivergenceOneFormAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (w : TM x) :
    tensorDivergenceOneFormAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x w = 0 := by
  unfold tensorDivergenceOneFormAt
  simp

/-- Exact trace-swap obligation for `covTensor2DerivAt`. -/
def CovTensor2DerivTraceSwapAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ w : TM x,
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, covTensor2DerivAt g h x ((Module.finBasis ℝ (TM x)) i)
        (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) w)
      = tensorDivergenceOneFormAt g h x w

/--
Closed `hTraceSwap`: slot-linearity of `covTensor2DerivAt` implies the
contracted raised/lowered slot exchange.
-/
theorem hTraceSwap
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hadd1 : ∀ w p₁ p₂ q : TM x,
      covTensor2DerivAt g h x (p₁ + p₂) q w =
        covTensor2DerivAt g h x p₁ q w + covTensor2DerivAt g h x p₂ q w)
    (hsmul1 : ∀ (c : ℝ) (w p q : TM x),
      covTensor2DerivAt g h x (c • p) q w =
        c • covTensor2DerivAt g h x p q w)
    (hadd2 : ∀ w p q₁ q₂ : TM x,
      covTensor2DerivAt g h x p (q₁ + q₂) w =
        covTensor2DerivAt g h x p q₁ w + covTensor2DerivAt g h x p q₂ w)
    (hsmul2 : ∀ (c : ℝ) (w p q : TM x),
      covTensor2DerivAt g h x p (c • q) w =
        c • covTensor2DerivAt g h x p q w) :
    CovTensor2DerivTraceSwapAt g h x := by
  intro w
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hswap := sum_metricDualVectorAt_contraction_swap
    (g := g) (x := x)
    (F := fun p q ↦ covTensor2DerivAt g h x p q w)
    (fun p₁ p₂ q ↦ hadd1 w p₁ p₂ q)
    (fun c p q ↦ hsmul1 c w p q)
    (fun p q₁ q₂ ↦ hadd2 w p q₁ q₂)
    (fun c p q ↦ hsmul2 c w p q)
  change (∑ i, covTensor2DerivAt g h x (b i) (sharp i) w) =
    tensorDivergenceOneFormAt g h x w
  unfold tensorDivergenceOneFormAt
  change (∑ i, covTensor2DerivAt g h x (b i) (sharp i) w) =
    ∑ i, covTensor2DerivAt g h x (sharp i) (b i) w
  exact hswap.symm

theorem covTensor2DerivTraceSwapAt_of_regular
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hAddL : Tensor2AddLeft h) (hSMulL : Tensor2SMulLeft h)
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h) :
    CovTensor2DerivTraceSwapAt g h x :=
  hTraceSwap g h x
    (fun w p₁ p₂ q ↦
      covTensor2DerivAt_add_deriv (g := g) (h := h) (x := x)
        hAddL hAddR p₁ p₂ q w)
    (fun c w p q ↦
      covTensor2DerivAt_smul_deriv (g := g) (h := h) (x := x)
        hSMulL hSMulR c p q w)
    (fun w p q₁ q₂ ↦
      covTensor2DerivAt_add_left (g := g) (h := h) (x := x)
        hDiff hAddL p q₁ q₂ w)
    (fun c w p q ↦
      covTensor2DerivAt_smul_left (g := g) (h := h) (x := x)
        hDiff hSMulL c p q w)

theorem covTensor2DerivTraceSwapAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    CovTensor2DerivTraceSwapAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x :=
  covTensor2DerivTraceSwapAt_of_regular g
    (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x
    (covTensor2ExtDifferentiableAt_zero x)
    tensor2AddLeft_zero tensor2SMulLeft_zero
    tensor2AddRight_zero tensor2SMulRight_zero

theorem covTensor2DerivTraceSwapAt_timeDeriv_of_regular
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x) :
    CovTensor2DerivTraceSwapAt (gt t₀) (timeDerivAt gt t₀) x :=
  covTensor2DerivTraceSwapAt_of_regular (gt t₀) (timeDerivAt gt t₀) x
    hDiff
    (tensor2AddLeft_timeDerivAt hgt)
    (tensor2SMulLeft_timeDerivAt hgt)
    (tensor2AddRight_timeDerivAt hgt)
    (tensor2SMulRight_timeDerivAt hgt)

/--
Exact `hTraceDeriv` obligation: the contracted covariant derivative of `h`
is the exterior derivative of its metric trace.
-/
def TraceMetricVariationDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ w : TM x,
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, covTensor2DerivAt g h x w ((Module.finBasis ℝ (TM x)) i)
        (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)))
      =
        extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w

set_option maxHeartbeats 5000000 in
/--
Direct discharge of the trace-variation derivative from the canonical Gram RHS:
the product-rule fixed-frame part contributes the covariant trace plus the two
Levi-Civita corrections, and the inverse-Gram derivative contraction cancels
exactly those corrections.
-/
theorem traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (hAddL : Tensor2AddLeft h) (hSMulL : Tensor2SMulLeft h)
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h)
    (B : ∀ y : M, LinearMap.BilinForm ℝ (TM y))
    (hB : ∀ y : M, ∀ p q : TM y, B y p q = h y p q) :
    TraceMetricVariationDerivAt g h x := by
  intro w
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  let Γ : TM x → TM x := fun p ↦ g.leviCivita (extend E p) x w
  let first : ℝ :=
    ∑ i, ∑ j,
      (gramMatrix g x x)⁻¹ i j *
        extDerivFun
          (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w
  let second : ℝ :=
    ∑ i, ∑ j,
      extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
        h x (gramFrame x x i) (gramFrame x x j)
  let covTrace : ℝ :=
    ∑ i, covTensor2DerivAt g h x w (b i) (sharp i)
  let corrL : ℝ := ∑ i, h x (Γ (b i)) (sharp i)
  let corrR : ℝ := ∑ i, h x (b i) (Γ (sharp i))
  have hTrace :=
    traceMetricVariationAt_extDerivFun_eq_gram_rhs
      (g := g) (h := h) (x := x) (B := B) (hB := hB) w
  have hProduct :=
    gram_rhs_extDerivFun_eq_sum_product
      (g := g) (h := h) (x := x) hDiff w
  have hFirst :
      first = covTrace + corrL + corrR := by
    simpa [first, covTrace, corrL, corrR, b, sharp, Γ] using
      gram_h_extDerivFun_contraction_eq_covTensor2DerivAt_add_corrections
        (g := g) (h := h) (x := x) hDiff hAddR hSMulR w
  have hSecond :
      second = -corrL - corrR := by
    simpa [second, corrL, corrR, b, sharp, Γ] using
      gram_inv_deriv_contraction_eq_leviCivita_corrections
        (g := g) (h := h) (x := x) hAddL hSMulL hAddR hSMulR w
  have hSplit :
      (∑ i, ∑ j,
        ((gramMatrix g x x)⁻¹ i j *
          extDerivFun
            (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w
         + extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
            h x (gramFrame x x i) (gramFrame x x j))) =
        first + second := by
    simp [first, second, Finset.sum_add_distrib]
  change covTrace = extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w
  rw [hTrace, hProduct, hSplit, hFirst, hSecond]
  ring

set_option maxHeartbeats 5000000 in
theorem closedRicciDerivativeExpansionAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ClosedRicciDerivativeExpansionAt g x := by
  intro v u w
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  let H : ∀ y : M, TM y → TM y → ℝ := closedRicciTraceFieldAt g u w
  let Γu : TM x := g.leviCivita (extend E u) x v
  let Γw : TM x := g.leviCivita (extend E w) x v
  have hTrace : TraceMetricVariationDerivAt g H x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := H) (x := x)
      (by
        simpa [H] using
          covTensor2ExtDifferentiableAt_closedRicciTraceFieldAt
            (g := g) (u := u) (w := w))
      (by
        simpa [H] using
          (tensor2AddLeft_closedRicciTraceFieldAt
            (g := g) (u := u) (w := w)))
      (by
        simpa [H] using
          (tensor2SMulLeft_closedRicciTraceFieldAt
            (g := g) (u := u) (w := w)))
      (by
        simpa [H] using
          (tensor2AddRight_closedRicciTraceFieldAt
            (g := g) (u := u) (w := w)))
      (by
        simpa [H] using
          (tensor2SMulRight_closedRicciTraceFieldAt
            (g := g) (u := u) (w := w)))
      (fun y ↦ closedRicciTraceBilinFormAt g u w y)
      (by intro y p q; rfl)
  have hTraceEq :
      extDerivFun (fun y : M ↦ traceMetricVariationAt g H y) x v =
        extDerivFun
          (fun y : M ↦ g.ricciAt y (extend E u y) (extend E w y)) x v := by
    have heq :
        (fun y : M ↦ traceMetricVariationAt g H y) =ᶠ[nhds x]
          (fun y : M ↦ g.ricciAt y (extend E u y) (extend E w y)) :=
      Filter.Eventually.of_forall fun y ↦ by
        simpa [H] using
          traceMetricVariationAt_closedRicciTraceFieldAt
            (g := g) (u := u) (w := w) (y := y)
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
      (CovariantDerivative.extDerivFun_congr heq)
  have hTraceV :
      (∑ i, covTensor2DerivAt g H x v (b i) (sharp i)) =
        extDerivFun (fun y : M ↦ traceMetricVariationAt g H y) x v := by
    simpa [H, b, sharp] using hTrace v
  have hEntry : ∀ i,
      covTensor2DerivAt g H x v (b i) (sharp i) =
        g.inner x (closedCurvatureCovDerivAt g x v (b i) u w) (sharp i)
          + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E (b i)) (extend E Γu) (extend E w) x) (sharp i)
          + g.inner x
            (CovariantDerivative.curvatureOp g.leviCivita
              (extend E (b i)) (extend E u) (extend E Γw) x) (sharp i) := by
    intro i
    simpa [H, b, sharp, Γu, Γw] using
      covTensor2DerivAt_closedRicciTraceFieldAt
        (g := g) (x := x) (v := v) (u := u) (w := w)
        (p := b i) (q := sharp i)
  have hCovTrace :
      (∑ i, covTensor2DerivAt g H x v (b i) (sharp i)) =
        closedCovRicciDerivAt g x v u w
          + g.ricciAt x Γu w
          + g.ricciAt x u Γw := by
    have hClosed :
        (∑ i, g.inner x
          (closedCurvatureCovDerivAt g x v (b i) u w) (sharp i)) =
          closedCovRicciDerivAt g x v u w := by
      simpa [b, sharp] using
        (closedCovRicciDerivAt_eq_inner_contraction
          (g := g) (x := x) (v := v) (u := u) (w := w)).symm
    have hRicU :
        (∑ i, g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E (b i)) (extend E Γu) (extend E w) x) (sharp i)) =
          g.ricciAt x Γu w := by
      simpa [b, sharp] using
        (ricciAt_eq_curvature_inner_contraction
          (g := g) (x := x) (u := Γu) (w := w)).symm
    have hRicW :
        (∑ i, g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E (b i)) (extend E u) (extend E Γw) x) (sharp i)) =
          g.ricciAt x u Γw := by
      simpa [b, sharp] using
        (ricciAt_eq_curvature_inner_contraction
          (g := g) (x := x) (u := u) (w := Γw)).symm
    calc
      (∑ i, covTensor2DerivAt g H x v (b i) (sharp i)) =
          ∑ i,
            (g.inner x (closedCurvatureCovDerivAt g x v (b i) u w) (sharp i)
              + g.inner x
                (CovariantDerivative.curvatureOp g.leviCivita
                  (extend E (b i)) (extend E Γu) (extend E w) x) (sharp i)
              + g.inner x
                (CovariantDerivative.curvatureOp g.leviCivita
                  (extend E (b i)) (extend E u) (extend E Γw) x) (sharp i)) := by
            exact Finset.sum_congr rfl fun i _ ↦ hEntry i
      _ =
          (∑ i, g.inner x
            (closedCurvatureCovDerivAt g x v (b i) u w) (sharp i))
            + (∑ i, g.inner x
              (CovariantDerivative.curvatureOp g.leviCivita
                (extend E (b i)) (extend E Γu) (extend E w) x) (sharp i))
            + (∑ i, g.inner x
              (CovariantDerivative.curvatureOp g.leviCivita
                (extend E (b i)) (extend E u) (extend E Γw) x) (sharp i)) := by
            simp [Finset.sum_add_distrib, add_assoc]
      _ = closedCovRicciDerivAt g x v u w
            + g.ricciAt x Γu w
            + g.ricciAt x u Γw := by
            rw [hClosed, hRicU, hRicW]
  calc
    extDerivFun
        (fun y : M ↦ g.ricciAt y (extend E u y) (extend E w y)) x v =
        extDerivFun (fun y : M ↦ traceMetricVariationAt g H y) x v := hTraceEq.symm
    _ = ∑ i, covTensor2DerivAt g H x v (b i) (sharp i) := hTraceV.symm
    _ = closedCovRicciDerivAt g x v u w
          + g.ricciAt x Γu w
          + g.ricciAt x u Γw := hCovTrace

theorem closedCovRicciDerivAt_symm
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w : TM x) :
    closedCovRicciDerivAt g x v u w =
      closedCovRicciDerivAt g x v w u := by
  rw [← covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt
      (g := g) (x := x)
      (hRic := closedRicciDerivativeExpansionAt_canonical g x)
      (v := v) (u := u) (w := w)]
  rw [← covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt
      (g := g) (x := x)
      (hRic := closedRicciDerivativeExpansionAt_canonical g x)
      (v := v) (u := w) (w := u)]
  exact covTensor2DerivAt_ricciVariationField_symm
    (g := g) (x := x) v u w

theorem eventually_closedRicciDerivativeExpansionAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y :=
  Filter.Eventually.of_forall fun y ↦
    closedRicciDerivativeExpansionAt_canonical g y

theorem traceMetricVariationDerivAt_timeDeriv_of_covTensor2ExtDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x) :
    TraceMetricVariationDerivAt (gt t₀) (timeDerivAt gt t₀) x :=
  traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
    (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
    hDiff
    (tensor2AddLeft_timeDerivAt hgt)
    (tensor2SMulLeft_timeDerivAt hgt)
    (tensor2AddRight_timeDerivAt hgt)
    (tensor2SMulRight_timeDerivAt hgt)
    (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
    (by
      intro y p q
      rfl)

theorem closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : ClosedRicciDerivativeExpansionAt g x)
    (hDiff : CovTensor2ExtDifferentiableAt (ricciVariationField g) x)
    (w : TM x) :
    closedScalarContractionDerivTraceAt g x w =
      extDerivFun (fun y : M ↦ g.scalarAt y) x w := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hTrace : TraceMetricVariationDerivAt g (ricciVariationField g) x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := ricciVariationField g) (x := x)
      hDiff
      (tensor2AddLeft_ricciVariationField g)
      (tensor2SMulLeft_ricciVariationField g)
      (tensor2AddRight_ricciVariationField g)
      (tensor2SMulRight_ricciVariationField g)
      (ricciVariationBilinForm g)
      (by intro y p q; rfl)
  have hTraceW :
      (∑ i, covTensor2DerivAt g (ricciVariationField g) x w (b i) (sharp i)) =
        extDerivFun
          (fun y : M ↦ traceMetricVariationAt g (ricciVariationField g) y)
          x w := by
    simpa [b, sharp] using hTrace w
  calc
    closedScalarContractionDerivTraceAt g x w =
        ∑ i, closedCovRicciDerivAt g x w (sharp i) (b i) := by
          simp [closedScalarContractionDerivTraceAt, b, sharp]
    _ = ∑ i, covTensor2DerivAt g (ricciVariationField g) x w (sharp i) (b i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact (covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt
            (g := g) (x := x) hRic w (sharp i) (b i)).symm
    _ = ∑ i, covTensor2DerivAt g (ricciVariationField g) x w (b i) (sharp i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact covTensor2DerivAt_ricciVariationField_symm
            (g := g) (x := x) w (sharp i) (b i)
    _ = extDerivFun
          (fun y : M ↦ traceMetricVariationAt g (ricciVariationField g) y)
          x w := hTraceW
    _ = extDerivFun (fun y : M ↦ g.scalarAt y) x w := by
          exact extDerivFun_traceMetricVariationAt_ricci (g := g) x w

theorem eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : ∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y)
    (hDiff :
      ∀ᶠ y in nhds x, CovTensor2ExtDifferentiableAt (ricciVariationField g) y) :
    ∀ᶠ y in nhds x, ∀ w : TM y,
      closedScalarContractionDerivTraceAt g y w =
        extDerivFun (fun z : M ↦ g.scalarAt z) y w := by
  filter_upwards [hRic, hDiff] with y hyRic hyDiff
  intro w
  exact closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt
    (g := g) (x := y) hyRic hyDiff w

theorem covTensor2ExtDifferentiableAt_ricciVariationField_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    CovTensor2ExtDifferentiableAt (ricciVariationField g) x := by
  intro p q
  let H : ∀ y : M, TM y → TM y → ℝ := closedRicciTraceFieldAt g p q
  have hTraceDiff :
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ traceMetricVariationAt g H y) x :=
    traceMetricVariationAt_mdiffAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := H) (x := x)
      (by
        simpa [H] using
          covTensor2ExtDifferentiableAt_closedRicciTraceFieldAt
            (g := g) (u := p) (w := q))
      (fun y ↦ closedRicciTraceBilinFormAt g p q y)
      (by intro y a b; rfl)
  have heq :
      (fun y : M ↦ ricciVariationField g y (extend E p y) (extend E q y))
        =ᶠ[nhds x]
      (fun y : M ↦ traceMetricVariationAt g H y) :=
    Filter.Eventually.of_forall fun y ↦ by
      simpa [ricciVariationField, H] using
        (traceMetricVariationAt_closedRicciTraceFieldAt
          (g := g) (u := p) (w := q) (y := y)).symm
  exact hTraceDiff.congr_of_eventuallyEq heq

theorem eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∀ᶠ y in nhds x, ∀ w : TM y,
      tensorDivergenceOneFormAt g (ricciVariationField g) y w =
        closedRicciDivergenceTraceAt g y w :=
  eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt
    (g := g) (x := x)
    (eventually_closedRicciDerivativeExpansionAt_canonical g x)

theorem eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∀ᶠ y in nhds x, ∀ w : TM y,
      closedScalarContractionDerivTraceAt g y w =
        extDerivFun (fun z : M ↦ g.scalarAt z) y w :=
  eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt
    (g := g) (x := x)
    (eventually_closedRicciDerivativeExpansionAt_canonical g x)
    (Filter.Eventually.of_forall fun y ↦
      covTensor2ExtDifferentiableAt_ricciVariationField_canonical
        (g := g) (x := y))

set_option maxHeartbeats 5000000 in
/--
The divergence-slot trace of the second covariant derivative is the covariant
derivative of the divergence one-form.
-/
theorem covTensor2SecondDerivAt_timeDeriv_divergence_trace_eq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (u w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun i ↦ metricDualVectorAt g x (b.coord i)
      ∑ i, covTensor2SecondDerivAt g H x u (b i) (sharp i) w)
      =
      (let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E w y))
          x u
        - tensorDivergenceOneFormAt g H x
          (g.leviCivita (extend E w) x u)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  let Γw : TM x := g.leviCivita (extend E w) x u
  let K : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦ covTensor2DerivAt g H y p q (extend E w y)
  have hHAddL : Tensor2AddLeft H := tensor2AddLeft_timeDerivAt hgt
  have hHSMulL : Tensor2SMulLeft H := tensor2SMulLeft_timeDerivAt hgt
  have hHAddR : Tensor2AddRight H := tensor2AddRight_timeDerivAt hgt
  have hHSMulR : Tensor2SMulRight H := tensor2SMulRight_timeDerivAt hgt
  have hKDiff : CovTensor2ExtDifferentiableAt K x := by
    intro p q
    simpa [K, g, H] using hSecond p q w
  have hKAddL : Tensor2AddLeft K := by
    intro y p₁ p₂ q
    dsimp [K]
    exact covTensor2DerivAt_add_deriv
      (g := g) (h := H) (x := y) hHAddL hHAddR
      p₁ p₂ q (extend E w y)
  have hKSMulL : Tensor2SMulLeft K := by
    intro y c p q
    dsimp [K]
    exact covTensor2DerivAt_smul_deriv
      (g := g) (h := H) (x := y) hHSMulL hHSMulR
      c p q (extend E w y)
  have hKAddR : Tensor2AddRight K := by
    intro y p q₁ q₂
    dsimp [K]
    exact covTensor2DerivAt_add_left
      (g := g) (h := H) (x := y) (hCovDiff y) hHAddL
      p q₁ q₂ (extend E w y)
  have hKSMulR : Tensor2SMulRight K := by
    intro y c p q
    dsimp [K]
    exact covTensor2DerivAt_smul_left
      (g := g) (h := H) (x := y) (hCovDiff y) hHSMulL
      c p q (extend E w y)
  let BK : ∀ y : M, LinearMap.BilinForm ℝ (TM y) :=
    fun y ↦ LinearMap.mk₂ ℝ (K y)
      (fun p p' q ↦ hKAddL y p p' q)
      (fun c p q ↦ hKSMulL y c p q)
      (fun p q q' ↦ hKAddR y p q q')
      (fun c p q ↦ hKSMulR y c p q)
  have hTraceK : TraceMetricVariationDerivAt g K x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := K) (x := x)
      hKDiff hKAddL hKSMulL hKAddR hKSMulR BK
      (by intro y p q; rfl)
  have hTraceField :
      (fun y : M ↦ traceMetricVariationAt g K y) =
        fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E w y) := by
    funext y
    have hswap : CovTensor2DerivTraceSwapAt g H y :=
      covTensor2DerivTraceSwapAt_timeDeriv_of_regular
        (gt := gt) (t₀ := t₀) (x := y) hgt (hCovDiff y)
    simpa [TraceMetricVariationDerivAt, traceMetricVariationAt,
      tensorDivergenceOneFormAt, K, g, H] using hswap (extend E w y)
  have hTraceK' :
      (∑ i, covTensor2DerivAt g K x u (b i) (sharp i)) =
        extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E w y))
          x u := by
    have h := hTraceK u
    rw [hTraceField] at h
    simpa [TraceMetricVariationDerivAt, traceMetricVariationAt, b, sharp] using h
  have hEntry : ∀ i : Fin (Module.finrank ℝ (TM x)),
      covTensor2DerivAt g K x u (b i) (sharp i) =
        covTensor2SecondDerivAt g H x u (b i) (sharp i) w
          + covTensor2DerivAt g H x (b i) (sharp i) Γw := by
    intro i
    let A : ℝ :=
      extDerivFun
        (fun y : M ↦ covTensor2DerivAt g H y
          (extend E (b i) y) (extend E (sharp i) y) (extend E w y)) x u
    let Cv : ℝ :=
      covTensor2DerivAt g H x
        (g.leviCivita (extend E (b i)) x u) (sharp i) w
    let Cp : ℝ :=
      covTensor2DerivAt g H x (b i)
        (g.leviCivita (extend E (sharp i)) x u) w
    let Cq : ℝ :=
      covTensor2DerivAt g H x (b i) (sharp i) Γw
    have hKentry :
        covTensor2DerivAt g K x u (b i) (sharp i) = A - Cv - Cp := by
      unfold covTensor2DerivAt
      simp [A, Cv, Cp, K, g, H]
    have hSecondEntry :
        covTensor2SecondDerivAt g H x u (b i) (sharp i) w =
          A - Cv - Cp - Cq := by
      unfold covTensor2SecondDerivAt
      simp [A, Cv, Cp, Cq, Γw, g, H]
    rw [hKentry, hSecondEntry]
    ring
  have hTraceSum :
      (∑ i, covTensor2DerivAt g K x u (b i) (sharp i)) =
        (∑ i, covTensor2SecondDerivAt g H x u (b i) (sharp i) w)
          + ∑ i, covTensor2DerivAt g H x (b i) (sharp i) Γw := by
    calc
      (∑ i, covTensor2DerivAt g K x u (b i) (sharp i))
          =
          ∑ i,
            (covTensor2SecondDerivAt g H x u (b i) (sharp i) w
              + covTensor2DerivAt g H x (b i) (sharp i) Γw) := by
            exact Finset.sum_congr rfl fun i _hi ↦ hEntry i
      _ =
          (∑ i, covTensor2SecondDerivAt g H x u (b i) (sharp i) w)
            + ∑ i, covTensor2DerivAt g H x (b i) (sharp i) Γw := by
            rw [Finset.sum_add_distrib]
  have hGammaTrace :
      (∑ i, covTensor2DerivAt g H x (b i) (sharp i) Γw) =
        tensorDivergenceOneFormAt g H x Γw := by
    have hswap : CovTensor2DerivTraceSwapAt g H x :=
      covTensor2DerivTraceSwapAt_timeDeriv_of_regular
        (gt := gt) (t₀ := t₀) (x := x) hgt (hCovDiff x)
    simpa [CovTensor2DerivTraceSwapAt, tensorDivergenceOneFormAt,
      g, H, b, sharp] using hswap Γw
  have hmain :
      (∑ i, covTensor2SecondDerivAt g H x u (b i) (sharp i) w)
          + tensorDivergenceOneFormAt g H x Γw =
        extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E w y))
          x u := by
    rw [← hGammaTrace]
    exact hTraceSum.symm.trans hTraceK'
  change (∑ i, covTensor2SecondDerivAt g H x u (b i) (sharp i) w) =
    extDerivFun
        (fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E w y))
        x u
      - tensorDivergenceOneFormAt g H x Γw
  linarith

set_option maxHeartbeats 5000000 in
/--
The scalar-entry bridge identifies the covariant derivative of the moving
inner-trace field with the fixed-base trace of
`g((∇_u δΓ)(eᵢ,eⁱ), w)`.
-/
theorem deltaGammaInnerTraceFieldDerivativeTraceAt_of_entryBridge
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x) :
    ∀ u w : TM x,
      (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        let g : ClosedSmoothRiemannianMetric n M := gt t₀
        let b := Module.finBasis ℝ (TM x)
        let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
          fun i ↦ metricDualVectorAt g x (b.coord i)
        ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
      =
        (let g : ClosedSmoothRiemannianMetric n M := gt t₀
        extDerivFun
            (fun y : M ↦ deltaGammaInnerTraceFieldAt g gt t₀ y (extend E w y))
            x u
          - deltaGammaInnerTraceFieldAt g gt t₀ x
            (g.leviCivita (extend E w) x u)) := by
  intro u w
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let hδ : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦ g.inner y (deltaGammaAt gt t₀ y p q) (extend E w y)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hDiff : CovTensor2ExtDifferentiableAt hδ x := by
    intro p q
    simpa [hδ, g] using
      deltaGammaInnerTraceEntry_mdiffAt_of_entryBridge
        (gt := gt) (t₀ := t₀) (x := x) hBridge p q w
  have hAddL : Tensor2AddLeft hδ := by
    intro y p₁ p₂ q
    dsimp [hδ]
    rw [deltaGammaAt_add_left (gt := gt) (t₀ := t₀) (x := y)
      (hreg.connection y) p₁ p₂ q]
    exact (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L (extend E w y))
      (map_add (g.inner y)
        (deltaGammaAt gt t₀ y p₁ q)
        (deltaGammaAt gt t₀ y p₂ q)) : _)
  have hSMulL : Tensor2SMulLeft hδ := by
    intro y c p q
    dsimp [hδ]
    rw [deltaGammaAt_smul_left (gt := gt) (t₀ := t₀) (x := y)
      (hreg.connection y) c p q]
    simpa [smul_eq_mul] using
      (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L (extend E w y))
        (map_smul (g.inner y) c (deltaGammaAt gt t₀ y p q)) : _)
  have hAddR : Tensor2AddRight hδ := by
    intro y p q₁ q₂
    dsimp [hδ]
    rw [deltaGammaAt_add_right (gt := gt) (t₀ := t₀) (x := y)
      (hreg.connection y) p q₁ q₂]
    exact (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L (extend E w y))
      (map_add (g.inner y)
        (deltaGammaAt gt t₀ y p q₁)
        (deltaGammaAt gt t₀ y p q₂)) : _)
  have hSMulR : Tensor2SMulRight hδ := by
    intro y c p q
    dsimp [hδ]
    rw [deltaGammaAt_smul_right (gt := gt) (t₀ := t₀) (x := y)
      (hreg.connection y) c p q]
    simpa [smul_eq_mul] using
      (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L (extend E w y))
        (map_smul (g.inner y) c (deltaGammaAt gt t₀ y p q)) : _)
  let B : ∀ y : M, LinearMap.BilinForm ℝ (TM y) :=
    fun y ↦ LinearMap.mk₂ ℝ (hδ y)
      (fun p p' q ↦ hAddL y p p' q)
      (fun c p q ↦ hSMulL y c p q)
      (fun p q q' ↦ hAddR y p q q')
      (fun c p q ↦ hSMulR y c p q)
  have hTraceDeriv : TraceMetricVariationDerivAt g hδ x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := hδ) (x := x)
      hDiff hAddL hSMulL hAddR hSMulR B (by intro y p q; rfl)
  have hFieldTrace :
      (fun y : M ↦ deltaGammaInnerTraceFieldAt g gt t₀ y (extend E w y)) =
        fun y : M ↦ traceMetricVariationAt g hδ y := by
    funext y
    letI : FiniteDimensional ℝ (TM y) := inferInstanceAs (FiniteDimensional ℝ E)
    unfold deltaGammaInnerTraceFieldAt traceMetricVariationAt
    refine Finset.sum_congr rfl fun i _hi ↦ ?_
    simp [hδ]
  have hCovEntry : ∀ i : Fin (Module.finrank ℝ (TM x)),
      covTensor2DerivAt g hδ x u (b i) (sharp i) =
        g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w
        + g.inner x (deltaGammaAt gt t₀ x (b i) (sharp i))
            (g.leviCivita (extend E w) x u) := by
    intro i
    have hbridge :=
      deltaGammaInnerTraceEntry_extDeriv_eq_of_entryBridge
        (gt := gt) (t₀ := t₀) (x := x) hBridge u (b i) (sharp i) w
    have hflat :
      extDerivFun
          (fun y : M ↦
            g.inner y
              (deltaGammaAt gt t₀ y (extend E (b i) y)
                (extend E (sharp i) y))
              (extend E w y)) x u
      =
          covTensor2DerivAt g hδ x u (b i) (sharp i)
          + g.inner x
              (deltaGammaAt gt t₀ x
                (g.leviCivita (extend E (b i)) x u) (sharp i)) w
          + g.inner x
              (deltaGammaAt gt t₀ x (b i)
                (g.leviCivita (extend E (sharp i)) x u)) w := by
      simpa [hδ] using
        extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections
          (g := g) (h := hδ) (x := x) (v := u)
          (p := b i) (q := sharp i)
    have heq := hflat.symm.trans hbridge
    linarith
  have hCovTrace :
      (∑ i, covTensor2DerivAt g hδ x u (b i) (sharp i)) =
        (∑ i, g.inner x
          (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
        + deltaGammaInnerTraceFieldAt g gt t₀ x
            (g.leviCivita (extend E w) x u) := by
    calc
      (∑ i, covTensor2DerivAt g hδ x u (b i) (sharp i))
          =
          ∑ i,
            (g.inner x
              (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w
              + g.inner x (deltaGammaAt gt t₀ x (b i) (sharp i))
                (g.leviCivita (extend E w) x u)) := by
            exact Finset.sum_congr rfl fun i _hi ↦ hCovEntry i
      _ =
          (∑ i, g.inner x
            (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
          + ∑ i, g.inner x (deltaGammaAt gt t₀ x (b i) (sharp i))
              (g.leviCivita (extend E w) x u) := by
            rw [Finset.sum_add_distrib]
      _ =
          (∑ i, g.inner x
            (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
          + deltaGammaInnerTraceFieldAt g gt t₀ x
              (g.leviCivita (extend E w) x u) := by
            simp [deltaGammaInnerTraceFieldAt, b, sharp]
  have hTrace := hTraceDeriv u
  have hTrace' :
      (∑ i, g.inner x
          (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
        + deltaGammaInnerTraceFieldAt g gt t₀ x
            (g.leviCivita (extend E w) x u)
      =
        extDerivFun
          (fun y : M ↦ deltaGammaInnerTraceFieldAt g gt t₀ y (extend E w y))
          x u := by
    rw [hFieldTrace]
    exact hCovTrace.symm.trans hTrace
  change (∑ i, g.inner x
      (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w) =
    extDerivFun
        (fun y : M ↦ deltaGammaInnerTraceFieldAt g gt t₀ y (extend E w y))
        x u
      - deltaGammaInnerTraceFieldAt g gt t₀ x
        (g.leviCivita (extend E w) x u)
  rw [← hTrace']
  ring

/-- The divergence contraction rewritten using the metric-dual raised basis. -/
theorem deltaGammaDivergenceAt_eq_inner_sum
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (u w : TM x) :
    deltaGammaDivergenceAt gt t₀ x u w =
      (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        let g : ClosedSmoothRiemannianMetric n M := gt t₀
        let b := Module.finBasis ℝ (TM x)
        let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
          fun i ↦ metricDualVectorAt g x (b.coord i)
        ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) u w) (sharp i)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  unfold deltaGammaDivergenceAt
  change (∑ i, b.coord i (covDeltaGammaDerivAt gt t₀ x (b i) u w)) =
    ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) u w) (sharp i)
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  simpa [g, b, sharp] using
    coord_eq_inner_metricDualVectorAt (g := g) (x := x) i
      (covDeltaGammaDerivAt gt t₀ x (b i) u w)

/--
The exact cyclic `∇δΓ` trace identity needed to replace the verified
inner-trace derivative contraction by `deltaGammaDivergenceAt`.

This lemma does not prove the cyclic identity; it records that, once the
curvature-free cyclic trace equality is supplied, the existing scalar-entry
bridge gives the divergence side in corrected inner-trace-field form.
-/
theorem deltaGammaDivergenceAt_eq_innerTraceFieldDerivative_of_entryBridge
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hcyclic :
      ∀ u w : TM x,
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          let g : ClosedSmoothRiemannianMetric n M := gt t₀
          let b := Module.finBasis ℝ (TM x)
          let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
            fun i ↦ metricDualVectorAt g x (b.coord i)
          ∑ i, g.inner x
            (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
        =
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          let g : ClosedSmoothRiemannianMetric n M := gt t₀
          let b := Module.finBasis ℝ (TM x)
          let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
            fun i ↦ metricDualVectorAt g x (b.coord i)
          ∑ i, g.inner x
            (covDeltaGammaDerivAt gt t₀ x (b i) w u) (sharp i))) :
    ∀ u w : TM x,
      deltaGammaDivergenceAt gt t₀ x w u =
        (let g : ClosedSmoothRiemannianMetric n M := gt t₀
        extDerivFun
            (fun y : M ↦ deltaGammaInnerTraceFieldAt g gt t₀ y (extend E w y))
            x u
          - deltaGammaInnerTraceFieldAt g gt t₀ x
            (g.leviCivita (extend E w) x u)) := by
  intro u w
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hderiv :
      (∑ i, g.inner x
          (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
        =
        extDerivFun
            (fun y : M ↦ deltaGammaInnerTraceFieldAt g gt t₀ y (extend E w y))
            x u
          - deltaGammaInnerTraceFieldAt g gt t₀ x
            (g.leviCivita (extend E w) x u) := by
    simpa [g, b, sharp] using
      deltaGammaInnerTraceFieldDerivativeTraceAt_of_entryBridge
        (gt := gt) (t₀ := t₀) (x := x) hreg hBridge u w
  have hcyclic' :
      (∑ i, g.inner x
          (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
        =
      (∑ i, g.inner x
          (covDeltaGammaDerivAt gt t₀ x (b i) w u) (sharp i)) := by
    simpa [g, b, sharp] using hcyclic u w
  have hdiv :
      deltaGammaDivergenceAt gt t₀ x w u =
        ∑ i, g.inner x
          (covDeltaGammaDerivAt gt t₀ x (b i) w u) (sharp i) := by
    simpa [g, b, sharp] using
      deltaGammaDivergenceAt_eq_inner_sum
        (gt := gt) (t₀ := t₀) (x := x) (u := w) (w := u)
  rw [hdiv]
  exact hcyclic'.symm.trans hderiv

set_option maxHeartbeats 5000000 in
/--
The scalar-entry derivative bridge closes the covariant derivative identity for
the first-slot `δΓ` trace field.
-/
theorem deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_of_entryBridge
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x) :
    DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x := by
  intro u w
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let hδ : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦ g.inner y (deltaGammaAt gt t₀ y p (extend E w y)) q
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hDiff : CovTensor2ExtDifferentiableAt hδ x := by
    intro p q
    simpa [hδ, g] using hBridge.mdifferentiable p q w
  have hAddL : Tensor2AddLeft hδ := by
    intro y p₁ p₂ q
    dsimp [hδ]
    rw [deltaGammaAt_add_left (gt := gt) (t₀ := t₀) (x := y)
      (hreg.connection y) p₁ p₂ (extend E w y)]
    exact (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L q)
      (map_add (g.inner y)
        (deltaGammaAt gt t₀ y p₁ (extend E w y))
        (deltaGammaAt gt t₀ y p₂ (extend E w y))) : _)
  have hSMulL : Tensor2SMulLeft hδ := by
    intro y c p q
    dsimp [hδ]
    rw [deltaGammaAt_smul_left (gt := gt) (t₀ := t₀) (x := y)
      (hreg.connection y) c p (extend E w y)]
    simpa [smul_eq_mul] using
      (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L q)
        (map_smul (g.inner y) c
          (deltaGammaAt gt t₀ y p (extend E w y))) : _)
  have hAddR : Tensor2AddRight hδ := by
    intro y p q₁ q₂
    dsimp [hδ]
    exact map_add (g.inner y (deltaGammaAt gt t₀ y p (extend E w y))) q₁ q₂
  have hSMulR : Tensor2SMulRight hδ := by
    intro y c p q
    dsimp [hδ]
    simpa [smul_eq_mul] using
      (map_smul (g.inner y (deltaGammaAt gt t₀ y p (extend E w y))) c q)
  let B : ∀ y : M, LinearMap.BilinForm ℝ (TM y) :=
    fun y ↦ LinearMap.mk₂ ℝ (hδ y)
      (fun p p' q ↦ hAddL y p p' q)
      (fun c p q ↦ hSMulL y c p q)
      (fun p q q' ↦ hAddR y p q q')
      (fun c p q ↦ hSMulR y c p q)
  have hTraceDeriv : TraceMetricVariationDerivAt g hδ x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := hδ) (x := x)
      hDiff hAddL hSMulL hAddR hSMulR B (by intro y p q; rfl)
  have hFieldTrace :
      (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y)) =
        fun y : M ↦ traceMetricVariationAt g hδ y := by
    funext y
    letI : FiniteDimensional ℝ (TM y) := inferInstanceAs (FiniteDimensional ℝ E)
    let bY := Module.finBasis ℝ (TM y)
    unfold deltaGammaFirstSlotTraceFieldAt traceMetricVariationAt
    refine Finset.sum_congr rfl fun i _hi ↦ ?_
    simpa [hδ, bY] using
      coord_eq_inner_metricDualVectorAt (g := g) (x := y) i
        (deltaGammaAt gt t₀ y (bY i) (extend E w y))
  have hCovEntry : ∀ i : Fin (Module.finrank ℝ (TM x)),
      covTensor2DerivAt g hδ x u (b i) (sharp i) =
        b.coord i (covDeltaGammaDerivAt gt t₀ x u (b i) w)
        + b.coord i
            (deltaGammaAt gt t₀ x (b i)
              (g.leviCivita (extend E w) x u)) := by
    intro i
    have hbridge := hBridge.extDeriv_eq u (b i) (sharp i) w
    have hcoord₁ :
        g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) w) (sharp i) =
          b.coord i (covDeltaGammaDerivAt gt t₀ x u (b i) w) := by
      simpa [g, b, sharp] using
        (coord_eq_inner_metricDualVectorAt (g := g) (x := x) i
          (covDeltaGammaDerivAt gt t₀ x u (b i) w)).symm
    have hcoord₂ :
        g.inner x
            (deltaGammaAt gt t₀ x (b i)
              (g.leviCivita (extend E w) x u)) (sharp i) =
          b.coord i
            (deltaGammaAt gt t₀ x (b i)
              (g.leviCivita (extend E w) x u)) := by
      simpa [g, b, sharp] using
        (coord_eq_inner_metricDualVectorAt (g := g) (x := x) i
          (deltaGammaAt gt t₀ x (b i)
            (g.leviCivita (extend E w) x u))).symm
    have hbridge' :
        extDerivFun
          (fun y : M ↦
            g.inner y
              (deltaGammaAt gt t₀ y (extend E (b i) y) (extend E w y))
              (extend E (sharp i) y)) x u
        =
          g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) w) (sharp i)
          + g.inner x
              (deltaGammaAt gt t₀ x
                (g.leviCivita (extend E (b i)) x u) w) (sharp i)
          + g.inner x
              (deltaGammaAt gt t₀ x (b i)
                (g.leviCivita (extend E w) x u)) (sharp i)
          + g.inner x
              (deltaGammaAt gt t₀ x (b i) w)
              (g.leviCivita (extend E (sharp i)) x u) := by
      simpa [g] using hbridge
    have hflat :
      extDerivFun
          (fun y : M ↦
            g.inner y
              (deltaGammaAt gt t₀ y (extend E (b i) y) (extend E w y))
              (extend E (sharp i) y)) x u
      =
          covTensor2DerivAt g hδ x u (b i) (sharp i)
          + g.inner x
              (deltaGammaAt gt t₀ x
                (g.leviCivita (extend E (b i)) x u) w) (sharp i)
          + g.inner x
              (deltaGammaAt gt t₀ x (b i) w)
              (g.leviCivita (extend E (sharp i)) x u) := by
      simpa [hδ] using
        extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections
          (g := g) (h := hδ) (x := x) (v := u)
          (p := b i) (q := sharp i)
    have heq := hflat.symm.trans hbridge'
    rw [hcoord₁, hcoord₂] at heq
    linarith
  have hCovTrace :
      (∑ i, covTensor2DerivAt g hδ x u (b i) (sharp i)) =
        deltaGammaContractionDerivAt gt t₀ x u w
        + deltaGammaFirstSlotTraceFieldAt gt t₀ x
            (g.leviCivita (extend E w) x u) := by
    calc
      (∑ i, covTensor2DerivAt g hδ x u (b i) (sharp i))
          =
          ∑ i,
            (b.coord i (covDeltaGammaDerivAt gt t₀ x u (b i) w)
              + b.coord i
                  (deltaGammaAt gt t₀ x (b i)
                    (g.leviCivita (extend E w) x u))) := by
            exact Finset.sum_congr rfl fun i _hi ↦ hCovEntry i
      _ =
          (∑ i, b.coord i (covDeltaGammaDerivAt gt t₀ x u (b i) w))
            + ∑ i, b.coord i
                (deltaGammaAt gt t₀ x (b i)
                  (g.leviCivita (extend E w) x u)) := by
            rw [Finset.sum_add_distrib]
      _ =
          deltaGammaContractionDerivAt gt t₀ x u w
            + deltaGammaFirstSlotTraceFieldAt gt t₀ x
              (g.leviCivita (extend E w) x u) := by
            simp [deltaGammaContractionDerivAt,
              deltaGammaFirstSlotTraceFieldAt, b]
  have hTrace := hTraceDeriv u
  have hTrace' :
      deltaGammaContractionDerivAt gt t₀ x u w
        + deltaGammaFirstSlotTraceFieldAt gt t₀ x
            (g.leviCivita (extend E w) x u)
      =
        extDerivFun
          (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
          x u := by
    rw [hFieldTrace]
    exact hCovTrace.symm.trans hTrace
  change deltaGammaContractionDerivAt gt t₀ x u w =
    extDerivFun
        (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
        x u
      - deltaGammaFirstSlotTraceFieldAt gt t₀ x
        (g.leviCivita (extend E w) x u)
  rw [← hTrace']
  ring

/--
Product-rule obligation for differentiating the metric trace.

It isolates the normed-space calculus step: the exterior derivative of
`tr_g h` is the finite sum of fixed-slot derivatives of `h` plus the
derivative of the raised dual basis vector.
-/
def TraceMetricVariationProductRuleAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ w : TM x,
    extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w =
      (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E);
        letI : T2Space (TM x) := inferInstanceAs (T2Space E);
        let b := Module.finBasis ℝ (TM x);
        let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
          fun i ↦ metricDualVectorAt g x (b.coord i);
        ∑ i,
          (extDerivFun (fun y : M ↦ h y (extend E (b i) y) (extend E (sharp i) y))
              x w
            + h x (b i)
              (spatialMetricDualVectorDerivAt g x w
                (LinearMap.toContinuousLinearMap (b.coord i)))))

/--
Discharge the trace product-rule obligation from its two local analytic pieces:
termwise differentiation in the transported finite frame, and the summand
product rule that uses the fixed-vector component regularity of `h`.
-/
theorem traceMetricVariationProductRuleAt_of_spatiallyDifferentiable
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hSpatial : VariationSpatiallyDifferentiableAt h x)
    (hFrame : ∀ w : TM x,
      extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w =
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E);
          let b := Module.finBasis ℝ (TM x);
          ∑ i, extDerivFun
            (fun y : M ↦ h y (extend E (b i) y)
              (metricDualVectorAt g y (b.coord i))) x w))
    (hSummand :
      ∀ (w : TM x) (i : Fin (Module.finrank ℝ (TM x))),
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E);
          letI : T2Space (TM x) := inferInstanceAs (T2Space E);
          let b := Module.finBasis ℝ (TM x);
          let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
            fun i ↦ metricDualVectorAt g x (b.coord i);
          MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ h y (b i) (sharp i)) x →
          extDerivFun
            (fun y : M ↦ h y (extend E (b i) y)
              (metricDualVectorAt g y (b.coord i))) x w =
            extDerivFun
              (fun y : M ↦ h y (extend E (b i) y) (extend E (sharp i) y))
              x w
              + h x (b i)
                (spatialMetricDualVectorDerivAt g x w
                  (LinearMap.toContinuousLinearMap (b.coord i))))) :
    TraceMetricVariationProductRuleAt g h x := by
  intro w
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hFrame' :
      extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w =
        ∑ i, extDerivFun
          (fun y : M ↦ h y (extend E (b i) y)
            (metricDualVectorAt g y (b.coord i))) x w := by
    simpa [b] using hFrame w
  rw [hFrame']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hcomp :
      MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ h y (b i) (sharp i)) x :=
    hSpatial (b i) (sharp i)
  simpa [b, sharp] using hSummand w i hcomp

/--
Raised-index cancellation obligation for the trace derivative.

This is the finite-sum algebra left after the derivative of the raised dual
basis has been identified as `spatialMetricDualVectorDerivAt`.
-/
def TraceMetricVariationRaiseCancellationAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ w : TM x,
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E);
      letI : T2Space (TM x) := inferInstanceAs (T2Space E);
      let b := Module.finBasis ℝ (TM x);
      ∑ i, h x (b i)
        (spatialMetricDualVectorDerivAt g x w
          (LinearMap.toContinuousLinearMap (b.coord i)))) =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E);
      letI : T2Space (TM x) := inferInstanceAs (T2Space E);
      let b := Module.finBasis ℝ (TM x);
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun i ↦ metricDualVectorAt g x (b.coord i);
      ∑ i,
        (-h x (g.leviCivita (extend E (b i)) x w) (sharp i)
          - h x (b i) (g.leviCivita (extend E (sharp i)) x w)))

theorem traceMetricVariationDerivAt_of_productRule_raiseCancellation
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hProduct : TraceMetricVariationProductRuleAt g h x)
    (hCancel : TraceMetricVariationRaiseCancellationAt g h x) :
    TraceMetricVariationDerivAt g h x := by
  intro w
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hProduct' :
      extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w =
        ∑ i,
          (extDerivFun
              (fun y : M ↦ h y (extend E (b i) y) (extend E (sharp i) y))
              x w
            + h x (b i)
              (spatialMetricDualVectorDerivAt g x w
                (LinearMap.toContinuousLinearMap (b.coord i)))) := by
    simpa [b, sharp] using hProduct w
  have hCancel' :
      (∑ i, h x (b i)
        (spatialMetricDualVectorDerivAt g x w
          (LinearMap.toContinuousLinearMap (b.coord i)))) =
        ∑ i,
          (-h x (g.leviCivita (extend E (b i)) x w) (sharp i)
            - h x (b i) (g.leviCivita (extend E (sharp i)) x w)) := by
    simpa [b, sharp] using hCancel w
  change (∑ i, covTensor2DerivAt g h x w (b i) (sharp i)) =
    extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w
  rw [hProduct', Finset.sum_add_distrib, hCancel', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [covTensor2DerivAt]
  ring

theorem traceMetricVariationDerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    TraceMetricVariationDerivAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x := by
  intro w
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  simp [extDerivFun_zero_at]

theorem traceMetricVariationDerivAt_const_timeDeriv
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TraceMetricVariationDerivAt g (timeDerivAt (fun _ : ℝ ↦ g) t₀) x := by
  have hzero :
      timeDerivAt (fun _ : ℝ ↦ g) t₀ =
        (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
    funext y v w
    exact timeDerivAt_const g t₀ y v w
  simpa [hzero] using traceMetricVariationDerivAt_zero (g := g) (x := x)

/--
Inner trace of the closed `δΓ` Koszul identity.

The two trace-commute hypotheses are the remaining closed-manifold
metric-compatibility obligations:
* `hTraceSwap` swaps the contracted derivative slot with the first tensor slot.
* `hTraceDeriv` identifies the contracted `∇h` trace with the derivative of
  `tr_g h`.

Both are used directly here; this lemma isolates the algebraic contraction of
`deltaGamma_koszul` from those still-open first-order trace facts.
-/
theorem deltaGamma_innerTrace_eq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hTraceSwap :
      ∀ w : TM x,
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          ∑ i, covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x
            ((Module.finBasis ℝ (TM x)) i)
            (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord i))
            w)
          = tensorDivergenceOneFormAt (gt t₀) (timeDerivAt gt t₀) x w)
    (hTraceDeriv :
      ∀ w : TM x,
        (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          ∑ i, covTensor2DerivAt (gt t₀) (timeDerivAt gt t₀) x w
            ((Module.finBasis ℝ (TM x)) i)
            (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord i)))
          = extDerivFun
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x w)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (gt t₀).inner x
        (deltaGammaAt gt t₀ x ((Module.finBasis ℝ (TM x)) i)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord i))) w)
      =
        tensorDivergenceOneFormAt (gt t₀) (timeDerivAt gt t₀) x w
          - (1 / 2 : ℝ) *
            extDerivFun
              (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y)
              x w := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hkoszul : ∀ i : Fin (Module.finrank ℝ (TM x)),
      g.inner x (deltaGammaAt gt t₀ x (b i) (sharp i)) w =
        (1 / 2 : ℝ) *
          (covTensor2DerivAt g H x (b i) (sharp i) w
            + covTensor2DerivAt g H x (sharp i) (b i) w
            - covTensor2DerivAt g H x w (b i) (sharp i)) := by
    intro i
    have hk := deltaGamma_koszul
      (gt := gt) (t₀ := t₀) (x := x) hreg hgt hExt (b i) (sharp i) w
    change 2 * g.inner x (deltaGammaAt gt t₀ x (b i) (sharp i)) w =
      covTensor2DerivAt g H x (b i) (sharp i) w
        + covTensor2DerivAt g H x (sharp i) (b i) w
        - covTensor2DerivAt g H x w (b i) (sharp i) at hk
    linarith
  have hA :
      (∑ i, covTensor2DerivAt g H x (b i) (sharp i) w) =
        tensorDivergenceOneFormAt g H x w := by
    simpa [g, H, b, sharp] using hTraceSwap w
  have hB :
      (∑ i, covTensor2DerivAt g H x (sharp i) (b i) w) =
        tensorDivergenceOneFormAt g H x w := by
    simp [tensorDivergenceOneFormAt, g, H, b, sharp]
  have hC :
      (∑ i, covTensor2DerivAt g H x w (b i) (sharp i)) =
        extDerivFun
          (fun y ↦ traceMetricVariationAt g H y) x w := by
    simpa [g, H, b, sharp] using hTraceDeriv w
  change (∑ i, g.inner x (deltaGammaAt gt t₀ x (b i) (sharp i)) w) =
    tensorDivergenceOneFormAt g H x w
      - (1 / 2 : ℝ) * extDerivFun
        (fun y ↦ traceMetricVariationAt g H y) x w
  rw [Finset.sum_congr rfl (fun i _ ↦ hkoszul i), ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC]
  ring

/--
Inner trace of `δΓ`, restated with named first-order trace regularity
obligations.
-/
theorem deltaGamma_innerTrace_eq'
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hTraceSwap :
      CovTensor2DerivTraceSwapAt (gt t₀) (timeDerivAt gt t₀) x)
    (hTraceDeriv :
      TraceMetricVariationDerivAt (gt t₀) (timeDerivAt gt t₀) x)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (gt t₀).inner x
        (deltaGammaAt gt t₀ x ((Module.finBasis ℝ (TM x)) i)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord i))) w)
      =
        tensorDivergenceOneFormAt (gt t₀) (timeDerivAt gt t₀) x w
          - (1 / 2 : ℝ) *
            extDerivFun
              (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y)
              x w :=
  deltaGamma_innerTrace_eq
    (gt := gt) (t₀ := t₀) (x := x)
    hreg hgt hExt hTraceSwap hTraceDeriv w

theorem deltaGamma_innerTrace_eq_of_covTensor2Regular
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (hTraceDeriv :
      TraceMetricVariationDerivAt (gt t₀) (timeDerivAt gt t₀) x)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (gt t₀).inner x
        (deltaGammaAt gt t₀ x ((Module.finBasis ℝ (TM x)) i)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord i))) w)
      =
        tensorDivergenceOneFormAt (gt t₀) (timeDerivAt gt t₀) x w
          - (1 / 2 : ℝ) *
            extDerivFun
              (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y)
              x w :=
  deltaGamma_innerTrace_eq'
    (gt := gt) (t₀ := t₀) (x := x)
    hreg hgt hExt
    (covTensor2DerivTraceSwapAt_timeDeriv_of_regular
      (gt := gt) (t₀ := t₀) (x := x) hgt hCovDiff)
    hTraceDeriv w

theorem deltaGamma_innerTrace_eq_of_covTensor2ExtDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (gt t₀).inner x
        (deltaGammaAt gt t₀ x ((Module.finBasis ℝ (TM x)) i)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord i))) w)
      =
        tensorDivergenceOneFormAt (gt t₀) (timeDerivAt gt t₀) x w
          - (1 / 2 : ℝ) *
            extDerivFun
              (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y)
              x w :=
  deltaGamma_innerTrace_eq_of_covTensor2Regular
    (gt := gt) (t₀ := t₀) (x := x)
    hreg hgt hExt hCovDiff
    (traceMetricVariationDerivAt_timeDeriv_of_covTensor2ExtDifferentiableAt
      (gt := gt) (t₀ := t₀) (x := x) hgt hCovDiff)
    w

/--
First-slot trace of `δΓ`.

This is the closed analogue of the model identity
`δΓᵏ_{kw} = 1/2 ∂_w tr_g h`.  It is still first-order: the only analytic
inputs are the Koszul variation formula and the already-proved Gram-route trace
derivative.
-/
theorem deltaGamma_firstSlot_trace_eq_of_covTensor2ExtDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (Module.finBasis ℝ (TM x)).coord i
        (deltaGammaAt gt t₀ x ((Module.finBasis ℝ (TM x)) i) w))
      =
        (1 / 2 : ℝ) *
          extDerivFun
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y)
            x w := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hTraceSwap :
      CovTensor2DerivTraceSwapAt g H x :=
    covTensor2DerivTraceSwapAt_timeDeriv_of_regular
      (gt := gt) (t₀ := t₀) (x := x) hgt hCovDiff
  have hTraceDeriv :
      TraceMetricVariationDerivAt g H x :=
    traceMetricVariationDerivAt_timeDeriv_of_covTensor2ExtDifferentiableAt
      (gt := gt) (t₀ := t₀) (x := x) hgt hCovDiff
  have hkoszul : ∀ i : Fin (Module.finrank ℝ (TM x)),
      b.coord i (deltaGammaAt gt t₀ x (b i) w) =
        (1 / 2 : ℝ) *
          (covTensor2DerivAt g H x (b i) w (sharp i)
            + covTensor2DerivAt g H x w (b i) (sharp i)
            - covTensor2DerivAt g H x (sharp i) (b i) w) := by
    intro i
    have hk := deltaGamma_koszul
      (gt := gt) (t₀ := t₀) (x := x) hreg hgt hExt (b i) w (sharp i)
    change 2 * g.inner x (deltaGammaAt gt t₀ x (b i) w) (sharp i) =
      covTensor2DerivAt g H x (b i) w (sharp i)
        + covTensor2DerivAt g H x w (b i) (sharp i)
        - covTensor2DerivAt g H x (sharp i) (b i) w at hk
    have hcoord :
        b.coord i (deltaGammaAt gt t₀ x (b i) w) =
          g.inner x (deltaGammaAt gt t₀ x (b i) w) (sharp i) := by
      simpa [g, b, sharp] using
        coord_eq_inner_metricDualVectorAt (g := g) (x := x) i
          (deltaGammaAt gt t₀ x (b i) w)
    rw [hcoord]
    linarith
  have hA :
      (∑ i, covTensor2DerivAt g H x (b i) w (sharp i)) =
        tensorDivergenceOneFormAt g H x w := by
    calc
      (∑ i, covTensor2DerivAt g H x (b i) w (sharp i)) =
          ∑ i, covTensor2DerivAt g H x (b i) (sharp i) w := by
            refine Finset.sum_congr rfl fun i _hi ↦ ?_
            exact covTensor2DerivAt_timeDeriv_symm
              (g := g) (gt := gt) (t₀ := t₀) (x := x) (v := b i)
              (p := w) (q := sharp i)
      _ = tensorDivergenceOneFormAt g H x w := by
            simpa [g, H, b, sharp] using hTraceSwap w
  have hB :
      (∑ i, covTensor2DerivAt g H x w (b i) (sharp i)) =
        extDerivFun (fun y ↦ traceMetricVariationAt g H y) x w := by
    simpa [g, H, b, sharp] using hTraceDeriv w
  have hC :
      (∑ i, covTensor2DerivAt g H x (sharp i) (b i) w) =
        tensorDivergenceOneFormAt g H x w := by
    simp [tensorDivergenceOneFormAt, g, H, b, sharp]
  change (∑ i, b.coord i (deltaGammaAt gt t₀ x (b i) w)) =
    (1 / 2 : ℝ) * extDerivFun
      (fun y ↦ traceMetricVariationAt g H y) x w
  rw [Finset.sum_congr rfl (fun i _ ↦ hkoszul i), ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC]
  ring

/-- Pointwise field form of `deltaGamma_firstSlot_trace_eq_of_covTensor2ExtDifferentiableAt`. -/
theorem deltaGammaFirstSlotTraceFieldAt_eq_half_trace_extDerivFun
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (w : TM x) :
    deltaGammaFirstSlotTraceFieldAt gt t₀ x w =
      (1 / 2 : ℝ) *
        extDerivFun
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y)
          x w := by
  simpa [deltaGammaFirstSlotTraceFieldAt] using
    deltaGamma_firstSlot_trace_eq_of_covTensor2ExtDifferentiableAt
      (gt := gt) (t₀ := t₀) (x := x) hreg hgt hExt hCovDiff w

/--
Neighborhood form of the first-slot trace field identity.  This is the
field-level reduction used before differentiating the trace form.
-/
theorem deltaGammaFirstSlotTraceFieldAt_eventually_eq_half_trace_extDerivFun
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (w : TM x) :
    (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
      =ᶠ[nhds x]
    (fun y : M ↦
      (1 / 2 : ℝ) *
        extDerivFun
          (fun z ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) z)
          y (extend E w y)) := by
  exact hNear.mono fun y hy ↦ by
    rcases hy with ⟨hreg, hCovDiff, hExt⟩
    exact deltaGammaFirstSlotTraceFieldAt_eq_half_trace_extDerivFun
      (gt := gt) (t₀ := t₀) (x := y) hreg hgt hExt hCovDiff (extend E w y)

/-- Differentiability of the first-slot trace field from local first-order
reduction and scalar trace C² regularity. -/
theorem deltaGammaFirstSlotTraceFieldDifferentiableAt_of_trace_extSecond
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hTrace₂ :
      TraceMetricVariationExtSecondDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x) :
    DeltaGammaFirstSlotTraceFieldDifferentiableAt gt t₀ x := by
  intro w
  have heq :=
    deltaGammaFirstSlotTraceFieldAt_eventually_eq_half_trace_extDerivFun
      (gt := gt) (t₀ := t₀) (x := x) hgt hNear w
  have hRhs : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        (1 / 2 : ℝ) *
          extDerivFun
            (fun z ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) z)
            y (extend E w y)) x := by
    exact (mdifferentiableAt_const (c := (1 / 2 : ℝ)) (x := x)).mul
      (hTrace₂ w)
  exact hRhs.congr_of_eventuallyEq heq

/--
Compatibility of the closed Hessian definition with differentiating the
exterior derivative field along a canonical extension.
-/
theorem extDerivFun_extDerivFun_extend_eq_hessianAt_add
    (g : ClosedSmoothRiemannianMetric n M) {f : M → ℝ} {x : M}
    (hgrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (u w : TM x) :
    extDerivFun (fun y : M ↦ extDerivFun f y (extend E w y)) x u =
      g.hessianAt f x u w +
        extDerivFun f x (g.leviCivita (extend E w) x u) := by
  let Y : ∀ y : M, TM y := extend E w
  have hY : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Y) x := by
    simpa [Y] using (mdifferentiableAt_extend (σ₀ := w) ..)
  have hYx : Y x = w := by simp [Y]
  have hpair :
      (fun y : M ↦ g.inner y ((g.gradient f) y) (Y y)) =
        fun y : M ↦ extDerivFun f y (Y y) := by
    funext y
    simpa [ClosedSmoothRiemannianMetric.gradient] using
      g.inner_gradientAt f y (Y y)
  have hgrad_cov :
      g.inner x ((g.gradient f) x) (g.leviCivita Y x u) =
        extDerivFun f x (g.leviCivita Y x u) := by
    simpa [ClosedSmoothRiemannianMetric.gradient] using
      g.inner_gradientAt f x (g.leviCivita Y x u)
  have h := g.leviCivita_metricCompatibleAt x hgrad hY u
  rw [hpair, hYx, hgrad_cov] at h
  simpa [ClosedSmoothRiemannianMetric.hessianAt, Y] using h

set_option maxHeartbeats 5000000 in
/--
The `H`-slot trace of the closed second covariant derivative is the Hessian of
the metric trace in the two remaining derivative slots.
-/
theorem covTensor2SecondDerivAt_Hslot_trace_eq_hessianAt
    (g : ClosedSmoothRiemannianMetric n M)
    (H : ∀ y : M, TM y → TM y → ℝ) {x : M}
    (hCovDiff : ∀ y : M, CovTensor2ExtDifferentiableAt H y)
    (hSecond : CovTensor2DerivExtDifferentiableAt g H x)
    (hAddL : Tensor2AddLeft H) (hSMulL : Tensor2SMulLeft H)
    (hAddR : Tensor2AddRight H) (hSMulR : Tensor2SMulRight H)
    (B : ∀ y : M, LinearMap.BilinForm ℝ (TM y))
    (hB : ∀ y : M, ∀ p q : TM y, B y p q = H y p q)
    (hgrad :
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (u w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
      =
      (let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      g.hessianAt f x u w) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  let Γw : TM x := g.leviCivita (extend E w) x u
  let K : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦ covTensor2DerivAt g H y (extend E w y) p q
  have hKDiff : CovTensor2ExtDifferentiableAt K x := by
    intro p q
    simpa [K] using hSecond w p q
  have hKAddL : Tensor2AddLeft K := by
    intro y p₁ p₂ q
    dsimp [K]
    exact covTensor2DerivAt_add_left
      (g := g) (h := H) (x := y) (hCovDiff y) hAddL
      (extend E w y) p₁ p₂ q
  have hKSMulL : Tensor2SMulLeft K := by
    intro y c p q
    dsimp [K]
    exact covTensor2DerivAt_smul_left
      (g := g) (h := H) (x := y) (hCovDiff y) hSMulL
      c (extend E w y) p q
  have hKAddR : Tensor2AddRight K := by
    intro y p q₁ q₂
    dsimp [K]
    exact covTensor2DerivAt_add_right
      (g := g) (h := H) (x := y) (hCovDiff y) hAddR
      (extend E w y) p q₁ q₂
  have hKSMulR : Tensor2SMulRight K := by
    intro y c p q
    dsimp [K]
    exact covTensor2DerivAt_smul_right
      (g := g) (h := H) (x := y) (hCovDiff y) hSMulR
      c (extend E w y) p q
  let BK : ∀ y : M, LinearMap.BilinForm ℝ (TM y) :=
    fun y ↦ LinearMap.mk₂ ℝ (K y)
      (fun p p' q ↦ hKAddL y p p' q)
      (fun c p q ↦ hKSMulL y c p q)
      (fun p q q' ↦ hKAddR y p q q')
      (fun c p q ↦ hKSMulR y c p q)
  have hTraceK : TraceMetricVariationDerivAt g K x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := K) (x := x)
      hKDiff hKAddL hKSMulL hKAddR hKSMulR BK
      (by intro y p q; rfl)
  have hTraceH : TraceMetricVariationDerivAt g H x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := H) (x := x)
      (hCovDiff x) hAddL hSMulL hAddR hSMulR B hB
  have hTraceField :
      (fun y : M ↦ traceMetricVariationAt g K y) =
        fun y : M ↦ extDerivFun f y (extend E w y) := by
    funext y
    have hTraceY : TraceMetricVariationDerivAt g H y :=
      traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
        (g := g) (h := H) (x := y)
        (hCovDiff y) hAddL hSMulL hAddR hSMulR B hB
    simpa [TraceMetricVariationDerivAt, traceMetricVariationAt, K, f] using
      hTraceY (extend E w y)
  have hTraceK' :
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j)) =
        extDerivFun
          (fun y : M ↦ extDerivFun f y (extend E w y)) x u := by
    have h := hTraceK u
    rw [hTraceField] at h
    simpa [TraceMetricVariationDerivAt, traceMetricVariationAt, b, sharp] using h
  have hEntry : ∀ j : Fin (Module.finrank ℝ (TM x)),
      covTensor2DerivAt g K x u (b j) (sharp j) =
        covTensor2SecondDerivAt g H x u w (b j) (sharp j)
          + covTensor2DerivAt g H x Γw (b j) (sharp j) := by
    intro j
    let A : ℝ :=
      extDerivFun
        (fun y : M ↦ covTensor2DerivAt g H y
          (extend E w y) (extend E (b j) y) (extend E (sharp j) y)) x u
    let Cw : ℝ := covTensor2DerivAt g H x Γw (b j) (sharp j)
    let Cp : ℝ :=
      covTensor2DerivAt g H x w
        (g.leviCivita (extend E (b j)) x u) (sharp j)
    let Cq : ℝ :=
      covTensor2DerivAt g H x w (b j)
        (g.leviCivita (extend E (sharp j)) x u)
    have hKentry :
        covTensor2DerivAt g K x u (b j) (sharp j) = A - Cp - Cq := by
      unfold covTensor2DerivAt
      simp [A, Cp, Cq, K]
    have hSecondEntry :
        covTensor2SecondDerivAt g H x u w (b j) (sharp j) =
          A - Cw - Cp - Cq := by
      unfold covTensor2SecondDerivAt
      simp [A, Cw, Cp, Cq, Γw]
    rw [hKentry, hSecondEntry]
    ring
  have hTraceSum :
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j)) =
        (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
          + ∑ j, covTensor2DerivAt g H x Γw (b j) (sharp j) := by
    calc
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j))
          =
          ∑ j,
            (covTensor2SecondDerivAt g H x u w (b j) (sharp j)
              + covTensor2DerivAt g H x Γw (b j) (sharp j)) := by
            exact Finset.sum_congr rfl fun j _hj ↦ hEntry j
      _ =
          (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
            + ∑ j, covTensor2DerivAt g H x Γw (b j) (sharp j) := by
            rw [Finset.sum_add_distrib]
  have hGammaTrace :
      (∑ j, covTensor2DerivAt g H x Γw (b j) (sharp j)) =
        extDerivFun f x Γw := by
    simpa [TraceMetricVariationDerivAt, f, b, sharp, Γw] using
      hTraceH Γw
  have hTraceSum' :
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j)) =
        (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
          + extDerivFun f x Γw := by
    rw [hTraceSum, hGammaTrace]
  have hcompat :
      extDerivFun
          (fun y : M ↦ extDerivFun f y (extend E w y)) x u =
        g.hessianAt f x u w + extDerivFun f x Γw := by
    simpa [f, Γw] using
      extDerivFun_extDerivFun_extend_eq_hessianAt_add
        (g := g) (f := f) (x := x)
        (by simpa [f] using hgrad) u w
  have hmain :
      (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
          + extDerivFun f x Γw =
        g.hessianAt f x u w + extDerivFun f x Γw := by
    exact hTraceSum'.symm.trans (hTraceK'.trans hcompat)
  linarith

set_option maxHeartbeats 5000000 in
/--
The `timeDerivAt` specialization of
`covTensor2SecondDerivAt_Hslot_trace_eq_hessianAt`.
-/
theorem covTensor2SecondDerivAt_timeDeriv_Hslot_trace_eq_hessianAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (u w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
      =
      (let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      g.hessianAt f x u w) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  let Γw : TM x := g.leviCivita (extend E w) x u
  let K : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦ covTensor2DerivAt g H y (extend E w y) p q
  have hHAddL : Tensor2AddLeft H := tensor2AddLeft_timeDerivAt hgt
  have hHSMulL : Tensor2SMulLeft H := tensor2SMulLeft_timeDerivAt hgt
  have hHAddR : Tensor2AddRight H := tensor2AddRight_timeDerivAt hgt
  have hHSMulR : Tensor2SMulRight H := tensor2SMulRight_timeDerivAt hgt
  have hKDiff : CovTensor2ExtDifferentiableAt K x := by
    intro p q
    simpa [K, g, H] using hSecond w p q
  have hKAddL : Tensor2AddLeft K := by
    intro y p₁ p₂ q
    dsimp [K]
    exact covTensor2DerivAt_add_left
      (g := g) (h := H) (x := y) (hCovDiff y) hHAddL
      (extend E w y) p₁ p₂ q
  have hKSMulL : Tensor2SMulLeft K := by
    intro y c p q
    dsimp [K]
    exact covTensor2DerivAt_smul_left
      (g := g) (h := H) (x := y) (hCovDiff y) hHSMulL
      c (extend E w y) p q
  have hKAddR : Tensor2AddRight K := by
    intro y p q₁ q₂
    dsimp [K]
    exact covTensor2DerivAt_add_right
      (g := g) (h := H) (x := y) (hCovDiff y) hHAddR
      (extend E w y) p q₁ q₂
  have hKSMulR : Tensor2SMulRight K := by
    intro y c p q
    dsimp [K]
    exact covTensor2DerivAt_smul_right
      (g := g) (h := H) (x := y) (hCovDiff y) hHSMulR
      c (extend E w y) p q
  let BK : ∀ y : M, LinearMap.BilinForm ℝ (TM y) :=
    fun y ↦ LinearMap.mk₂ ℝ (K y)
      (fun p p' q ↦ hKAddL y p p' q)
      (fun c p q ↦ hKSMulL y c p q)
      (fun p q q' ↦ hKAddR y p q q')
      (fun c p q ↦ hKSMulR y c p q)
  have hTraceK : TraceMetricVariationDerivAt g K x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := K) (x := x)
      hKDiff hKAddL hKSMulL hKAddR hKSMulR BK
      (by intro y p q; rfl)
  have hTraceH : TraceMetricVariationDerivAt g H x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := H) (x := x)
      (hCovDiff x) hHAddL hHSMulL hHAddR hHSMulR
      (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
      (by intro y p q; rfl)
  have hTraceField :
      (fun y : M ↦ traceMetricVariationAt g K y) =
        fun y : M ↦ extDerivFun f y (extend E w y) := by
    funext y
    have hTraceY : TraceMetricVariationDerivAt g H y :=
      traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
        (g := g) (h := H) (x := y)
        (hCovDiff y) hHAddL hHSMulL hHAddR hHSMulR
        (fun z ↦ timeDerivBilinAt gt t₀ z (hgt z))
        (by intro z p q; rfl)
    simpa [TraceMetricVariationDerivAt, traceMetricVariationAt, K, f, g, H] using
      hTraceY (extend E w y)
  have hTraceK' :
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j)) =
        extDerivFun
          (fun y : M ↦ extDerivFun f y (extend E w y)) x u := by
    have h := hTraceK u
    rw [hTraceField] at h
    simpa [TraceMetricVariationDerivAt, traceMetricVariationAt, b, sharp] using h
  have hEntry : ∀ j : Fin (Module.finrank ℝ (TM x)),
      covTensor2DerivAt g K x u (b j) (sharp j) =
        covTensor2SecondDerivAt g H x u w (b j) (sharp j)
          + covTensor2DerivAt g H x Γw (b j) (sharp j) := by
    intro j
    let A : ℝ :=
      extDerivFun
        (fun y : M ↦ covTensor2DerivAt g H y
          (extend E w y) (extend E (b j) y) (extend E (sharp j) y)) x u
    let Cw : ℝ := covTensor2DerivAt g H x Γw (b j) (sharp j)
    let Cp : ℝ :=
      covTensor2DerivAt g H x w
        (g.leviCivita (extend E (b j)) x u) (sharp j)
    let Cq : ℝ :=
      covTensor2DerivAt g H x w (b j)
        (g.leviCivita (extend E (sharp j)) x u)
    have hKentry :
        covTensor2DerivAt g K x u (b j) (sharp j) = A - Cp - Cq := by
      unfold covTensor2DerivAt
      simp [A, Cp, Cq, K, g, H]
    have hSecondEntry :
        covTensor2SecondDerivAt g H x u w (b j) (sharp j) =
          A - Cw - Cp - Cq := by
      unfold covTensor2SecondDerivAt
      simp [A, Cw, Cp, Cq, Γw, g, H]
    rw [hKentry, hSecondEntry]
    ring
  have hTraceSum :
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j)) =
        (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
          + ∑ j, covTensor2DerivAt g H x Γw (b j) (sharp j) := by
    calc
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j))
          =
          ∑ j,
            (covTensor2SecondDerivAt g H x u w (b j) (sharp j)
              + covTensor2DerivAt g H x Γw (b j) (sharp j)) := by
            exact Finset.sum_congr rfl fun j _hj ↦ hEntry j
      _ =
          (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
            + ∑ j, covTensor2DerivAt g H x Γw (b j) (sharp j) := by
            rw [Finset.sum_add_distrib]
  have hGammaTrace :
      (∑ j, covTensor2DerivAt g H x Γw (b j) (sharp j)) =
        extDerivFun f x Γw := by
    simpa [TraceMetricVariationDerivAt, f, b, sharp, Γw, g, H] using
      hTraceH Γw
  have hTraceSum' :
      (∑ j, covTensor2DerivAt g K x u (b j) (sharp j)) =
        (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
          + extDerivFun f x Γw := by
    rw [hTraceSum, hGammaTrace]
  have hcompat :
      extDerivFun
          (fun y : M ↦ extDerivFun f y (extend E w y)) x u =
        g.hessianAt f x u w + extDerivFun f x Γw := by
    simpa [g, H, f, Γw] using
      extDerivFun_extDerivFun_extend_eq_hessianAt_add
        (g := g) (f := f) (x := x)
        (by simpa [g, H, f] using hgrad) u w
  have hmain :
      (∑ j, covTensor2SecondDerivAt g H x u w (b j) (sharp j))
          + extDerivFun f x Γw =
        g.hessianAt f x u w + extDerivFun f x Γw := by
    exact hTraceSum'.symm.trans (hTraceK'.trans hcompat)
  linarith

set_option maxHeartbeats 5000000 in
/--
The trace block in the summed divergence trace is the raised Hessian trace of
`traceMetricVariationAt`.
-/
theorem deltaGammaDivergenceTraceSecondDerivTraceBlockAt_eq_sum_hessianAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    deltaGammaDivergenceTraceSecondDerivTraceBlockAt
        (gt t₀) (timeDerivAt gt t₀) x =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j, g.hessianAt f x (b j) (sharp j)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  change
      (∑ j, ∑ i,
        covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j))
      =
      ∑ j, g.hessianAt f x (b j) (sharp j)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  simpa [g, H, f, b, sharp] using
    covTensor2SecondDerivAt_timeDeriv_Hslot_trace_eq_hessianAt
      (gt := gt) (t₀ := t₀) (x := x)
      hgt hCovDiff hSecond hgrad (b i) (sharp i)

omit [T2Space M] in
/--
Closed Schwarz identity for canonical extensions, in its raw antisymmetric
form.  The obstruction to swapping the two exterior-derivative directions is
exactly the derivative along the manifold Lie bracket of the two extended
direction fields.
-/
theorem extDerivFun_extDerivFun_extend_sub_swap_eq_bracket
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (u v : TM x) :
    extDerivFun (fun y : M ↦ extDerivFun f y (extend E v y)) x u -
        extDerivFun (fun y : M ↦ extDerivFun f y (extend E u y)) x v =
      extDerivFun f x (VectorField.mlieBracket I (extend E u) (extend E v) x) := by
  have hU : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E u)) x := by
    simpa using (mdifferentiableAt_extend I E u)
  have hV : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E v)) x := by
    simpa using (mdifferentiableAt_extend I E v)
  have h := (extDerivFun_apply_mlieBracket (I' := I) hf hU hV).symm
  simpa using h

/--
Closed Schwarz identity after subtracting the first-order connection
corrections introduced by moving the canonical extension fields.  This is the
form supplied by `hessianAt_symm'` and the Hessian compatibility bridge.
-/
theorem extDerivFun_extDerivFun_extend_corrected_symm
    (g : ClosedSmoothRiemannianMetric n M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (u v : TM x) :
    extDerivFun (fun y : M ↦ extDerivFun f y (extend E v y)) x u -
        extDerivFun f x (g.leviCivita (extend E v) x u) =
      extDerivFun (fun y : M ↦ extDerivFun f y (extend E u y)) x v -
        extDerivFun f x (g.leviCivita (extend E u) x v) := by
  have hgrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x :=
    g.mdifferentiableAt_gradient hf
  have huv :=
    extDerivFun_extDerivFun_extend_eq_hessianAt_add
      (g := g) (f := f) (x := x) hgrad u v
  have hvu :=
    extDerivFun_extDerivFun_extend_eq_hessianAt_add
      (g := g) (f := f) (x := x) hgrad v u
  have hsymm := g.hessianAt_symm' hf u v
  rw [huv, hvu, hsymm]
  ring

/-- Scalar connection-entry field `g(∇_w z, q)` in canonical extension slots. -/
noncomputable def closedConnectionEntryFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} (w z q : TM x) : M → ℝ :=
  fun y : M ↦
    g.inner y
      (g.leviCivita (extend E z) y (extend E w y))
      (extend E q y)

/-- The scalar connection entries used in the mixed second-connection block are `C²`. -/
theorem closedConnectionEntry_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (w z q : TM x) :
    ContMDiffAt I 𝓘(ℝ) 2 (closedConnectionEntryFieldAt g w z q) x := by
  let W : Π y : M, TM y := extend E w
  let Z : Π y : M, TM y := extend E z
  let Q : Π y : M, TM y := extend E q
  have hW2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% W) x := by
    simpa [W] using (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
  have hZ3 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% Z) x := by
    simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 3) I E z)
  have hQ2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Q) x := by
    simpa [Q] using (FiberBundle.contMDiffAt_extend' (k := 2) I E q)
  haveI : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 2 :=
    ClosedSmoothRiemannianMetric.leviCivita_contMDiff₂ g
  have hA :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
        (T% (fun y : M ↦ g.leviCivita Z y (W y))) x :=
    CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
      (cov := g.leviCivita) hZ3 hW2
  exact g.metric_pairing_contMDiffAt_two
    (by simpa [W, Z] using hA) hQ2

/--
Metric-compatibility derivative of the scalar connection entry
`g(∇_u z, q)`: the exterior derivative is the iterated connection entry plus
the output-slot Levi-Civita correction.
-/
theorem closedConnectionEntry_extDerivFun_eq_iterated_add_output
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (v u z q : TM x) :
    extDerivFun (closedConnectionEntryFieldAt g u z q) x v =
      closedIteratedConnectionEntryFieldAt g u z x v q
        + closedConnectionEntryFieldAt g u z
          (g.leviCivita (extend E q) x v) x := by
  let U : Π y : M, TM y := extend E u
  let Z : Π y : M, TM y := extend E z
  let Q : Π y : M, TM y := extend E q
  let A : Π y : M, TM y := fun y ↦ g.leviCivita Z y (U y)
  have hZ2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Z) x := by
    simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 2) I E z)
  have hU : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% U) x := by
    simpa [U] using (mdifferentiableAt_extend I E u)
  have hA : MDiffAtTangentField A x := by
    simpa [MDiffAtTangentField, A] using
      (CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
        (cov := g.leviCivita) hZ2 hU)
  have hQ : MDiffAtTangentField Q x := by
    simpa [MDiffAtTangentField, Q] using (mdifferentiableAt_extend I E q)
  have h := g.leviCivita_metricCompatibleAt x hA hQ v
  simpa [closedConnectionEntryFieldAt, closedIteratedConnectionEntryFieldAt,
    A, U, Z, Q] using h

/--
Output-slot correction field in the moving first-derivative bridge for
`g(∇_u z, q)`: the extra term from differentiating the output section `q`.
-/
noncomputable def closedConnectionEntryOutputConnectionFieldAt
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} (a u z q : TM x) : M → ℝ :=
  fun y : M ↦
    g.inner y
      (g.leviCivita (extend E z) y (extend E u y))
      (g.leviCivita (extend E q) y (extend E a y))

/--
Moving-field form of the metric-compatibility derivative bridge for
`g(∇_u z, q)`, with the differentiating slot supplied by `extend E a`.
-/
theorem closedConnectionEntry_extDerivFun_extend_eq_iterated_add_output_eventually
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (a u z q : TM x) :
    (fun y : M ↦
      extDerivFun (closedConnectionEntryFieldAt g u z q) y (extend E a y))
      =ᶠ[nhds x]
    (fun y : M ↦
      closedIteratedConnectionEntryFieldAt g u z y
          (extend E a y) (extend E q y)
        + closedConnectionEntryOutputConnectionFieldAt g a u z q y) := by
  let U : Π y : M, TM y := extend E u
  let Z : Π y : M, TM y := extend E z
  let Q : Π y : M, TM y := extend E q
  let A : Π y : M, TM y := fun y ↦ g.leviCivita Z y (U y)
  have hZev := eventually_contMDiffAt_two_extend (n := n) (M := M) z
  have hUev := eventually_contMDiffAt_two_extend (n := n) (M := M) u
  have hQev := eventually_contMDiffAt_two_extend (n := n) (M := M) q
  filter_upwards [hZev, hUev, hQev] with y hZ2 hU2 hQ2
  have hU : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% U) y := by
    exact hU2.mdifferentiableAt (by norm_num)
  have hA : MDiffAtTangentField A y := by
    simpa [MDiffAtTangentField, A] using
      (CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
        (cov := g.leviCivita) hZ2 hU)
  have hQ : MDiffAtTangentField Q y := by
    simpa [MDiffAtTangentField, Q] using
      hQ2.mdifferentiableAt (by norm_num)
  have h := g.leviCivita_metricCompatibleAt y hA hQ (extend E a y)
  simpa [closedConnectionEntryFieldAt, closedIteratedConnectionEntryFieldAt,
    closedConnectionEntryOutputConnectionFieldAt, A, U, Z, Q] using h

/-- First-order regularity of the output-slot correction field. -/
theorem closedConnectionEntryOutputConnection_mdiffAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (a u z q : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (closedConnectionEntryOutputConnectionFieldAt g a u z q) x := by
  let A : Π y : M, TM y := extend E a
  let U : Π y : M, TM y := extend E u
  let Z : Π y : M, TM y := extend E z
  let Q : Π y : M, TM y := extend E q
  have hU : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% U) x := by
    simpa [U] using (mdifferentiableAt_extend I E u)
  have hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% A) x := by
    simpa [A] using (mdifferentiableAt_extend I E a)
  have hZ2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Z) x := by
    simpa [Z] using (FiberBundle.contMDiffAt_extend' (k := 2) I E z)
  have hQ2 : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Q) x := by
    simpa [Q] using (FiberBundle.contMDiffAt_extend' (k := 2) I E q)
  have hLeft :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦ g.leviCivita Z y (U y))) x :=
    CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
      (cov := g.leviCivita) hZ2 hU
  have hRight :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦ g.leviCivita Q y (A y))) x :=
    CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
      (cov := g.leviCivita) hQ2 hA
  exact g.metric_pairing_mdiffAt
    (by
      simpa [closedConnectionEntryOutputConnectionFieldAt, A, U, Z, Q] using hLeft)
    (by
      simpa [closedConnectionEntryOutputConnectionFieldAt, A, U, Z, Q] using hRight)

/--
Corrected second directional derivative of a scalar field in canonical
extension directions.  This is the scalar `∂∂` block after subtracting the
first-order connection correction from the moving inner direction.
-/
noncomputable def closedSecondDirectionalEntryAt
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ)
    (x : M) (v u : TM x) : ℝ :=
  extDerivFun (fun y : M ↦ extDerivFun f y (extend E u y)) x v
    - extDerivFun f x (g.leviCivita (extend E u) x v)

/--
Corrected second directional derivative of `g(∇_u z, q)` after the
metric-compatibility bridge.  This exposes the raw iterated-connection
derivative plus the output-slot correction derivative.
-/
theorem closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (v a u z q : TM x) :
    closedSecondDirectionalEntryAt g
        (closedConnectionEntryFieldAt g u z q) x v a =
      extDerivFun
          (fun y : M ↦
            closedIteratedConnectionEntryFieldAt g u z y
              (extend E a y) (extend E q y)) x v
        + extDerivFun
          (closedConnectionEntryOutputConnectionFieldAt g a u z q) x v
        - (closedIteratedConnectionEntryFieldAt g u z x
            (g.leviCivita (extend E a) x v) q
          + closedConnectionEntryOutputConnectionFieldAt g
            (g.leviCivita (extend E a) x v) u z q x) := by
  let F : M → ℝ := fun y : M ↦
    extDerivFun (closedConnectionEntryFieldAt g u z q) y (extend E a y)
  let A : M → ℝ := fun y : M ↦
    closedIteratedConnectionEntryFieldAt g u z y
      (extend E a y) (extend E q y)
  let B : M → ℝ := closedConnectionEntryOutputConnectionFieldAt g a u z q
  have heq : F =ᶠ[nhds x] fun y : M ↦ A y + B y := by
    simpa [F, A, B] using
      closedConnectionEntry_extDerivFun_extend_eq_iterated_add_output_eventually
        (g := g) (x := x) a u z q
  have hderiv :
      extDerivFun F x v =
        extDerivFun (fun y : M ↦ A y + B y) x v := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
      (CovariantDerivative.extDerivFun_congr heq)
  have hA : MDifferentiableAt I 𝓘(ℝ) A x := by
    simpa [A] using closedIteratedConnectionEntry_mdiffAt
      (g := g) (a := a) (u := u) (w := z) (q := q)
  have hB : MDifferentiableAt I 𝓘(ℝ) B x := by
    simpa [B] using closedConnectionEntryOutputConnection_mdiffAt
      (g := g) (a := a) (u := u) (z := z) (q := q)
  have hsplit :
      extDerivFun (fun y : M ↦ A y + B y) x v =
        extDerivFun A x v + extDerivFun B x v := by
    have h :=
      congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
        (extDerivFun_add hA hB)
    simpa using h
  have hcorr :
      extDerivFun (closedConnectionEntryFieldAt g u z q) x
          (g.leviCivita (extend E a) x v) =
        closedIteratedConnectionEntryFieldAt g u z x
          (g.leviCivita (extend E a) x v) q
          + closedConnectionEntryOutputConnectionFieldAt g
            (g.leviCivita (extend E a) x v) u z q x := by
    simpa [closedConnectionEntryFieldAt,
      closedConnectionEntryOutputConnectionFieldAt] using
      closedConnectionEntry_extDerivFun_eq_iterated_add_output
        (g := g) (x := x)
        (v := g.leviCivita (extend E a) x v)
        (u := u) (z := z) (q := q)
  unfold closedSecondDirectionalEntryAt
  change extDerivFun F x v
      - extDerivFun (closedConnectionEntryFieldAt g u z q) x
        (g.leviCivita (extend E a) x v) =
    extDerivFun A x v + extDerivFun B x v
      - (closedIteratedConnectionEntryFieldAt g u z x
          (g.leviCivita (extend E a) x v) q
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E a) x v) u z q x)
  calc
    extDerivFun F x v
        - extDerivFun (closedConnectionEntryFieldAt g u z q) x
          (g.leviCivita (extend E a) x v)
        =
      extDerivFun (fun y : M ↦ A y + B y) x v
        - extDerivFun (closedConnectionEntryFieldAt g u z q) x
          (g.leviCivita (extend E a) x v) := by rw [hderiv]
    _ =
      (extDerivFun A x v + extDerivFun B x v)
        - extDerivFun (closedConnectionEntryFieldAt g u z q) x
          (g.leviCivita (extend E a) x v) := by rw [hsplit]
    _ =
      extDerivFun A x v + extDerivFun B x v
        - (closedIteratedConnectionEntryFieldAt g u z x
            (g.leviCivita (extend E a) x v) q
          + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E a) x v) u z q x) := by
      rw [hcorr]

/--
One curvature defining expansion rewritten through the raw corrected
second-directional connection-entry block.  The remaining terms are exactly
the output-slot and bracket residue that the cyclic group-2/3 bookkeeping must
cancel.
-/
theorem closedCurvatureDefExpansionAt_eq_secondDirectional_residue
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u z q : TM x) :
    closedCurvatureDefExpansionAt g x v a u z q =
      closedSecondDirectionalEntryAt g
          (closedConnectionEntryFieldAt g u z q) x v a
        - closedSecondDirectionalEntryAt g
          (closedConnectionEntryFieldAt g a z q) x v u
        - extDerivFun
          (fun y : M ↦
            closedBracketConnectionEntryFieldAt g a u z y
              (extend E q y)) x v
        - extDerivFun
          (closedConnectionEntryOutputConnectionFieldAt g a u z q) x v
        + extDerivFun
          (closedConnectionEntryOutputConnectionFieldAt g u a z q) x v
        + closedIteratedConnectionEntryFieldAt g u z x
          (g.leviCivita (extend E a) x v) q
        - closedIteratedConnectionEntryFieldAt g a z x
          (g.leviCivita (extend E u) x v) q
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E a) x v) u z q x
        - closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E u) x v) a z q x := by
  rw [closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := v) (a := a) (u := u) (z := z) (q := q),
    closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := v) (a := u) (u := a) (z := z) (q := q)]
  unfold closedCurvatureDefExpansionAt covTensor2DerivAt
    closedBracketConnectionEntryDerivAt
  ring

/--
The non-Schwarz residue in one differentiated curvature defining expansion
after extracting the raw corrected second-directional connection-entry pair.
-/
noncomputable def closedCurvatureDefExpansionResidueAt
    (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (v a u z q : TM x) : ℝ :=
  - extDerivFun
      (fun y : M ↦
        closedBracketConnectionEntryFieldAt g a u z y
          (extend E q y)) x v
    - extDerivFun
      (closedConnectionEntryOutputConnectionFieldAt g a u z q) x v
    + extDerivFun
      (closedConnectionEntryOutputConnectionFieldAt g u a z q) x v
    + closedIteratedConnectionEntryFieldAt g u z x
      (g.leviCivita (extend E a) x v) q
    - closedIteratedConnectionEntryFieldAt g a z x
      (g.leviCivita (extend E u) x v) q
    + closedConnectionEntryOutputConnectionFieldAt g
      (g.leviCivita (extend E a) x v) u z q x
    - closedConnectionEntryOutputConnectionFieldAt g
      (g.leviCivita (extend E u) x v) a z q x

theorem closedCurvatureDefExpansionAt_eq_secondDirectional_add_residue
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u z q : TM x) :
    closedCurvatureDefExpansionAt g x v a u z q =
      closedSecondDirectionalEntryAt g
          (closedConnectionEntryFieldAt g u z q) x v a
        - closedSecondDirectionalEntryAt g
          (closedConnectionEntryFieldAt g a z q) x v u
        + closedCurvatureDefExpansionResidueAt g x v a u z q := by
  rw [closedCurvatureDefExpansionAt_eq_secondDirectional_residue
      (g := g) (x := x) (v := v) (a := a) (u := u) (z := z) (q := q)]
  unfold closedCurvatureDefExpansionResidueAt
  ring

/-- Closed Schwarz symmetry for corrected scalar second directional entries. -/
theorem closedSecondDirectionalEntryAt_comm
    (g : ClosedSmoothRiemannianMetric n M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (u v : TM x) :
    closedSecondDirectionalEntryAt g f x v u =
      closedSecondDirectionalEntryAt g f x u v := by
  simpa [closedSecondDirectionalEntryAt] using
    (extDerivFun_extDerivFun_extend_corrected_symm
      (g := g) (f := f) (x := x) hf u v).symm

/-- Closed Schwarz symmetry for scalar connection entries `g(∇_w z, q)`. -/
theorem closedConnectionEntry_secondDirectional_comm
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (w z q u v : TM x) :
    closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g w z q) x v u =
      closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g w z q) x u v :=
  closedSecondDirectionalEntryAt_comm (g := g)
    (closedConnectionEntry_contMDiffAt_two (g := g) w z q) u v

/--
The three raw mixed second-connection scalar-entry pairs in the cyclic
second-Bianchi expansion cancel by closed Schwarz symmetry.
-/
theorem closedConnectionEntry_mixed_second_cyclic_cancel
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g w z q) x v u
      - closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g w z q) x u v
      + closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g v z q) x u w
      - closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g v z q) x w u
      + closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g u z q) x w v
      - closedSecondDirectionalEntryAt g (closedConnectionEntryFieldAt g u z q) x v w = 0 := by
  rw [closedConnectionEntry_secondDirectional_comm
      (g := g) (w := w) (z := z) (q := q) (u := u) (v := v),
    closedConnectionEntry_secondDirectional_comm
      (g := g) (w := v) (z := z) (q := q) (u := w) (v := u),
    closedConnectionEntry_secondDirectional_comm
      (g := g) (w := u) (z := z) (q := q) (u := v) (v := w)]
  ring

/--
Group-1 wiring for the cyclic differentiated curvature defining expansion:
after the raw mixed-second derivatives cancel, only the three explicit
residue blocks remain.
-/
theorem closedCurvatureDefExpansionAt_cyclic_eq_residue_cyclic
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    closedCurvatureDefExpansionAt g x v u w z q
      + closedCurvatureDefExpansionAt g x u w v z q
      + closedCurvatureDefExpansionAt g x w v u z q =
        closedCurvatureDefExpansionResidueAt g x v u w z q
          + closedCurvatureDefExpansionResidueAt g x u w v z q
          + closedCurvatureDefExpansionResidueAt g x w v u z q := by
  rw [closedCurvatureDefExpansionAt_eq_secondDirectional_add_residue
      (g := g) (x := x) (v := v) (a := u) (u := w) (z := z) (q := q),
    closedCurvatureDefExpansionAt_eq_secondDirectional_add_residue
      (g := g) (x := x) (v := u) (a := w) (u := v) (z := z) (q := q),
    closedCurvatureDefExpansionAt_eq_secondDirectional_add_residue
      (g := g) (x := x) (v := w) (a := v) (u := u) (z := z) (q := q)]
  have hraw :=
    closedConnectionEntry_mixed_second_cyclic_cancel
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  linarith

/--
After group-1 wiring, the displayed scalar cancellation is reduced exactly to
the cyclic residue block minus the cyclic curvature-slot correction block.
-/
theorem closedCurvatureDefExpansionAt_cyclic_sub_corrections_eq_residue_sub_corrections
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    closedCurvatureDefExpansionAt g x v u w z q
      + closedCurvatureDefExpansionAt g x u w v z q
      + closedCurvatureDefExpansionAt g x w v u z q
      - (closedCurvatureCovDerivAtCorrectionAt g x v u w z q
        + closedCurvatureCovDerivAtCorrectionAt g x u w v z q
        + closedCurvatureCovDerivAtCorrectionAt g x w v u z q)
      =
        closedCurvatureDefExpansionResidueAt g x v u w z q
          + closedCurvatureDefExpansionResidueAt g x u w v z q
          + closedCurvatureDefExpansionResidueAt g x w v u z q
          - (closedCurvatureCovDerivAtCorrectionAt g x v u w z q
            + closedCurvatureCovDerivAtCorrectionAt g x u w v z q
            + closedCurvatureCovDerivAtCorrectionAt g x w v u z q) := by
  rw [closedCurvatureDefExpansionAt_cyclic_eq_residue_cyclic
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)]

/--
Torsion-free alignment for the bracket connection entry:
`∇_[a,u] w` is the difference of the two connection-slot products coming
from `∇_a u - ∇_u a`.
-/
theorem closedBracketConnectionEntryFieldAt_eq_connectionEntry_sub
    (g : ClosedSmoothRiemannianMetric n M) {x : M} (a u w q : TM x) :
    closedBracketConnectionEntryFieldAt g a u w x q =
      closedConnectionEntryFieldAt g (g.leviCivita (extend E u) x a) w q x
        - closedConnectionEntryFieldAt g (g.leviCivita (extend E a) x u) w q x := by
  have hbr :
      g.leviCivita (extend E u) x a - g.leviCivita (extend E a) x u =
        VectorField.mlieBracket I (extend E a) (extend E u) x := by
    have htf := g.leviCivita_torsionFreeAt x
      (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E a))
      (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E u))
    rwa [extend_apply_self, extend_apply_self] at htf
  unfold closedBracketConnectionEntryFieldAt closedConnectionEntryFieldAt
  rw [← hbr]
  simp [map_sub]

/--
The same torsion-free bracket alignment in the output connection slot used by
`closedCurvatureDefExpansionAt`.
-/
theorem closedBracketConnectionEntryFieldAt_outputConnection_eq_connectionEntry_sub
    (g : ClosedSmoothRiemannianMetric n M) {x : M} (v a u w q : TM x) :
    closedBracketConnectionEntryFieldAt g a u w x
        (g.leviCivita (extend E q) x v) =
      closedConnectionEntryFieldAt g (g.leviCivita (extend E u) x a) w
          (g.leviCivita (extend E q) x v) x
        - closedConnectionEntryFieldAt g (g.leviCivita (extend E a) x u) w
          (g.leviCivita (extend E q) x v) x := by
  simpa using
    closedBracketConnectionEntryFieldAt_eq_connectionEntry_sub
      (g := g) (a := a) (u := u) (w := w)
      (q := g.leviCivita (extend E q) x v)

/--
Cyclic form of the output-slot bracket block after the torsion-free
alignment.  This is the bracket part of the group-2 bookkeeping in the
cyclic second-Bianchi expansion.
-/
theorem closedBracketConnectionEntryFieldAt_cyclic_outputConnection_eq_connectionEntry_sub
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (u v w z q : TM x) :
    closedBracketConnectionEntryFieldAt g u w z x (g.leviCivita (extend E q) x v)
      + closedBracketConnectionEntryFieldAt g w v z x (g.leviCivita (extend E q) x u)
      + closedBracketConnectionEntryFieldAt g v u z x (g.leviCivita (extend E q) x w) =
        (closedConnectionEntryFieldAt g (g.leviCivita (extend E w) x u) z
            (g.leviCivita (extend E q) x v) x
          - closedConnectionEntryFieldAt g (g.leviCivita (extend E u) x w) z
            (g.leviCivita (extend E q) x v) x)
        + (closedConnectionEntryFieldAt g (g.leviCivita (extend E v) x w) z
            (g.leviCivita (extend E q) x u) x
          - closedConnectionEntryFieldAt g (g.leviCivita (extend E w) x v) z
            (g.leviCivita (extend E q) x u) x)
        + (closedConnectionEntryFieldAt g (g.leviCivita (extend E u) x v) z
            (g.leviCivita (extend E q) x w) x
          - closedConnectionEntryFieldAt g (g.leviCivita (extend E v) x u) z
            (g.leviCivita (extend E q) x w) x) := by
  rw [closedBracketConnectionEntryFieldAt_outputConnection_eq_connectionEntry_sub
      (g := g) (x := x) (v := v) (a := u) (u := w) (w := z) (q := q),
    closedBracketConnectionEntryFieldAt_outputConnection_eq_connectionEntry_sub
      (g := g) (x := x) (v := u) (a := w) (u := v) (w := z) (q := q),
    closedBracketConnectionEntryFieldAt_outputConnection_eq_connectionEntry_sub
      (g := g) (x := x) (v := w) (a := v) (u := u) (w := z) (q := q)]

set_option maxHeartbeats 5000000 in
/--
Route-2 product-rule bridge for the cyclic output-connection derivative block.
It is the raw mixed-second Schwarz cancellation expanded through
`closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output`.
-/
theorem closedConnectionEntryOutputConnection_extDerivFun_cyclic_eq_covTensor2DerivAt_cyclic
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u w z q) x v
      + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w u z q) x v
      - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w v z q) x u
      + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v w z q) x u
      - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v u z q) x w
      + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u v z q) x w =
        covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g w z) x v u q
        - covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g w z) x u v q
        + covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g v z) x u w q
        - covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g v z) x w u q
        + covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g u z) x w v q
        - covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g u z) x v w q
        + closedIteratedConnectionEntryFieldAt g w z x u
          (g.leviCivita (extend E q) x v)
        - closedIteratedConnectionEntryFieldAt g w z x v
          (g.leviCivita (extend E q) x u)
        + closedIteratedConnectionEntryFieldAt g v z x w
          (g.leviCivita (extend E q) x u)
        - closedIteratedConnectionEntryFieldAt g v z x u
          (g.leviCivita (extend E q) x w)
        + closedIteratedConnectionEntryFieldAt g u z x v
          (g.leviCivita (extend E q) x w)
        - closedIteratedConnectionEntryFieldAt g u z x w
          (g.leviCivita (extend E q) x v)
        - closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E u) x v) w z q x
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E v) x u) w z q x
        - closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E w) x u) v z q x
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E u) x w) v z q x
        - closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E v) x w) u z q x
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E w) x v) u z q x := by
  have hraw :=
    closedConnectionEntry_mixed_second_cyclic_cancel
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  rw [closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := v) (a := u) (u := w) (z := z) (q := q),
    closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := u) (a := v) (u := w) (z := z) (q := q),
    closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := u) (a := w) (u := v) (z := z) (q := q),
    closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := w) (a := u) (u := v) (z := z) (q := q),
    closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := w) (a := v) (u := u) (z := z) (q := q),
    closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
      (g := g) (x := x) (v := v) (a := w) (u := u) (z := z) (q := q)] at hraw
  rw [closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := v) (a := u) (u := w) (w := z) (q := q),
    closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := u) (a := v) (u := w) (w := z) (q := q),
    closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := u) (a := w) (u := v) (w := z) (q := q),
    closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := w) (a := u) (u := v) (w := z) (q := q),
    closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := w) (a := v) (u := u) (w := z) (q := q),
    closedIteratedConnectionEntry_extDerivFun_eq
      (g := g) (x := x) (v := v) (a := w) (u := u) (w := z) (q := q)] at hraw
  linarith

/-- Cyclic covariant derivative block for the iterated connection-entry field. -/
noncomputable def closedIteratedConnectionEntryCovDerivCyclicAt
    (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (u v w z q : TM x) : ℝ :=
  covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g w z) x v u q
    - covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g w z) x u v q
    + covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g v z) x u w q
    - covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g v z) x w u q
    + covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g u z) x w v q
    - covTensor2DerivAt g (closedIteratedConnectionEntryFieldAt g u z) x v w q

theorem closedConnectionEntryOutputConnection_extDerivFun_cyclic_eq_packaged
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u w z q) x v
      + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w u z q) x v
      - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w v z q) x u
      + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v w z q) x u
      - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v u z q) x w
      + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u v z q) x w =
        closedIteratedConnectionEntryCovDerivCyclicAt g x u v w z q
        + closedIteratedConnectionEntryFieldAt g w z x u
          (g.leviCivita (extend E q) x v)
        - closedIteratedConnectionEntryFieldAt g w z x v
          (g.leviCivita (extend E q) x u)
        + closedIteratedConnectionEntryFieldAt g v z x w
          (g.leviCivita (extend E q) x u)
        - closedIteratedConnectionEntryFieldAt g v z x u
          (g.leviCivita (extend E q) x w)
        + closedIteratedConnectionEntryFieldAt g u z x v
          (g.leviCivita (extend E q) x w)
        - closedIteratedConnectionEntryFieldAt g u z x w
          (g.leviCivita (extend E q) x v)
        - closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E u) x v) w z q x
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E v) x u) w z q x
        - closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E w) x u) v z q x
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E u) x w) v z q x
        - closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E v) x w) u z q x
        + closedConnectionEntryOutputConnectionFieldAt g
          (g.leviCivita (extend E w) x v) u z q x := by
  simpa [closedIteratedConnectionEntryCovDerivCyclicAt] using
    closedConnectionEntryOutputConnection_extDerivFun_cyclic_eq_covTensor2DerivAt_cyclic
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)

theorem closedLeviCivita_extend_symm_at
    (g : ClosedSmoothRiemannianMetric n M) {x : M} (u v : TM x) :
    g.leviCivita (extend E u) x v =
      g.leviCivita (extend E v) x u := by
  have htf := g.leviCivita_torsionFreeAt x
    (X := extend E u) (Y := extend E v)
    (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E u))
    (by simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E v))
  have hbr := mlieBracket_extend_extend_apply_self (n := n) (M := M)
    (x := x) u v
  rw [extend_apply_self, extend_apply_self, hbr] at htf
  exact (sub_eq_zero.mp htf).symm

/--
Canonical-extension curvature bridge: antisymmetrizing the derivative of the
slot connection field gives the closed curvature operator.  The bracket term
in the definition of `curvatureOp` vanishes at the base point for canonical
extensions.
-/
theorem closedChristoffel_antisymm_deriv_eq_curvature
    (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (u v p : TM x) :
    g.leviCivita (fun y : M ↦ g.leviCivita (extend E p) y (extend E v y)) x u
        - g.leviCivita (fun y : M ↦ g.leviCivita (extend E p) y (extend E u y)) x v =
      CovariantDerivative.curvatureOp g.leviCivita
        (extend E u) (extend E v) (extend E p) x := by
  rw [CovariantDerivative.curvatureOp_apply]
  have hbr : VectorField.mlieBracket I (extend E u) (extend E v) x = 0 :=
    mlieBracket_extend_extend_apply_self (n := n) (M := M) (x := x) u v
  simp [extend_apply_self, hbr]

theorem closedConnectionEntryOutputConnection_extDerivFun_eq_iterated_pair
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (v a u z q : TM x) :
    extDerivFun (closedConnectionEntryOutputConnectionFieldAt g a u z q) x v =
      closedIteratedConnectionEntryFieldAt g u z x v
        (g.leviCivita (extend E q) x a)
      + closedIteratedConnectionEntryFieldAt g a q x v
        (g.leviCivita (extend E z) x u) := by
  let A : Π y : M, TM y :=
    fun y ↦ g.leviCivita (extend E z) y (extend E u y)
  let B : Π y : M, TM y :=
    fun y ↦ g.leviCivita (extend E q) y (extend E a y)
  have hU :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (extend E u)) x := by
    simpa using (mdifferentiableAt_extend I E u)
  have hAsec : MDiffAtTangentField A x := by
    have hZ2 :
        ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
          (T% (extend E z)) x := by
      simpa using (FiberBundle.contMDiffAt_extend' (k := 2) I E z)
    simpa [MDiffAtTangentField, A] using
      (CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
        (cov := g.leviCivita) hZ2 hU)
  have hAext :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (extend E a)) x := by
    simpa using (mdifferentiableAt_extend I E a)
  have hBsec : MDiffAtTangentField B x := by
    have hQ2 :
        ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
          (T% (extend E q)) x := by
      simpa using (FiberBundle.contMDiffAt_extend' (k := 2) I E q)
    simpa [MDiffAtTangentField, B] using
      (CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
        (cov := g.leviCivita) hQ2 hAext)
  have hcompat := g.leviCivita_metricCompatibleAt x hAsec hBsec v
  have hsym :
      g.inner x (A x) (g.leviCivita B x v) =
        g.inner x (g.leviCivita B x v) (A x) :=
    g.inner_symm x _ _
  change
    (extDerivFun (fun y : M => g.inner y (A y) (B y)) x) v =
      closedIteratedConnectionEntryFieldAt g u z x v
        (g.leviCivita (extend E q) x a)
      + closedIteratedConnectionEntryFieldAt g a q x v
        (g.leviCivita (extend E z) x u)
  rw [hcompat, hsym]
  simp [closedIteratedConnectionEntryFieldAt, A, B, extend_apply_self]

theorem closedCurvaturePairSymmAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (a b c d : TM x) :
    g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E b) (extend E c) x) d =
      g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E c) (extend E d) (extend E a) x) b := by
  exact CovariantDerivative.curvature_pair_symm
    (cov := g.leviCivita) (g := g.inner)
    (fun y ↦ g.leviCivita_torsionFreeAt y)
    (fun y ↦ g.leviCivita_metricCompatibleAt y)
    (fun v w ↦ g.inner_symm x v w)
    (fun A B hA hB ↦ g.metric_pairing_contMDiffAt_two hA hB)
    (fun A B hA hB ↦ g.metric_pairing_mdiffAt hA hB)
    a b c d

theorem closedCurvaturePairLastPairAntisymmAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (a b c d : TM x) :
    g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E b) (extend E c) x) d =
      -g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E b) (extend E d) x) c := by
  rw [closedCurvaturePairSymmAt (g := g) (x := x) a b c d,
    closedCurvaturePairSymmAt (g := g) (x := x) a b d c]
  rw [CovariantDerivative.curvatureOp_antisymm_apply]
  simp

theorem closedCurvaturePairSwapAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (a b c d : TM x) :
    g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E b) (extend E c) x) d =
      g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E b) (extend E a) (extend E d) x) c := by
  rw [closedCurvaturePairLastPairAntisymmAt
      (g := g) (x := x) a b c d]
  rw [CovariantDerivative.curvatureOp_antisymm_apply]
  simp

theorem closedCurvatureEntryAt_eq_iteratedConnectionEntry_sub
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (a u w q : TM x) :
    g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) x) q =
      closedIteratedConnectionEntryFieldAt g u w x a q
        - closedIteratedConnectionEntryFieldAt g a w x u q := by
  have h :=
    (curvature_def_eventually (g := g) (x := x) a u w q).self_of_nhds
  have hb := closedBracketConnectionEntryFieldAt_apply_self_eq_zero
    (g := g) (x := x) a u w q
  simpa [extend_apply_self, hb] using h

set_option maxHeartbeats 5000000 in
theorem closedIteratedConnectionEntry_output_q_cyclic_eq_middle_z_cyclic
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    - closedIteratedConnectionEntryFieldAt g u q x v
        (g.leviCivita (extend E z) x w)
      + closedIteratedConnectionEntryFieldAt g w q x v
        (g.leviCivita (extend E z) x u)
      - closedIteratedConnectionEntryFieldAt g w q x u
        (g.leviCivita (extend E z) x v)
      + closedIteratedConnectionEntryFieldAt g v q x u
        (g.leviCivita (extend E z) x w)
      - closedIteratedConnectionEntryFieldAt g v q x w
        (g.leviCivita (extend E z) x u)
      + closedIteratedConnectionEntryFieldAt g u q x w
        (g.leviCivita (extend E z) x v) =
        closedIteratedConnectionEntryFieldAt g w
          (g.leviCivita (extend E z) x v) x u q
        - closedIteratedConnectionEntryFieldAt g u
          (g.leviCivita (extend E z) x v) x w q
        + closedIteratedConnectionEntryFieldAt g v
          (g.leviCivita (extend E z) x u) x w q
        - closedIteratedConnectionEntryFieldAt g w
          (g.leviCivita (extend E z) x u) x v q
        + closedIteratedConnectionEntryFieldAt g u
          (g.leviCivita (extend E z) x w) x v q
        - closedIteratedConnectionEntryFieldAt g v
          (g.leviCivita (extend E z) x w) x u q := by
  let Γzu : TM x := g.leviCivita (extend E z) x u
  let Γzv : TM x := g.leviCivita (extend E z) x v
  let Γzw : TM x := g.leviCivita (extend E z) x w
  have hE_u := closedCurvatureEntryAt_eq_iteratedConnectionEntry_sub
    (g := g) (x := x) (a := v) (u := w) (w := q) (q := Γzu)
  have hM_u := closedCurvatureEntryAt_eq_iteratedConnectionEntry_sub
    (g := g) (x := x) (a := w) (u := v) (w := Γzu) (q := q)
  have hswap_u := closedCurvaturePairSwapAt
    (g := g) (x := x) (a := v) (b := w) (c := q) (d := Γzu)
  have hu :
      closedIteratedConnectionEntryFieldAt g w q x v Γzu
        - closedIteratedConnectionEntryFieldAt g v q x w Γzu =
      closedIteratedConnectionEntryFieldAt g v Γzu x w q
        - closedIteratedConnectionEntryFieldAt g w Γzu x v q := by
    linarith
  have hE_w := closedCurvatureEntryAt_eq_iteratedConnectionEntry_sub
    (g := g) (x := x) (a := u) (u := v) (w := q) (q := Γzw)
  have hM_w := closedCurvatureEntryAt_eq_iteratedConnectionEntry_sub
    (g := g) (x := x) (a := v) (u := u) (w := Γzw) (q := q)
  have hswap_w := closedCurvaturePairSwapAt
    (g := g) (x := x) (a := u) (b := v) (c := q) (d := Γzw)
  have hw :
      closedIteratedConnectionEntryFieldAt g v q x u Γzw
        - closedIteratedConnectionEntryFieldAt g u q x v Γzw =
      closedIteratedConnectionEntryFieldAt g u Γzw x v q
        - closedIteratedConnectionEntryFieldAt g v Γzw x u q := by
    linarith
  have hE_v := closedCurvatureEntryAt_eq_iteratedConnectionEntry_sub
    (g := g) (x := x) (a := w) (u := u) (w := q) (q := Γzv)
  have hM_v := closedCurvatureEntryAt_eq_iteratedConnectionEntry_sub
    (g := g) (x := x) (a := u) (u := w) (w := Γzv) (q := q)
  have hswap_v := closedCurvaturePairSwapAt
    (g := g) (x := x) (a := w) (b := u) (c := q) (d := Γzv)
  have hv :
      closedIteratedConnectionEntryFieldAt g u q x w Γzv
        - closedIteratedConnectionEntryFieldAt g w q x u Γzv =
      closedIteratedConnectionEntryFieldAt g w Γzv x u q
        - closedIteratedConnectionEntryFieldAt g u Γzv x w q := by
    linarith
  change
    -closedIteratedConnectionEntryFieldAt g u q x v Γzw
      + closedIteratedConnectionEntryFieldAt g w q x v Γzu
      - closedIteratedConnectionEntryFieldAt g w q x u Γzv
      + closedIteratedConnectionEntryFieldAt g v q x u Γzw
      - closedIteratedConnectionEntryFieldAt g v q x w Γzu
      + closedIteratedConnectionEntryFieldAt g u q x w Γzv =
        closedIteratedConnectionEntryFieldAt g w Γzv x u q
        - closedIteratedConnectionEntryFieldAt g u Γzv x w q
        + closedIteratedConnectionEntryFieldAt g v Γzu x w q
        - closedIteratedConnectionEntryFieldAt g w Γzu x v q
        + closedIteratedConnectionEntryFieldAt g u Γzw x v q
        - closedIteratedConnectionEntryFieldAt g v Γzw x u q
  linarith

set_option maxHeartbeats 5000000 in
theorem closedIteratedConnectionEntryCovDerivCyclicAt_eq_correction_iterated_cyclic
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    closedIteratedConnectionEntryCovDerivCyclicAt g x u v w z q =
      - closedIteratedConnectionEntryFieldAt g
        (g.leviCivita (extend E u) x v) z x w q
      + closedIteratedConnectionEntryFieldAt g
        (g.leviCivita (extend E w) x v) z x u q
      + closedIteratedConnectionEntryFieldAt g w
        (g.leviCivita (extend E z) x v) x u q
      - closedIteratedConnectionEntryFieldAt g u
        (g.leviCivita (extend E z) x v) x w q
      - closedIteratedConnectionEntryFieldAt g
        (g.leviCivita (extend E w) x u) z x v q
      + closedIteratedConnectionEntryFieldAt g
        (g.leviCivita (extend E v) x u) z x w q
      + closedIteratedConnectionEntryFieldAt g v
        (g.leviCivita (extend E z) x u) x w q
      - closedIteratedConnectionEntryFieldAt g w
        (g.leviCivita (extend E z) x u) x v q
      - closedIteratedConnectionEntryFieldAt g
        (g.leviCivita (extend E v) x w) z x u q
      + closedIteratedConnectionEntryFieldAt g
        (g.leviCivita (extend E u) x w) z x v q
      + closedIteratedConnectionEntryFieldAt g u
        (g.leviCivita (extend E z) x w) x v q
      - closedIteratedConnectionEntryFieldAt g v
        (g.leviCivita (extend E z) x w) x u q := by
  have hout :=
    closedConnectionEntryOutputConnection_extDerivFun_cyclic_eq_packaged
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  rw [closedConnectionEntryOutputConnection_extDerivFun_eq_iterated_pair
      (g := g) (x := x) (v := v) (a := u) (u := w) (z := z) (q := q),
    closedConnectionEntryOutputConnection_extDerivFun_eq_iterated_pair
      (g := g) (x := x) (v := v) (a := w) (u := u) (z := z) (q := q),
    closedConnectionEntryOutputConnection_extDerivFun_eq_iterated_pair
      (g := g) (x := x) (v := u) (a := w) (u := v) (z := z) (q := q),
    closedConnectionEntryOutputConnection_extDerivFun_eq_iterated_pair
      (g := g) (x := x) (v := u) (a := v) (u := w) (z := z) (q := q),
    closedConnectionEntryOutputConnection_extDerivFun_eq_iterated_pair
      (g := g) (x := x) (v := w) (a := v) (u := u) (z := z) (q := q),
    closedConnectionEntryOutputConnection_extDerivFun_eq_iterated_pair
      (g := g) (x := x) (v := w) (a := u) (u := v) (z := z) (q := q)] at hout
  have hpair :=
    closedIteratedConnectionEntry_output_q_cyclic_eq_middle_z_cyclic
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  have huv := closedLeviCivita_extend_symm_at (g := g) (x := x) u v
  have huw := closedLeviCivita_extend_symm_at (g := g) (x := x) u w
  have hvw := closedLeviCivita_extend_symm_at (g := g) (x := x) v w
  rw [huv, huw, hvw] at hout ⊢
  ring_nf at hout hpair ⊢
  linarith

set_option maxHeartbeats 5000000 in
theorem closedCurvatureDefExpansionResidueAt_cyclic_eq_correction_cyclic
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    closedCurvatureDefExpansionResidueAt g x v u w z q
      + closedCurvatureDefExpansionResidueAt g x u w v z q
      + closedCurvatureDefExpansionResidueAt g x w v u z q =
        closedCurvatureCovDerivAtCorrectionAt g x v u w z q
          + closedCurvatureCovDerivAtCorrectionAt g x u w v z q
          + closedCurvatureCovDerivAtCorrectionAt g x w v u z q := by
  have hout :=
    closedConnectionEntryOutputConnection_extDerivFun_cyclic_eq_packaged
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  have hcov :=
    closedIteratedConnectionEntryCovDerivCyclicAt_eq_correction_iterated_cyclic
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  rw [closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms
      (g := g) (x := x) (v := v) (a := u) (u := w) (z := z) (q := q),
    closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms
      (g := g) (x := x) (v := u) (a := w) (u := v) (z := z) (q := q),
    closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms
      (g := g) (x := x) (v := w) (a := v) (u := u) (z := z) (q := q)]
  unfold closedCurvatureDefExpansionResidueAt
  rw [closedBracketConnectionEntryFieldAt_extend_extDerivFun_eq_zero
      (g := g) (x := x) (v := v) (a := u) (u := w) (w := z) (q := q),
    closedBracketConnectionEntryFieldAt_extend_extDerivFun_eq_zero
      (g := g) (x := x) (v := u) (a := w) (u := v) (w := z) (q := q),
    closedBracketConnectionEntryFieldAt_extend_extDerivFun_eq_zero
      (g := g) (x := x) (v := w) (a := v) (u := u) (w := z) (q := q)]
  repeat rw [closedBracketConnectionEntryFieldAt_apply_self_eq_zero]
  ring_nf at hout hcov ⊢
  linarith

set_option maxHeartbeats 5000000 in
theorem closedCurvatureCovDerivAt_cyclic_inner_eq_zero
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v u w z) q
      + g.inner x (closedCurvatureCovDerivAt g x u w v z) q
      + g.inner x (closedCurvatureCovDerivAt g x w v u z) q = 0 := by
  rw [closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)]
  have hsub :=
    closedCurvatureDefExpansionAt_cyclic_sub_corrections_eq_residue_sub_corrections
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  have hres :=
    closedCurvatureDefExpansionResidueAt_cyclic_eq_correction_cyclic
      (g := g) (x := x) (u := u) (v := v) (w := w) (z := z) (q := q)
  linarith

theorem eventually_closed_cyclic_second_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    ∀ᶠ y in nhds x, ∀ u v w z : TM y,
      closedCurvatureCovDerivAt g y v u w z
        + closedCurvatureCovDerivAt g y u w v z
        + closedCurvatureCovDerivAt g y w v u z = 0 := by
  refine eventually_closed_cyclic_second_bianchi_of_inner_sum
    (g := g) (x := x) ?_
  exact Filter.Eventually.of_forall fun y u v w z q =>
    closedCurvatureCovDerivAt_cyclic_inner_eq_zero
      (g := g) (x := y) (u := u) (v := v) (w := w) (z := z) (q := q)

theorem closedCurvatureEntry_pair_symm_eventually
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (a u w q : TM x) :
    (fun y : M ↦
      g.inner y
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) y)
        (extend E q y)) =ᶠ[nhds x]
    (fun y : M ↦
      g.inner y
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E q) (extend E a) y)
        (extend E u y)) := by
  have hA := eventually_contMDiffAt_two_extend (n := n) (M := M) a
  have hU := eventually_contMDiffAt_two_extend (n := n) (M := M) u
  have hW := eventually_contMDiffAt_two_extend (n := n) (M := M) w
  have hQ := eventually_contMDiffAt_two_extend (n := n) (M := M) q
  filter_upwards [hA, hU, hW, hQ] with y hA2 hU2 hW2 hQ2
  let ay : TM y := extend E a y
  let uy : TM y := extend E u y
  let wy : TM y := extend E w y
  let qy : TM y := extend E q y
  have hLthird :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E wy) y := by
    exact CovariantDerivative.curvatureOp_congr_of_value_eq
      (cov := g.leviCivita)
      (Z := extend E w) (Z' := extend E wy)
      (X := extend E a) (Y := extend E u)
      hW2
      (FiberBundle.contMDiffAt_extend' (k := 2) I E wy)
      (by simp [wy])
      (hA2.mdifferentiableAt two_ne_zero)
      (hU2.mdifferentiableAt two_ne_zero)
  have hLfirst :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E wy) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E ay) (extend E u) (extend E wy) y := by
    refine curvatureOp_congr_fst_of_value_eq
      (cov := g.leviCivita) (x := y)
      (Y := extend E u) (Z := extend E wy)
      (CovariantDerivative.derivRegularAt_extend g.leviCivita wy)
      ?_ ?_ ?_ ?_
    · simpa [MDiffAtTangentField] using hA2.mdifferentiableAt two_ne_zero
    · simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E ay)
    · simpa [MDiffAtTangentField] using hU2.mdifferentiableAt two_ne_zero
    · simp [ay]
  have hLsecond :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E ay) (extend E u) (extend E wy) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E ay) (extend E uy) (extend E wy) y := by
    refine curvatureOp_congr_snd_of_value_eq
      (cov := g.leviCivita) (x := y)
      (X := extend E ay) (Z := extend E wy)
      (CovariantDerivative.derivRegularAt_extend g.leviCivita wy)
      ?_ ?_ ?_ ?_
    · simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E ay)
    · simpa [MDiffAtTangentField] using hU2.mdifferentiableAt two_ne_zero
    · simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E uy)
    · simp [uy]
  have hL :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E ay) (extend E uy) (extend E wy) y := by
    rw [hLthird, hLfirst, hLsecond]
  have hRthird :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E q) (extend E a) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E q) (extend E ay) y := by
    exact CovariantDerivative.curvatureOp_congr_of_value_eq
      (cov := g.leviCivita)
      (Z := extend E a) (Z' := extend E ay)
      (X := extend E w) (Y := extend E q)
      hA2
      (FiberBundle.contMDiffAt_extend' (k := 2) I E ay)
      (by simp [ay])
      (hW2.mdifferentiableAt two_ne_zero)
      (hQ2.mdifferentiableAt two_ne_zero)
  have hRfirst :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E q) (extend E ay) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E wy) (extend E q) (extend E ay) y := by
    refine curvatureOp_congr_fst_of_value_eq
      (cov := g.leviCivita) (x := y)
      (Y := extend E q) (Z := extend E ay)
      (CovariantDerivative.derivRegularAt_extend g.leviCivita ay)
      ?_ ?_ ?_ ?_
    · simpa [MDiffAtTangentField] using hW2.mdifferentiableAt two_ne_zero
    · simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E wy)
    · simpa [MDiffAtTangentField] using hQ2.mdifferentiableAt two_ne_zero
    · simp [wy]
  have hRsecond :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E wy) (extend E q) (extend E ay) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E wy) (extend E qy) (extend E ay) y := by
    refine curvatureOp_congr_snd_of_value_eq
      (cov := g.leviCivita) (x := y)
      (X := extend E wy) (Z := extend E ay)
      (CovariantDerivative.derivRegularAt_extend g.leviCivita ay)
      ?_ ?_ ?_ ?_
    · simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E wy)
    · simpa [MDiffAtTangentField] using hQ2.mdifferentiableAt two_ne_zero
    · simpa [MDiffAtTangentField] using (mdifferentiableAt_extend I E qy)
    · simp [qy]
  have hR :
      CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E q) (extend E a) y =
        CovariantDerivative.curvatureOp g.leviCivita
          (extend E wy) (extend E qy) (extend E ay) y := by
    rw [hRthird, hRfirst, hRsecond]
  have hpair := closedCurvaturePairSymmAt (g := g) (x := y) ay uy wy qy
  rw [hL, hR]
  simpa [ay, uy, wy, qy] using hpair

theorem closedCurvatureCovDerivAtCorrection_pair_symm
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    closedCurvatureCovDerivAtCorrectionAt g x v a u w q =
      closedCurvatureCovDerivAtCorrectionAt g x v w q a u := by
  let Γa : TM x := g.leviCivita (extend E a) x v
  let Γu : TM x := g.leviCivita (extend E u) x v
  let Γw : TM x := g.leviCivita (extend E w) x v
  let Γq : TM x := g.leviCivita (extend E q) x v
  have h1 := closedCurvaturePairSymmAt (g := g) (x := x) Γa u w q
  have h2 := closedCurvaturePairSymmAt (g := g) (x := x) a Γu w q
  have h3 := closedCurvaturePairSymmAt (g := g) (x := x) a u Γw q
  have h4 := closedCurvaturePairSymmAt (g := g) (x := x) a u w Γq
  unfold closedCurvatureCovDerivAtCorrectionAt
  change
    g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γa) (extend E u) (extend E w) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E Γu) (extend E w) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E Γw) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) x) Γq
      =
    g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γw) (extend E q) (extend E a) x) u
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E Γq) (extend E a) x) u
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E q) (extend E Γa) x) u
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E q) (extend E a) x) Γu
  rw [h1, h2, h3, h4]
  ring

theorem closedCurvatureCovDerivAt_pair_symm_inner
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v a u w) q =
      g.inner x (closedCurvatureCovDerivAt g x v w q a) u := by
  have hEntryEventual := closedCurvatureEntry_pair_symm_eventually
    (g := g) (x := x) a u w q
  have hEntry :
      closedCurvatureEntryDerivAt g x v a u w q =
        closedCurvatureEntryDerivAt g x v w q a u := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L v)
      (CovariantDerivative.extDerivFun_congr hEntryEventual)
  have hCorr := closedCurvatureCovDerivAtCorrection_pair_symm
    (g := g) (x := x) v a u w q
  rw [closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := v) (a := a) (u := u) (w := w) (q := q),
    closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := v) (a := w) (u := q) (w := a) (q := u),
    hEntry, hCorr]

theorem closedCurvatureEntryDerivAt_first_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    closedCurvatureEntryDerivAt g x v a u w q
      + closedCurvatureEntryDerivAt g x v u w a q
      + closedCurvatureEntryDerivAt g x v w a u q = 0 := by
  let f₁ : M → ℝ := fun y ↦
    g.inner y
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E a) (extend E u) (extend E w) y)
      (extend E q y)
  let f₂ : M → ℝ := fun y ↦
    g.inner y
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E u) (extend E w) (extend E a) y)
      (extend E q y)
  let f₃ : M → ℝ := fun y ↦
    g.inner y
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E w) (extend E a) (extend E u) y)
      (extend E q y)
  have hA := eventually_contMDiffAt_two_extend (n := n) (M := M) a
  have hU := eventually_contMDiffAt_two_extend (n := n) (M := M) u
  have hW := eventually_contMDiffAt_two_extend (n := n) (M := M) w
  have hsum : (fun y : M ↦ f₁ y + f₂ y + f₃ y) =ᶠ[nhds x]
      fun _ : M ↦ (0 : ℝ) := by
    filter_upwards [hA, hU, hW] with y hA2 hU2 hW2
    have hb := CovariantDerivative.bianchi_first_at
      (cov := g.leviCivita) (x := y)
      (fun y ↦ g.leviCivita_torsionFreeAt y)
      hA2 hU2 hW2
    have hp := congrArg (fun z : TM y ↦ g.inner y z (extend E q y)) hb
    simpa [f₁, f₂, f₃, map_add] using hp
  have hzero : extDerivFun (fun y : M ↦ f₁ y + f₂ y + f₃ y) x v = 0 := by
    rw [CovariantDerivative.extDerivFun_congr hsum]
    simp [extDerivFun_zero_at]
  have h₁ := (closedCurvatureEntryDerivativeBridgeAt_canonical g x).mdifferentiable a u w q
  have h₂ := (closedCurvatureEntryDerivativeBridgeAt_canonical g x).mdifferentiable u w a q
  have h₃ := (closedCurvatureEntryDerivativeBridgeAt_canonical g x).mdifferentiable w a u q
  unfold closedCurvatureEntryDerivAt
  change extDerivFun f₁ x v + extDerivFun f₂ x v + extDerivFun f₃ x v = 0
  have hadd12 := extDerivFun_add h₁ h₂
  have hadd123 := extDerivFun_add (h₁.add h₂) h₃
  have hsplit :
      extDerivFun (fun y : M ↦ f₁ y + f₂ y + f₃ y) x v =
        extDerivFun f₁ x v + extDerivFun f₂ x v + extDerivFun f₃ x v := by
    change (extDerivFun ((f₁ + f₂) + f₃) x) v =
      (extDerivFun f₁ x) v + (extDerivFun f₂ x) v + (extDerivFun f₃ x) v
    rw [hadd123, hadd12]
    rfl
  rw [← hsplit]
  exact hzero

theorem closedCurvatureCovDerivAtCorrection_cyclic_eq_zero
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    closedCurvatureCovDerivAtCorrectionAt g x v a u w q
      + closedCurvatureCovDerivAtCorrectionAt g x v u w a q
      + closedCurvatureCovDerivAtCorrectionAt g x v w a u q = 0 := by
  let Γa : TM x := g.leviCivita (extend E a) x v
  let Γu : TM x := g.leviCivita (extend E u) x v
  let Γw : TM x := g.leviCivita (extend E w) x v
  let Γq : TM x := g.leviCivita (extend E q) x v
  have hbΓa := CovariantDerivative.bianchi_first_at
    (cov := g.leviCivita) (x := x)
    (fun y ↦ g.leviCivita_torsionFreeAt y)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E Γa)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E u)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
  have hbΓu := CovariantDerivative.bianchi_first_at
    (cov := g.leviCivita) (x := x)
    (fun y ↦ g.leviCivita_torsionFreeAt y)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E a)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E Γu)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
  have hbΓw := CovariantDerivative.bianchi_first_at
    (cov := g.leviCivita) (x := x)
    (fun y ↦ g.leviCivita_torsionFreeAt y)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E a)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E u)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E Γw)
  have hbΓq := CovariantDerivative.bianchi_first_at
    (cov := g.leviCivita) (x := x)
    (fun y ↦ g.leviCivita_torsionFreeAt y)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E a)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E u)
    (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
  have hΓa :
      g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E Γa) (extend E u) (extend E w) x) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E u) (extend E w) (extend E Γa) x) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E w) (extend E Γa) (extend E u) x) q = 0 := by
    simpa [map_add] using congrArg (fun z : TM x ↦ g.inner x z q) hbΓa
  have hΓu :
      g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E a) (extend E Γu) (extend E w) x) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E Γu) (extend E w) (extend E a) x) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E w) (extend E a) (extend E Γu) x) q = 0 := by
    simpa [map_add] using congrArg (fun z : TM x ↦ g.inner x z q) hbΓu
  have hΓw :
      g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E a) (extend E u) (extend E Γw) x) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E u) (extend E Γw) (extend E a) x) q
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E Γw) (extend E a) (extend E u) x) q = 0 := by
    simpa [map_add] using congrArg (fun z : TM x ↦ g.inner x z q) hbΓw
  have hΓq :
      g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E a) (extend E u) (extend E w) x) Γq
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E u) (extend E w) (extend E a) x) Γq
        + g.inner x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E w) (extend E a) (extend E u) x) Γq = 0 := by
    simpa [map_add] using congrArg (fun z : TM x ↦ g.inner x z Γq) hbΓq
  unfold closedCurvatureCovDerivAtCorrectionAt
  change
    (g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γa) (extend E u) (extend E w) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E Γu) (extend E w) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E Γw) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u) (extend E w) x) Γq)
    +
    (g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γu) (extend E w) (extend E a) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E u) (extend E Γw) (extend E a) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E u) (extend E w) (extend E Γa) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E u) (extend E w) (extend E a) x) Γq)
    +
    (g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E Γw) (extend E a) (extend E u) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E Γa) (extend E u) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E a) (extend E Γu) x) q
      + g.inner x
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E w) (extend E a) (extend E u) x) Γq) = 0
  linarith

theorem closedCurvatureCovDerivAt_first_bianchi_inner
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u w q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v a u w) q
      + g.inner x (closedCurvatureCovDerivAt g x v u w a) q
      + g.inner x (closedCurvatureCovDerivAt g x v w a u) q = 0 := by
  have hEntry := closedCurvatureEntryDerivAt_first_bianchi
    (g := g) (x := x) v a u w q
  have hCorr := closedCurvatureCovDerivAtCorrection_cyclic_eq_zero
    (g := g) (x := x) v a u w q
  rw [closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := v) (a := a) (u := u) (w := w) (q := q),
    closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := v) (a := u) (u := w) (w := a) (q := q),
    closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
      (g := g) (x := x) (v := v) (a := w) (u := a) (w := u) (q := q)]
  linarith

theorem closedCurvatureCovDerivAt_applied_skew_inner
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u p q : TM x) :
    g.inner x (closedCurvatureCovDerivAt g x v a u p) q =
      -g.inner x (closedCurvatureCovDerivAt g x v a u q) p := by
  rw [closedCurvatureCovDerivAt_pair_symm_inner
      (g := g) (x := x) (v := v) (a := a) (u := u) (w := p) (q := q)]
  rw [closedCurvatureCovDerivAt_antisymm (g := g) (x := x) v p q a]
  simp only [map_neg, ContinuousLinearMap.neg_apply]
  rw [closedCurvatureCovDerivAt_pair_symm_inner
      (g := g) (x := x) (v := v) (a := q) (u := p) (w := a) (q := u)]

theorem curvatureOp_extend_add_fst
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (a₁ a₂ u z : TM x) :
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E (a₁ + a₂)) (extend E u) (extend E z) x =
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a₁) (extend E u) (extend E z) x +
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a₂) (extend E u) (extend E z) x := by
  let hreg := CovariantDerivative.derivRegularAt_extend g.leviCivita z
  have hleft := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E (a₁ + a₂)) (Y := extend E u)
    (mdifferentiableAt_extend I E (a₁ + a₂))
    (mdifferentiableAt_extend I E u)
  have h1 := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a₁) (Y := extend E u)
    (mdifferentiableAt_extend I E a₁)
    (mdifferentiableAt_extend I E u)
  have h2 := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a₂) (Y := extend E u)
    (mdifferentiableAt_extend I E a₂)
    (mdifferentiableAt_extend I E u)
  rw [← hleft, ← h1, ← h2]
  simp [ContinuousLinearMap.map_add]

theorem curvatureOp_extend_smul_fst
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (c : ℝ) (a u z : TM x) :
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E (c • a)) (extend E u) (extend E z) x =
    c • CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E u) (extend E z) x := by
  let hreg := CovariantDerivative.derivRegularAt_extend g.leviCivita z
  have hleft := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E (c • a)) (Y := extend E u)
    (mdifferentiableAt_extend I E (c • a))
    (mdifferentiableAt_extend I E u)
  have h1 := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a) (Y := extend E u)
    (mdifferentiableAt_extend I E a)
    (mdifferentiableAt_extend I E u)
  rw [← hleft, ← h1]
  simp

theorem curvatureOp_extend_add_snd
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (a u₁ u₂ z : TM x) :
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E (u₁ + u₂)) (extend E z) x =
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E u₁) (extend E z) x +
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E u₂) (extend E z) x := by
  let hreg := CovariantDerivative.derivRegularAt_extend g.leviCivita z
  have hleft := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a) (Y := extend E (u₁ + u₂))
    (mdifferentiableAt_extend I E a)
    (mdifferentiableAt_extend I E (u₁ + u₂))
  have h1 := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a) (Y := extend E u₁)
    (mdifferentiableAt_extend I E a)
    (mdifferentiableAt_extend I E u₁)
  have h2 := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a) (Y := extend E u₂)
    (mdifferentiableAt_extend I E a)
    (mdifferentiableAt_extend I E u₂)
  rw [← hleft, ← h1, ← h2]
  simp [ContinuousLinearMap.map_add]

theorem curvatureOp_extend_smul_snd
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M} (c : ℝ) (a u z : TM x) :
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E (c • u)) (extend E z) x =
    c • CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E u) (extend E z) x := by
  let hreg := CovariantDerivative.derivRegularAt_extend g.leviCivita z
  have hleft := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a) (Y := extend E (c • u))
    (mdifferentiableAt_extend I E a)
    (mdifferentiableAt_extend I E (c • u))
  have h1 := CovariantDerivative.curvatureTensorAt_apply
    (cov := g.leviCivita) (hreg := hreg)
    (X := extend E a) (Y := extend E u)
    (mdifferentiableAt_extend I E a)
    (mdifferentiableAt_extend I E u)
  rw [← hleft, ← h1]
  simp

theorem closedCurvatureCovDerivAt_add_deriv
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v₁ v₂ a u w : TM x) :
    closedCurvatureCovDerivAt g x (v₁ + v₂) a u w =
      closedCurvatureCovDerivAt g x v₁ a u w +
      closedCurvatureCovDerivAt g x v₂ a u w := by
  let R : ∀ y : M, TM y := fun y ↦
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E u) (extend E w) y
  have hΓa :
      g.leviCivita (extend E a) x (v₁ + v₂) =
        g.leviCivita (extend E a) x v₁ + g.leviCivita (extend E a) x v₂ := by
    simp
  have hΓu :
      g.leviCivita (extend E u) x (v₁ + v₂) =
        g.leviCivita (extend E u) x v₁ + g.leviCivita (extend E u) x v₂ := by
    simp
  have hΓw :
      g.leviCivita (extend E w) x (v₁ + v₂) =
        g.leviCivita (extend E w) x v₁ + g.leviCivita (extend E w) x v₂ := by
    simp
  unfold closedCurvatureCovDerivAt
  change g.leviCivita R x (v₁ + v₂)
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E (g.leviCivita (extend E a) x (v₁ + v₂)))
          (extend E u) (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a)
          (extend E (g.leviCivita (extend E u) x (v₁ + v₂)))
          (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u)
          (extend E (g.leviCivita (extend E w) x (v₁ + v₂))) x
    =
    (g.leviCivita R x v₁
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E (g.leviCivita (extend E a) x v₁))
          (extend E u) (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a)
          (extend E (g.leviCivita (extend E u) x v₁))
          (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u)
          (extend E (g.leviCivita (extend E w) x v₁)) x)
    +
    (g.leviCivita R x v₂
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E (g.leviCivita (extend E a) x v₂))
          (extend E u) (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a)
          (extend E (g.leviCivita (extend E u) x v₂))
          (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u)
          (extend E (g.leviCivita (extend E w) x v₂)) x)
  rw [map_add, hΓa, hΓu, hΓw]
  rw [curvatureOp_extend_add_fst]
  rw [curvatureOp_extend_add_snd]
  rw [CovariantDerivative.curvatureOp_extend_add]
  abel

theorem closedCurvatureCovDerivAt_smul_deriv
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (c : ℝ) (v a u w : TM x) :
    closedCurvatureCovDerivAt g x (c • v) a u w =
      c • closedCurvatureCovDerivAt g x v a u w := by
  let R : ∀ y : M, TM y := fun y ↦
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E u) (extend E w) y
  have hΓa :
      g.leviCivita (extend E a) x (c • v) =
        c • g.leviCivita (extend E a) x v := by
    simp
  have hΓu :
      g.leviCivita (extend E u) x (c • v) =
        c • g.leviCivita (extend E u) x v := by
    simp
  have hΓw :
      g.leviCivita (extend E w) x (c • v) =
        c • g.leviCivita (extend E w) x v := by
    simp
  unfold closedCurvatureCovDerivAt
  change g.leviCivita R x (c • v)
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E (g.leviCivita (extend E a) x (c • v)))
          (extend E u) (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a)
          (extend E (g.leviCivita (extend E u) x (c • v)))
          (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u)
          (extend E (g.leviCivita (extend E w) x (c • v))) x
    =
    c •
    (g.leviCivita R x v
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E (g.leviCivita (extend E a) x v))
          (extend E u) (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a)
          (extend E (g.leviCivita (extend E u) x v))
          (extend E w) x
      - CovariantDerivative.curvatureOp g.leviCivita
          (extend E a) (extend E u)
          (extend E (g.leviCivita (extend E w) x v)) x)
  rw [map_smul, hΓa, hΓu, hΓw]
  rw [curvatureOp_extend_smul_fst]
  rw [curvatureOp_extend_smul_snd]
  rw [CovariantDerivative.curvatureOp_extend_smul]
  module

theorem closedCurvatureCovDerivAt_skew_trace_zero
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v a u : TM x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun i ↦ metricDualVectorAt g x (b.coord i)
      ∑ i, g.inner x (closedCurvatureCovDerivAt g x v a u (b i)) (sharp i))
      = 0 := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  let F : TM x → TM x → ℝ :=
    fun p q ↦ g.inner x (closedCurvatureCovDerivAt g x v a u p) q
  have hswap := sum_metricDualVectorAt_contraction_swap
    (g := g) (x := x) (F := F)
    (hadd1 := by
      intro p₁ p₂ q
      have hskew12 := closedCurvatureCovDerivAt_applied_skew_inner
        (g := g) (x := x) v a u (p₁ + p₂) q
      have hskew1 := closedCurvatureCovDerivAt_applied_skew_inner
        (g := g) (x := x) v a u p₁ q
      have hskew2 := closedCurvatureCovDerivAt_applied_skew_inner
        (g := g) (x := x) v a u p₂ q
      dsimp [F]
      rw [hskew12, hskew1, hskew2, map_add]
      ring)
    (hsmul1 := by
      intro c p q
      have hskewc := closedCurvatureCovDerivAt_applied_skew_inner
        (g := g) (x := x) v a u (c • p) q
      have hskew := closedCurvatureCovDerivAt_applied_skew_inner
        (g := g) (x := x) v a u p q
      dsimp [F]
      rw [hskewc, hskew, map_smul]
      simp [smul_eq_mul])
    (hadd2 := by
      intro p q₁ q₂
      dsimp [F]
      rw [map_add])
    (hsmul2 := by
      intro c p q
      dsimp [F]
      rw [map_smul]
      simp [smul_eq_mul])
  have hneg :
      (∑ i, F (sharp i) (b i)) =
        -∑ i, F (b i) (sharp i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp [F]
    rw [closedCurvatureCovDerivAt_applied_skew_inner
      (g := g) (x := x) v a u (sharp i) (b i)]
  change (∑ i, F (b i) (sharp i)) = 0
  rw [hneg] at hswap
  linarith

set_option maxHeartbeats 5000000 in
theorem closedCurvatureDivergenceAt_contraction_eq_closedRicciDivergenceTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      ∑ i, closedCurvatureDivergenceAt g x w
        (metricDualVectorAt g x (b.coord i)) (b i))
      = closedRicciDivergenceTraceAt g x w := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  unfold closedCurvatureDivergenceAt closedRicciDivergenceTraceAt
    closedCovRicciDerivAt
  change
      (∑ k, ∑ j, b.coord j
        (closedCurvatureCovDerivAt g x (b j) w (sharp k) (b k))) =
      ∑ k, ∑ j, b.coord j
        (closedCurvatureCovDerivAt g x (sharp k) (b j) w (b k))
  calc
    (∑ k, ∑ j, b.coord j
        (closedCurvatureCovDerivAt g x (b j) w (sharp k) (b k)))
        = ∑ k, ∑ j,
            g.inner x
              (closedCurvatureCovDerivAt g x (b j) w (sharp k) (b k))
              (sharp j) := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [coord_eq_inner_metricDualVectorAt_of_basis
            (g := g) (x := x) (b := b)]
    _ = ∑ k, ∑ j,
            g.inner x
              (closedCurvatureCovDerivAt g x (sharp j) (b k) (b j) w)
              (sharp k) := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          calc
            (∑ j,
              g.inner x
                (closedCurvatureCovDerivAt g x (b j) w (sharp k) (b k))
                (sharp j))
                = ∑ j,
                    g.inner x
                      (closedCurvatureCovDerivAt g x (b j) (b k) (sharp j) w)
                      (sharp k) := by
                  refine Finset.sum_congr rfl fun j _ ↦ ?_
                  exact closedCurvatureCovDerivAt_pair_symm_inner
                    (g := g) (x := x) (v := b j)
                    (a := w) (u := sharp k) (w := b k) (q := sharp j)
            _ = ∑ j,
                    g.inner x
                      (closedCurvatureCovDerivAt g x (sharp j) (b k) (b j) w)
                      (sharp k) := by
                  exact sum_metricDualVectorAt_contraction_swap
                    (g := g) (x := x)
                    (F := fun p q ↦
                      g.inner x
                        (closedCurvatureCovDerivAt g x q (b k) p w)
                        (sharp k))
                    (hadd1 := by
                      intro p₁ p₂ q
                      have hp12 := closedCurvatureCovDerivAt_pair_symm_inner
                        (g := g) (x := x) (v := q)
                        (a := b k) (u := p₁ + p₂) (w := w) (q := sharp k)
                      have hp1 := closedCurvatureCovDerivAt_pair_symm_inner
                        (g := g) (x := x) (v := q)
                        (a := b k) (u := p₁) (w := w) (q := sharp k)
                      have hp2 := closedCurvatureCovDerivAt_pair_symm_inner
                        (g := g) (x := x) (v := q)
                        (a := b k) (u := p₂) (w := w) (q := sharp k)
                      dsimp
                      rw [hp12, hp1, hp2, map_add]
                    )
                    (hsmul1 := by
                      intro c p q
                      have hpc := closedCurvatureCovDerivAt_pair_symm_inner
                        (g := g) (x := x) (v := q)
                        (a := b k) (u := c • p) (w := w) (q := sharp k)
                      have hp := closedCurvatureCovDerivAt_pair_symm_inner
                        (g := g) (x := x) (v := q)
                        (a := b k) (u := p) (w := w) (q := sharp k)
                      dsimp
                      rw [hpc, hp, map_smul]
                      simp [smul_eq_mul])
                    (hadd2 := by
                      intro p q₁ q₂
                      dsimp
                      rw [closedCurvatureCovDerivAt_add_deriv]
                      rw [map_add]
                      simp [ContinuousLinearMap.add_apply])
                    (hsmul2 := by
                      intro c p q
                      dsimp
                      rw [closedCurvatureCovDerivAt_smul_deriv]
                      rw [map_smul]
                      simp [ContinuousLinearMap.smul_apply, smul_eq_mul])
    _ = ∑ j, ∑ k,
            g.inner x
              (closedCurvatureCovDerivAt g x (sharp j) (b k) (b j) w)
              (sharp k) := by
          rw [Finset.sum_comm]
    _ = ∑ j, ∑ k,
            g.inner x
              (closedCurvatureCovDerivAt g x (sharp j) (b k) w (b j))
              (sharp k) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          have hzero := closedCurvatureCovDerivAt_skew_trace_zero
            (g := g) (x := x) (v := sharp j) (a := b j) (u := w)
          change
            (∑ k,
              g.inner x
                (closedCurvatureCovDerivAt g x (sharp j) (b k) (b j) w)
                (sharp k))
              =
            ∑ k,
              g.inner x
                (closedCurvatureCovDerivAt g x (sharp j) (b k) w (b j))
                (sharp k)
          calc
            (∑ k,
              g.inner x
                (closedCurvatureCovDerivAt g x (sharp j) (b k) (b j) w)
                (sharp k))
                =
              ∑ k,
                (-g.inner x
                    (closedCurvatureCovDerivAt g x (sharp j) (b j) w (b k))
                    (sharp k)
                  + g.inner x
                    (closedCurvatureCovDerivAt g x (sharp j) (b k) w (b j))
                    (sharp k)) := by
                  refine Finset.sum_congr rfl fun k _ ↦ ?_
                  have hFB := closedCurvatureCovDerivAt_first_bianchi_inner
                    (g := g) (x := x) (v := sharp j)
                    (a := b k) (u := b j) (w := w) (q := sharp k)
                  have hAnti := closedCurvatureCovDerivAt_antisymm
                    (g := g) (x := x) (v := sharp j) (u := w)
                    (w := b k) (z := b j)
                  have hPA :
                      g.inner x
                        (closedCurvatureCovDerivAt g x (sharp j) w (b k) (b j))
                        (sharp k)
                        =
                      -g.inner x
                        (closedCurvatureCovDerivAt g x (sharp j) (b k) w (b j))
                        (sharp k) := by
                    rw [hAnti, map_neg]
                    simp
                  linarith
            _ =
              (∑ k,
                -g.inner x
                    (closedCurvatureCovDerivAt g x (sharp j) (b j) w (b k))
                    (sharp k))
                +
              ∑ k,
                g.inner x
                  (closedCurvatureCovDerivAt g x (sharp j) (b k) w (b j))
                  (sharp k) := by
                  rw [Finset.sum_add_distrib]
            _ =
              ∑ k,
                g.inner x
                  (closedCurvatureCovDerivAt g x (sharp j) (b k) w (b j))
                  (sharp k) := by
                  rw [Finset.sum_neg_distrib]
                  change - (∑ k,
                    g.inner x
                      (closedCurvatureCovDerivAt g x (sharp j) (b j) w (b k))
                      (sharp k))
                    + _ = _
                  rw [hzero]
                  simp
    _ = ∑ k, ∑ j,
            g.inner x
              (closedCurvatureCovDerivAt g x (sharp k) (b j) w (b k))
              (sharp j) := by
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ j, b.coord j
        (closedCurvatureCovDerivAt g x (sharp k) (b j) w (b k)) := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [coord_eq_inner_metricDualVectorAt_of_basis
            (g := g) (x := x) (b := b)]

theorem eventually_closedCurvatureDivergenceAt_contraction_eq_closedRicciDivergenceTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    ∀ᶠ y in nhds x, ∀ w : TM y,
      (letI : FiniteDimensional ℝ (TM y) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        let b := Module.finBasis ℝ (TM y)
        ∑ i, closedCurvatureDivergenceAt g y w
          (metricDualVectorAt g y (b.coord i)) (b i))
        = closedRicciDivergenceTraceAt g y w :=
  Filter.Eventually.of_forall fun y w ↦
    closedCurvatureDivergenceAt_contraction_eq_closedRicciDivergenceTraceAt
      (g := g) (x := y) w

/--
Hessian identification for the first-slot trace field from the local
first-order identity and scalar trace C² regularity.
-/
theorem deltaGammaFirstSlotTraceFieldHessianAt_of_trace_extSecond
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hTrace₂ :
      TraceMetricVariationExtSecondDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    DeltaGammaFirstSlotTraceFieldHessianAt gt t₀ x := by
  intro u w
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  have heq :=
    deltaGammaFirstSlotTraceFieldAt_eventually_eq_half_trace_extDerivFun
      (gt := gt) (t₀ := t₀) (x := x) hgt hNear w
  have hderiv :
      extDerivFun
          (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
          x u =
        extDerivFun
          (fun y : M ↦
            (1 / 2 : ℝ) *
              extDerivFun (fun z : M ↦ traceMetricVariationAt g H z)
                y (extend E w y))
          x u := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L u)
      (CovariantDerivative.extDerivFun_congr heq)
  have hscale :
      extDerivFun
          (fun y : M ↦
            (1 / 2 : ℝ) *
              extDerivFun (fun z : M ↦ traceMetricVariationAt g H z)
                y (extend E w y))
          x u =
        (1 / 2 : ℝ) *
          extDerivFun
            (fun y : M ↦
              extDerivFun (fun z : M ↦ traceMetricVariationAt g H z)
                y (extend E w y))
            x u := by
    have h :=
      congrArg (fun L : TM x →L[ℝ] ℝ ↦ L u)
        (extDerivFun_const_smul_at
          (n := n) (M := M)
          (f := fun y : M ↦
            extDerivFun (fun z : M ↦ traceMetricVariationAt g H z)
              y (extend E w y))
          (x := x) (hTrace₂ w) (1 / 2 : ℝ))
    simpa [Pi.smul_apply, smul_eq_mul, g, H, f] using h
  have hcorr :
      deltaGammaFirstSlotTraceFieldAt gt t₀ x
          (g.leviCivita (extend E w) x u) =
        (1 / 2 : ℝ) *
          extDerivFun (fun y : M ↦ traceMetricVariationAt g H y) x
            (g.leviCivita (extend E w) x u) := by
    simpa [g, H, f] using
      deltaGammaFirstSlotTraceFieldAt_eq_half_trace_extDerivFun
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt hCovDiff (g.leviCivita (extend E w) x u)
  have hcompat :
      extDerivFun
          (fun y : M ↦
            extDerivFun (fun z : M ↦ traceMetricVariationAt g H z)
              y (extend E w y))
          x u =
        g.hessianAt f x u w +
          extDerivFun (fun y : M ↦ traceMetricVariationAt g H y) x
            (g.leviCivita (extend E w) x u) := by
    simpa [f] using
      extDerivFun_extDerivFun_extend_eq_hessianAt_add
        (g := g) (f := f) (x := x) hgrad u w
  change
      extDerivFun
          (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
          x u
        - deltaGammaFirstSlotTraceFieldAt gt t₀ x
          (g.leviCivita (extend E w) x u)
      =
        (1 / 2 : ℝ) * g.hessianAt f x u w
  rw [hderiv, hscale, hcorr, hcompat]
  ring

theorem deltaGamma_innerTrace_eq_of_covTensor2Regular_traceProduct
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (hTraceProduct :
      TraceMetricVariationProductRuleAt (gt t₀) (timeDerivAt gt t₀) x)
    (hTraceCancel :
      TraceMetricVariationRaiseCancellationAt (gt t₀) (timeDerivAt gt t₀) x)
    (w : TM x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ i, (gt t₀).inner x
        (deltaGammaAt gt t₀ x ((Module.finBasis ℝ (TM x)) i)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord i))) w)
      =
        tensorDivergenceOneFormAt (gt t₀) (timeDerivAt gt t₀) x w
          - (1 / 2 : ℝ) *
            extDerivFun
              (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y)
              x w :=
  deltaGamma_innerTrace_eq_of_covTensor2Regular
    (gt := gt) (t₀ := t₀) (x := x)
    hreg hgt hExt hCovDiff
    (traceMetricVariationDerivAt_of_productRule_raiseCancellation
      (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
      hTraceProduct hTraceCancel)
    w

/--
The double divergence of a raw metric variation:
`div div h = Σⱼ (∇_{♯eʲ} div h)(eⱼ)`.

This is the closed-manifold analogue of the model `tensorDoubleDivergence`;
the outer one-form derivative is written directly with `extDerivFun` and the
canonical Levi-Civita correction on the test slot.
-/
noncomputable def tensorDoubleDivergenceAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  ∑ j,
    (extDerivFun
        (fun y : M ↦ tensorDivergenceOneFormAt g h y
          (extend E (b j) y)) x
        (metricDualVectorAt g x (b.coord j))
      - tensorDivergenceOneFormAt g h x
        ((g.leviCivita (extend E (b j)) x
          (metricDualVectorAt g x (b.coord j)))))

@[simp] theorem tensorDoubleDivergenceAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    tensorDoubleDivergenceAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x = 0 := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold tensorDoubleDivergenceAt
  simp [tensorDivergenceOneFormAt_zero, extDerivFun_zero_at]

theorem covTensor2DerivAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hEq : ∀ᶠ y in nhds x, ∀ v w : TM y, h y v w = k y v w)
    (v p q : TM x) :
    covTensor2DerivAt g h x v p q =
      covTensor2DerivAt g k x v p q := by
  have hEntry :
      (fun y : M ↦ h y (extend E p y) (extend E q y)) =ᶠ[nhds x]
        fun y : M ↦ k y (extend E p y) (extend E q y) := by
    exact hEq.mono fun y hy ↦ hy _ _
  have hx : ∀ v w : TM x, h x v w = k x v w :=
    hEq.self_of_nhds
  unfold covTensor2DerivAt
  rw [CovariantDerivative.extDerivFun_congr hEntry]
  rw [hx (g.leviCivita (extend E p) x v) q]
  rw [hx p (g.leviCivita (extend E q) x v)]

theorem covTensor2DerivAt_smul_field
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (c : ℝ) (v p q : TM x) :
    covTensor2DerivAt g (fun y v w ↦ c * h y v w) x v p q =
      c * covTensor2DerivAt g h x v p q := by
  have hEntry :
      (fun y : M ↦ c * h y (extend E p y) (extend E q y)) =
        c • (fun y : M ↦ h y (extend E p y) (extend E q y)) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  unfold covTensor2DerivAt
  rw [hEntry]
  rw [extDerivFun_const_smul_at (hDiff p q) c]
  simp [Pi.smul_apply, smul_eq_mul]
  ring

theorem tensorDivergenceOneFormAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hEq : ∀ᶠ y in nhds x, ∀ v w : TM y, h y v w = k y v w)
    (w : TM x) :
    tensorDivergenceOneFormAt g h x w =
      tensorDivergenceOneFormAt g k x w := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold tensorDivergenceOneFormAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact covTensor2DerivAt_congr_of_eventuallyEq
    (g := g) (h := h) (k := k) (x := x) hEq _ _ _

theorem tensorDivergenceOneFormAt_smul_field
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : CovTensor2ExtDifferentiableAt h x)
    (c : ℝ) (w : TM x) :
    tensorDivergenceOneFormAt g (fun y v w ↦ c * h y v w) x w =
      c * tensorDivergenceOneFormAt g h x w := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold tensorDivergenceOneFormAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact covTensor2DerivAt_smul_field
    (g := g) (h := h) (x := x) hDiff c _ _ _

theorem tensorDoubleDivergenceAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hEq : ∀ᶠ y in nhds x, ∀ v w : TM y, h y v w = k y v w) :
    tensorDoubleDivergenceAt g h x =
      tensorDoubleDivergenceAt g k x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  change
    (∑ j,
      (extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g h y
            (extend E (b j) y)) x (sharp j)
        - tensorDivergenceOneFormAt g h x
          (g.leviCivita (extend E (b j)) x (sharp j)))) =
    (∑ j,
      (extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g k y
            (extend E (b j) y)) x (sharp j)
        - tensorDivergenceOneFormAt g k x
          (g.leviCivita (extend E (b j)) x (sharp j))))
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hDiv :
      (fun y : M ↦ tensorDivergenceOneFormAt g h y
        (extend E (b j) y)) =ᶠ[nhds x]
        fun y : M ↦ tensorDivergenceOneFormAt g k y
          (extend E (b j) y) := by
    filter_upwards [hEq.eventually_nhds] with y hy
    exact tensorDivergenceOneFormAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := y) hy _
  have hDeriv :
      extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g h y
            (extend E (b j) y)) x (sharp j) =
        extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g k y
            (extend E (b j) y)) x (sharp j) := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L (sharp j))
      (CovariantDerivative.extDerivFun_congr hDiv)
  have hCorr :
      tensorDivergenceOneFormAt g h x
          (g.leviCivita (extend E (b j)) x (sharp j)) =
        tensorDivergenceOneFormAt g k x
          (g.leviCivita (extend E (b j)) x (sharp j)) :=
    tensorDivergenceOneFormAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq _
  rw [hDeriv, hCorr]

theorem tensorDoubleDivergenceAt_smul_field
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ tensorDivergenceOneFormAt g h y (extend E w y)) x)
    (c : ℝ) :
    tensorDoubleDivergenceAt g (fun y v w ↦ c * h y v w) x =
      c * tensorDoubleDivergenceAt g h x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  change
    (∑ j,
      (extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g
            (fun z v w ↦ c * h z v w) y (extend E (b j) y))
          x (sharp j)
        - tensorDivergenceOneFormAt g
          (fun z v w ↦ c * h z v w) x
          (g.leviCivita (extend E (b j)) x (sharp j)))) =
      c * (∑ j,
        (extDerivFun
            (fun y : M ↦ tensorDivergenceOneFormAt g h y
              (extend E (b j) y)) x (sharp j)
          - tensorDivergenceOneFormAt g h x
            (g.leviCivita (extend E (b j)) x (sharp j))))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  let f : M → ℝ :=
    fun y ↦ tensorDivergenceOneFormAt g h y (extend E (b j) y)
  have hDiv :
      (fun y : M ↦ tensorDivergenceOneFormAt g
        (fun z v w ↦ c * h z v w) y (extend E (b j) y)) =ᶠ[nhds x]
        c • f := by
    refine Filter.Eventually.of_forall fun y ↦ ?_
    change tensorDivergenceOneFormAt g
        (fun z v w ↦ c * h z v w) y (extend E (b j) y) =
      c * tensorDivergenceOneFormAt g h y (extend E (b j) y)
    exact tensorDivergenceOneFormAt_smul_field
      (g := g) (h := h) (x := y) (hDiff y) c _
  have hDerivCongr :
      extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g
            (fun z v w ↦ c * h z v w) y (extend E (b j) y))
          x (sharp j) =
        extDerivFun (c • f) x (sharp j) := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L (sharp j))
      (CovariantDerivative.extDerivFun_congr hDiv)
  have hDerivScale :
      extDerivFun (c • f) x (sharp j) =
        c * extDerivFun f x (sharp j) := by
    have h :=
      congrArg (fun L : TM x →L[ℝ] ℝ ↦ L (sharp j))
        (extDerivFun_const_smul_at
          (n := n) (M := M) (f := f) (x := x) (hDivDiff (b j)) c)
    simpa [Pi.smul_apply, smul_eq_mul, f] using h
  have hCorr :
      tensorDivergenceOneFormAt g
          (fun z v w ↦ c * h z v w) x
          (g.leviCivita (extend E (b j)) x (sharp j)) =
        c * tensorDivergenceOneFormAt g h x
          (g.leviCivita (extend E (b j)) x (sharp j)) :=
    tensorDivergenceOneFormAt_smul_field
      (g := g) (h := h) (x := x) (hDiff x) c _
  rw [hDerivCongr, hDerivScale, hCorr]
  ring

/-- The double divergence of the Ricci tensor, `div div Ric`. -/
noncomputable def ricciDoubleDivergenceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : ℝ :=
  tensorDoubleDivergenceAt g (ricciVariationField g) x

/--
Honest analytic linearity obligation for the closed double-divergence operator
on the Ricci field under multiplication by `-2`.
-/
def TensorDoubleDivergenceNegTwoRicciLinearityAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  tensorDoubleDivergenceAt g (negTwoRicciVariationField g) x =
    -2 * ricciDoubleDivergenceAt g x

theorem TensorDoubleDivergenceNegTwoRicciLinearityAt.of_covTensor2Regular
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRicDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (ricciVariationField g) y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt g (ricciVariationField g) y
            (extend E w y)) x) :
    TensorDoubleDivergenceNegTwoRicciLinearityAt g x := by
  unfold TensorDoubleDivergenceNegTwoRicciLinearityAt
  unfold ricciDoubleDivergenceAt
  unfold negTwoRicciVariationField
  simpa [ricciVariationField] using
    tensorDoubleDivergenceAt_smul_field
      (g := g) (h := ricciVariationField g) (x := x)
      hRicDiff hRicDivDiff (-2 : ℝ)

/-- Substitution of `h = -2 Ric` in the double-divergence term. -/
theorem tensorDoubleDivergenceAt_negTwoRicci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt g x) :
    tensorDoubleDivergenceAt g (negTwoRicciVariationField g) x =
      -2 * ricciDoubleDivergenceAt g x :=
  hlin

/--
Closed twice-contracted Bianchi obligation:
`div div Ric = (1 / 2) ΔR` at `x`.

This is the closed-manifold analogue of the proved model-space
`coord_twice_contracted_bianchi`; its intrinsic closed proof is future work.
-/
def ClosedContractedBianchiAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ricciDoubleDivergenceAt g x =
    (1 / 2 : ℝ) * g.laplacianAt (fun y ↦ g.scalarAt y) x

/--
Closed contracted Bianchi in one-form form:
`div Ric = 1/2 dR` at `x`.

This is the remaining intrinsic identity needed before tracing once more to
obtain `ClosedContractedBianchiAt`.
-/
def ClosedContractedBianchiOneFormAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ w : TM x,
    tensorDivergenceOneFormAt g (ricciVariationField g) x w =
      (1 / 2 : ℝ) * extDerivFun (fun y : M ↦ g.scalarAt y) x w

theorem ClosedContractedBianchiOneFormAt.of_two_tensorDivergenceOneForm_eq_extDerivFun
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (h :
      ∀ w : TM x,
        2 * tensorDivergenceOneFormAt g (ricciVariationField g) x w =
          extDerivFun (fun y : M ↦ g.scalarAt y) x w) :
    ClosedContractedBianchiOneFormAt g x := by
  intro w
  have hw := h w
  linarith

theorem ClosedContractedBianchiOneFormAt.of_closed_trace_contraction
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hDivTrace :
      ∀ w : TM x,
        tensorDivergenceOneFormAt g (ricciVariationField g) x w =
          closedRicciDivergenceTraceAt g x w)
    (hScalarTrace :
      ∀ w : TM x,
        closedScalarContractionDerivTraceAt g x w =
          extDerivFun (fun y : M ↦ g.scalarAt y) x w)
    (hTraceBianchi :
      ∀ w : TM x,
        2 * closedRicciDivergenceTraceAt g x w =
          closedScalarContractionDerivTraceAt g x w) :
    ClosedContractedBianchiOneFormAt g x := by
  refine
    ClosedContractedBianchiOneFormAt.of_two_tensorDivergenceOneForm_eq_extDerivFun
      (g := g) (x := x) ?_
  intro w
  rw [hDivTrace w, hTraceBianchi w, hScalarTrace w]

/--
If the closed Ricci divergence one-form is the half-gradient of scalar
curvature on a neighborhood of `x`, then tracing its covariant derivative gives
the frozen closed twice-contracted Bianchi predicate.
-/
theorem ClosedContractedBianchiAt.of_tensorDivergenceOneForm_eq_half_extDerivFun_near
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hDiv :
      ∀ᶠ y in nhds x, ∀ w : TM y,
        tensorDivergenceOneFormAt g (ricciVariationField g) y w =
          (1 / 2 : ℝ) *
            extDerivFun (fun z : M ↦ g.scalarAt z) y w)
    (hScalar₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x)
    (hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ g.scalarAt z) y (extend E w y)) x) :
    ClosedContractedBianchiAt g x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let f : M → ℝ := fun y ↦ g.scalarAt y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hgrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    simpa [f] using g.mdifferentiableAt_gradient hScalar₂
  unfold ClosedContractedBianchiAt ricciDoubleDivergenceAt tensorDoubleDivergenceAt
  change
    (∑ j,
      (extDerivFun
          (fun y : M ↦
            tensorDivergenceOneFormAt g (ricciVariationField g) y
              (extend E (b j) y)) x (sharp j)
        - tensorDivergenceOneFormAt g (ricciVariationField g) x
          (g.leviCivita (extend E (b j)) x (sharp j)))) =
      (1 / 2 : ℝ) * g.laplacianAt f x
  have hterm : ∀ j,
      (extDerivFun
          (fun y : M ↦
            tensorDivergenceOneFormAt g (ricciVariationField g) y
              (extend E (b j) y)) x (sharp j)
        - tensorDivergenceOneFormAt g (ricciVariationField g) x
          (g.leviCivita (extend E (b j)) x (sharp j))) =
        (1 / 2 : ℝ) * g.hessianAt f x (sharp j) (b j) := by
    intro j
    let F : M → ℝ :=
      fun y ↦ extDerivFun f y (extend E (b j) y)
    have hDivField :
        (fun y : M ↦
          tensorDivergenceOneFormAt g (ricciVariationField g) y
            (extend E (b j) y)) =ᶠ[nhds x]
          fun y : M ↦ (1 / 2 : ℝ) * F y := by
      filter_upwards [hDiv] with y hy
      simpa [F, f] using hy (extend E (b j) y)
    have hDerivCongr :
        extDerivFun
            (fun y : M ↦
              tensorDivergenceOneFormAt g (ricciVariationField g) y
                (extend E (b j) y)) x (sharp j) =
          extDerivFun (fun y : M ↦ (1 / 2 : ℝ) * F y) x
            (sharp j) := by
      exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L (sharp j))
        (CovariantDerivative.extDerivFun_congr hDivField)
    have hDerivScale :
        extDerivFun (fun y : M ↦ (1 / 2 : ℝ) * F y) x (sharp j) =
          (1 / 2 : ℝ) * extDerivFun F x (sharp j) := by
      have h :=
        congrArg (fun L : TM x →L[ℝ] ℝ ↦ L (sharp j))
          (extDerivFun_const_smul_at
            (n := n) (M := M) (f := F) (x := x)
            (by simpa [F, f] using hScalarExt₂ (b j)) (1 / 2 : ℝ))
      simpa [Pi.smul_apply, smul_eq_mul, F] using h
    have hCompat :
        extDerivFun F x (sharp j) =
          g.hessianAt f x (sharp j) (b j) +
            extDerivFun f x
              (g.leviCivita (extend E (b j)) x (sharp j)) := by
      simpa [F] using
        extDerivFun_extDerivFun_extend_eq_hessianAt_add
          (g := g) (f := f) (x := x) hgrad (sharp j) (b j)
    have hCorr :
        tensorDivergenceOneFormAt g (ricciVariationField g) x
            (g.leviCivita (extend E (b j)) x (sharp j)) =
          (1 / 2 : ℝ) * extDerivFun f x
            (g.leviCivita (extend E (b j)) x (sharp j)) := by
      simpa [f] using
        (hDiv.self_of_nhds
          (g.leviCivita (extend E (b j)) x (sharp j)))
    rw [hDerivCongr, hDerivScale, hCompat, hCorr]
    ring
  calc
    (∑ j,
      (extDerivFun
          (fun y : M ↦
            tensorDivergenceOneFormAt g (ricciVariationField g) y
              (extend E (b j) y)) x (sharp j)
        - tensorDivergenceOneFormAt g (ricciVariationField g) x
          (g.leviCivita (extend E (b j)) x (sharp j))))
        = ∑ j, (1 / 2 : ℝ) * g.hessianAt f x (sharp j) (b j) := by
          exact Finset.sum_congr rfl fun j _ ↦ hterm j
    _ = (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (sharp j) (b j) := by
          rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (b j) (sharp j) := by
          congr 1
          exact Finset.sum_congr rfl fun j _ ↦
            g.hessianAt_symm hScalar₂ hgrad (sharp j) (b j)
    _ = (1 / 2 : ℝ) * g.laplacianAt f x := by
          rw [laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x)]

/--
Predicate-form wrapper for the local one-form contracted Bianchi identity.
-/
theorem ClosedContractedBianchiAt.of_oneForm_near
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hOne :
      ∀ᶠ y in nhds x, ClosedContractedBianchiOneFormAt g y)
    (hScalar₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x)
    (hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ g.scalarAt z) y (extend E w y)) x) :
    ClosedContractedBianchiAt g x :=
  ClosedContractedBianchiAt.of_tensorDivergenceOneForm_eq_half_extDerivFun_near
    (g := g) (x := x)
    (hOne.mono fun _ hy w ↦ hy w)
    hScalar₂ hScalarExt₂

theorem ClosedContractedBianchiAt.of_closed_trace_contraction_near
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hDivTrace :
      ∀ᶠ y in nhds x, ∀ w : TM y,
        tensorDivergenceOneFormAt g (ricciVariationField g) y w =
          closedRicciDivergenceTraceAt g y w)
    (hScalarTrace :
      ∀ᶠ y in nhds x, ∀ w : TM y,
        closedScalarContractionDerivTraceAt g y w =
          extDerivFun (fun z : M ↦ g.scalarAt z) y w)
    (hTraceBianchi :
      ∀ᶠ y in nhds x, ∀ w : TM y,
        2 * closedRicciDivergenceTraceAt g y w =
          closedScalarContractionDerivTraceAt g y w)
    (hScalar₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x)
    (hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ g.scalarAt z) y (extend E w y)) x) :
    ClosedContractedBianchiAt g x := by
  refine ClosedContractedBianchiAt.of_oneForm_near
    (g := g) (x := x) ?_ hScalar₂ hScalarExt₂
  filter_upwards [hDivTrace, hScalarTrace, hTraceBianchi] with y hyDiv hyScalar hyBianchi
  exact ClosedContractedBianchiOneFormAt.of_closed_trace_contraction
    (g := g) (x := y) hyDiv hyScalar hyBianchi

theorem ClosedContractedBianchiAt.of_closed_trace_contraction_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (hTraceBianchi :
      ∀ᶠ y in nhds x, ∀ w : TM y,
        2 * closedRicciDivergenceTraceAt g y w =
          closedScalarContractionDerivTraceAt g y w)
    (hScalar₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x)
    (hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ g.scalarAt z) y (extend E w y)) x) :
    ClosedContractedBianchiAt g x :=
  ClosedContractedBianchiAt.of_closed_trace_contraction_near
    (g := g) (x := x)
    (eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt_canonical
      g x)
    (eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt_canonical
      g x)
    hTraceBianchi hScalar₂ hScalarExt₂

theorem closedContractedBianchiAt_canonical
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hScalar₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x)
    (hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ g.scalarAt z) y (extend E w y)) x) :
    ClosedContractedBianchiAt g x := by
  exact ClosedContractedBianchiAt.of_closed_trace_contraction_canonical
    (g := g) (x := x)
    (eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi
      (g := g) (x := x)
      (eventually_closed_cyclic_second_bianchi (g := g) x)
      (eventually_closedCurvatureDivergenceAt_contraction_eq_closedRicciDivergenceTraceAt
        (g := g) x))
    hScalar₂ hScalarExt₂

/-- Under twice-contracted Bianchi, `div div (-2 Ric) = -ΔR`. -/
theorem tensorDoubleDivergenceAt_negTwoRicci_eq_neg_laplacian_scalar
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt g x)
    (hBianchi : ClosedContractedBianchiAt g x) :
    tensorDoubleDivergenceAt g (negTwoRicciVariationField g) x =
      -g.laplacianAt (fun y ↦ g.scalarAt y) x := by
  rw [tensorDoubleDivergenceAt_negTwoRicci g x hlin]
  rw [hBianchi]
  ring

/--
Honest substitution obligation for the double-divergence operator: the
time-variation field has the same double divergence as `-2 Ric`.
-/
def TensorDoubleDivergenceTimeDerivNegTwoRicciAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x =
    tensorDoubleDivergenceAt (gt t₀) (negTwoRicciVariationField (gt t₀)) x

theorem eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y) :
    ∀ᶠ y in nhds x, ∀ v w : TM y,
      timeDerivAt gt t₀ y v w = -2 * (gt t₀).ricciAt y v w := by
  exact hNear.mono fun y hy v w ↦
    isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt
      hy.1 hy.2 v w

theorem TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_eventually_eq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hEq : ∀ᶠ y in nhds x, ∀ v w : TM y,
      timeDerivAt gt t₀ y v w = -2 * (gt t₀).ricciAt y v w) :
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x := by
  change
    tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x =
      tensorDoubleDivergenceAt (gt t₀)
        (negTwoRicciVariationField (gt t₀)) x
  apply tensorDoubleDivergenceAt_congr_of_eventuallyEq
  exact hEq.mono fun y hy v w ↦ by
    simpa [negTwoRicciVariationField] using hy v w

theorem TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y) :
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x :=
  TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_eventually_eq
    (eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt
      (gt := gt) (t₀ := t₀) (x := x) hNear)

/--
Honest substitution obligation under the scalar Laplacian:
`Δ(tr h) = Δ(-2 R)` for the Ricci-flow variation field.
-/
def TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  (gt t₀).laplacianAt
      (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x =
    -2 * (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x

theorem TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_eventually_eq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hEq : ∀ᶠ y in nhds x, ∀ v w : TM y,
      timeDerivAt gt t₀ y v w = -2 * (gt t₀).ricciAt y v w)
    (hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let fTrace : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  let fScalar : M → ℝ := fun y ↦ g.scalarAt y
  let fNegScalar : M → ℝ := fun y ↦ (-2 : ℝ) * fScalar y
  have hTraceEq : fTrace =ᶠ[nhds x] fNegScalar := by
    filter_upwards [hEq] with y hy
    exact traceMetricVariationAt_timeDeriv_eq_negTwoRicci
      (gt := gt) (t₀ := t₀) (x := y) hy
  have hCongr :
      g.laplacianAt fTrace x = g.laplacianAt fNegScalar x :=
    g.laplacianAt_congr_of_eventuallyEq hTraceEq hTraceGrad hNegScalarGrad
  have hScale :
      g.laplacianAt fNegScalar x =
        -2 * g.laplacianAt fScalar x := by
    have h :=
      g.laplacianAt_const_smul
        (f := fScalar) (x := x) (-2 : ℝ) hScalarDiff hScalarGrad
    simpa [fNegScalar, fScalar, Pi.smul_apply, smul_eq_mul] using h
  change g.laplacianAt fTrace x =
    -2 * g.laplacianAt fScalar x
  rw [hCongr, hScale]

theorem TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x :=
  TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_eventually_eq
    (eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt
      (gt := gt) (t₀ := t₀) (x := x) hNear)
    hTraceGrad hNegScalarGrad hScalarDiff hScalarGrad

theorem covTensor2SecondDerivAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hEq : ∀ᶠ y in nhds x, ∀ v w : TM y, h y v w = k y v w)
    (u v p q : TM x) :
    covTensor2SecondDerivAt g h x u v p q =
      covTensor2SecondDerivAt g k x u v p q := by
  have hEntry :
      (fun y : M ↦ covTensor2DerivAt g h y
        (extend E v y) (extend E p y) (extend E q y))
        =ᶠ[nhds x]
      (fun y : M ↦ covTensor2DerivAt g k y
        (extend E v y) (extend E p y) (extend E q y)) := by
    filter_upwards [hEq.eventually_nhds] with y hy
    exact covTensor2DerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := y) hy _ _ _
  have hDeriv :
      extDerivFun
          (fun y : M ↦ covTensor2DerivAt g h y
            (extend E v y) (extend E p y) (extend E q y)) x u =
        extDerivFun
          (fun y : M ↦ covTensor2DerivAt g k y
            (extend E v y) (extend E p y) (extend E q y)) x u := by
    exact congrArg (fun L : TM x →L[ℝ] ℝ ↦ L u)
      (CovariantDerivative.extDerivFun_congr hEntry)
  have hV :
      covTensor2DerivAt g h x (g.leviCivita (extend E v) x u) p q =
        covTensor2DerivAt g k x (g.leviCivita (extend E v) x u) p q :=
    covTensor2DerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq _ _ _
  have hP :
      covTensor2DerivAt g h x v (g.leviCivita (extend E p) x u) q =
        covTensor2DerivAt g k x v (g.leviCivita (extend E p) x u) q :=
    covTensor2DerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq _ _ _
  have hQ :
      covTensor2DerivAt g h x v p (g.leviCivita (extend E q) x u) =
        covTensor2DerivAt g k x v p (g.leviCivita (extend E q) x u) :=
    covTensor2DerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq _ _ _
  unfold covTensor2SecondDerivAt
  rw [hDeriv, hV, hP, hQ]

/--
Ricci-flow specialization of the first connection-variation Koszul formula.

The `IsClosedRicciFlowSolutionAt` neighborhood hypothesis supplies
`timeDerivAt = -2 Ric`; the remaining hypotheses are exactly the regularity
needed by the already-proved `deltaGamma_koszul` and tensor-linearity lemmas.
-/
theorem deltaGamma_koszul_negTwoRicci_of_isClosedRicciFlowSolutionAt_near
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hFlowNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hRicDiff :
      CovTensor2ExtDifferentiableAt (ricciVariationField (gt t₀)) x)
    (v w z : TM x) :
    2 * (gt t₀).inner x (deltaGammaAt gt t₀ x v w) z =
      -2 * covTensor2DerivAt (gt t₀) (ricciVariationField (gt t₀)) x v w z
        - 2 * covTensor2DerivAt (gt t₀) (ricciVariationField (gt t₀)) x w v z
        + 2 * covTensor2DerivAt (gt t₀) (ricciVariationField (gt t₀)) x z v w := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hEq :
      ∀ᶠ y in nhds x, ∀ v w : TM y,
        timeDerivAt gt t₀ y v w = -2 * g.ricciAt y v w :=
    eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt
      (gt := gt) (t₀ := t₀) (x := x) hFlowNear
  have h1 :
      covTensor2DerivAt g (timeDerivAt gt t₀) x v w z =
        covTensor2DerivAt g (negTwoRicciVariationField g) x v w z := by
    exact covTensor2DerivAt_congr_of_eventuallyEq
      (g := g) (h := timeDerivAt gt t₀)
      (k := negTwoRicciVariationField g) (x := x)
      (hEq.mono fun y hy a b ↦ by
        simpa [g, negTwoRicciVariationField] using hy a b) _ _ _
  have h2 :
      covTensor2DerivAt g (timeDerivAt gt t₀) x w v z =
        covTensor2DerivAt g (negTwoRicciVariationField g) x w v z := by
    exact covTensor2DerivAt_congr_of_eventuallyEq
      (g := g) (h := timeDerivAt gt t₀)
      (k := negTwoRicciVariationField g) (x := x)
      (hEq.mono fun y hy a b ↦ by
        simpa [g, negTwoRicciVariationField] using hy a b) _ _ _
  have h3 :
      covTensor2DerivAt g (timeDerivAt gt t₀) x z v w =
        covTensor2DerivAt g (negTwoRicciVariationField g) x z v w := by
    exact covTensor2DerivAt_congr_of_eventuallyEq
      (g := g) (h := timeDerivAt gt t₀)
      (k := negTwoRicciVariationField g) (x := x)
      (hEq.mono fun y hy a b ↦ by
        simpa [g, negTwoRicciVariationField] using hy a b) _ _ _
  have hs1 :
      covTensor2DerivAt g (negTwoRicciVariationField g) x v w z =
        -2 * covTensor2DerivAt g (ricciVariationField g) x v w z := by
    let K : ∀ y : M, TM y → TM y → ℝ :=
      fun y a b ↦ (-2 : ℝ) * ricciVariationField g y a b
    have hK : K = negTwoRicciVariationField g := by
      funext y a b
      simp [K, negTwoRicciVariationField, ricciVariationField]
    rw [← hK]
    exact
      covTensor2DerivAt_smul_field
        (g := g) (h := ricciVariationField g) (x := x)
        hRicDiff (-2 : ℝ) v w z
  have hs2 :
      covTensor2DerivAt g (negTwoRicciVariationField g) x w v z =
        -2 * covTensor2DerivAt g (ricciVariationField g) x w v z := by
    let K : ∀ y : M, TM y → TM y → ℝ :=
      fun y a b ↦ (-2 : ℝ) * ricciVariationField g y a b
    have hK : K = negTwoRicciVariationField g := by
      funext y a b
      simp [K, negTwoRicciVariationField, ricciVariationField]
    rw [← hK]
    exact
      covTensor2DerivAt_smul_field
        (g := g) (h := ricciVariationField g) (x := x)
        hRicDiff (-2 : ℝ) w v z
  have hs3 :
      covTensor2DerivAt g (negTwoRicciVariationField g) x z v w =
        -2 * covTensor2DerivAt g (ricciVariationField g) x z v w := by
    let K : ∀ y : M, TM y → TM y → ℝ :=
      fun y a b ↦ (-2 : ℝ) * ricciVariationField g y a b
    have hK : K = negTwoRicciVariationField g := by
      funext y a b
      simp [K, negTwoRicciVariationField, ricciVariationField]
    rw [← hK]
    exact
      covTensor2DerivAt_smul_field
        (g := g) (h := ricciVariationField g) (x := x)
        hRicDiff (-2 : ℝ) z v w
  calc
    2 * g.inner x (deltaGammaAt gt t₀ x v w) z =
        covTensor2DerivAt g (timeDerivAt gt t₀) x v w z
          + covTensor2DerivAt g (timeDerivAt gt t₀) x w v z
          - covTensor2DerivAt g (timeDerivAt gt t₀) x z v w := by
          simpa [g] using
            deltaGamma_koszul
              (gt := gt) (t₀ := t₀) (x := x)
              hreg hgt hExt v w z
    _ = covTensor2DerivAt g (negTwoRicciVariationField g) x v w z
          + covTensor2DerivAt g (negTwoRicciVariationField g) x w v z
          - covTensor2DerivAt g (negTwoRicciVariationField g) x z v w := by
          rw [h1, h2, h3]
    _ = -2 * covTensor2DerivAt g (ricciVariationField g) x v w z
          - 2 * covTensor2DerivAt g (ricciVariationField g) x w v z
          + 2 * covTensor2DerivAt g (ricciVariationField g) x z v w := by
          rw [hs1, hs2, hs3]
          ring

/--
Ricci-flow specialization of the covariant differentiated Koszul formula.

This is the opening tensor-level commutation slice: it rewires the existing
closed `covDeltaGamma_koszul_secondDerivAt` identity under the neighborhood
flow equation `timeDerivAt = -2 Ric`, producing the pure three-term
second-covariant-derivative form with `negTwoRicciVariationField`.
-/
theorem covDeltaGamma_koszul_secondDerivAt_negTwoRicci_of_isClosedRicciFlowSolutionAt_near
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hFlowNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (u v w z : TM x) :
    2 * (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u v w) z =
      covTensor2SecondDerivAt
          (gt t₀) (negTwoRicciVariationField (gt t₀)) x u v w z
        + covTensor2SecondDerivAt
          (gt t₀) (negTwoRicciVariationField (gt t₀)) x u w v z
        - covTensor2SecondDerivAt
          (gt t₀) (negTwoRicciVariationField (gt t₀)) x u z v w := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hEq :
      ∀ᶠ y in nhds x, ∀ v w : TM y,
        timeDerivAt gt t₀ y v w = -2 * g.ricciAt y v w :=
    eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt
      (gt := gt) (t₀ := t₀) (x := x) hFlowNear
  have h1 :
      covTensor2SecondDerivAt g (timeDerivAt gt t₀) x u v w z =
        covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u v w z := by
    exact covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := timeDerivAt gt t₀)
      (k := negTwoRicciVariationField g) (x := x)
      (hEq.mono fun y hy a b ↦ by
        simpa [g, negTwoRicciVariationField] using hy a b)
      u v w z
  have h2 :
      covTensor2SecondDerivAt g (timeDerivAt gt t₀) x u w v z =
        covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u w v z := by
    exact covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := timeDerivAt gt t₀)
      (k := negTwoRicciVariationField g) (x := x)
      (hEq.mono fun y hy a b ↦ by
        simpa [g, negTwoRicciVariationField] using hy a b)
      u w v z
  have h3 :
      covTensor2SecondDerivAt g (timeDerivAt gt t₀) x u z v w =
        covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u z v w := by
    exact covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := timeDerivAt gt t₀)
      (k := negTwoRicciVariationField g) (x := x)
      (hEq.mono fun y hy a b ↦ by
        simpa [g, negTwoRicciVariationField] using hy a b)
      u z v w
  calc
    2 * g.inner x (covDeltaGammaDerivAt gt t₀ x u v w) z =
      covTensor2SecondDerivAt g (timeDerivAt gt t₀) x u v w z
        + covTensor2SecondDerivAt g (timeDerivAt gt t₀) x u w v z
        - covTensor2SecondDerivAt g (timeDerivAt gt t₀) x u z v w := by
        simpa [g] using
          covDeltaGamma_koszul_secondDerivAt
            (gt := gt) (t₀ := t₀) (x := x)
            hreg hgt hExt hNear hBridge hSecond u v w z
    _ =
      covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u v w z
        + covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u w v z
        - covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u z v w := by
        rw [h1, h2, h3]

/--
The explicit second-covariant-derivative contraction obtained by substituting
the differentiated Koszul identity into both `δΓ` contractions in `deltaRicciAt`.
-/
noncomputable def deltaRicciSecondDerivContractionAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  (∑ i, (1 / 2 : ℝ) *
    (covTensor2SecondDerivAt g h x (b i) u w (sharp i)
      + covTensor2SecondDerivAt g h x (b i) w u (sharp i)
      - covTensor2SecondDerivAt g h x (b i) (sharp i) u w))
    -
  (∑ i, (1 / 2 : ℝ) *
    (covTensor2SecondDerivAt g h x u (b i) w (sharp i)
      + covTensor2SecondDerivAt g h x u w (b i) (sharp i)
      - covTensor2SecondDerivAt g h x u (sharp i) (b i) w))

theorem deltaRicciSecondDerivContractionAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hEq : ∀ᶠ y in nhds x, ∀ v w : TM y, h y v w = k y v w)
    (u w : TM x) :
    deltaRicciSecondDerivContractionAt g h x u w =
      deltaRicciSecondDerivContractionAt g k x u w := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  unfold deltaRicciSecondDerivContractionAt
  change
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g h x (b i) u w (sharp i)
        + covTensor2SecondDerivAt g h x (b i) w u (sharp i)
        - covTensor2SecondDerivAt g h x (b i) (sharp i) u w))
      -
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g h x u (b i) w (sharp i)
        + covTensor2SecondDerivAt g h x u w (b i) (sharp i)
        - covTensor2SecondDerivAt g h x u (sharp i) (b i) w))
      =
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g k x (b i) u w (sharp i)
        + covTensor2SecondDerivAt g k x (b i) w u (sharp i)
        - covTensor2SecondDerivAt g k x (b i) (sharp i) u w))
      -
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g k x u (b i) w (sharp i)
        + covTensor2SecondDerivAt g k x u w (b i) (sharp i)
        - covTensor2SecondDerivAt g k x u (sharp i) (b i) w))
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq (b i) u w (sharp i)]
    rw [covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq (b i) w u (sharp i)]
    rw [covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq (b i) (sharp i) u w]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq u (b i) w (sharp i)]
    rw [covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq u w (b i) (sharp i)]
    rw [covTensor2SecondDerivAt_congr_of_eventuallyEq
      (g := g) (h := h) (k := k) (x := x) hEq u (sharp i) (b i) w]

theorem covTensor2SecondDerivAt_smul_field
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hSecond : CovTensor2DerivExtDifferentiableAt g h x)
    (c : ℝ) (u v p q : TM x) :
    covTensor2SecondDerivAt g (fun y v w ↦ c * h y v w) x u v p q =
      c * covTensor2SecondDerivAt g h x u v p q := by
  unfold covTensor2SecondDerivAt
  have hfun :
      (fun y : M ↦
          covTensor2DerivAt g (fun z v w ↦ c * h z v w) y
            (extend E v y) (extend E p y) (extend E q y)) =
        c • (fun y : M ↦
          covTensor2DerivAt g h y
            (extend E v y) (extend E p y) (extend E q y)) := by
    funext y
    simpa [Pi.smul_apply, smul_eq_mul] using
      covTensor2DerivAt_smul_field
        (g := g) (h := h) (x := y) (hDiff y) c
        (extend E v y) (extend E p y) (extend E q y)
  rw [hfun]
  rw [extDerivFun_const_smul_at (hSecond v p q) c]
  rw [covTensor2DerivAt_smul_field
      (g := g) (h := h) (x := x) (hDiff x) c
      (g.leviCivita (extend E v) x u) p q]
  rw [covTensor2DerivAt_smul_field
      (g := g) (h := h) (x := x) (hDiff x) c
      v (g.leviCivita (extend E p) x u) q]
  rw [covTensor2DerivAt_smul_field
      (g := g) (h := h) (x := x) (hDiff x) c
      v p (g.leviCivita (extend E q) x u)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring_nf

theorem covTensor2SecondDerivAt_negTwoRicciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRicSecond : CovTensor2DerivExtDifferentiableAt g (ricciVariationField g) x)
    (u v w z : TM x) :
    covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u v w z =
      -2 * covTensor2SecondDerivAt g (ricciVariationField g) x u v w z := by
  unfold negTwoRicciVariationField
  simpa [ricciVariationField] using
    covTensor2SecondDerivAt_smul_field
      (g := g) (h := ricciVariationField g) (x := x)
      (fun y ↦ covTensor2ExtDifferentiableAt_ricciVariationField_canonical
        (g := g) y)
      hRicSecond (-2 : ℝ) u v w z

theorem deltaRicciSecondDerivContractionAt_negTwoRicci_eq_neg_two_ricci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRicSecond : CovTensor2DerivExtDifferentiableAt g (ricciVariationField g) x)
    (u w : TM x) :
    deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
      -2 * deltaRicciSecondDerivContractionAt g (ricciVariationField g) x u w := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  unfold deltaRicciSecondDerivContractionAt
  change
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
          (b i) u w (sharp i)
        + covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
          (b i) w u (sharp i)
        - covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
          (b i) (sharp i) u w))
      -
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
          u (b i) w (sharp i)
        + covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
          u w (b i) (sharp i)
        - covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
          u (sharp i) (b i) w))
      =
    -2 * ((∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g (ricciVariationField g) x
          (b i) u w (sharp i)
        + covTensor2SecondDerivAt g (ricciVariationField g) x
          (b i) w u (sharp i)
        - covTensor2SecondDerivAt g (ricciVariationField g) x
          (b i) (sharp i) u w))
      -
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g (ricciVariationField g) x
          u (b i) w (sharp i)
        + covTensor2SecondDerivAt g (ricciVariationField g) x
          u w (b i) (sharp i)
        - covTensor2SecondDerivAt g (ricciVariationField g) x
          u (sharp i) (b i) w)))
  have hdiv :
      (∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
            (b i) u w (sharp i)
          + covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
            (b i) w u (sharp i)
          - covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
            (b i) (sharp i) u w))
        =
      -2 * (∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g (ricciVariationField g) x
            (b i) u w (sharp i)
          + covTensor2SecondDerivAt g (ricciVariationField g) x
            (b i) w u (sharp i)
          - covTensor2SecondDerivAt g (ricciVariationField g) x
            (b i) (sharp i) u w)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [covTensor2SecondDerivAt_negTwoRicciVariationField
      (g := g) (x := x) hRicSecond (b i) u w (sharp i)]
    rw [covTensor2SecondDerivAt_negTwoRicciVariationField
      (g := g) (x := x) hRicSecond (b i) w u (sharp i)]
    rw [covTensor2SecondDerivAt_negTwoRicciVariationField
      (g := g) (x := x) hRicSecond (b i) (sharp i) u w]
    ring
  have hcon :
      (∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
            u (b i) w (sharp i)
          + covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
            u w (b i) (sharp i)
          - covTensor2SecondDerivAt g (negTwoRicciVariationField g) x
            u (sharp i) (b i) w))
        =
      -2 * (∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g (ricciVariationField g) x
            u (b i) w (sharp i)
          + covTensor2SecondDerivAt g (ricciVariationField g) x
            u w (b i) (sharp i)
          - covTensor2SecondDerivAt g (ricciVariationField g) x
            u (sharp i) (b i) w)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [covTensor2SecondDerivAt_negTwoRicciVariationField
      (g := g) (x := x) hRicSecond u (b i) w (sharp i)]
    rw [covTensor2SecondDerivAt_negTwoRicciVariationField
      (g := g) (x := x) hRicSecond u w (b i) (sharp i)]
    rw [covTensor2SecondDerivAt_negTwoRicciVariationField
      (g := g) (x := x) hRicSecond u (sharp i) (b i) w]
    ring
  rw [hdiv, hcon]
  ring

set_option maxHeartbeats 5000000 in
theorem deltaRicciAt_eq_secondDerivContractionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (u w : TM x) :
    deltaRicciAt gt t₀ x u w =
      deltaRicciSecondDerivContractionAt
        (gt t₀) (timeDerivAt gt t₀) x u w := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hdiv :
      (∑ i, b.coord i (covDeltaGammaDerivAt gt t₀ x (b i) u w)) =
        ∑ i, (1 / 2 : ℝ) *
          (covTensor2SecondDerivAt g H x (b i) u w (sharp i)
            + covTensor2SecondDerivAt g H x (b i) w u (sharp i)
            - covTensor2SecondDerivAt g H x (b i) (sharp i) u w) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hcoord :
        b.coord i (covDeltaGammaDerivAt gt t₀ x (b i) u w) =
          g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) u w) (sharp i) := by
      simpa [g, b, sharp] using
        coord_eq_inner_metricDualVectorAt (g := g) (x := x) i
          (covDeltaGammaDerivAt gt t₀ x (b i) u w)
    have hk :=
      covDeltaGamma_koszul_secondDerivAt
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt hNear hBridge hSecond
        (b i) u w (sharp i)
    change
      2 * g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) u w) (sharp i) =
        covTensor2SecondDerivAt g H x (b i) u w (sharp i)
          + covTensor2SecondDerivAt g H x (b i) w u (sharp i)
          - covTensor2SecondDerivAt g H x (b i) (sharp i) u w at hk
    rw [hcoord]
    nlinarith
  have hcon :
      (∑ i, b.coord i (covDeltaGammaDerivAt gt t₀ x u (b i) w)) =
        ∑ i, (1 / 2 : ℝ) *
          (covTensor2SecondDerivAt g H x u (b i) w (sharp i)
            + covTensor2SecondDerivAt g H x u w (b i) (sharp i)
            - covTensor2SecondDerivAt g H x u (sharp i) (b i) w) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hcoord :
        b.coord i (covDeltaGammaDerivAt gt t₀ x u (b i) w) =
          g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) w) (sharp i) := by
      simpa [g, b, sharp] using
        coord_eq_inner_metricDualVectorAt (g := g) (x := x) i
          (covDeltaGammaDerivAt gt t₀ x u (b i) w)
    have hk :=
      covDeltaGamma_koszul_secondDerivAt
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt hNear hBridge hSecond
        u (b i) w (sharp i)
    change
      2 * g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) w) (sharp i) =
        covTensor2SecondDerivAt g H x u (b i) w (sharp i)
          + covTensor2SecondDerivAt g H x u w (b i) (sharp i)
          - covTensor2SecondDerivAt g H x u (sharp i) (b i) w at hk
    rw [hcoord]
    nlinarith
  unfold deltaRicciAt deltaGammaDivergenceAt deltaGammaContractionDerivAt
    deltaRicciSecondDerivContractionAt
  change
    (∑ i, b.coord i (covDeltaGammaDerivAt gt t₀ x (b i) u w))
      - (∑ i, b.coord i (covDeltaGammaDerivAt gt t₀ x u (b i) w)) =
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g H x (b i) u w (sharp i)
        + covTensor2SecondDerivAt g H x (b i) w u (sharp i)
        - covTensor2SecondDerivAt g H x (b i) (sharp i) u w))
      -
    (∑ i, (1 / 2 : ℝ) *
      (covTensor2SecondDerivAt g H x u (b i) w (sharp i)
        + covTensor2SecondDerivAt g H x u w (b i) (sharp i)
        - covTensor2SecondDerivAt g H x u (sharp i) (b i) w))
  rw [hdiv, hcon]

theorem deltaRicciAt_eq_negTwoRicci_secondDerivContractionAt_of_isClosedRicciFlowSolutionAt_near
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hFlowNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (u w : TM x) :
    deltaRicciAt gt t₀ x u w =
      deltaRicciSecondDerivContractionAt
        (gt t₀) (negTwoRicciVariationField (gt t₀)) x u w := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hEq :
      ∀ᶠ y in nhds x, ∀ v w : TM y,
        timeDerivAt gt t₀ y v w = -2 * g.ricciAt y v w :=
    eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt
      (gt := gt) (t₀ := t₀) (x := x) hFlowNear
  rw [deltaRicciAt_eq_secondDerivContractionAt
    (gt := gt) (t₀ := t₀) (x := x)
    hreg hgt hExt hNear hBridge hSecond u w]
  exact deltaRicciSecondDerivContractionAt_congr_of_eventuallyEq
    (g := g) (h := timeDerivAt gt t₀)
    (k := negTwoRicciVariationField g) (x := x)
    (hEq.mono fun y hy a b ↦ by
      simpa [g, negTwoRicciVariationField] using hy a b)
    u w

/--
The rough connection Laplacian of a raw `(0,2)` tensor, written as the metric
trace of `covTensor2SecondDerivAt` over the two derivative slots.
-/
noncomputable def roughTensorLaplacianAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  ∑ i, covTensor2SecondDerivAt g h x (b i) (sharp i) u w

/--
Deprecated correction-history version of the curvature action from M4-prep-1.

This traced the antisymmetric first curvature pair `(bᵢ, ♯bⁱ)`.  The
M4-prep-2 trace check refuted it for the Ricci-evolution target: that
first-pair trace is identically zero and cannot produce the expected Ricci
reaction term.  Keep this definition only as a ledger of the corrected slot
mistake; use `lichnerowiczCurvatureAt` below.
-/
noncomputable def lichnerowiczFirstPairCurvatureAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  ∑ i,
    (h x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (b i)) (extend E (sharp i)) (extend E u) x)
      w
      + h x u
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E (b i)) (extend E (sharp i)) (extend E w) x))

/--
The corrected curvature action part of the Lichnerowicz Laplacian.

This is the mixed Riemann contraction
`Σᵢ h(R(bᵢ,u)w, ♯bⁱ)`, equivalently
`Σᵢⱼ R(bᵢ,u,w,bⱼ) h(♯bⁱ,♯bʲ)`.  It is the slot convention needed for
the Ricci-evolution trace: for `h = Ric`, `ricciQuadraticAt` is exactly
twice this corrected curvature term, so the `-2 Rm·Ric` part of
`lichnerowiczLaplacianAt` cancels the explicit quadratic curvature reaction.
-/
noncomputable def lichnerowiczCurvatureAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  ∑ i,
    h x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (b i)) (extend E u) (extend E w) x)
      (sharp i)

@[simp] theorem lichnerowiczCurvatureAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TM x) :
    lichnerowiczCurvatureAt g
      (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) x u w = 0 := by
  simp [lichnerowiczCurvatureAt]

/--
The Ricci-endomorphism action on a `(0,2)` tensor:
`h(Ric♯ u,w) + h(u,Ric♯ w)`.
-/
noncomputable def ricciActionOnTensorAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u w : TM x) : ℝ :=
  h x (g.ricciEndoAt x u) w + h x u (g.ricciEndoAt x w)

/--
The closed-manifold Lichnerowicz Laplacian on a raw `(0,2)` tensor.

This is intended for symmetric two-tensors; symmetry is deliberately not
baked into the type so it can be reused with the existing raw tensor fields.
The convention mirrors the model definition:
`Δ_L h = Δ_∇ h - 2 Rm·h + Ric·h + h·Ric`.
-/
noncomputable def lichnerowiczLaplacianAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u w : TM x) : ℝ :=
  roughTensorLaplacianAt g h x u w
    - 2 * lichnerowiczCurvatureAt g h x u w
    + ricciActionOnTensorAt g h x u w

/--
The curvature-quadratic Ricci reaction vocabulary for the Ricci tensor
evolution target.  It is a concrete `Rm * Ric` contraction: one curvature
operator slot is traced against a raised basis vector, and the resulting vector
is paired with the Ricci tensor.
-/
noncomputable def ricciQuadraticAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  2 * ∑ i,
    g.ricciAt x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E (b i)) (extend E u) (extend E w) x)
      (sharp i)

theorem ricciQuadraticAt_eq_two_lichnerowiczCurvatureAt_ricciVariationField
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    ricciQuadraticAt g x u w =
      2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w := by
  rfl

/--
Pointwise commutation target for the Ricci second-derivative contraction.

This is the tensor-level Ricci-evolution RHS before it is packaged as a
time-derivative statement.
-/
def RicciSecondDerivCommutationAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ u w : TM x,
    deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
      lichnerowiczLaplacianAt g (ricciVariationField g) x u w
        + ricciQuadraticAt g x u w

/--
Expanded curvature-commutation form before folding the three Lichnerowicz
blocks back into `lichnerowiczLaplacianAt`.
-/
def RicciSecondDerivCurvatureCommutationAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ u w : TM x,
    deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
      roughTensorLaplacianAt g (ricciVariationField g) x u w
        - 2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
        + ricciActionOnTensorAt g (ricciVariationField g) x u w
        + ricciQuadraticAt g x u w

theorem RicciSecondDerivCommutationAt.of_closed_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : ClosedRicciDerivativeExpansionAt g x)
    (hSecond : ∀ u v w z : TM x,
      closedCurvatureCovDerivAt g x v u w z
        + closedCurvatureCovDerivAt g x u w v z
        + closedCurvatureCovDerivAt g x w v u z = 0)
    (hCurvComm : RicciSecondDerivCurvatureCommutationAt g x) :
    RicciSecondDerivCommutationAt g x := by
  intro u w
  have hRicEntry :
      covTensor2DerivAt g (ricciVariationField g) x u w u =
        closedCovRicciDerivAt g x u w u :=
    covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt
      (g := g) (x := x) hRic u w u
  have hFirst :
      closedCovRicciDerivAt g x u w w
        + closedCurvatureDivergenceAt g x w u w
        - closedCovRicciDerivAt g x w u w = 0 :=
    closed_first_contracted_bianchi_of_second_bianchi
      (g := g) (x := x) hSecond u w w
  have hExpanded := hCurvComm u w
  calc
    deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
        roughTensorLaplacianAt g (ricciVariationField g) x u w
          - 2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
          + ricciActionOnTensorAt g (ricciVariationField g) x u w
          + ricciQuadraticAt g x u w := hExpanded
    _ = lichnerowiczLaplacianAt g (ricciVariationField g) x u w
          + ricciQuadraticAt g x u w := by
        rw [lichnerowiczLaplacianAt]

/--
Antisymmetrizing the two differentiated slots of `covTensor2SecondDerivAt`
removes the connection correction in the differentiated-vector slot.  The
remaining terms are the raw antisymmetrized derivative of `covTensor2DerivAt`
and the two tensor-slot correction blocks.
-/
theorem covTensor2SecondDerivAt_antisymm_expansion
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ} (x : M)
    (u v p q : TM x) :
    covTensor2SecondDerivAt g h x u v p q
        - covTensor2SecondDerivAt g h x v u p q =
      (extDerivFun
          (fun y : M ↦ covTensor2DerivAt g h y
            (extend E v y) (extend E p y) (extend E q y)) x u
        - extDerivFun
          (fun y : M ↦ covTensor2DerivAt g h y
            (extend E u y) (extend E p y) (extend E q y)) x v)
        - (covTensor2DerivAt g h x v
            (g.leviCivita (extend E p) x u) q
          - covTensor2DerivAt g h x u
            (g.leviCivita (extend E p) x v) q)
        - (covTensor2DerivAt g h x v p
            (g.leviCivita (extend E q) x u)
          - covTensor2DerivAt g h x u p
            (g.leviCivita (extend E q) x v)) := by
  have huv :
      g.leviCivita (extend E v) x u =
        g.leviCivita (extend E u) x v :=
    closedLeviCivita_extend_symm_at (g := g) (x := x) v u
  unfold covTensor2SecondDerivAt
  rw [huv]
  ring

/--
Pure scalar-entry Schwarz cancellation for the `(0,2)` tensor commutator.
This is the block before the two tensor-slot connection-correction families
are folded into curvature.
-/
theorem covTensor2SecondDerivAt_pure_schwarz_cancel
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hC2 : CovTensor2ExtContMDiffAt h x 2)
    (u v p q : TM x) :
    extDerivFun
          (fun y : M ↦
            extDerivFun
              (fun z : M ↦ h z (extend E p z) (extend E q z)) y
              (extend E v y)) x u
      - extDerivFun
          (fun y : M ↦
            extDerivFun
              (fun z : M ↦ h z (extend E p z) (extend E q z)) y
              (extend E u y)) x v = 0 := by
  let f : M → ℝ := fun z : M ↦ h z (extend E p z) (extend E q z)
  have hcomm :
      extDerivFun (fun y : M ↦ extDerivFun f y (extend E v y)) x u
          - extDerivFun f x (g.leviCivita (extend E v) x u) =
        extDerivFun (fun y : M ↦ extDerivFun f y (extend E u y)) x v
          - extDerivFun f x (g.leviCivita (extend E u) x v) := by
    simpa [f] using
      extDerivFun_extDerivFun_extend_corrected_symm
        (g := g) (f := f) (x := x) (hC2 p q) u v
  have hΓ :
      g.leviCivita (extend E v) x u =
        g.leviCivita (extend E u) x v :=
    closedLeviCivita_extend_symm_at (g := g) (x := x) v u
  rw [hΓ] at hcomm
  linarith

/--
Curvature-action side of the `(0,2)` tensor Ricci identity in the closed
`covTensor2SecondDerivAt` API.

The intended next commutator is
`∇²_{u,v} h - ∇²_{v,u} h = covTensor2SecondDerivCurvatureActionAt g h ...`.
-/
noncomputable def covTensor2SecondDerivCurvatureActionAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (u v p q : TM x) : ℝ :=
  -h x
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E u) (extend E v) (extend E p) x) q
    - h x p
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E u) (extend E v) (extend E q) x)

/--
The curvature-action obstruction is antisymmetric in the two differentiated
directions for any bilinear `(0,2)` tensor field.
-/
theorem covTensor2SecondDerivCurvatureActionAt_antisymm
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ}
    (hLeft : Tensor2SMulLeft h) (hRight : Tensor2SMulRight h)
    (x : M) (u v p q : TM x) :
    covTensor2SecondDerivCurvatureActionAt g h x u v p q =
      -covTensor2SecondDerivCurvatureActionAt g h x v u p q := by
  let Ruvp : TM x :=
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E u) (extend E v) (extend E p) x
  let Ruvq : TM x :=
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E u) (extend E v) (extend E q) x
  have hp :
      h x
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E v) (extend E u) (extend E p) x) q =
        -h x Ruvp q := by
    rw [CovariantDerivative.curvatureOp_antisymm_apply]
    simpa [Ruvp] using hLeft x (-1 : ℝ) Ruvp q
  have hq :
      h x p
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E v) (extend E u) (extend E q) x) =
        -h x p Ruvq := by
    rw [CovariantDerivative.curvatureOp_antisymm_apply]
    simpa [Ruvq] using hRight x (-1 : ℝ) p Ruvq
  unfold covTensor2SecondDerivCurvatureActionAt
  rw [hp, hq]
  ring

/--
Ricci-field specialization of the closed curvature-action antisymmetry needed
by the tensor Ricci-identity discharge.
-/
theorem covTensor2SecondDerivCurvatureActionAt_ricciVariationField_antisymm
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v p q : TM x) :
    covTensor2SecondDerivCurvatureActionAt g (ricciVariationField g) x u v p q =
      -covTensor2SecondDerivCurvatureActionAt g (ricciVariationField g) x v u p q :=
  covTensor2SecondDerivCurvatureActionAt_antisymm
    (g := g)
    (hLeft := tensor2SMulLeft_ricciVariationField g)
    (hRight := tensor2SMulRight_ricciVariationField g)
    x u v p q

theorem lichnerowiczCurvatureAt_ricciQuadraticAt_trace_cancellation
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j);
      -2 * (∑ j, lichnerowiczCurvatureAt g (ricciVariationField g) x
          (b j) (sharp j))
        + (∑ j, ricciQuadraticAt g x (b j) (sharp j))) = 0 := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hsum :
      (∑ j, ricciQuadraticAt g x (b j) (sharp j)) =
        ∑ j, 2 * lichnerowiczCurvatureAt g (ricciVariationField g) x
          (b j) (sharp j) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact ricciQuadraticAt_eq_two_lichnerowiczCurvatureAt_ricciVariationField
      (g := g) (x := x) (u := b j) (w := sharp j)
  change
    -2 * (∑ j, lichnerowiczCurvatureAt g (ricciVariationField g) x
        (b j) (sharp j))
      + (∑ j, ricciQuadraticAt g x (b j) (sharp j)) = 0
  rw [hsum, ← Finset.mul_sum]
  ring

/--
Trace identity obligation for the rough Laplacian on the Ricci field:
`tr_g(Δ_∇ Ric) = ΔR`.
-/
def RoughTensorLaplacianRicciTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    let b := Module.finBasis ℝ (TM x)
    let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
      fun j ↦ metricDualVectorAt g x (b.coord j);
    ∑ j, roughTensorLaplacianAt g (ricciVariationField g) x
      (b j) (sharp j))
    = g.laplacianAt (fun y ↦ g.scalarAt y) x

/--
Trace identity obligation for the Ricci-endomorphism action on the Ricci field:
`tr_g(Ric·Ric + Ric·Ric) = 2 |Ric|²`.
-/
def RicciActionRicciTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    let b := Module.finBasis ℝ (TM x)
    let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
      fun j ↦ metricDualVectorAt g x (b.coord j);
    ∑ j, ricciActionOnTensorAt g (ricciVariationField g) x
      (b j) (sharp j))
    = 2 * g.ricciNormSqAt x

set_option maxHeartbeats 5000000 in
theorem ricciActionRicciTraceAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    RicciActionRicciTraceAt g x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  let A : TM x →ₗ[ℝ] TM x := g.ricciEndoAt x
  have hleft : ∀ j : Fin (Module.finrank ℝ (TM x)),
      g.ricciAt x (A (b j)) (sharp j) =
        b.coord j ((A ∘ₗ A) (b j)) := by
    intro j
    calc
      g.ricciAt x (A (b j)) (sharp j) =
          g.inner x (A (A (b j))) (sharp j) := by
            rw [g.inner_ricciEndoAt]
      _ = b.coord j ((A ∘ₗ A) (b j)) := by
            rw [LinearMap.comp_apply, coord_eq_inner_metricDualVectorAt]
  have hright : ∀ j : Fin (Module.finrank ℝ (TM x)),
      g.ricciAt x (b j) (A (sharp j)) =
        b.coord j ((A ∘ₗ A) (b j)) := by
    intro j
    calc
      g.ricciAt x (b j) (A (sharp j)) =
          g.inner x (A (b j)) (A (sharp j)) := by
            rw [g.inner_ricciEndoAt]
      _ = g.inner x (A (A (b j))) (sharp j) := by
            exact (g.ricciEndoAt_selfAdjoint x (A (b j)) (sharp j)).symm
      _ = b.coord j ((A ∘ₗ A) (b j)) := by
            rw [LinearMap.comp_apply, coord_eq_inner_metricDualVectorAt]
  have hsum :
      (∑ j, ricciActionOnTensorAt g (ricciVariationField g) x
        (b j) (sharp j)) =
        ∑ j, 2 * b.coord j ((A ∘ₗ A) (b j)) := by
    refine Finset.sum_congr rfl fun j _hj ↦ ?_
    simp [ricciActionOnTensorAt, ricciVariationField, A, hleft j, hright j]
    ring
  rw [RicciActionRicciTraceAt]
  change
    (∑ j, ricciActionOnTensorAt g (ricciVariationField g) x
      (b j) (sharp j)) = 2 * g.ricciNormSqAt x
  rw [hsum, g.ricciNormSqAt_eq_trace,
    LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  have hmatrix :
      (∑ i, ((LinearMap.toMatrix b b)
        (g.ricciEndoAt x ∘ₗ g.ricciEndoAt x)).diag i) =
        ∑ i, b.coord i ((A ∘ₗ A) (b i)) := by
    refine Finset.sum_congr rfl fun i _hi ↦ ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [hmatrix]
  rw [← Finset.mul_sum]

/--
Regularity package for the Ricci-evolution trace route.

The first-order Ricci field differentiability is already canonical; the
entrywise `C²` package is the honest remaining regularity expected by the
rough-Laplacian trace identity.
-/
def RicciEvolutionTraceRegularityAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  CovTensor2ExtDifferentiableAt (ricciVariationField g) x ∧
    TraceMetricVariationEntriesExtContMDiffAt g (ricciVariationField g) x 2

/--
Full second-regularity class used by the Ricci-evolution trace consistency
route.  Besides the Gram-route entry `C²` trace regularity, the rough Laplacian
trace needs differentiability of the covariant derivative of the Ricci field.
-/
def RicciEvolutionTraceSecondRegularityAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  TraceMetricVariationEntriesExtContMDiffAt g (ricciVariationField g) x 2 ∧
    CovTensor2DerivExtDifferentiableAt g (ricciVariationField g) x

theorem ricciEvolutionTraceRegularityAt_firstOrder
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    CovTensor2ExtDifferentiableAt (ricciVariationField g) x :=
  covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x

theorem roughTensorLaplacianRicciTraceAt_of_traceSecondRegularity
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hReg : RicciEvolutionTraceSecondRegularityAt g x) :
    RoughTensorLaplacianRicciTraceAt g x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  let H : ∀ y : M, TM y → TM y → ℝ := ricciVariationField g
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  rcases hReg with ⟨hEntries, hSecond⟩
  have hTrace₂ : ContMDiffAt I 𝓘(ℝ) 2 f x :=
    traceMetricVariationAt_contMDiffAt_two_of_entries
      (g := g) (h := H) (x := x) hEntries
      (ricciVariationBilinForm g)
      (by intro y p q; rfl)
  have hgrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    simpa [f] using g.mdifferentiableAt_gradient hTrace₂
  have hHslot : ∀ i : Fin (Module.finrank ℝ (TM x)),
      (∑ j, covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j)) =
        g.hessianAt f x (b i) (sharp i) := by
    intro i
    simpa [H, f, b, sharp] using
      covTensor2SecondDerivAt_Hslot_trace_eq_hessianAt
        (g := g) (H := H) (x := x)
        (fun y ↦ covTensor2ExtDifferentiableAt_ricciVariationField_canonical
          (g := g) (x := y))
        hSecond
        (tensor2AddLeft_ricciVariationField g)
        (tensor2SMulLeft_ricciVariationField g)
        (tensor2AddRight_ricciVariationField g)
        (tensor2SMulRight_ricciVariationField g)
        (ricciVariationBilinForm g)
        (by intro y p q; rfl)
        (by simpa [f, H] using hgrad)
        (b i) (sharp i)
  have hrough :
      (∑ j, roughTensorLaplacianAt g H x (b j) (sharp j)) =
        ∑ i, g.hessianAt f x (b i) (sharp i) := by
    unfold roughTensorLaplacianAt
    change
      (∑ j, ∑ i,
        covTensor2SecondDerivAt g H x (b i) (sharp i) (b j) (sharp j)) =
        ∑ i, g.hessianAt f x (b i) (sharp i)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _hi ↦ hHslot i
  have hlap :
      g.laplacianAt f x =
        ∑ i, g.hessianAt f x (b i) (sharp i) := by
    simpa [f, b, sharp] using
      laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x)
  have hf_scalar : f = fun y : M ↦ g.scalarAt y := by
    funext y
    simpa [f, H] using traceMetricVariationAt_ricci (g := g) y
  rw [RoughTensorLaplacianRicciTraceAt]
  change
    (∑ j, roughTensorLaplacianAt g H x (b j) (sharp j)) =
      g.laplacianAt (fun y ↦ g.scalarAt y) x
  rw [hrough, ← hlap, hf_scalar]

def RicciEvolutionTraceIdentitiesAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  RoughTensorLaplacianRicciTraceAt g x ∧
    RicciActionRicciTraceAt g x

theorem ricciEvolutionTraceIdentitiesAt_of_traceSecondRegularity
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hReg : RicciEvolutionTraceSecondRegularityAt g x) :
    RicciEvolutionTraceIdentitiesAt g x :=
  ⟨roughTensorLaplacianRicciTraceAt_of_traceSecondRegularity
      (g := g) (x := x) hReg,
    ricciActionRicciTraceAt (g := g) (x := x)⟩

theorem ricciEvolution_rhs_trace_eq_hamilton_rhs
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hTrace : RicciEvolutionTraceIdentitiesAt g x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j);
      ∑ j,
        (lichnerowiczLaplacianAt g (ricciVariationField g) x
            (b j) (sharp j)
          + ricciQuadraticAt g x (b j) (sharp j)))
      =
        g.laplacianAt (fun y ↦ g.scalarAt y) x +
          2 * g.ricciNormSqAt x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  rcases hTrace with ⟨hRough, hAction⟩
  have hRough' :
      (∑ j, roughTensorLaplacianAt g (ricciVariationField g) x
        (b j) (sharp j)) =
        g.laplacianAt (fun y ↦ g.scalarAt y) x := by
    simpa [RoughTensorLaplacianRicciTraceAt, b, sharp] using hRough
  have hAction' :
      (∑ j, ricciActionOnTensorAt g (ricciVariationField g) x
        (b j) (sharp j)) =
        2 * g.ricciNormSqAt x := by
    simpa [RicciActionRicciTraceAt, b, sharp] using hAction
  have hCancel :
      -2 * (∑ j, lichnerowiczCurvatureAt g (ricciVariationField g) x
        (b j) (sharp j))
        + (∑ j, ricciQuadraticAt g x (b j) (sharp j)) = 0 := by
    simpa [b, sharp] using
      lichnerowiczCurvatureAt_ricciQuadraticAt_trace_cancellation
        (g := g) (x := x)
  have hDecomp :
      (∑ j,
        (lichnerowiczLaplacianAt g (ricciVariationField g) x
            (b j) (sharp j)
          + ricciQuadraticAt g x (b j) (sharp j))) =
        (∑ j, roughTensorLaplacianAt g (ricciVariationField g) x
          (b j) (sharp j))
          - 2 * (∑ j, lichnerowiczCurvatureAt g
            (ricciVariationField g) x (b j) (sharp j))
          + (∑ j, ricciActionOnTensorAt g (ricciVariationField g) x
            (b j) (sharp j))
          + (∑ j, ricciQuadraticAt g x (b j) (sharp j)) := by
    simp only [lichnerowiczLaplacianAt]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  change
    (∑ j,
      (lichnerowiczLaplacianAt g (ricciVariationField g) x
          (b j) (sharp j)
        + ricciQuadraticAt g x (b j) (sharp j))) =
      g.laplacianAt (fun y ↦ g.scalarAt y) x +
        2 * g.ricciNormSqAt x
  rw [hDecomp, hRough', hAction']
  linarith

theorem ricciEvolution_rhs_trace_eq_hamilton_rhs_of_traceSecondRegularity
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hReg : RicciEvolutionTraceSecondRegularityAt g x) :
    (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j);
      ∑ j,
        (lichnerowiczLaplacianAt g (ricciVariationField g) x
            (b j) (sharp j)
          + ricciQuadraticAt g x (b j) (sharp j)))
      =
        g.laplacianAt (fun y ↦ g.scalarAt y) x +
          2 * g.ricciNormSqAt x :=
  ricciEvolution_rhs_trace_eq_hamilton_rhs
    (g := g) (x := x)
    (ricciEvolutionTraceIdentitiesAt_of_traceSecondRegularity
      (g := g) (x := x) hReg)

/--
Target statement for the closed Ricci-tensor evolution equation under Ricci
flow.

This is a statement-layer target only: no theorem below claims the target from
`IsClosedRicciFlowSolutionAt`.  The scalar trace of this target now matches the
already-proved Hamilton scalar evolution statement under the honest
`RicciEvolutionTraceSecondRegularityAt` class.  The remaining content for
deriving this Prop from Ricci flow is the pointwise Ricci-identity commutation
campaign producing the target equation itself.
-/
def SatisfiesRicciEvolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∀ u w : TM x,
    HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
      (lichnerowiczLaplacianAt
          (gt t₀) (ricciVariationField (gt t₀)) x u w
        + ricciQuadraticAt (gt t₀) x u w) t₀

@[simp] theorem satisfiesRicciEvolutionAt_iff
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    SatisfiesRicciEvolutionAt gt t₀ x ↔
      ∀ u w : TM x,
        HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
          (lichnerowiczLaplacianAt
              (gt t₀) (ricciVariationField (gt t₀)) x u w
            + ricciQuadraticAt (gt t₀) x u w) t₀ :=
  Iff.rfl

theorem satisfiesRicciEvolutionAt_of_secondDerivCommutation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hDeltaRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciSecondDerivContractionAt
          (gt t₀) (negTwoRicciVariationField (gt t₀)) x u w) t₀)
    (hComm : RicciSecondDerivCommutationAt (gt t₀) x) :
    SatisfiesRicciEvolutionAt gt t₀ x := by
  intro u w
  simpa [SatisfiesRicciEvolutionAt, hComm u w] using hDeltaRic u w

/--
Exact divergence assembly for the first `δΓ` contraction:
the divergence of the inner-trace one-form gives
`div div h - 1/2 Δ tr h`.
-/
def DeltaGammaDivergenceTraceAssemblyAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ∑ j, deltaGammaDivergenceAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
      (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
    =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (1 / 2 : ℝ) * (gt t₀).laplacianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x

/--
Exact divergence assembly for the second `δΓ` contraction:
the trace derivative contributes the remaining `1/2 Δ tr h`.
-/
def DeltaGammaContractionTraceAssemblyAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ∑ j, deltaGammaContractionDerivAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
      (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
    =
      (1 / 2 : ℝ) * (gt t₀).laplacianAt
        (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x

/--
Hessian-trace form of `DeltaGammaDivergenceTraceAssemblyAt`.

This isolates the remaining second-derivative content from the purely
linear-algebraic recognition of the Laplacian as the raised Hessian trace.
-/
def DeltaGammaDivergenceTraceHessianAssemblyAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ∑ j, deltaGammaDivergenceAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
      (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
    =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (1 / 2 : ℝ) *
          (letI : FiniteDimensional ℝ (TM x) :=
            inferInstanceAs (FiniteDimensional ℝ E)
          ∑ j, (gt t₀).hessianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
            ((Module.finBasis ℝ (TM x)) j)
            (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))

/--
Hessian-trace form of `DeltaGammaContractionTraceAssemblyAt`.

The remaining proof obligation is the second-derivative trace identity for the
`δΓ` contraction; the conversion from Hessian trace to `laplacianAt` is
separate and already proved by `laplacianAt_eq_sum_hessianAt`.
-/
def DeltaGammaContractionTraceHessianAssemblyAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ∑ j, deltaGammaContractionDerivAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
      (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
    =
      (1 / 2 : ℝ) *
        (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        ∑ j, (gt t₀).hessianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
          ((Module.finBasis ℝ (TM x)) j)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))

/--
Second-order bridge for the first-slot `δΓ` trace form.

The first-order theorem
`deltaGamma_firstSlot_trace_eq_of_covTensor2ExtDifferentiableAt` identifies
`Σᵢ eⁱ(δΓ(eᵢ,w))` with `1/2 d(tr_g h)(w)`.  This predicate is the honest
remaining field-derivative statement: the covariant derivative represented by
`deltaGammaContractionDerivAt` is the Hessian of that scalar trace.
-/
def DeltaGammaContractionTraceHessianDerivativeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ u w : TM x,
    deltaGammaContractionDerivAt gt t₀ x u w =
      (1 / 2 : ℝ) * (gt t₀).hessianAt
        (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x u w

/--
Second-order bridge for the divergence of the lower-slot `δΓ` trace.

This is the field-derivative form of
`deltaGamma_innerTrace_eq_of_covTensor2ExtDifferentiableAt`: after
differentiating the inner-trace one-form and taking the raised metric trace,
the `tensorDivergenceOneFormAt` part gives the explicit double divergence and
the scalar trace part gives the Hessian trace.
-/
def DeltaGammaDivergenceTraceInnerHessianDerivativeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ∑ j, deltaGammaDivergenceAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
      (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
    =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j,
        (extDerivFun
            (fun y : M ↦ tensorDivergenceOneFormAt g H y
              (extend E (b j) y)) x (sharp j)
          - tensorDivergenceOneFormAt g H x
            (g.leviCivita (extend E (b j)) x (sharp j))))
      - (1 / 2 : ℝ) *
        (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        ∑ j, (gt t₀).hessianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
          ((Module.finBasis ℝ (TM x)) j)
          (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))

theorem deltaGammaContractionTraceHessianDerivativeAt_of_firstSlotTraceField
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hField : DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x)
    (hHess : DeltaGammaFirstSlotTraceFieldHessianAt gt t₀ x) :
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x := by
  intro u w
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  have hField' :
      deltaGammaContractionDerivAt gt t₀ x u w =
        extDerivFun
            (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
            x u
          - deltaGammaFirstSlotTraceFieldAt gt t₀ x
            (g.leviCivita (extend E w) x u) := by
    simpa [DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt, g] using hField u w
  have hHess' :
        extDerivFun
            (fun y : M ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y))
            x u
          - deltaGammaFirstSlotTraceFieldAt gt t₀ x
            (g.leviCivita (extend E w) x u)
      =
        (1 / 2 : ℝ) * g.hessianAt f x u w := by
    simpa [DeltaGammaFirstSlotTraceFieldHessianAt, g, H, f] using hHess u w
  rw [hField', hHess']

theorem deltaGammaContractionTraceHessianDerivativeAt_of_firstSlot_trace_extSecond
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hField : DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hTrace₂ :
      TraceMetricVariationExtSecondDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x :=
  deltaGammaContractionTraceHessianDerivativeAt_of_firstSlotTraceField hField
    (deltaGammaFirstSlotTraceFieldHessianAt_of_trace_extSecond
      (gt := gt) (t₀ := t₀) (x := x)
      hreg hgt hExt hCovDiff hNear hTrace₂ hgrad)

theorem deltaGammaContractionTraceHessianDerivativeAt_of_firstSlot_entries_contMDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hField : DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hEntries : TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x := by
  have hOld :=
    timeVariationTraceEntriesExtContMDiffAt_two_old_regularities
      (gt := gt) (t₀ := t₀) (x := x) hEntries
  exact
    deltaGammaContractionTraceHessianDerivativeAt_of_firstSlot_trace_extSecond
      (gt := gt) (t₀ := t₀) (x := x)
      hField hreg hgt hExt hOld.1 hNear
      (traceMetricVariationExtSecondDifferentiableAt_timeDeriv_of_entries_contMDiffAt
        (gt := gt) (t₀ := t₀) (x := x) hgt hEntries)
      hgrad

theorem deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_trace_extSecond
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hCovDiff : CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) x)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hTrace₂ :
      TraceMetricVariationExtSecondDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x :=
  deltaGammaContractionTraceHessianDerivativeAt_of_firstSlot_trace_extSecond
    (gt := gt) (t₀ := t₀) (x := x)
    (deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_of_entryBridge
      (gt := gt) (t₀ := t₀) (x := x) hreg hBridge)
    hreg hgt hExt hCovDiff hNear hTrace₂ hgrad

theorem deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_entries_contMDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hEntries : TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x :=
  deltaGammaContractionTraceHessianDerivativeAt_of_firstSlot_entries_contMDiffAt
    (gt := gt) (t₀ := t₀) (x := x)
    (deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_of_entryBridge
      (gt := gt) (t₀ := t₀) (x := x) hreg hBridge)
    hreg hgt hExt hNear hEntries hgrad

/--
Final trace-Hessian route with the scalar-entry bridge discharged from the
`δΓ` field differentiability product rule.
-/
theorem deltaGammaContractionTraceHessianDerivativeAt_of_deltaGammaFieldMDifferentiableAt_entries_contMDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hδ : DeltaGammaFieldMDifferentiableAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hEntries : TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x :=
  deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_entries_contMDiffAt
    (gt := gt) (t₀ := t₀) (x := x)
    (hBridge :=
      deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt
        (gt := gt) (t₀ := t₀) (x := x) hδ)
    hreg hgt hExt hNear hEntries hgrad

theorem deltaGammaDivergenceTraceInnerHessianDerivativeAt_of_innerTraceField
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hField : DeltaGammaInnerTraceFieldCovariantDerivativeAt gt t₀ x) :
    DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  let A : Fin (Module.finrank ℝ (TM x)) → ℝ := fun j ↦
    extDerivFun
        (fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E (b j) y))
        x (sharp j)
      - tensorDivergenceOneFormAt g H x
        (g.leviCivita (extend E (b j)) x (sharp j))
  let B : Fin (Module.finrank ℝ (TM x)) → ℝ := fun j ↦
    g.hessianAt f x (b j) (sharp j)
  have hsum :
      (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
        ∑ j, (A j - (1 / 2 : ℝ) * B j) := by
    refine Finset.sum_congr rfl fun j _hj ↦ ?_
    simpa [DeltaGammaInnerTraceFieldCovariantDerivativeAt, g, H, f, b, sharp, A, B]
      using hField (sharp j) (b j)
  change (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
    (∑ j, A j) - (1 / 2 : ℝ) * ∑ j, B j
  rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem deltaGammaContractionTraceHessianDerivativeAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    DeltaGammaContractionTraceHessianDerivativeAt (fun _ : ℝ ↦ g) t₀ x := by
  intro u w
  have hH :
      timeDerivAt (fun _ : ℝ ↦ g) t₀ =
        (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
    funext y v w
    simp
  have htrace :
      (fun y : M ↦
        traceMetricVariationAt g (timeDerivAt (fun _ : ℝ ↦ g) t₀) y) =
        fun _ : M ↦ (0 : ℝ) := by
    funext y
    simp [hH]
  change deltaGammaContractionDerivAt (fun _ : ℝ ↦ g) t₀ x u w =
    (1 / 2 : ℝ) *
      g.hessianAt
        (fun y : M ↦
          traceMetricVariationAt g (timeDerivAt (fun _ : ℝ ↦ g) t₀) y) x u w
  rw [deltaGammaContractionDerivAt_const, htrace,
    ClosedSmoothRiemannianMetric.hessianAt_const]
  ring

theorem deltaGammaDivergenceTraceInnerHessianDerivativeAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    DeltaGammaDivergenceTraceInnerHessianDerivativeAt (fun _ : ℝ ↦ g) t₀ x := by
  have hH :
      timeDerivAt (fun _ : ℝ ↦ g) t₀ =
        (fun y : M ↦ fun _ _ : TM y ↦ (0 : ℝ)) := by
    funext y v w
    simp
  simp [DeltaGammaDivergenceTraceInnerHessianDerivativeAt, hH,
    extDerivFun_zero_at, ClosedSmoothRiemannianMetric.hessianAt_const]

set_option maxHeartbeats 5000000 in
/-- The closed double divergence is the `T2` second-derivative double trace. -/
theorem tensorDoubleDivergenceAt_eq_sum_sum_positive_T2
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x) :
    tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let b := Module.finBasis ℝ (TM x)
      let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
        fun j ↦ metricDualVectorAt g x (b.coord j)
      ∑ j, ∑ i,
        covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hHAddL : Tensor2AddLeft H := tensor2AddLeft_timeDerivAt hgt
  have hHSMulL : Tensor2SMulLeft H := tensor2SMulLeft_timeDerivAt hgt
  have hHAddR : Tensor2AddRight H := tensor2AddRight_timeDerivAt hgt
  have hHSMulR : Tensor2SMulRight H := tensor2SMulRight_timeDerivAt hgt
  have hDivTrace :
      tensorDoubleDivergenceAt g H x =
        ∑ j, ∑ i,
          covTensor2SecondDerivAt g H x (sharp j) (b i) (sharp i) (b j) := by
    unfold tensorDoubleDivergenceAt
    change
      (∑ j,
        (extDerivFun
            (fun y : M ↦ tensorDivergenceOneFormAt g H y
              (extend E (b j) y)) x (sharp j)
          - tensorDivergenceOneFormAt g H x
            (g.leviCivita (extend E (b j)) x (sharp j)))) =
        ∑ j, ∑ i,
          covTensor2SecondDerivAt g H x (sharp j) (b i) (sharp i) (b j)
    refine Finset.sum_congr rfl fun j _hj ↦ ?_
    symm
    simpa [g, H, b, sharp] using
      covTensor2SecondDerivAt_timeDeriv_divergence_trace_eq
        (gt := gt) (t₀ := t₀) (x := x)
        hgt hCovDiff hSecond (sharp j) (b j)
  have hOuterSwap :
      (∑ j, ∑ i,
          covTensor2SecondDerivAt g H x (sharp j) (b i) (sharp i) (b j))
        =
        ∑ j, ∑ i,
          covTensor2SecondDerivAt g H x (b j) (b i) (sharp i) (sharp j) := by
    exact sum_metricDualVectorAt_contraction_swap
      (g := g) (x := x)
      (F := fun a q ↦
        ∑ i, covTensor2SecondDerivAt g H x a (b i) (sharp i) q)
      (fun a₁ a₂ q ↦ by
        dsimp only
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _hi ↦ ?_
        exact covTensor2SecondDerivAt_add_outer
          (g := g) (h := H) (x := x)
          (hCovDiff x) hHAddL hHAddR a₁ a₂ (b i) (sharp i) q)
      (fun c a q ↦ by
        dsimp only
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _hi ↦ ?_
        exact covTensor2SecondDerivAt_smul_outer
          (g := g) (h := H) (x := x)
          (hCovDiff x) hHSMulL hHSMulR c a (b i) (sharp i) q)
      (fun a q₁ q₂ ↦ by
        dsimp only
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _hi ↦ ?_
        exact covTensor2SecondDerivAt_add_right
          (g := g) (h := H) (x := x)
          hSecond hCovDiff hHAddR a (b i) (sharp i) q₁ q₂)
      (fun c a q ↦ by
        dsimp only
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _hi ↦ ?_
        exact covTensor2SecondDerivAt_smul_right
          (g := g) (h := H) (x := x)
          hSecond hCovDiff hHSMulR c a (b i) (sharp i) q)
  have hInnerSwap :
      (∑ j, ∑ i,
          covTensor2SecondDerivAt g H x (b j) (b i) (sharp i) (sharp j))
        =
        ∑ j, ∑ i,
          covTensor2SecondDerivAt g H x (b j) (sharp i) (b i) (sharp j) := by
    refine Finset.sum_congr rfl fun j _hj ↦ ?_
    have hswap := sum_metricDualVectorAt_contraction_swap
      (g := g) (x := x)
      (F := fun a p ↦ covTensor2SecondDerivAt g H x (b j) a p (sharp j))
      (fun a₁ a₂ p ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_add_inner
          (g := g) (h := H) (x := x)
          hSecond hHAddL hHAddR (b j) a₁ a₂ p (sharp j))
      (fun c a p ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_smul_inner
          (g := g) (h := H) (x := x)
          hSecond hHSMulL hHSMulR c (b j) a p (sharp j))
      (fun a p₁ p₂ ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_add_left
          (g := g) (h := H) (x := x)
          hSecond hCovDiff hHAddL (b j) a p₁ p₂ (sharp j))
      (fun c a p ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_smul_left
          (g := g) (h := H) (x := x)
          hSecond hCovDiff hHSMulL c (b j) a p (sharp j))
    simpa [b, sharp] using hswap.symm
  rw [hDivTrace, hOuterSwap, hInnerSwap]
  rw [Finset.sum_comm]

set_option maxHeartbeats 5000000 in
/-- The positive `(T1 + T2)` block is the double divergence. -/
theorem deltaGammaDivergenceTraceSecondDerivPositiveBlockAt_eq_tensorDoubleDivergenceAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x) :
    deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
      (gt t₀) (timeDerivAt gt t₀) x =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hHAddL : Tensor2AddLeft H := tensor2AddLeft_timeDerivAt hgt
  have hHSMulL : Tensor2SMulLeft H := tensor2SMulLeft_timeDerivAt hgt
  have hHAddR : Tensor2AddRight H := tensor2AddRight_timeDerivAt hgt
  have hHSMulR : Tensor2SMulRight H := tensor2SMulRight_timeDerivAt hgt
  let T1 : ℝ := ∑ j, ∑ i,
    covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
  let T2 : ℝ := ∑ j, ∑ i,
    covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)
  have hT1eqT2 : T1 = T2 := by
    dsimp [T1, T2]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _hi ↦ ?_
    have hswap := sum_metricDualVectorAt_contraction_swap
      (g := g) (x := x)
      (F := fun a p ↦ covTensor2SecondDerivAt g H x (b i) a p (sharp i))
      (fun a₁ a₂ p ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_add_inner
          (g := g) (h := H) (x := x)
          hSecond hHAddL hHAddR (b i) a₁ a₂ p (sharp i))
      (fun c a p ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_smul_inner
          (g := g) (h := H) (x := x)
          hSecond hHSMulL hHSMulR c (b i) a p (sharp i))
      (fun a p₁ p₂ ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_add_left
          (g := g) (h := H) (x := x)
          hSecond hCovDiff hHAddL (b i) a p₁ p₂ (sharp i))
      (fun c a p ↦ by
        dsimp only
        exact covTensor2SecondDerivAt_smul_left
          (g := g) (h := H) (x := x)
          hSecond hCovDiff hHSMulL c (b i) a p (sharp i))
    simpa [b, sharp] using hswap.symm
  have hPositive :
      deltaGammaDivergenceTraceSecondDerivPositiveBlockAt g H x = T2 := by
    unfold deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
    change
      (∑ j, ∑ i, (1 / 2 : ℝ) *
        (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
          + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)))
        = T2
    have hsplit :
        (∑ j, ∑ i, (1 / 2 : ℝ) *
          (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
            + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)))
          =
          (1 / 2 : ℝ) * T1 + (1 / 2 : ℝ) * T2 := by
      dsimp [T1, T2]
      calc
        (∑ j, ∑ i, (1 / 2 : ℝ) *
          (covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i)
            + covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)))
            =
            ∑ j,
              ((1 / 2 : ℝ) *
                  (∑ i,
                    covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i))
                + (1 / 2 : ℝ) *
                  (∑ i,
                    covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i))) := by
              refine Finset.sum_congr rfl fun j _hj ↦ ?_
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _hi ↦ ?_
              ring
        _ =
            (1 / 2 : ℝ) *
                (∑ j, ∑ i,
                  covTensor2SecondDerivAt g H x (b i) (b j) (sharp j) (sharp i))
              + (1 / 2 : ℝ) *
                (∑ j, ∑ i,
                  covTensor2SecondDerivAt g H x (b i) (sharp j) (b j) (sharp i)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsplit, hT1eqT2]
    ring
  have hT2 :
      tensorDoubleDivergenceAt g H x = T2 := by
    simpa [g, H, b, sharp, T2] using
      tensorDoubleDivergenceAt_eq_sum_sum_positive_T2
        (gt := gt) (t₀ := t₀) (x := x) hgt hCovDiff hSecond
  rw [hPositive, hT2]

set_option maxHeartbeats 5000000 in
/--
Assembly of the summed divergence trace from the two genuine double-trace
second-derivative group evaluations.

The two hypotheses are the exact remaining model sub-identities in closed
notation:
* the positive `T1 + T2` block is `tensorDoubleDivergenceAt`;
* the `T3` block is the Hessian trace of `traceMetricVariationAt`.
-/
theorem deltaGammaDivergenceTraceHessianAssemblyAt_of_sndDeriv_groups
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hPositive :
      deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
        (gt t₀) (timeDerivAt gt t₀) x =
        tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x)
    (hTrace :
      deltaGammaDivergenceTraceSecondDerivTraceBlockAt
        (gt t₀) (timeDerivAt gt t₀) x =
        (letI : FiniteDimensional ℝ (TM x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        let g : ClosedSmoothRiemannianMetric n M := gt t₀
        let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
        let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
        let b := Module.finBasis ℝ (TM x)
        let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
          fun j ↦ metricDualVectorAt g x (b.coord j)
        ∑ j, g.hessianAt f x (b j) (sharp j))) :
    DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x := by
  classical
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hsnd :=
    deltaGammaDivergenceTrace_sndDerivAt_blocks
      (gt := gt) (t₀ := t₀) (x := x)
      hreg hgt hExt hNear hBridge hSecond
  have hTrace' :
      deltaGammaDivergenceTraceSecondDerivTraceBlockAt g H x =
        ∑ j, g.hessianAt f x (b j) (sharp j) := by
    simpa [g, H, f, b, sharp] using hTrace
  change (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
    tensorDoubleDivergenceAt g H x
      - (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (b j) (sharp j)
  rw [hsnd]
  rw [hPositive, hTrace']

set_option maxHeartbeats 5000000 in
/--
Assembly after discharging the `T3` trace block: only the positive
`T1 + T2` block remains as a group-evaluation hypothesis.
-/
theorem deltaGammaDivergenceTraceHessianAssemblyAt_of_positiveBlock
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hPositive :
      deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
        (gt t₀) (timeDerivAt gt t₀) x =
        tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x) :
    DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x :=
  deltaGammaDivergenceTraceHessianAssemblyAt_of_sndDeriv_groups
    (gt := gt) (t₀ := t₀) (x := x)
    hreg hgt hExt hNear hBridge hSecond hPositive
    (deltaGammaDivergenceTraceSecondDerivTraceBlockAt_eq_sum_hessianAt
      (gt := gt) (t₀ := t₀) (x := x)
      hgt hCovDiff hSecond hgrad)

set_option maxHeartbeats 5000000 in
/-- Discharged Hessian assembly for the summed divergence trace. -/
theorem deltaGammaDivergenceTraceHessianAssemblyAt_of_covTensor2Regular
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀)
    (hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hgrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x :=
  deltaGammaDivergenceTraceHessianAssemblyAt_of_positiveBlock
    (gt := gt) (t₀ := t₀) (x := x)
    hreg hgt hExt hNear hBridge hSecond hCovDiff hgrad
    (deltaGammaDivergenceTraceSecondDerivPositiveBlockAt_eq_tensorDoubleDivergenceAt
      (gt := gt) (t₀ := t₀) (x := x) hgt hCovDiff hSecond)

theorem deltaGammaDivergenceTraceHessianAssemblyAt_of_innerHessianDerivative
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hDiv :
      DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x) :
    DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ :=
    fun y ↦ traceMetricVariationAt g H y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hDiv' :
      (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
        (∑ j,
          (extDerivFun
              (fun y : M ↦ tensorDivergenceOneFormAt g H y
                (extend E (b j) y)) x (sharp j)
            - tensorDivergenceOneFormAt g H x
              (g.leviCivita (extend E (b j)) x (sharp j))))
          - (1 / 2 : ℝ) *
            (∑ j, g.hessianAt f x (b j) (sharp j)) := by
    simpa [DeltaGammaDivergenceTraceInnerHessianDerivativeAt, g, H, f, b, sharp]
      using hDiv
  change (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
    tensorDoubleDivergenceAt g H x
      - (1 / 2 : ℝ) * (∑ j, g.hessianAt f x (b j) (sharp j))
  rw [hDiv']
  simp [tensorDoubleDivergenceAt, g, H, b, sharp]

theorem deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hCon :
      DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x) :
    DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let f : M → ℝ :=
    fun y ↦ traceMetricVariationAt g (timeDerivAt gt t₀) y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  change (∑ j, deltaGammaContractionDerivAt gt t₀ x (b j) (sharp j)) =
    (1 / 2 : ℝ) * ∑ j, g.hessianAt f x (b j) (sharp j)
  rw [Finset.sum_congr rfl (fun j _ ↦ by
    simpa [DeltaGammaContractionTraceHessianDerivativeAt, g, f, b, sharp]
      using hCon (b j) (sharp j))]
  rw [← Finset.mul_sum]
  simp [g, f, b, sharp, one_div]

theorem deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hDiv : DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x) :
    DeltaGammaDivergenceTraceAssemblyAt gt t₀ x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let f : M → ℝ :=
    fun y ↦ traceMetricVariationAt g (timeDerivAt gt t₀) y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hlap :
      g.laplacianAt f x =
        ∑ j, g.hessianAt f x (b j) (sharp j) := by
    simpa [g, f, b, sharp] using
      (laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x))
  have hDiv' :
      (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
        tensorDoubleDivergenceAt g (timeDerivAt gt t₀) x
          - (1 / 2 : ℝ) *
            (∑ j, g.hessianAt f x (b j) (sharp j)) := by
    simpa [DeltaGammaDivergenceTraceHessianAssemblyAt, g, f, b, sharp] using hDiv
  change (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
    tensorDoubleDivergenceAt g (timeDerivAt gt t₀) x
      - (1 / 2 : ℝ) * g.laplacianAt f x
  rw [hDiv', hlap]

theorem deltaGammaContractionTraceAssemblyAt_of_hessianAssembly
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hCon : DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x) :
    DeltaGammaContractionTraceAssemblyAt gt t₀ x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let f : M → ℝ :=
    fun y ↦ traceMetricVariationAt g (timeDerivAt gt t₀) y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  have hlap :
      g.laplacianAt f x =
        ∑ j, g.hessianAt f x (b j) (sharp j) := by
    simpa [g, f, b, sharp] using
      (laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x))
  have hCon' :
      (∑ j, deltaGammaContractionDerivAt gt t₀ x (b j) (sharp j)) =
        (1 / 2 : ℝ) *
          (∑ j, g.hessianAt f x (b j) (sharp j)) := by
    simpa [DeltaGammaContractionTraceHessianAssemblyAt, g, f, b, sharp] using hCon
  change (∑ j, deltaGammaContractionDerivAt gt t₀ x (b j) (sharp j)) =
    (1 / 2 : ℝ) * g.laplacianAt f x
  rw [hCon', hlap]

theorem deltaRicciAt_raised_trace_eq_doubleDivergence_sub_laplacian
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ j, deltaRicciAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
        (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
      =
        tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt (gt t₀) x (b.coord j)
  let L : ℝ := (gt t₀).laplacianAt
    (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
  have hsplit := deltaRicciAt_raised_trace_eq_deltaGamma_contractions gt t₀ x
  change (∑ j, deltaRicciAt gt t₀ x (b j) (sharp j)) =
    tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x - L
  change (∑ j, deltaRicciAt gt t₀ x (b j) (sharp j)) =
      (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) -
        (∑ j, deltaGammaContractionDerivAt gt t₀ x (b j) (sharp j)) at hsplit
  rw [hsplit]
  have hDiv' :
      (∑ j, deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)) =
        tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (1 / 2 : ℝ) * L := by
    simpa [DeltaGammaDivergenceTraceAssemblyAt, b, sharp, L] using hDiv
  have hCon' :
      (∑ j, deltaGammaContractionDerivAt gt t₀ x (b j) (sharp j)) =
        (1 / 2 : ℝ) * L := by
    simpa [DeltaGammaContractionTraceAssemblyAt, b, sharp, L] using hCon
  rw [hDiv', hCon']
  ring

theorem deltaRicciAt_raised_trace_eq_doubleDivergence_sub_laplacian_of_hessianAssemblies
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hDiv : DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x) :
    (letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
      ∑ j, deltaRicciAt gt t₀ x ((Module.finBasis ℝ (TM x)) j)
        (metricDualVectorAt (gt t₀) x ((Module.finBasis ℝ (TM x)).coord j)))
      =
        tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x :=
  deltaRicciAt_raised_trace_eq_doubleDivergence_sub_laplacian gt t₀ x
    (deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly hDiv)
    (deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hCon)

theorem hDeltaGammaTrace
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x) :
      let hRic : ∀ u w : TM x,
          HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
            (deltaRicciAt gt t₀ x u w) t₀ :=
        fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
      LinearMap.trace ℝ (TM x)
        (((((gt t₀).metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x)
              (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
        = tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x := by
  let hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciAt gt t₀ x u w) t₀ :=
    fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
  have htrace :=
    trace_metricRaise_deltaRicciAt_eq_sum (gt := gt) (t₀ := t₀) (x := x) hreg
  have hassembly :=
    deltaRicciAt_raised_trace_eq_doubleDivergence_sub_laplacian
      gt t₀ x hDiv hCon
  simpa [hRic] using htrace.trans hassembly

theorem hDeltaGammaTrace_of_hessianAssemblies
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hDiv : DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x) :
      let hRic : ∀ u w : TM x,
          HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
            (deltaRicciAt gt t₀ x u w) t₀ :=
        fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
      LinearMap.trace ℝ (TM x)
        (((((gt t₀).metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x)
              (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
        = tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x :=
  hDeltaGammaTrace
    (gt := gt) (t₀ := t₀) (x := x) hreg
    (deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly hDiv)
    (deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hCon)

/--
First closed Lichnerowicz assembly, with the two remaining algebraic/analytic
bridges stated as honest named obligations.

Open obligation `hRaiseTrace`: the trace contribution from differentiating the
metric inverse is `-⟨h,Ric⟩`.

Open obligation `hDeltaGammaTrace`: the metric-raised trace of the `δΓ`
contraction formula is the double-divergence minus Laplacian trace term.  This
is the closed analogue of the model
`ricciDeriv_raised_trace_contracted_lichnerowicz`, whose core is the
`deltaGamma_koszul`/inner-trace keystone.
-/
theorem scalarVariation_lichnerowicz_shape
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hRaiseTrace :
      LinearMap.trace ℝ (TM x)
        ((raise'.comp ((gt t₀).ricciDualContinuousAt x) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
        = -metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x)
    (hDeltaGammaTrace :
      let hRic : ∀ u w : TM x,
          HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
            (deltaRicciAt gt t₀ x u w) t₀ :=
        fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
      LinearMap.trace ℝ (TM x)
        (((((gt t₀).metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x)
              (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
        = tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x) :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (gt t₀).laplacianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
        - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x := by
  let hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciAt gt t₀ x u w) t₀ :=
    fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
  have hscalar :=
    deriv_scalarAt_eq_trace_deltaRicciAt_of_metricFlowRegularAt
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise') hreg hRaise
  have hscalar' :
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        LinearMap.trace ℝ (TM x)
          (((raise'.comp ((gt t₀).ricciDualContinuousAt x) +
              ((gt t₀).metricRaiseContinuousAt x).comp
                (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                  (gt := gt) (t₀ := t₀) (x := x)
                  (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
            TM x →ₗ[ℝ] TM x) := by
    simpa [hRic] using hscalar
  rw [hscalar']
  change
      LinearMap.trace ℝ (TM x)
          (((raise'.comp ((gt t₀).ricciDualContinuousAt x) : TM x →L[ℝ] TM x) :
              TM x →ₗ[ℝ] TM x) +
            (((((gt t₀).metricRaiseContinuousAt x).comp
                (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                  (gt := gt) (t₀ := t₀) (x := x)
                  (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
              TM x →ₗ[ℝ] TM x)) =
        tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
          - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x
  rw [map_add]
  rw [hRaiseTrace]
  rw [show
      LinearMap.trace ℝ (TM x)
        (((((gt t₀).metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x)
              (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
        = tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x by
      simpa [hRic] using hDeltaGammaTrace]
  ring

/--
Scalar variation in Lichnerowicz form with the raise-map trace discharged.
The remaining hypothesis is the raised `deltaRicciAt` trace contraction.
-/
theorem scalarVariation_lichnerowicz_shape'
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDeltaGammaTrace :
      let hRic : ∀ u w : TM x,
          HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
            (deltaRicciAt gt t₀ x u w) t₀ :=
        fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
      LinearMap.trace ℝ (TM x)
        (((((gt t₀).metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x)
              (deltaRicciAt gt t₀ x) hRic)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
        = tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x) :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (gt t₀).laplacianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
        - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x :=
  scalarVariation_lichnerowicz_shape
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hreg hRaise
    (metricRaise_trace_ricciDualContinuousAt_eq_neg
      (gt := gt) (t₀ := t₀) (x := x) hgt hRaise)
    hDeltaGammaTrace

/--
Closed scalar variation in Lichnerowicz form after the raised `δRic` trace is
assembled from the two named `δΓ` divergence contractions.
-/
theorem scalarVariation_lichnerowicz
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x) :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (gt t₀).laplacianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
        - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x :=
  scalarVariation_lichnerowicz_shape'
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hreg hgt hRaise
    (hDeltaGammaTrace (gt := gt) (t₀ := t₀) (x := x) hreg hDiv hCon)

theorem scalarVariation_lichnerowicz_of_hessianAssemblies
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x) :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (gt t₀).laplacianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
        - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x :=
  scalarVariation_lichnerowicz
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hreg hgt hRaise
    (deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly hDiv)
    (deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hCon)

theorem scalarVariation_lichnerowicz_of_traceHessianDerivatives
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x) :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (gt t₀).laplacianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
        - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x :=
  scalarVariation_lichnerowicz_of_hessianAssemblies
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hreg hgt hRaise
    (deltaGammaDivergenceTraceHessianAssemblyAt_of_innerHessianDerivative hDiv)
    (deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative hCon)

/-- `HasDerivAt` form of the closed Lichnerowicz scalar-variation formula. -/
theorem hasDerivAt_scalarAt_lichnerowicz
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x) :
    HasDerivAt (fun t ↦ (gt t).scalarAt x)
      (tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
        - (gt t₀).laplacianAt
          (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
        - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x) t₀ := by
  let hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciAt gt t₀ x u w) t₀ :=
    fun u w ↦ ricciVariation_eq_deltaGamma_contractions' hreg u w
  let A' : TM x →L[ℝ] TM x :=
    raise'.comp ((gt t₀).ricciDualContinuousAt x) +
      ((gt t₀).metricRaiseContinuousAt x).comp
        (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
          (gt := gt) (t₀ := t₀) (x := x) (deltaRicciAt gt t₀ x) hRic)
  have hA : ClosedSmoothRiemannianMetric.RicciEndoHasDerivAt gt t₀ x A' := by
    dsimp [A']
    exact ClosedSmoothRiemannianMetric.ricciEndoHasDerivAt_of_ricciBilinearHasDerivAt
      (gt := gt) (t₀ := t₀) (x := x)
      (δRic := deltaRicciAt gt t₀ x) (raise' := raise') hRaise hRic
  have hHas :=
    ClosedSmoothRiemannianMetric.hasDerivAt_scalarAt_of_ricciEndoHasDerivAt
      (gt := gt) (t₀ := t₀) (x := x) hA
  have hDeriv := scalarVariation_lichnerowicz
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hreg hgt hRaise hDiv hCon
  have hTrace :
      LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x) =
        tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
          - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x := by
    rw [← hHas.deriv]
    exact hDeriv
  convert hHas using 1
  exact hTrace.symm

end Poincare
