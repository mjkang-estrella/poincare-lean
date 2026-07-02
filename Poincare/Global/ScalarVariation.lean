import Poincare.Global.MetricVariation
import Poincare.Global.Laplacian
import Poincare.Global.RicciNorm

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

/-- First-slot trace form of `δΓ`, evaluated fiberwise. -/
noncomputable def deltaGammaFirstSlotTraceFieldAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (y : M) (w : TM y) : ℝ :=
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, (Module.finBasis ℝ (TM y)).coord i
    (deltaGammaAt gt t₀ y ((Module.finBasis ℝ (TM y)) i) w)

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
