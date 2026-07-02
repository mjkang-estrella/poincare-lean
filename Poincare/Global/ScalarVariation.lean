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

def CovTensor2ExtDifferentiableAt
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : Prop :=
  ∀ p q : TM x,
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ h y (extend E p y) (extend E q y)) x

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
