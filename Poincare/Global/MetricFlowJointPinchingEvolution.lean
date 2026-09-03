import Poincare.Global.MetricFlowJointRicciTensorEvolution
import Poincare.Global.ParabolicMinimumContinuousOn
import Poincare.Global.MetricFlowJointScalarTraceZoneBridge
import Poincare.Global.ScalarEvolution

/-!
# Hamilton pinching evolution from joint metric entries

This module feeds the automatic Ricci-tensor and scalar evolution theorems
into Hamilton's pinching APIs.  The finite Gram formulas turn the `C²` Ricci
entries supplied by a joint `C³` Ricci flow into `C²` regularity of
`|Ric|²`.  All quotient, gradient, inverse-metric, and Bochner regularity
premises are then reconstructed rather than carried as independent inputs.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Entrywise `C²` Ricci regularity makes its squared metric norm `C²`. -/
theorem contMDiffAt_two_ricciNormSqAt_of_ricci_entries
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRic : CovTensor2ExtContMDiffAt (ricciVariationField g) x 2) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.ricciNormSqAt y) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let rhs : M → ℝ := fun y ↦
    ∑ a, ∑ b', ∑ c, ∑ d,
      (gramMatrix g x y)⁻¹ a c *
        (gramMatrix g x y)⁻¹ b' d *
        g.ricciAt y (gramFrame x y a) (gramFrame x y b') *
        g.ricciAt y (gramFrame x y c) (gramFrame x y d)
  have hMetric : MetricExtContMDiffAt g x 2 :=
    metricExtContMDiffAt_two g x
  have hsum : ContMDiffAt I 𝓘(ℝ) 2 rhs x := by
    dsimp only [rhs]
    refine contMDiffAt_two_finset_sum_real
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
    intro a _
    refine contMDiffAt_two_finset_sum_real
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
    intro b' _
    refine contMDiffAt_two_finset_sum_real
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
    intro c _
    refine contMDiffAt_two_finset_sum_real
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
    intro d _
    have hac : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gramMatrix g x y)⁻¹ a c) x :=
      gramMatrix_inv_entry_contMDiffAt_two_of_metricExtContMDiffAt
        g x hMetric a c
    have hbd : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gramMatrix g x y)⁻¹ b' d) x :=
      gramMatrix_inv_entry_contMDiffAt_two_of_metricExtContMDiffAt
        g x hMetric b' d
    have hab : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦
          g.ricciAt y (gramFrame x y a) (gramFrame x y b')) x := by
      simpa [ricciVariationField, gramFrame, b] using hRic (b a) (b b')
    have hcd : ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦
          g.ricciAt y (gramFrame x y c) (gramFrame x y d)) x := by
      simpa [ricciVariationField, gramFrame, b] using hRic (b c) (b d)
    exact (((hac.smul hbd).smul hab).smul hcd)
  exact hsum.congr_of_eventuallyEq
    ((gramMatrix_eventually_isUnit (g := g) x).mono fun y hy ↦ by
      calc
        g.ricciNormSqAt y =
            metricVariationRicciPairingAt g (ricciVariationField g) y :=
          (metricVariationRicciPairingAt_ricci g y).symm
        _ = rhs y := by
          simpa [rhs] using
            metricVariationRicciPairingAt_ricci_eq_sum_gram_inv g x y hy)

/-- The squared Ricci norm of a closed smooth metric is canonically `C²`. -/
theorem ricciNormSqAt_contMDiffAt_two_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x := by
  exact contMDiffAt_two_ricciNormSqAt_of_ricci_entries g x
    (covTensor2ExtContMDiffAt_ricciVariationField_canonical g x)

/-- The Bochner pairing field is differentiable once `|Ric|²` is `C²`. -/
theorem covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hNorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x)
    (w : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ covRicciRicciPairingAt g y (extend E w y)) x := by
  let f : M → ℝ := fun y ↦ g.ricciNormSqAt y
  let W : ∀ y : M, TM y := extend E w
  have hW : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% W) x := by
    simpa [W] using (mdifferentiableAt_extend I E w)
  have hd : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ extDerivFun f y (W y)) x := by
    exact CovariantDerivative.mdiffAt_extDerivFun_apply hNorm hW
  have heq :
      (fun y : M ↦ covRicciRicciPairingAt g y (W y)) =
        fun y : M ↦ (1 / 2 : ℝ) * extDerivFun f y (W y) := by
    funext y
    have h := extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
      g y (W y)
    change extDerivFun f y (W y) = 2 * covRicciRicciPairingAt g y (W y) at h
    rw [h]
    ring
  rw [heq]
  exact mdifferentiableAt_const.mul hd

/-- A nonzero scalar denominator makes the ordinary pinching quotient `C²`. -/
theorem contMDiffAt_two_pinchingQuotientAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hNorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x)
    (hScalar : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x)
    (hR : g.scalarAt x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.pinchingQuotientAt y) x := by
  have hden : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (g.scalarAt y) ^ 2) x := by
    simpa [pow_two] using hScalar.smul hScalar
  have hinv : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ ((g.scalarAt y) ^ 2)⁻¹) x :=
    hden.inv₀ (pow_ne_zero 2 hR)
  simpa [ClosedSmoothRiemannianMetric.pinchingQuotientAt,
    div_eq_mul_inv] using hNorm.smul hinv

/-- The trace-form traceless Ricci norm inherits `C²` regularity. -/
theorem contMDiffAt_two_tracelessRicciNormSqAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hNorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x)
    (hScalar : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.tracelessRicciNormSqAt y) x := by
  have hc : ContMDiffAt I 𝓘(ℝ) 2
      (fun _ : M ↦ ((n : ℝ)⁻¹)) x := contMDiffAt_const
  have hsquare : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (g.scalarAt y) ^ 2) x := by
    simpa [pow_two] using hScalar.smul hScalar
  simpa [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt,
    div_eq_mul_inv, mul_comm] using hNorm.sub (hc.smul hsquare)

/-- Composition with a nonzero-base real power preserves manifold `C²`. -/
theorem contMDiffAt_two_rpow_const_of_ne
    {f : M → ℝ} {x : M} (p : ℝ)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hfx : f x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ f y ^ p) x := by
  have hp : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) 2 (fun r : ℝ ↦ r ^ p) (f x) :=
    contMDiffAt_iff_contDiffAt.mpr
      (Real.contDiffAt_rpow_const_of_ne hfx)
  exact hp.comp x hf

/-- A positive scalar denominator makes the improved traceless quotient `C²`. -/
theorem contMDiffAt_two_tracelessPinchingAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (delta : ℝ)
    (hTraceNorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.tracelessRicciNormSqAt y) x)
    (hScalar : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x)
    (hR : 0 < g.scalarAt x) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.tracelessPinchingAt y delta) x := by
  have hpow : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (g.scalarAt y) ^ (2 - delta)) x :=
    contMDiffAt_two_rpow_const_of_ne (2 - delta) hScalar hR.ne'
  have hinv : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ ((g.scalarAt y) ^ (2 - delta))⁻¹) x :=
    hpow.inv₀ (Real.rpow_pos_of_pos hR (2 - delta)).ne'
  simpa [ClosedSmoothRiemannianMetric.tracelessPinchingAt,
    div_eq_mul_inv] using hTraceNorm.smul hinv

/-- Symmetry of the lower Ricci tensor persists in any pointwise time derivative. -/
theorem ricciBilinearDeriv_symm
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀)
    (u w : TM x) :
    δRic u w = δRic w u := by
  have htarget := hRic u w
  have hother := hRic w u
  have hpath :
      (fun t ↦ (gt t).ricciAt x u w) =
        fun t ↦ (gt t).ricciAt x w u := by
    funext t
    exact (gt t).ricciAt_symm x u w
  rw [hpath] at htarget
  exact htarget.unique hother

/--
The lower-Ricci derivative part of the Ricci-norm trace is the metric pairing
of that derivative with Ricci.  This is the continuous-linear trace form of
the same arbitrary-basis contraction.
-/
theorem trace_metricRaise_ricciDerivativeDual_comp_ricciEndo_eq_pairing
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {δRic : TM x → TM x → ℝ}
    (hRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic u w) t₀)
    (h : ∀ y : M, TM y → TM y → ℝ)
    (hAt : ∀ u w : TM x, h x u w = δRic u w) :
    let L : TM x →L[ℝ] TM x :=
      (((gt t₀).metricRaiseContinuousAt x).comp
        (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
          (gt := gt) (t₀ := t₀) (x := x) δRic hRic)).comp
        ((gt t₀).ricciEndoContinuousAt x)
    LinearMap.trace ℝ (TM x) L.toLinearMap =
      metricVariationRicciPairingAt (gt t₀) h x := by
  dsimp only
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt (gt t₀) x (b.coord i)
  let B : LinearMap.BilinForm ℝ (TM x) :=
    LinearMap.mk₂ ℝ δRic
      (fun u u' w ↦
        ClosedSmoothRiemannianMetric.ricciBilinearDeriv_add_left hRic u u' w)
      (fun c u w ↦
        ClosedSmoothRiemannianMetric.ricciBilinearDeriv_smul_left hRic c u w)
      (fun u w w' ↦
        ClosedSmoothRiemannianMetric.ricciBilinearDeriv_add_right hRic u w w')
      (fun c u w ↦
        ClosedSmoothRiemannianMetric.ricciBilinearDeriv_smul_right hRic c u w)
  have hPair :
      metricVariationRicciPairingAt (gt t₀) h x =
        metricRicciPairingTraceInBasisAt (gt t₀) x B b :=
    metricVariationRicciPairingAt_eq_metricRicciPairingTraceInBasisAt
      (gt t₀) h x B
      (fun u w ↦ (hAt u w).symm)
      (fun u w ↦ by
        rw [hAt u w, hAt w u]
        exact ricciBilinearDeriv_symm hRic u w)
      b
  rw [hPair]
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  unfold metricRicciPairingTraceInBasisAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change b.coord i
      ((gt t₀).metricRaiseContinuousAt x
        (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
          (gt := gt) (t₀ := t₀) (x := x) δRic hRic
          ((gt t₀).ricciEndoContinuousAt x (b i)))) =
    B ((gt t₀).ricciEndoAt x (b i))
      (metricDualVectorAt (gt t₀) x (b.coord i))
  rw [coord_eq_inner_metricDualVectorAt_of_basis
    (g := gt t₀) (x := x) (b := b)]
  rw [ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  simp [B, b]
  rfl

/-- Pairing the metric tensor with Ricci gives scalar curvature. -/
theorem metricVariationRicciPairingAt_metric_eq_scalar
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    metricVariationRicciPairingAt g
      (fun y : M ↦ fun u w : TM y ↦ g.inner y u w) x =
      g.scalarAt x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  have hPair :
      metricVariationRicciPairingAt g
          (fun y : M ↦ fun u w : TM y ↦ g.inner y u w) x =
        metricRicciPairingTraceInBasisAt g x (g.metricBilinAt x) b :=
    metricVariationRicciPairingAt_eq_metricRicciPairingTraceInBasisAt
      g (fun y : M ↦ fun u w : TM y ↦ g.inner y u w) x
      (g.metricBilinAt x) (fun _ _ ↦ rfl)
      (fun u w ↦ g.inner_symm x u w) b
  rw [hPair, g.scalarAt_eq_trace_ricciEndoAt x,
    LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  unfold metricRicciPairingTraceInBasisAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact (coord_eq_inner_metricDualVectorAt_of_basis
    (g := g) (x := x) (b := b) i (g.ricciEndoAt x (b i))).symm

/-- Pairing `Ric²` with Ricci gives the invariant cubic Ricci trace. -/
theorem metricVariationRicciPairingAt_ricciSq_eq_cubic
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    metricVariationRicciPairingAt g
      (fun y : M ↦ fun u w : TM y ↦
        g.ricciAt y (g.ricciEndoAt y u) w) x =
      g.ricciCubicTraceAt x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let A : TM x →ₗ[ℝ] TM x := g.ricciEndoAt x
  let B : LinearMap.BilinForm ℝ (TM x) :=
    LinearMap.mk₂ ℝ (fun u w ↦ g.ricciAt x (A u) w)
      (by
        intro u u' w
        change g.ricciAt x (A (u + u')) w =
          g.ricciAt x (A u) w + g.ricciAt x (A u') w
        rw [map_add]
        exact g.ricciAt_add_left x (A u) (A u') w)
      (by
        intro c u w
        change g.ricciAt x (A (c • u)) w = c • g.ricciAt x (A u) w
        rw [map_smul]
        simpa [smul_eq_mul] using g.ricciAt_smul_left x c (A u) w)
      (by
        intro u w w'
        exact g.ricciAt_add_right x (A u) w w')
      (by
        intro c u w
        simpa [smul_eq_mul] using g.ricciAt_smul_right x c (A u) w)
  have hSymm : ∀ u w : TM x,
      g.ricciAt x (A u) w = g.ricciAt x (A w) u := by
    intro u w
    calc
      g.ricciAt x (A u) w = g.inner x (A (A u)) w := by
        rw [ClosedSmoothRiemannianMetric.inner_ricciEndoAt]
      _ = g.inner x (A u) (A w) :=
        g.ricciEndoAt_selfAdjoint x (A u) w
      _ = g.inner x (A w) (A u) := g.inner_symm x _ _
      _ = g.inner x (A (A w)) u :=
        (g.ricciEndoAt_selfAdjoint x (A w) u).symm
      _ = g.ricciAt x (A w) u := by
        rw [ClosedSmoothRiemannianMetric.inner_ricciEndoAt]
  have hPair :
      metricVariationRicciPairingAt g
          (fun y : M ↦ fun u w : TM y ↦
            g.ricciAt y (g.ricciEndoAt y u) w) x =
        metricRicciPairingTraceInBasisAt g x B b :=
    metricVariationRicciPairingAt_eq_metricRicciPairingTraceInBasisAt
      g (fun y : M ↦ fun u w : TM y ↦
        g.ricciAt y (g.ricciEndoAt y u) w) x B
      (fun _ _ ↦ rfl) hSymm b
  rw [hPair, g.ricciCubicTraceAt_eq_trace x,
    LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  unfold metricRicciPairingTraceInBasisAt
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change g.ricciAt x (A (A (b i)))
      (metricDualVectorAt g x (b.coord i)) =
    b.coord i (((A ∘ₗ A) ∘ₗ A) (b i))
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    coord_eq_inner_metricDualVectorAt_of_basis
      (g := g) (x := x) (b := b)]
  rw [ClosedSmoothRiemannianMetric.inner_ricciEndoAt]

/--
Pairing the pinned three-dimensional Ricci reaction tensor with Ricci gives
its rough term plus the invariant quadratic/cubic reaction polynomial.
-/
theorem metricVariationRicciPairingAt_ricciEvolution3ReactionRHSAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    metricVariationRicciPairingAt g
      (fun y : M ↦ fun u w : TM y ↦
        ricciEvolution3ReactionRHSAt g y u w) x =
      roughRicciLaplacianPairingAt g x
        + 5 * g.scalarAt x * g.ricciNormSqAt x
        - (g.scalarAt x) ^ 3
        - 6 * g.ricciCubicTraceAt x := by
  let rough : ∀ y : M, TM y → TM y → ℝ :=
    fun y u w ↦
      roughTensorLaplacianAt g (ricciVariationField g) y u w
  let ric : ∀ y : M, TM y → TM y → ℝ :=
    ricciVariationField g
  let ricSq : ∀ y : M, TM y → TM y → ℝ :=
    fun y u w ↦ g.ricciAt y (g.ricciEndoAt y u) w
  let metric : ∀ y : M, TM y → TM y → ℝ :=
    fun y u w ↦ g.inner y u w
  let frozen : ∀ y : M, TM y → TM y → ℝ :=
    fun y u w ↦
      rough y u w
        + (3 * g.scalarAt x) * ric y u w
        + (-6 : ℝ) * ricSq y u w
        + (2 * g.ricciNormSqAt x - (g.scalarAt x) ^ 2) * metric y u w
  have hCongr :
      metricVariationRicciPairingAt g
          (fun y : M ↦ fun u w : TM y ↦
            ricciEvolution3ReactionRHSAt g y u w) x =
        metricVariationRicciPairingAt g frozen x := by
    apply metricVariationRicciPairingAt_congr_at
    intro u w
    simp only [ricciEvolution3ReactionRHSAt, frozen, rough, ric, ricSq,
      metric, ricciVariationField]
    ring
  rw [hCongr]
  change metricVariationRicciPairingAt g
      (fun y u w ↦
        rough y u w
          + (3 * g.scalarAt x) * ric y u w
          + (-6 : ℝ) * ricSq y u w
          + (2 * g.ricciNormSqAt x - (g.scalarAt x) ^ 2) * metric y u w) x = _
  rw [metricVariationRicciPairingAt_add,
    metricVariationRicciPairingAt_add,
    metricVariationRicciPairingAt_add,
    metricVariationRicciPairingAt_smul,
    metricVariationRicciPairingAt_smul,
    metricVariationRicciPairingAt_smul]
  have hrough : metricVariationRicciPairingAt g rough x =
      roughRicciLaplacianPairingAt g x := rfl
  have hric : metricVariationRicciPairingAt g ric x =
      g.ricciNormSqAt x := by
    simpa [ric] using metricVariationRicciPairingAt_ricci g x
  have hricSq : metricVariationRicciPairingAt g ricSq x =
      g.ricciCubicTraceAt x := by
    simpa [ricSq] using metricVariationRicciPairingAt_ricciSq_eq_cubic g x
  have hmetric : metricVariationRicciPairingAt g metric x =
      g.scalarAt x := by
    simpa [metric] using metricVariationRicciPairingAt_metric_eq_scalar g x
  rw [hrough, hric, hricSq, hmetric]
  ring

/--
Under the Ricci-flow metric motion, the inverse-metric part of the
Ricci-norm derivative contributes twice the cubic Ricci trace before the
outer product-rule factor of two.
-/
theorem trace_metricRaiseDeriv_ricciDual_comp_ricciEndo_eq_two_cubic
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hFlow : IsClosedRicciFlowSolutionAt gt t₀ x) :
    let K : TM x →L[ℝ] TM x :=
      ((metricRaiseDerivAt gt t₀ x hgt).comp
        ((gt t₀).ricciDualContinuousAt x)).comp
        ((gt t₀).ricciEndoContinuousAt x)
    LinearMap.trace ℝ (TM x) K.toLinearMap =
      2 * (gt t₀).ricciCubicTraceAt x := by
  dsimp only
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let b := Module.finBasis ℝ (TM x)
  let A : TM x →ₗ[ℝ] TM x := g.ricciEndoAt x
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hRaiseRic : ∀ v : TM x,
      g.metricRaiseContinuousAt x (g.ricciDualContinuousAt x v) = A v := by
    intro v
    have h := congrArg (fun L : TM x →L[ℝ] TM x ↦ L v)
      (g.ricciEndoContinuousAt_eq_metricRaise_comp_ricciDualContinuousAt x)
    simpa [A, ContinuousLinearMap.comp_apply] using h.symm
  rw [g.ricciCubicTraceAt_eq_trace x,
    LinearMap.trace_eq_matrix_trace ℝ b,
    LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  change b.coord i
      (metricRaiseDerivAt gt t₀ x hgt
        (g.ricciDualContinuousAt x
          (g.ricciEndoContinuousAt x (b i)))) =
    2 * b.coord i (((A ∘ₗ A) ∘ₗ A) (b i))
  rw [coord_eq_inner_metricDualVectorAt_of_basis
    (g := g) (x := x) (b := b)]
  rw [metricRaiseDerivAt_inner_apply hgt]
  rw [hRaiseRic]
  have hEq :=
    isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt
      (gt := gt) (t₀ := t₀) (x := x) hFlow
      (closedRicciFlowExtensionRegularAt_canonical gt t₀ x)
      (A (A (b i))) (sharp i)
  change timeDerivAt gt t₀ x (A (A (b i))) (sharp i) =
    -2 * g.ricciAt x (A (A (b i))) (sharp i) at hEq
  change -timeDerivAt gt t₀ x (A (A (b i))) (sharp i) =
    2 * b.coord i (((A ∘ₗ A) ∘ₗ A) (b i))
  rw [hEq]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    coord_eq_inner_metricDualVectorAt_of_basis
      (g := g) (x := x) (b := b)]
  rw [ClosedSmoothRiemannianMetric.inner_ricciEndoAt]
  ring

/--
The reaction trace produced by a Ricci-tensor evolution witness and a chosen
time derivative of the inverse metric.  This records exactly the reaction
term computed by the tensor-to-pinching assembly, without identifying it with
the separately defined cubic Ricci invariant.
-/
noncomputable def ricciEvolutionPinchingReactionMotionTraceAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x)
    (hRicci : SatisfiesRicciEvolutionAt gt t₀ x)
    (hn : n = 3) : ℝ :=
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let δRic3 : TM x → TM x → ℝ :=
    fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
  let hRic3 : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
    SatisfiesRicciEvolutionAt.reaction3
      (gt := gt) (t₀ := t₀) (x := x) hRicci hn
  let fullTrace : ℝ :=
    2 * LinearMap.trace ℝ (TM x)
      ((((raise'.comp (g.ricciDualContinuousAt x) +
          (g.metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
          (g.ricciEndoContinuousAt x)) : TM x →L[ℝ] TM x) :
        TM x →ₗ[ℝ] TM x)
  g.pinchingRicciNormReactionMotionTraceAt x fullTrace

set_option maxHeartbeats 4000000 in
/--
For a genuine three-dimensional Ricci flow, the reaction trace assembled
directly from the inverse-metric motion and the lower-Ricci evolution is
exactly Hamilton's invariant cubic reaction polynomial.
-/
theorem ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hFlow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hRicci : SatisfiesRicciEvolutionAt gt t₀ x)
    (hn : n = 3) :
    ricciEvolutionPinchingReactionMotionTraceAt
        (metricRaiseDerivAt gt t₀ x hgt) hRicci hn =
      (gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let δRic3 : TM x → TM x → ℝ :=
    fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
  let hRic3 : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
    SatisfiesRicciEvolutionAt.reaction3
      (gt := gt) (t₀ := t₀) (x := x) hRicci hn
  let K : TM x →L[ℝ] TM x :=
    ((metricRaiseDerivAt gt t₀ x hgt).comp
      (g.ricciDualContinuousAt x)).comp
      (g.ricciEndoContinuousAt x)
  let L : TM x →L[ℝ] TM x :=
    ((g.metricRaiseContinuousAt x).comp
      (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
        (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
      (g.ricciEndoContinuousAt x)
  have hSplit :
      (((metricRaiseDerivAt gt t₀ x hgt).comp
            (g.ricciDualContinuousAt x) +
          (g.metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
          (g.ricciEndoContinuousAt x)) = K + L := by
    ext v
    simp [K, L]
  have hTraceSplit :
      LinearMap.trace ℝ (TM x)
          ((((metricRaiseDerivAt gt t₀ x hgt).comp
                (g.ricciDualContinuousAt x) +
              (g.metricRaiseContinuousAt x).comp
                (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                  (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
              (g.ricciEndoContinuousAt x)).toLinearMap) =
        LinearMap.trace ℝ (TM x) K.toLinearMap +
          LinearMap.trace ℝ (TM x) L.toLinearMap := by
    rw [hSplit]
    exact map_add (LinearMap.trace ℝ (TM x)) K.toLinearMap L.toLinearMap
  have hTraceK :
      LinearMap.trace ℝ (TM x) K.toLinearMap =
        2 * g.ricciCubicTraceAt x := by
    simpa [g, K] using
      trace_metricRaiseDeriv_ricciDual_comp_ricciEndo_eq_two_cubic
        (gt := gt) (t₀ := t₀) (x := x) hgt hFlow
  have hTraceL :
      LinearMap.trace ℝ (TM x) L.toLinearMap =
        metricVariationRicciPairingAt g
          (fun y : M ↦ fun u w : TM y ↦
            ricciEvolution3ReactionRHSAt g y u w) x := by
    simpa [g, δRic3, hRic3, L] using
      trace_metricRaise_ricciDerivativeDual_comp_ricciEndo_eq_pairing
        (gt := gt) (t₀ := t₀) (x := x) hRic3
        (fun y : M ↦ fun u w : TM y ↦
          ricciEvolution3ReactionRHSAt g y u w)
        (fun _ _ ↦ rfl)
  have hReactionPairing :=
    metricVariationRicciPairingAt_ricciEvolution3ReactionRHSAt g x
  unfold ricciEvolutionPinchingReactionMotionTraceAt
  dsimp only
  unfold ClosedSmoothRiemannianMetric.pinchingRicciNormReactionMotionTraceAt
  rw [hTraceSplit, hTraceK, hTraceL, hReactionPairing]
  unfold ClosedSmoothRiemannianMetric.pinchingRicciNormReactionMotionTraceCubicAt
  ring

set_option maxHeartbeats 12000000 in
/--
Hamilton's improved traceless pinching evolution follows from a genuine
three-dimensional Ricci flow with globally joint `C³` metric entries and
positive scalar curvature on the time slice.

The only hypotheses not reconstructed from the flow are the geometric range
`0 < δ ≤ 1`, the dimension identity, and positivity of scalar curvature.
The reaction witness is the exact tensor-evolution trace computed above.
-/
theorem satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} {δ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hn : n = 3)
    (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y) :
    let htime : TimeDifferentiableAt gt t₀ x :=
      timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
        ((hJoint x).of_le (by norm_num))
    let raise' := metricRaiseDerivAt gt t₀ x htime
    let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
      satisfiesRicciEvolutionAt_of_ricciFlow_joint_metric_entries_three
        hFlow hJoint
    ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
      gt t₀ x δ
        (ricciEvolutionPinchingReactionMotionTraceAt raise' hRicci hn) := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let htime : TimeDifferentiableAt gt t₀ x :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint x).of_le (by norm_num))
  let raise' := metricRaiseDerivAt gt t₀ x htime
  let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
    satisfiesRicciEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hFlow hJoint
  change
    ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
      gt t₀ x δ
        (ricciEvolutionPinchingReactionMotionTraceAt raise' hRicci hn)
  have hRaise :
      HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ := by
    exact hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_ricciFlow hFlow hEntries y
  have hNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.ricciNormSqAt z) y := fun y ↦
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g y (hRicC2 y)
  have hScalar2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.scalarAt z) y := fun y ↦
    scalarAt_contMDiffAt_two_of_ricciFlow hFlow hEntries y
  have hScalarSq2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.scalarAt z ^ 2) y := fun y ↦ by
    simpa [pow_two] using (hScalar2 y).smul (hScalar2 y)
  have hTraceNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.tracelessRicciNormSqAt z) y := fun y ↦
    contMDiffAt_two_tracelessRicciNormSqAt
      g y (hNorm2 y) (hScalar2 y)
  have hTraceQuot2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.tracelessPinchingAt z δ) y := fun y ↦
    contMDiffAt_two_tracelessPinchingAt
      g y δ (hTraceNorm2 y) (hScalar2 y) (hRpos y)
  have hScalarPow2SubDelta2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.scalarAt z ^ (2 - δ)) y := fun y ↦
    contMDiffAt_two_rpow_const_of_ne
      (2 - δ) (hScalar2 y) (hRpos y).ne'
  have hPairDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ covRicciRicciPairingAt g y (extend E w y)) x :=
    fun w ↦
      covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
        g x (hNorm2 x) w
  have hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        g (ricciVariationField g) x :=
    covTensor2DerivExtDifferentiableAt_of_extSecond
      (g := g) (h := ricciVariationField g) (x := x)
      (covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two (hRicC2 x))
      (fun y ↦ covTensor2ExtDifferentiableAt_of_contMDiffAt_two (hRicC2 y))
      (tensor2AddLeft_ricciVariationField g)
      (tensor2SMulLeft_ricciVariationField g)
      (tensor2AddRight_ricciVariationField g)
      (tensor2SMulRight_ricciVariationField g)
  have hScalar : SatisfiesHamiltonScalarEvolutionAt gt t₀ x :=
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hFlow hJoint
  have hScalarSqDiff : ∀ y : M, MDifferentiableAt I 𝓘(ℝ)
      (fun z : M ↦ g.scalarAt z ^ 2) y := fun y ↦
    (hScalarSq2 y).mdifferentiableAt two_ne_zero
  have hScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun z : M ↦ g.scalarAt z ^ 2))) x :=
    g.mdifferentiableAt_gradient (hScalarSq2 x)
  have hTraceQuotGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.tracelessPinchingAt y δ))) x :=
    g.mdifferentiableAt_gradient (hTraceQuot2 x)
  have hScalarGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.scalarAt y))) x :=
    g.mdifferentiableAt_gradient (hScalar2 x)
  have hTraceProduct2 : ContMDiffAt I 𝓘(ℝ) 2
      ((fun y : M ↦ g.tracelessPinchingAt y δ) *
        (fun y : M ↦ g.scalarAt y ^ (2 - δ))) x := by
    simpa only [Pi.mul_apply] using
      (hTraceQuot2 x).smul (hScalarPow2SubDelta2 x)
  have hTraceProductGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient
          ((fun y : M ↦ g.tracelessPinchingAt y δ) *
            (fun y : M ↦ g.scalarAt y ^ (2 - δ))))) x :=
    g.mdifferentiableAt_gradient hTraceProduct2
  have hTraceNormGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.tracelessRicciNormSqAt y))) x :=
    g.mdifferentiableAt_gradient (hTraceNorm2 x)
  have hEvol :=
    satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow
      (gt := gt) (t₀ := t₀) (x := x) (δ := δ) (raise' := raise')
      hRaise hRicci hScalar hn hδpos hδle (hRpos x)
      hNorm2 hScalar2 hScalarSqDiff hScalarSqGrad hPairDiff hRicSecond
      (hScalar2 x).continuousAt
      (fun y ↦ (hScalar2 y).mdifferentiableAt two_ne_zero)
      (fun y ↦ (hRpos y).ne')
      (fun y ↦ (hTraceQuot2 y).mdifferentiableAt two_ne_zero)
      hTraceQuotGrad hScalarGrad hTraceProductGrad hTraceNormGrad
  simpa [ricciEvolutionPinchingReactionMotionTraceAt] using hEvol

/--
Automatic improved traceless pinching evolution in the invariant cubic form
consumed by Hamilton's maximum-principle theorems.
-/
theorem satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow_joint_metric_entries_three_cubic
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} {δ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hn : n = 3)
    (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y) :
    ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
      gt t₀ x δ
        ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x) := by
  let htime : TimeDifferentiableAt gt t₀ x :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint x).of_le (by norm_num))
  let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
    satisfiesRicciEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hFlow hJoint
  have hEvol :=
    satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow_joint_metric_entries_three
      (gt := gt) (t₀ := t₀) (x := x) (δ := δ)
      hFlow hJoint hn hδpos hδle hRpos
  change ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
    gt t₀ x δ
      (ricciEvolutionPinchingReactionMotionTraceAt
        (metricRaiseDerivAt gt t₀ x htime) hRicci hn) at hEvol
  rw [ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic
    htime (hFlow x) hRicci hn] at hEvol
  exact hEvol

set_option maxHeartbeats 8000000 in
/--
The ordinary Hamilton quotient evolution is likewise automatic from global
joint `C³` metric entries.  Global scalar positivity supplies every quotient
denominator and is the sole slice-wide geometric hypothesis.
-/
theorem satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hn : n = 3)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y) :
    let htime : TimeDifferentiableAt gt t₀ x :=
      timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
        ((hJoint x).of_le (by norm_num))
    let raise' := metricRaiseDerivAt gt t₀ x htime
    let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
      satisfiesRicciEvolutionAt_of_ricciFlow_joint_metric_entries_three
        hFlow hJoint
    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
      gt t₀ x
        (ricciEvolutionPinchingReactionMotionTraceAt raise' hRicci hn) := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let htime : TimeDifferentiableAt gt t₀ x :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint x).of_le (by norm_num))
  let raise' := metricRaiseDerivAt gt t₀ x htime
  let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
    satisfiesRicciEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hFlow hJoint
  change
    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
      gt t₀ x
        (ricciEvolutionPinchingReactionMotionTraceAt raise' hRicci hn)
  have hRaise :
      HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ :=
    hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_ricciFlow hFlow hEntries y
  have hNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.ricciNormSqAt z) y := fun y ↦
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g y (hRicC2 y)
  have hScalar2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.scalarAt z) y := fun y ↦
    scalarAt_contMDiffAt_two_of_ricciFlow hFlow hEntries y
  have hQuot2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.pinchingQuotientAt z) y := fun y ↦
    contMDiffAt_two_pinchingQuotientAt
      g y (hNorm2 y) (hScalar2 y) (hRpos y).ne'
  have hPairDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ covRicciRicciPairingAt g y (extend E w y)) x :=
    fun w ↦
      covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
        g x (hNorm2 x) w
  have hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        g (ricciVariationField g) x :=
    covTensor2DerivExtDifferentiableAt_of_extSecond
      (g := g) (h := ricciVariationField g) (x := x)
      (covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two (hRicC2 x))
      (fun y ↦ covTensor2ExtDifferentiableAt_of_contMDiffAt_two (hRicC2 y))
      (tensor2AddLeft_ricciVariationField g)
      (tensor2SMulLeft_ricciVariationField g)
      (tensor2AddRight_ricciVariationField g)
      (tensor2SMulRight_ricciVariationField g)
  have hScalar : SatisfiesHamiltonScalarEvolutionAt gt t₀ x :=
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hFlow hJoint
  have hScalarGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.scalarAt y))) x :=
    g.mdifferentiableAt_gradient (hScalar2 x)
  have hQuotGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.pinchingQuotientAt y))) x :=
    g.mdifferentiableAt_gradient (hQuot2 x)
  have hScalarSq2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y * g.scalarAt y) x :=
    (hScalar2 x).smul (hScalar2 x)
  have hScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient
          (fun y : M ↦ g.scalarAt y * g.scalarAt y))) x :=
    g.mdifferentiableAt_gradient hScalarSq2
  have hQuotScalarSq2 : ContMDiffAt I 𝓘(ℝ) 2
      ((fun y : M ↦ g.pinchingQuotientAt y) *
        (fun y : M ↦ g.scalarAt y * g.scalarAt y)) x := by
    simpa only [Pi.mul_apply] using (hQuot2 x).smul hScalarSq2
  have hQuotScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient
          ((fun y : M ↦ g.pinchingQuotientAt y) *
            (fun y : M ↦ g.scalarAt y * g.scalarAt y)))) x :=
    g.mdifferentiableAt_gradient hQuotScalarSq2
  have hEvol :=
    satisfiesPinchingQuotientEvolutionAt_of_ricciFlow
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
      hRaise hRicci hScalar hn (hRpos x) (hNorm2 x) hPairDiff hRicSecond
      (hScalar2 x).continuousAt
      (fun y ↦ (hScalar2 y).mdifferentiableAt two_ne_zero)
      (fun y ↦ (hQuot2 y).mdifferentiableAt two_ne_zero)
      hScalarGrad hQuotGrad hScalarSqGrad hQuotScalarSqGrad
  simpa [ricciEvolutionPinchingReactionMotionTraceAt] using hEvol

/--
Automatic ordinary pinching-quotient evolution in the invariant cubic form
consumed by Hamilton's maximum-principle theorems.
-/
theorem satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_joint_metric_entries_three_cubic
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hn : n = 3)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y) :
    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
      gt t₀ x
        ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x) := by
  let htime : TimeDifferentiableAt gt t₀ x :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint x).of_le (by norm_num))
  let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
    satisfiesRicciEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hFlow hJoint
  have hEvol :=
    satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_joint_metric_entries_three
      (gt := gt) (t₀ := t₀) (x := x)
      hFlow hJoint hn hRpos
  change ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
    gt t₀ x
      (ricciEvolutionPinchingReactionMotionTraceAt
        (metricRaiseDerivAt gt t₀ x htime) hRicci hn) at hEvol
  rw [ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic
    htime (hFlow x) hRicci hn] at hEvol
  exact hEvol

/-! ## Joint continuity of the pinching quotients -/

/--
The fixed-coordinate contraction representing `|Ric|²` in an anchor chart.
Both inverse metric factors and both lower-Ricci factors are kept explicit so
joint regularity follows directly from the existing coordinate APIs.
-/
noncomputable def anchorChartRicciNormSqFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z : E) : ℝ :=
  let b := Module.finBasis ℝ E
  ∑ j, ∑ i, ∑ k, ∑ l,
    anchorChartInverseMetricCoeffFlow gt x t z j k *
      anchorChartInverseMetricCoeffFlow gt x t z i l *
      anchorChartRicciEntryFlow gt x t z (b k) (b l) *
      anchorChartRicciEntryFlow gt x t z (b i) (b j)

/-- Joint `C³` metric entries make the spatial Fréchet derivative of each
fixed-vector coordinate Ricci entry jointly continuous at the anchor. -/
theorem anchorChartRicciEntryFlow_spatialFDeriv_continuousAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) (v w : E) :
    ContinuousAt
      (fun p : ℝ × E ↦
        fderiv ℝ
          (fun z : E ↦ anchorChartRicciEntryFlow gt x p.1 z v w) p.2)
      (t₀, extChartAt I x x) := by
  exact continuousAt_spatial_fderiv_of_joint_contDiffAt_one_vector
    (fun t z ↦ anchorChartRicciEntryFlow gt x t z v w)
    t₀ (extChartAt I x x)
    (anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
      hJoint v w)

/-- Joint `C³` metric entries make the coordinate Ricci norm jointly `C¹`. -/
theorem anchorChartRicciNormSqFlow_jointContDiffAt_one_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 1
      (Function.uncurry (anchorChartRicciNormSqFlow gt x))
      (t₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  unfold anchorChartRicciNormSqFlow
  dsimp only
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.sum
  intro l _
  have hjk : ContDiffAt ℝ 1
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z j k))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint j k).of_le (by norm_num)
  have hil : ContDiffAt ℝ 1
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z i l))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint i l).of_le (by norm_num)
  have hkl :=
    anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
      hJoint (b k) (b l)
  have hij :=
    anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
      hJoint (b i) (b j)
  exact ((hjk.mul hil).mul hkl).mul hij

/--
On the cutoff-one part of the preferred chart, the finite coordinate
contraction is exactly the intrinsic squared Ricci norm.
-/
theorem anchorChartRicciNormSqFlow_eq_ricciNormSqAt_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in 𝓝 z,
      GeodesicTransport.cutoff (n := n) x z' = 1) :
    anchorChartRicciNormSqFlow gt x t z =
      (gt t).ricciNormSqAt ((extChartAt I x).symm z) := by
  classical
  let g : ClosedSmoothRiemannianMetric n M := gt t
  let y : M := (extChartAt I x).symm z
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  let b := Module.finBasis ℝ E
  let B := chartTangentBasisAt (n := n) (M := M) x hz
  let G := anchorBlendedMetricFlow gt x t z
  let raised : Fin (Module.finrank ℝ E) → E := fun i ↦
    G.inverse (LinearMap.toContinuousLinearMap (b.coord i))
  have hχ : GeodesicTransport.cutoff (n := n) x z = 1 :=
    hχone.self_of_nhds
  have he : (e : E →L[ℝ] E) =
      ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z :=
    chartInverseTangentEquiv_toContinuousLinearMap x z hz
  have hRic : ∀ v w : E,
      anchorChartRicciEntryFlow gt x t z v w =
        g.ricciAt y (e v) (e w) := by
    intro v w
    rw [anchorChartRicciEntryFlow_eq_deTurckChartRicciBilin_zone
      gt x t hz hχone]
    unfold deTurckChartRicciBilin
    rw [CovariantDerivative.chartMetric_apply]
    change ricciContinuousBilinAt g y
        (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z v)
        (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z w) = _
    rw [← he, ricciContinuousBilinAt_apply]
    rfl
  have hBasis : ∀ i, B i = e (b i) := by
    intro i
    rw [show B = b.map e.toLinearEquiv by
      simpa [B, b, e] using
        chartTangentBasisAt_eq_finBasis_map_chartInverseTangentEquiv x hz]
    rfl
  have hRaised : ∀ i,
      e (raised i) = metricDualVectorAt g y (B.coord i) := by
    intro i
    simpa [raised, G, g, y, e, B, b] using
      chartInverseTangentEquiv_anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt_zone
        gt x t hz hχ i
  have hInv : ∀ i k,
      anchorChartInverseMetricCoeffFlow gt x t z i k =
        b.coord k (raised i) := by
    intro i k
    rfl
  have hMapRepr : ∀ q : E,
      (∑ i, b.coord i q • e (b i)) = e q := by
    intro q
    have hrepr : (∑ i, b.coord i q • b i) = q := by
      change (∑ i, (b.repr q) i • b i) = q
      exact b.sum_repr q
    calc
      (∑ i, b.coord i q • e (b i)) =
          ∑ i, e (b.coord i q • b i) := by simp
      _ = e (∑ i, b.coord i q • b i) := by rw [map_sum]
      _ = e q := by rw [hrepr]
  have hRight : ∀ v q : E,
      (∑ i, b.coord i q * g.ricciAt y (e v) (e (b i))) =
        g.ricciAt y (e v) (e q) := by
    intro v q
    let R : E →L[ℝ] ℝ := ricciContinuousBilinAt g y (e v)
    calc
      (∑ i, b.coord i q * g.ricciAt y (e v) (e (b i))) =
          ∑ i, R (b.coord i q • e (b i)) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          b.coord i q * g.ricciAt y (e v) (e (b i)) =
              b.coord i q * R (e (b i)) := by
            rw [show R (e (b i)) = g.ricciAt y (e v) (e (b i)) by
              exact ricciContinuousBilinAt_apply g y (e v) (e (b i))]
          _ = b.coord i q • R (e (b i)) := rfl
          _ = R (b.coord i q • e (b i)) := by rw [map_smul]
      _ = R (∑ i, b.coord i q • e (b i)) := by rw [map_sum]
      _ = R (e q) := by rw [hMapRepr]
      _ = g.ricciAt y (e v) (e q) :=
        ricciContinuousBilinAt_apply g y (e v) (e q)
  have hDouble : ∀ j i,
      (∑ k, ∑ l,
        b.coord k (raised j) * b.coord l (raised i) *
          g.ricciAt y (e (b k)) (e (b l))) =
        g.ricciAt y (e (raised j)) (e (raised i)) := by
    intro j i
    calc
      (∑ k, ∑ l,
          b.coord k (raised j) * b.coord l (raised i) *
            g.ricciAt y (e (b k)) (e (b l))) =
          ∑ k, b.coord k (raised j) *
            (∑ l, b.coord l (raised i) *
              g.ricciAt y (e (b k)) (e (b l))) := by
        simp [Finset.mul_sum, mul_assoc]
      _ = ∑ k, b.coord k (raised j) *
          g.ricciAt y (e (b k)) (e (raised i)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hRight (b k) (raised i)]
      _ = ∑ k, b.coord k (raised j) *
          g.ricciAt y (e (raised i)) (e (b k)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [g.ricciAt_symm]
      _ = g.ricciAt y (e (raised i)) (e (raised j)) :=
        hRight (raised i) (raised j)
      _ = g.ricciAt y (e (raised j)) (e (raised i)) :=
        g.ricciAt_symm y _ _
  calc
    anchorChartRicciNormSqFlow gt x t z =
        ∑ j, ∑ i,
          (∑ k, ∑ l,
            b.coord k (raised j) * b.coord l (raised i) *
              g.ricciAt y (e (b k)) (e (b l))) *
            g.ricciAt y (e (b i)) (e (b j)) := by
      unfold anchorChartRicciNormSqFlow
      dsimp only
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [hInv j k, hInv i l, hRic (b k) (b l), hRic (b i) (b j)]
    _ = ∑ j, ∑ i,
        g.ricciAt y (e (raised j)) (e (raised i)) *
          g.ricciAt y (e (b i)) (e (b j)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hDouble j i]
    _ = ∑ j, ∑ i,
        g.ricciAt y (metricDualVectorAt g y (B.coord j))
            (metricDualVectorAt g y (B.coord i)) *
          g.ricciAt y (B i) (B j) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [← hRaised j, ← hRaised i, hBasis i, hBasis j]
    _ = g.ricciNormSqAt y :=
      (ricciNormSqAt_eq_basis_sum (g := g) (x := y) B).symm
    _ = (gt t).ricciNormSqAt ((extChartAt I x).symm z) := rfl

/-- Joint `C³` metric entries give genuine joint space-time continuity of
the intrinsic squared Ricci norm. -/
theorem continuousAt_ricciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt (fun p : ℝ × M ↦ (gt p.1).ricciNormSqAt p.2) (t₀, x) := by
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ nhds (extChartAt I x x) := by
    apply hopen.mem_nhds
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hchart :
      ContinuousAt (fun p : ℝ × M ↦ extChartAt I x p.2) (t₀, x) :=
    ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ p.2)
      (g := fun y : M ↦ extChartAt I x y)
      (x := (t₀, x)) (continuousAt_extChartAt x) continuousAt_snd
  have hchartPair :
      ContinuousAt
        (fun p : ℝ × M ↦ (p.1, extChartAt I x p.2)) (t₀, x) :=
    continuousAt_fst.prodMk hchart
  have hcoord :
      ContinuousAt
        (Function.uncurry (anchorChartRicciNormSqFlow gt x))
        (t₀, extChartAt I x x) :=
    (anchorChartRicciNormSqFlow_jointContDiffAt_one_of_metricEntries
      hJoint).continuousAt
  have hchartNorm :
      ContinuousAt
        (fun p : ℝ × M ↦
          anchorChartRicciNormSqFlow gt x p.1 (extChartAt I x p.2))
        (t₀, x) :=
    ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
      (g := Function.uncurry (anchorChartRicciNormSqFlow gt x))
      (x := (t₀, x)) hcoord hchartPair
  have hsource :
      ∀ᶠ p : ℝ × M in nhds (t₀, x),
        p.2 ∈ (extChartAt I x).source :=
    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
  have hone :
      ∀ᶠ p : ℝ × M in nhds (t₀, x),
        extChartAt I x p.2 ∈ oneLocus :=
    hchart.eventually hone_mem
  have hEq :
      (fun p : ℝ × M ↦ (gt p.1).ricciNormSqAt p.2)
        =ᶠ[nhds (t₀, x)]
      (fun p : ℝ × M ↦
        anchorChartRicciNormSqFlow gt x p.1 (extChartAt I x p.2)) := by
    filter_upwards [hsource, hone] with p hpSource hpOne
    have hz : extChartAt I x p.2 ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hpSource
    have hχone :
        ∀ᶠ z' in nhds (extChartAt I x p.2),
          GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    symm
    calc
      anchorChartRicciNormSqFlow gt x p.1 (extChartAt I x p.2) =
          (gt p.1).ricciNormSqAt
            ((extChartAt I x).symm (extChartAt I x p.2)) :=
        anchorChartRicciNormSqFlow_eq_ricciNormSqAt_zone
          gt x p.1 hz hχone
      _ = (gt p.1).ricciNormSqAt p.2 := by
        rw [(extChartAt I x).left_inv hpSource]
  exact hchartNorm.congr_of_eventuallyEq hEq

/-- Joint continuity of Hamilton's ordinary quotient at every point where
scalar curvature is nonzero. -/
theorem continuousAt_pinchingQuotientAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (hRne : (gt t₀).scalarAt x ≠ 0) :
    ContinuousAt (fun p : ℝ × M ↦ (gt p.1).pinchingQuotientAt p.2)
      (t₀, x) := by
  have hNorm :=
    continuousAt_ricciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
      hJoint
  have hScalar :=
    continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three hJoint
  simpa [ClosedSmoothRiemannianMetric.pinchingQuotientAt] using
    hNorm.div (hScalar.pow 2) (pow_ne_zero 2 hRne)

/-- Joint continuity of the improved traceless quotient on the
positive-scalar-curvature region. -/
theorem continuousAt_tracelessPinchingAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ δ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (hRpos : 0 < (gt t₀).scalarAt x) :
    ContinuousAt (fun p : ℝ × M ↦ (gt p.1).tracelessPinchingAt p.2 δ)
      (t₀, x) := by
  have hNorm :=
    continuousAt_ricciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
      hJoint
  have hScalar :=
    continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three hJoint
  have hTraceNorm : ContinuousAt
      (fun p : ℝ × M ↦ (gt p.1).tracelessRicciNormSqAt p.2)
      (t₀, x) := by
    simpa [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt] using
      hNorm.sub ((hScalar.pow 2).div_const n)
  have hPow : ContinuousAt
      (fun p : ℝ × M ↦ ((gt p.1).scalarAt p.2) ^ (2 - δ))
      (t₀, x) :=
    hScalar.rpow_const (Or.inl hRpos.ne')
  have hPowNe : ((gt t₀).scalarAt x) ^ (2 - δ) ≠ 0 :=
    (Real.rpow_pos_of_pos hRpos (2 - δ)).ne'
  simpa [ClosedSmoothRiemannianMetric.tracelessPinchingAt] using
    hTraceNorm.div hPow hPowNe

/-- Global joint metric-entry regularity and scalar nonvanishing automatically
supply the ordinary quotient-track continuity used by the compact maximum
principle. -/
theorem continuous_pinchingQuotientTrack_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} (t₀ : ℝ)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hRne : ∀ t : ℝ, ∀ x : M, (gt t).scalarAt x ≠ 0) :
    Continuous ↿(fun τ (x : M) ↦
      (gt (t₀ + τ)).pinchingQuotientAt x) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨τ, x⟩
  have hQ :=
    continuousAt_pinchingQuotientAt_joint_of_metricEntriesJointContDiffAt_three
      (hJoint (t₀ + τ) x) (hRne (t₀ + τ) x)
  have hshift : ContinuousAt
      (fun p : ℝ × M ↦ (t₀ + p.1, p.2)) (τ, x) :=
    (continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd
  simpa using ContinuousAt.comp'
    (f := fun p : ℝ × M ↦ (t₀ + p.1, p.2))
    (g := fun p : ℝ × M ↦ (gt p.1).pinchingQuotientAt p.2)
    (x := (τ, x)) hQ hshift

/-- Global positive scalar curvature gives automatic continuity of every
improved traceless quotient track. -/
theorem continuous_tracelessPinchingTrack_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} (t₀ δ : ℝ)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hRpos : ∀ t : ℝ, ∀ x : M, 0 < (gt t).scalarAt x) :
    Continuous ↿(fun τ (x : M) ↦
      (gt (t₀ + τ)).tracelessPinchingAt x δ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨τ, x⟩
  have hQ :=
    continuousAt_tracelessPinchingAt_joint_of_metricEntriesJointContDiffAt_three
      (δ := δ) (hJoint (t₀ + τ) x) (hRpos (t₀ + τ) x)
  have hshift : ContinuousAt
      (fun p : ℝ × M ↦ (t₀ + p.1, p.2)) (τ, x) :=
    (continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd
  simpa using ContinuousAt.comp'
    (f := fun p : ℝ × M ↦ (t₀ + p.1, p.2))
    (g := fun p : ℝ × M ↦ (gt p.1).tracelessPinchingAt p.2 δ)
    (x := (τ, x)) hQ hshift

/-- Interval-local joint regularity already gives the exact `ContinuousOn`
ordinary quotient track on the maximum-principle slab. -/
theorem continuousOn_pinchingQuotientAt_timeShift_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
    (hJoint : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      MetricEntriesJointContDiffAt gt (t₀ + τ) x 3)
    (hRne : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).scalarAt x ≠ 0) :
    ContinuousOn
      (↿fun τ (x : M) ↦ (gt (t₀ + τ)).pinchingQuotientAt x)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
  intro p hp
  have hQ :=
    continuousAt_pinchingQuotientAt_joint_of_metricEntriesJointContDiffAt_three
      (hJoint p.1 hp.1 p.2) (hRne p.1 hp.1 p.2)
  have hshift : ContinuousAt
      (fun q : ℝ × M ↦ (t₀ + q.1, q.2)) p :=
    (continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd
  exact (ContinuousAt.comp'
    (f := fun q : ℝ × M ↦ (t₀ + q.1, q.2))
    (g := fun q : ℝ × M ↦ (gt q.1).pinchingQuotientAt q.2)
    (x := p) hQ hshift).continuousWithinAt

/-- Interval-local joint regularity and positivity likewise give the exact
`ContinuousOn` improved quotient track on the slab. -/
theorem continuousOn_tracelessPinchingAt_timeShift_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T δ : ℝ}
    (hJoint : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      MetricEntriesJointContDiffAt gt (t₀ + τ) x 3)
    (hRpos : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      0 < (gt (t₀ + τ)).scalarAt x) :
    ContinuousOn
      (↿fun τ (x : M) ↦ (gt (t₀ + τ)).tracelessPinchingAt x δ)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
  intro p hp
  have hQ :=
    continuousAt_tracelessPinchingAt_joint_of_metricEntriesJointContDiffAt_three
      (δ := δ) (hJoint p.1 hp.1 p.2) (hRpos p.1 hp.1 p.2)
  have hshift : ContinuousAt
      (fun q : ℝ × M ↦ (t₀ + q.1, q.2)) p :=
    (continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd
  exact (ContinuousAt.comp'
    (f := fun q : ℝ × M ↦ (t₀ + q.1, q.2))
    (g := fun q : ℝ × M ↦ (gt q.1).tracelessPinchingAt q.2 δ)
    (x := p) hQ hshift).continuousWithinAt

/--
Joint `C³` metric entries on a Ricci-flow slice automatically give the
spatial `C²` regularity of Hamilton's ordinary pinching quotient.
-/
theorem contMDiffAt_two_pinchingQuotientAt_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).pinchingQuotientAt y) x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_ricciFlow hFlow hEntries y
  have hNorm2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x :=
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g x (hRicC2 x)
  have hScalar2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x :=
    scalarAt_contMDiffAt_two_of_ricciFlow hFlow hEntries x
  exact contMDiffAt_two_pinchingQuotientAt
    g x hNorm2 hScalar2 (hRpos x).ne'

/--
The improved traceless quotient has the same automatic spatial `C²`
regularity on every positive-scalar-curvature Ricci-flow slice.
-/
theorem contMDiffAt_two_tracelessPinchingAt_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (x : M) (δ : ℝ)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).tracelessPinchingAt y δ) x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_ricciFlow hFlow hEntries y
  have hNorm2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x :=
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g x (hRicC2 x)
  have hScalar2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x :=
    scalarAt_contMDiffAt_two_of_ricciFlow hFlow hEntries x
  have hTraceNorm2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.tracelessRicciNormSqAt y) x :=
    contMDiffAt_two_tracelessRicciNormSqAt g x hNorm2 hScalar2
  exact contMDiffAt_two_tracelessPinchingAt
    g x δ hTraceNorm2 hScalar2 (hRpos x)

/--
At a spatial maximum, the automatic cubic quotient evolution already gives
Hamilton's nonpositive time-derivative step, with no separate regularity or
tensor-evolution witnesses.
-/
theorem hamilton_pinching_spatial_max_step_at_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3)
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y)
    (hmax :
      IsMaxOn (fun y : M ↦ (gt t₀).pinchingQuotientAt y) Set.univ x) :
    ∃ Q' : ℝ,
      HasDerivAt (fun t ↦ (gt t).pinchingQuotientAt x) Q' t₀ ∧
        Q' ≤ 0 := by
  have hQ₂ : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ (gt t₀).pinchingQuotientAt z) y := fun y ↦
    contMDiffAt_two_pinchingQuotientAt_of_ricciFlow_joint_metric_entries_three
      (gt := gt) (t₀ := t₀) y hFlow hJoint hRpos
  have hEvol :
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt t₀ x
          ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x) :=
    satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_joint_metric_entries_three_cubic
      (gt := gt) (t₀ := t₀) (x := x) hFlow hJoint hn hRpos
  exact hamilton_pinching_spatial_max_step_at hn hEvol hQ₂ hmax

/--
The corresponding spatial-maximum step for Hamilton's improved traceless
quotient.  The only extra input is the eigenvalue floor that makes the exact
cubic reaction nonpositive.
-/
theorem hamilton_traceless_pinching_spatial_max_step_at_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ ε δ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3)
    (hεpos : 0 < ε) (hεle : ε ≤ 1 / 3)
    (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hδadm : δ ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 ε)
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y)
    (hPin :
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (μ : Fin 3 → ℝ),
        (∀ i : Fin 3, (gt t₀).ricciEndoAt x (b i) = μ i • b i) →
          ∀ i : Fin 3, ε * (gt t₀).scalarAt x ≤ μ i)
    (hmax :
      IsMaxOn (fun y : M ↦ (gt t₀).tracelessPinchingAt y δ)
        Set.univ x) :
    ∃ F' : ℝ,
      HasDerivAt (fun t ↦ (gt t).tracelessPinchingAt x δ) F' t₀ ∧
        F' ≤ 0 := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let Qf : M → ℝ := fun y ↦ g.tracelessPinchingAt y δ
  have hQ₂ : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 Qf y := fun y ↦ by
    simpa [g, Qf] using
      contMDiffAt_two_tracelessPinchingAt_of_ricciFlow_joint_metric_entries_three
        (gt := gt) (t₀ := t₀) y δ hFlow hJoint hRpos
  have hEvol :
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t₀ x δ
          (g.pinchingRicciNormReactionMotionTraceCubicAt x) := by
    simpa [g] using
      satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow_joint_metric_entries_three_cubic
        (gt := gt) (t₀ := t₀) (x := x) (δ := δ)
        hFlow hJoint hn hδpos hδle hRpos
  rcases hEvol with ⟨_, _, hRx, F', hFderiv, hFineq⟩
  refine ⟨F', hFderiv, ?_⟩
  have hlocalMax : IsLocalMax Qf x := by
    simpa [g, Qf] using hmax.isLocalMax Filter.univ_mem
  have hlap : g.laplacianAt Qf x ≤ 0 :=
    laplacianAt_nonpos_of_isLocalMax
      (g := g) (f := Qf) (x := x) hQ₂ hlocalMax
  have hgrad : g.gradientAt Qf x = 0 :=
    gradientAt_eq_zero_of_isLocalMax
      (g := g) (f := Qf) (x := x) (hQ₂ x) hlocalMax
  have hdrift : g.tracelessPinchingGradientDrift3At x δ = 0 := by
    unfold ClosedSmoothRiemannianMetric.tracelessPinchingGradientDrift3At
    change ((2 - δ) / g.scalarAt x) *
      g.inner x (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
        (g.gradientAt Qf x) = 0
    rw [hgrad]
    simp
  have hreact :
      g.tracelessPinchingReactionTermAt x δ
          (g.pinchingTracelessRicciReactionTrace3At x
            (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ≤ 0 :=
    g.tracelessPinchingReactionTermAt_nonpos_of_eigenvalue_pinched
      hn hεpos hεle (le_of_lt hδpos) hδadm hRx (by simpa [g] using hPin)
  have hFineq' : F' ≤ g.laplacianAt Qf x +
      g.tracelessPinchingGradientDrift3At x δ +
        g.tracelessPinchingReactionTermAt x δ
          (g.pinchingTracelessRicciReactionTrace3At x
            (g.pinchingRicciNormReactionMotionTraceCubicAt x)) := by
    simpa [g, Qf] using hFineq
  linarith

/--
Hamilton's slab-local pinching preservation theorem for the scalar-normalized Ricci
quotient on a compact closed three-dimensional Ricci-flow track.

The statement is the maximum-track form: the spatial maximum of
`|Ric|² / R²` is nonincreasing on the shifted interval `[0, T]`.
-/
theorem hamilton_pinching_preserved_continuousOn
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 ≤ T)
    (hQ_cont :
      ContinuousOn
        (↿fun τ (x : M) ↦ (gt (t₀ + τ)).pinchingQuotientAt x)
        (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hQ₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).pinchingQuotientAt y) x)
    (hEvol : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t₀ + τ) x
          ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x)) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      pinchingMaximumTrack gt t₀ τ ≤ pinchingMaximumTrack gt t₀ 0 := by
  classical
  let Q : ℝ → M → ℝ := fun τ x ↦ (gt (t₀ + τ)).pinchingQuotientAt x
  let C : ℝ := pinchingMaximumTrack gt t₀ 0
  let u : ℝ → M → ℝ := fun τ x ↦ C - Q τ x
  let Q' : ℝ → M → ℝ := fun τ x ↦
    if hτ : τ ∈ Icc (0 : ℝ) T then
      Classical.choose (hEvol τ hτ x).2
    else 0
  let u' : ℝ → M → ℝ := fun τ x ↦ -Q' τ x
  let L : ℝ → (M → ℝ) → M → ℝ := fun τ f x ↦
    let g := gt (t₀ + τ)
    g.laplacianAt f x +
      (2 / g.scalarAt x) *
        g.inner x
          (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
          (g.gradientAt f x)
  have hQd : ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ Q s x) (Q' τ x) τ := by
    intro x τ hτ
    have hτpair : 0 ≤ τ ∧ τ ≤ T := ⟨hτ.1, hτ.2⟩
    have hspec := Classical.choose_spec (hEvol τ hτpair x).2
    have hbase :
        HasDerivAt (fun t ↦ (gt t).pinchingQuotientAt x) (Q' τ x) (t₀ + τ) := by
      simpa [Q', hτpair] using hspec.1
    have hshift : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add t₀
    simpa [Q] using hbase.comp τ hshift
  have hud : ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' τ x) τ := by
    intro x τ hτ
    have hconst : HasDerivAt (fun _ : ℝ ↦ C) 0 τ := hasDerivAt_const τ C
    simpa [u, u'] using hconst.sub (hQd x τ hτ)
  have hQ0₂ :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t₀).pinchingQuotientAt y) x := by
    intro x
    simpa using hQ₂ 0 ⟨le_refl 0, hT0⟩ x
  have h0point : ∀ x : M, 0 ≤ u 0 x := by
    intro x
    have hle :=
      pinchingQuotientAt_le_pinchingMaximumAt
        (g := gt t₀) hQ0₂ x
    simpa [u, Q, C, pinchingMaximumTrack] using sub_nonneg.mpr hle
  have hQtoU₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2 (u τ) x := by
    intro τ hτ x
    have hconst : ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ C) x :=
      contMDiffAt_const
    simpa [u, Q] using hconst.sub (hQ₂ τ hτ x)
  have hlap_add_const : ∀ τ ∈ Icc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      L τ (fun y : M ↦ u τ y + k) x = L τ (u τ) x := by
    intro τ hτ k x
    let g := gt (t₀ + τ)
    have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (u τ) y :=
      hQtoU₂ τ hτ
    have hk : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ k) y :=
      fun _ ↦ contMDiffAt_const
    have hlap :
        g.laplacianAt (fun y : M ↦ u τ y + k) x =
          g.laplacianAt (u τ) x := by
      change g.laplacianAt ((u τ) + fun _ : M ↦ k) x =
        g.laplacianAt (u τ) x
      rw [g.laplacianAt_add' (f := u τ) (h := fun _ : M ↦ k) (x := x) hf hk]
      rw [g.laplacianAt_const k x]
      ring
    have hgrad :
        g.gradientAt (fun y : M ↦ u τ y + k) x =
          g.gradientAt (u τ) x := by
      change g.gradientAt ((u τ) + fun _ : M ↦ k) x =
        g.gradientAt (u τ) x
      rw [g.gradientAt_add
        ((hf x).mdifferentiableAt two_ne_zero) mdifferentiableAt_const]
      rw [g.gradientAt_const k x]
      simp
    change
      g.laplacianAt (fun y : M ↦ u τ y + k) x +
          (2 / g.scalarAt x) *
            g.inner x
              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
              (g.gradientAt (fun y : M ↦ u τ y + k) x) =
        g.laplacianAt (u τ) x +
          (2 / g.scalarAt x) *
            g.inner x
              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
              (g.gradientAt (u τ) x)
    rw [hlap, hgrad]
  have hsuper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      L τ (u τ) x ≤ u' τ x := by
    intro τ hτ x
    let g := gt (t₀ + τ)
    have hfQ : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (Q τ) y := by
      intro y
      simpa [Q, g] using hQ₂ τ hτ y
    have hfU : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (u τ) y :=
      hQtoU₂ τ hτ
    have hτpair : 0 ≤ τ ∧ τ ≤ T := ⟨hτ.1, hτ.2⟩
    have hspec := Classical.choose_spec (hEvol τ hτpair x).2
    have hRpos : 0 < g.scalarAt x := by
      simpa [g] using (hEvol τ hτ x).1
    have hQineq :
        Q' τ x ≤
          g.laplacianAt (Q τ) x
            + g.pinchingQuotientGradientDrift3At x
            + g.pinchingGradientDampingAt x
            + (2 / (g.scalarAt x) ^ 4) *
              g.pinchingReactionRemainderAt x
                (g.pinchingRicciNormReactionMotionTraceCubicAt x) := by
      simpa [Q', Q, g, hτpair] using hspec.2
    have hdamp :
        g.pinchingGradientDampingAt x ≤ 0 :=
      g.pinchingGradientDampingAt_nonpos hRpos
    have hreact :
        g.pinchingReactionRemainderAt x
            (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤ 0 :=
      g.pinchingReactionRemainderAt_nonpos_of_scalar_pos hn hRpos
    have hcoef_nonneg :
        0 ≤ 2 / (g.scalarAt x) ^ 4 := by
      have hpow : 0 < (g.scalarAt x) ^ 4 := pow_pos hRpos 4
      exact le_of_lt (div_pos (by norm_num) hpow)
    have hreactTerm :
        (2 / (g.scalarAt x) ^ 4) *
            g.pinchingReactionRemainderAt x
              (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg hreact
    have hQineq' :
        Q' τ x ≤ g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x := by
      linarith
    have hUfun :
        u τ = (fun _ : M ↦ C) + (-1 : ℝ) • (Q τ) := by
      funext y
      simp [u, Q, sub_eq_add_neg]
    have hlapU :
        g.laplacianAt (u τ) x = -g.laplacianAt (Q τ) x := by
      rw [hUfun]
      rw [g.laplacianAt_add' (f := fun _ : M ↦ C)
        (h := (-1 : ℝ) • (Q τ)) (x := x)
        (fun _ ↦ contMDiffAt_const)
        (fun y ↦ contMDiffAt_const.smul (hfQ y))]
      rw [g.laplacianAt_const C x]
      rw [g.laplacianAt_const_smul' (c := -1) (f := Q τ) (x := x) hfQ]
      ring
    have hgradU :
        g.gradientAt (u τ) x = -g.gradientAt (Q τ) x := by
      rw [hUfun]
      rw [g.gradientAt_add
        (f := fun _ : M ↦ C) (h := (-1 : ℝ) • (Q τ)) (x := x)
        mdifferentiableAt_const
        ((contMDiffAt_const.smul (hfQ x)).mdifferentiableAt two_ne_zero)]
      rw [g.gradientAt_const C x]
      rw [g.gradientAt_const_smul (c := -1) (f := Q τ) (x := x)
        ((hfQ x).mdifferentiableAt two_ne_zero)]
      simp
    have hdriftU :
        (2 / g.scalarAt x) *
            g.inner x
              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
              (g.gradientAt (u τ) x) =
          -g.pinchingQuotientGradientDrift3At x := by
      have hQfun : Q τ = fun y : M ↦ g.pinchingQuotientAt y := by
        funext y
        simp [Q, g]
      unfold ClosedSmoothRiemannianMetric.pinchingQuotientGradientDrift3At
      rw [hgradU, hQfun]
      simp
    have hL :
        L τ (u τ) x =
          -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x) := by
      change
        g.laplacianAt (u τ) x +
            (2 / g.scalarAt x) *
              g.inner x
                (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
                (g.gradientAt (u τ) x) =
          -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x)
      rw [hlapU, hdriftU]
      ring
    rw [hL]
    simpa [u'] using neg_le_neg hQineq'
  have hmin_lap : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u τ) Set.univ x → 0 ≤ L τ (u τ) x := by
    intro τ hτ x hmin
    let g := gt (t₀ + τ)
    have hfU : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (u τ) y :=
      hQtoU₂ τ hτ
    have hlocalMin : IsLocalMin (u τ) x :=
      hmin.isLocalMin Filter.univ_mem
    have hlap :
        0 ≤ g.laplacianAt (u τ) x :=
      laplacianAt_nonneg_of_isLocalMin
        (g := g) (f := u τ) (x := x) (hfU x)
        (g.mdifferentiableAt_gradient (hfU x)) hlocalMin
    have hgrad :
        g.gradientAt (u τ) x = 0 :=
      gradientAt_eq_zero_of_isLocalMin
        (g := g) (f := u τ) (x := x) (hfU x) hlocalMin
    change
      0 ≤ g.laplacianAt (u τ) x +
        (2 / g.scalarAt x) *
          g.inner x
            (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
            (g.gradientAt (u τ) x)
    rw [hgrad]
    simpa using hlap
  have hkey := closed_parabolic_min_principle_var_continuousOn
    (lap := L) (u := u) (u' := u') (c := fun _ _ ↦ (0 : ℝ))
    (T := T) (M₀ := 0)
    hT0
    (by intro τ hτ x; exact le_refl (0 : ℝ))
    (by
      simpa [u, Q, C, Function.uncurry] using
        (continuous_const.continuousOn.sub hQ_cont))
    hud
    hlap_add_const
    (by
      intro τ hτ x
      simpa using hsuper τ hτ x)
    hmin_lap
    h0point
  intro τ hτ
  obtain ⟨xτ, hxτmax⟩ :=
    exists_pinchingQuotientAt_isMaxOn
      (g := gt (t₀ + τ)) (hQ₂ τ hτ)
  have hnonneg := hkey τ hτ xτ
  have hQle : Q τ xτ ≤ C := by
    simpa [u] using hnonneg
  rw [pinchingMaximumTrack, pinchingMaximumAt_eq_of_isMaxOn
    (g := gt (t₀ + τ)) hxτmax]
  simpa [Q, C] using hQle


/--
Hamilton's compact-track pinching preservation theorem with every local PDE
and spatial regularity hypothesis reconstructed from a genuine Ricci flow
whose metric entries are jointly `C³` along the interval.
-/
theorem hamilton_pinching_preserved_of_ricciFlow_joint_metric_entries_three
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 ≤ T)
    (hFlow : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      IsClosedRicciFlowSolutionAt gt (t₀ + τ) y)
    (hJoint : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      MetricEntriesJointContDiffAt gt (t₀ + τ) y 3)
    (hRpos : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      0 < (gt (t₀ + τ)).scalarAt y) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      pinchingMaximumTrack gt t₀ τ ≤ pinchingMaximumTrack gt t₀ 0 := by
  have hQ₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).pinchingQuotientAt y) x := by
    intro τ hτ x
    exact contMDiffAt_two_pinchingQuotientAt_of_ricciFlow_joint_metric_entries_three
      (gt := gt) (t₀ := t₀ + τ) x
      (hFlow τ hτ) (hJoint τ hτ) (hRpos τ hτ)
  have hEvol : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t₀ + τ) x
          ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x) := by
    intro τ hτ x
    exact satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_joint_metric_entries_three_cubic
      (gt := gt) (t₀ := t₀ + τ) (x := x)
      (hFlow τ hτ) (hJoint τ hτ) hn (hRpos τ hτ)
  have hQ_cont : ContinuousOn
      (↿fun τ (x : M) ↦ (gt (t₀ + τ)).pinchingQuotientAt x)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    continuousOn_pinchingQuotientAt_timeShift_of_metricEntriesJointContDiffAt_three
      hJoint (fun τ hτ x ↦ (hRpos τ hτ x).ne')
  exact hamilton_pinching_preserved_continuousOn
    (gt := gt) (t₀ := t₀) (T := T)
    hn hT0 hQ_cont hQ₂ hEvol

/--
Hamilton's slab-local improved traceless pinching maximum principle.  Under positive
scalar curvature, the improved evolution inequality, and an epsilon
Ricci-eigenvalue pinching floor strong enough to make the improved reaction
nonpositive, the spatial maximum of
`|Ric°|² / R^(2 - delta)` is nonincreasing.
-/
theorem hamilton_pinching_improvement_continuousOn
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T ε δ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 ≤ T)
    (hεpos : 0 < ε) (hεle : ε ≤ 1 / 3)
    (hδnonneg : 0 ≤ δ)
    (hδadm : δ ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 ε)
    (hQ_cont :
      ContinuousOn
        (↿fun τ (x : M) ↦ (gt (t₀ + τ)).tracelessPinchingAt x δ)
        (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hQ₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).tracelessPinchingAt y δ) x)
    (hEvol : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t₀ + τ) x δ
          ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hPin : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (μ : Fin 3 → ℝ),
        (∀ i : Fin 3, (gt (t₀ + τ)).ricciEndoAt x (b i) = μ i • b i) →
          ∀ i : Fin 3, ε * (gt (t₀ + τ)).scalarAt x ≤ μ i) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      tracelessPinchingMaximumTrack gt t₀ δ τ ≤
        tracelessPinchingMaximumTrack gt t₀ δ 0 := by
  classical
  let Q : ℝ → M → ℝ := fun τ x ↦ (gt (t₀ + τ)).tracelessPinchingAt x δ
  let C : ℝ := tracelessPinchingMaximumTrack gt t₀ δ 0
  let u : ℝ → M → ℝ := fun τ x ↦ C - Q τ x
  let Q' : ℝ → M → ℝ := fun τ x ↦
    if hτ : τ ∈ Icc (0 : ℝ) T then
      Classical.choose (hEvol τ hτ x).2.2.2
    else 0
  let u' : ℝ → M → ℝ := fun τ x ↦ -Q' τ x
  let L : ℝ → (M → ℝ) → M → ℝ := fun τ f x ↦
    let g := gt (t₀ + τ)
    g.laplacianAt f x +
      ((2 - δ) / g.scalarAt x) *
        g.inner x
          (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
          (g.gradientAt f x)
  have hQd : ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ Q s x) (Q' τ x) τ := by
    intro x τ hτ
    have hτpair : 0 ≤ τ ∧ τ ≤ T := ⟨hτ.1, hτ.2⟩
    have hspec := Classical.choose_spec (hEvol τ hτpair x).2.2.2
    have hbase :
        HasDerivAt (fun t ↦ (gt t).tracelessPinchingAt x δ)
          (Q' τ x) (t₀ + τ) := by
      simpa [Q', hτpair] using hspec.1
    have hshift : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add t₀
    simpa [Q] using hbase.comp τ hshift
  have hud : ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' τ x) τ := by
    intro x τ hτ
    have hconst : HasDerivAt (fun _ : ℝ ↦ C) 0 τ := hasDerivAt_const τ C
    simpa [u, u'] using hconst.sub (hQd x τ hτ)
  have hQ0₂ :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t₀).tracelessPinchingAt y δ) x := by
    intro x
    simpa using hQ₂ 0 ⟨le_refl 0, hT0⟩ x
  have h0point : ∀ x : M, 0 ≤ u 0 x := by
    intro x
    have hle :=
      tracelessPinchingAt_le_tracelessPinchingMaximumAt
        (g := gt t₀) δ hQ0₂ x
    simpa [u, Q, C, tracelessPinchingMaximumTrack] using sub_nonneg.mpr hle
  have hQtoU₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2 (u τ) x := by
    intro τ hτ x
    have hconst : ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ C) x :=
      contMDiffAt_const
    simpa [u, Q] using hconst.sub (hQ₂ τ hτ x)
  have hlap_add_const : ∀ τ ∈ Icc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      L τ (fun y : M ↦ u τ y + k) x = L τ (u τ) x := by
    intro τ hτ k x
    let g := gt (t₀ + τ)
    have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (u τ) y :=
      hQtoU₂ τ hτ
    have hk : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ k) y :=
      fun _ ↦ contMDiffAt_const
    have hlap :
        g.laplacianAt (fun y : M ↦ u τ y + k) x =
          g.laplacianAt (u τ) x := by
      change g.laplacianAt ((u τ) + fun _ : M ↦ k) x =
        g.laplacianAt (u τ) x
      rw [g.laplacianAt_add' (f := u τ) (h := fun _ : M ↦ k) (x := x) hf hk]
      rw [g.laplacianAt_const k x]
      ring
    have hgrad :
        g.gradientAt (fun y : M ↦ u τ y + k) x =
          g.gradientAt (u τ) x := by
      change g.gradientAt ((u τ) + fun _ : M ↦ k) x =
        g.gradientAt (u τ) x
      rw [g.gradientAt_add
        ((hf x).mdifferentiableAt two_ne_zero) mdifferentiableAt_const]
      rw [g.gradientAt_const k x]
      simp
    change
      g.laplacianAt (fun y : M ↦ u τ y + k) x +
          ((2 - δ) / g.scalarAt x) *
            g.inner x
              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
              (g.gradientAt (fun y : M ↦ u τ y + k) x) =
        g.laplacianAt (u τ) x +
          ((2 - δ) / g.scalarAt x) *
            g.inner x
              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
              (g.gradientAt (u τ) x)
    rw [hlap, hgrad]
  have hsuper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      L τ (u τ) x ≤ u' τ x := by
    intro τ hτ x
    let g := gt (t₀ + τ)
    have hfQ : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (Q τ) y := by
      intro y
      simpa [Q, g] using hQ₂ τ hτ y
    have hτpair : 0 ≤ τ ∧ τ ≤ T := ⟨hτ.1, hτ.2⟩
    have hspec := Classical.choose_spec (hEvol τ hτpair x).2.2.2
    have hRpos : 0 < g.scalarAt x := by
      simpa [g] using (hEvol τ hτ x).2.2.1
    have hQineq :
        Q' τ x ≤
          g.laplacianAt (Q τ) x
            + g.tracelessPinchingGradientDrift3At x δ
            + g.tracelessPinchingReactionTermAt x δ
              (g.pinchingTracelessRicciReactionTrace3At x
                (g.pinchingRicciNormReactionMotionTraceCubicAt x)) := by
      simpa [Q', Q, g, hτpair] using hspec.2
    have hreact :
        g.tracelessPinchingReactionTermAt x δ
            (g.pinchingTracelessRicciReactionTrace3At x
              (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ≤ 0 := by
      exact g.tracelessPinchingReactionTermAt_nonpos_of_eigenvalue_pinched
        hn hεpos hεle hδnonneg hδadm hRpos (hPin τ hτ x)
    have hQineq' :
        Q' τ x ≤ g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ := by
      linarith
    have hUfun :
        u τ = (fun _ : M ↦ C) + (-1 : ℝ) • (Q τ) := by
      funext y
      simp [u, Q, sub_eq_add_neg]
    have hlapU :
        g.laplacianAt (u τ) x = -g.laplacianAt (Q τ) x := by
      rw [hUfun]
      rw [g.laplacianAt_add' (f := fun _ : M ↦ C)
        (h := (-1 : ℝ) • (Q τ)) (x := x)
        (fun _ ↦ contMDiffAt_const)
        (fun y ↦ contMDiffAt_const.smul (hfQ y))]
      rw [g.laplacianAt_const C x]
      rw [g.laplacianAt_const_smul' (c := -1) (f := Q τ) (x := x) hfQ]
      ring
    have hgradU :
        g.gradientAt (u τ) x = -g.gradientAt (Q τ) x := by
      rw [hUfun]
      rw [g.gradientAt_add
        (f := fun _ : M ↦ C) (h := (-1 : ℝ) • (Q τ)) (x := x)
        mdifferentiableAt_const
        ((contMDiffAt_const.smul (hfQ x)).mdifferentiableAt two_ne_zero)]
      rw [g.gradientAt_const C x]
      rw [g.gradientAt_const_smul (c := -1) (f := Q τ) (x := x)
        ((hfQ x).mdifferentiableAt two_ne_zero)]
      simp
    have hdriftU :
        ((2 - δ) / g.scalarAt x) *
            g.inner x
              (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
              (g.gradientAt (u τ) x) =
          -g.tracelessPinchingGradientDrift3At x δ := by
      have hQfun : Q τ = fun y : M ↦ g.tracelessPinchingAt y δ := by
        funext y
        simp [Q, g]
      unfold ClosedSmoothRiemannianMetric.tracelessPinchingGradientDrift3At
      rw [hgradU, hQfun]
      simp
    have hL :
        L τ (u τ) x =
          -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ) := by
      change
        g.laplacianAt (u τ) x +
            ((2 - δ) / g.scalarAt x) *
              g.inner x
                (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
                (g.gradientAt (u τ) x) =
          -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ)
      rw [hlapU, hdriftU]
      ring
    rw [hL]
    simpa [u'] using neg_le_neg hQineq'
  have hmin_lap : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u τ) Set.univ x → 0 ≤ L τ (u τ) x := by
    intro τ hτ x hmin
    let g := gt (t₀ + τ)
    have hfU : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (u τ) y :=
      hQtoU₂ τ hτ
    have hlocalMin : IsLocalMin (u τ) x :=
      hmin.isLocalMin Filter.univ_mem
    have hlap :
        0 ≤ g.laplacianAt (u τ) x :=
      laplacianAt_nonneg_of_isLocalMin
        (g := g) (f := u τ) (x := x) (hfU x)
        (g.mdifferentiableAt_gradient (hfU x)) hlocalMin
    have hgrad :
        g.gradientAt (u τ) x = 0 :=
      gradientAt_eq_zero_of_isLocalMin
        (g := g) (f := u τ) (x := x) (hfU x) hlocalMin
    change
      0 ≤ g.laplacianAt (u τ) x +
        ((2 - δ) / g.scalarAt x) *
          g.inner x
            (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
            (g.gradientAt (u τ) x)
    rw [hgrad]
    simpa using hlap
  have hkey := closed_parabolic_min_principle_var_continuousOn
    (lap := L) (u := u) (u' := u') (c := fun _ _ ↦ (0 : ℝ))
    (T := T) (M₀ := 0)
    hT0
    (by intro τ hτ x; exact le_refl (0 : ℝ))
    (by
      simpa [u, Q, C, Function.uncurry] using
        (continuous_const.continuousOn.sub hQ_cont))
    hud
    hlap_add_const
    (by
      intro τ hτ x
      simpa using hsuper τ hτ x)
    hmin_lap
    h0point
  intro τ hτ
  obtain ⟨xτ, hxτmax⟩ :=
    exists_tracelessPinchingAt_isMaxOn
      (g := gt (t₀ + τ)) δ (hQ₂ τ hτ)
  have hnonneg := hkey τ hτ xτ
  have hQle : Q τ xτ ≤ C := by
    simpa [u] using hnonneg
  rw [tracelessPinchingMaximumTrack, tracelessPinchingMaximumAt_eq_of_isMaxOn
    (g := gt (t₀ + τ)) δ hxτmax]
  simpa [Q, C] using hQle


/--
Hamilton's improved compact-track traceless pinching theorem with the full
local evolution and spatial `C²` quotient theory generated from joint `C³`
metric entries.  The remaining eigenvalue floor is precisely the algebraic
sign input used by the improved reaction estimate.
-/
theorem hamilton_pinching_improvement_of_ricciFlow_joint_metric_entries_three
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ T ε δ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 ≤ T)
    (hεpos : 0 < ε) (hεle : ε ≤ 1 / 3)
    (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hδadm : δ ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 ε)
    (hFlow : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      IsClosedRicciFlowSolutionAt gt (t₀ + τ) y)
    (hJoint : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      MetricEntriesJointContDiffAt gt (t₀ + τ) y 3)
    (hRpos : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      0 < (gt (t₀ + τ)).scalarAt y)
    (hPin : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (μ : Fin 3 → ℝ),
        (∀ i : Fin 3,
          (gt (t₀ + τ)).ricciEndoAt x (b i) = μ i • b i) →
          ∀ i : Fin 3, ε * (gt (t₀ + τ)).scalarAt x ≤ μ i) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      tracelessPinchingMaximumTrack gt t₀ δ τ ≤
        tracelessPinchingMaximumTrack gt t₀ δ 0 := by
  have hQ₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).tracelessPinchingAt y δ) x := by
    intro τ hτ x
    exact contMDiffAt_two_tracelessPinchingAt_of_ricciFlow_joint_metric_entries_three
      (gt := gt) (t₀ := t₀ + τ) x δ
      (hFlow τ hτ) (hJoint τ hτ) (hRpos τ hτ)
  have hEvol : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t₀ + τ) x δ
          ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x) := by
    intro τ hτ x
    exact satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow_joint_metric_entries_three_cubic
      (gt := gt) (t₀ := t₀ + τ) (x := x) (δ := δ)
      (hFlow τ hτ) (hJoint τ hτ) hn hδpos hδle (hRpos τ hτ)
  have hQ_cont : ContinuousOn
      (↿fun τ (x : M) ↦ (gt (t₀ + τ)).tracelessPinchingAt x δ)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    continuousOn_tracelessPinchingAt_timeShift_of_metricEntriesJointContDiffAt_three
      hJoint hRpos
  exact hamilton_pinching_improvement_continuousOn
    (gt := gt) (t₀ := t₀) (T := T) (ε := ε) (δ := δ)
    hn hT0 hεpos hεle (le_of_lt hδpos) hδadm
    hQ_cont hQ₂ hEvol hPin

/--
Fully automatic ordinary pinching preservation under global joint `C³`
metric-entry regularity and global positive scalar curvature.  In particular,
the quotient-track continuity premise of the underlying maximum principle is
now a theorem rather than an independent assumption.
-/
theorem hamilton_pinching_preserved_of_ricciFlow_global_joint_metric_entries_three
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 ≤ T)
    (hFlow : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      IsClosedRicciFlowSolutionAt gt (t₀ + τ) y)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hRpos : ∀ t : ℝ, ∀ y : M, 0 < (gt t).scalarAt y) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      pinchingMaximumTrack gt t₀ τ ≤ pinchingMaximumTrack gt t₀ 0 := by
  exact hamilton_pinching_preserved_of_ricciFlow_joint_metric_entries_three
    (gt := gt) (t₀ := t₀) (T := T)
    hn hT0 hFlow
    (fun τ _ y ↦ hJoint (t₀ + τ) y)
    (fun τ _ y ↦ hRpos (t₀ + τ) y)

/--
Fully automatic improved traceless pinching on a compact track under global
joint `C³` metric entries and positive scalar curvature.  The sole remaining
non-flow input is the algebraic eigenvalue floor used to sign the cubic
reaction.
-/
theorem hamilton_pinching_improvement_of_ricciFlow_global_joint_metric_entries_three
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ T ε δ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : n = 3) (hT0 : 0 ≤ T)
    (hεpos : 0 < ε) (hεle : ε ≤ 1 / 3)
    (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hδadm : δ ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 ε)
    (hFlow : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : M,
      IsClosedRicciFlowSolutionAt gt (t₀ + τ) y)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hRpos : ∀ t : ℝ, ∀ y : M, 0 < (gt t).scalarAt y)
    (hPin : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (μ : Fin 3 → ℝ),
        (∀ i : Fin 3,
          (gt (t₀ + τ)).ricciEndoAt x (b i) = μ i • b i) →
          ∀ i : Fin 3, ε * (gt (t₀ + τ)).scalarAt x ≤ μ i) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      tracelessPinchingMaximumTrack gt t₀ δ τ ≤
        tracelessPinchingMaximumTrack gt t₀ δ 0 := by
  exact hamilton_pinching_improvement_of_ricciFlow_joint_metric_entries_three
    (gt := gt) (t₀ := t₀) (T := T) (ε := ε) (δ := δ)
    hn hT0 hεpos hεle hδpos hδle hδadm hFlow
    (fun τ _ y ↦ hJoint (t₀ + τ) y)
    (fun τ _ y ↦ hRpos (t₀ + τ) y)
    hPin

end Poincare
