import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
import Poincare.Global.DeTurckPrincipalIdentity

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.IntrinsicLaplacianCoordinateForm

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The intrinsic Hessian trace contracts with the inverse Gram matrix in any basis. -/
theorem laplacianAt_eq_inverseGram_hessian
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ (TM x)) :
    g.laplacianAt f x = ∑ i, ∑ j,
      (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [Poincare.laplacianAt_eq_sum_hessianAt_basis g f x b]
  apply Finset.sum_congr rfl
  intro i _
  rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
  change g.hessianDualAt f x (b i) (∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j • b j) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- In the inverse-chart frame the Laplacian uses the genuine inverse Gram field. -/
theorem laplacianAt_eq_chart_hessian
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (p : M)
    (z : (extChartAt I p).target) :
    g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
      ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
        g.hessianAt f ((extChartAt I p).symm z)
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
            (EuclideanSpace.basisFun (Fin n) ℝ i))
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
            (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p z.2
  have hG : g.metricMatrixInBasisAt ((extChartAt I p).symm z) b =
      inverseChartPullbackGramMatrixField g p z := by
    ext i j
    simp only [ClosedSmoothRiemannianMetric.metricMatrixInBasisAt_apply,
      ClosedSmoothRiemannianMetric.metricBilinAt_apply, b,
      ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
    rfl
  change g.laplacianAt f ((extChartAt I p).symm z) = _
  rw [laplacianAt_eq_inverseGram_hessian g f _ b, hG]
  simp only [b, ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]

/-- Pairing the transported intrinsic gradient with the chart metric gives the
ordinary differential of the coordinate scalar. -/
theorem chartMetric_transported_gradient
    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
    {z : E} (hz : z ∈ (extChartAt I p).target)
    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) (w : E) :
    CovariantDerivative.chartMetric g.inner p z
      (CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z) w =
      fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z w := by
  let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
  have hD : D.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm hz
  have heq : ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f =ᶠ[𝓝 z]
      f ∘ (extChartAt I p).symm := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
    exact indicator_of_mem hy _
  rw [heq.fderiv_eq, CovariantDerivative.chartMetric_apply,
    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
  change g.inner ((extChartAt I p).symm z)
    (D (D.inverse (g.gradient f ((extChartAt I p).symm z)))) (D w) = _
  rw [hD.self_apply_inverse]
  change g.inner ((extChartAt I p).symm z)
    (g.gradientAt f ((extChartAt I p).symm z)) (D w) = _
  rw [g.inner_gradientAt, extDerivFun_apply_fixed_chart ((extChartAt I p).map_target hz) hf,
    (extChartAt I p).right_inv hz]
  have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz
  have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hc
  change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z) (D w) = w at hw
  exact congrArg (fderiv ℝ (f ∘ (extChartAt I p).symm) z) hw

/-- The inverse-chart pullback of the intrinsic gradient is the coordinate gradient. -/
theorem transported_gradient_eq_coordGradient
    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
    {z : E} (hz : z ∈ (extChartAt I p).target)
    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) :
    CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z =
      RicciFlow.RicciFlow.coordGradient (CovariantDerivative.chartMetric g.inner p)
        (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z := by
  let G := CovariantDerivative.chartMetric g.inner p
  have hpos (v : E) (hv : v ≠ 0) : 0 < G z v v :=
    CovariantDerivative.chartMetric_posDef g.inner
      (fun y u hu ↦ g.inner_pos y hu) p
      (isInvertible_mfderivWithin_extChartAt_symm hz) hv
  have hnondeg : (RicciFlow.RicciFlow.metricBilin (G z)).Nondegenerate := by
    constructor
    · intro v hv
      by_contra h
      exact (ne_of_gt (hpos v h)) (hv v)
    · intro v hv
      by_contra h
      exact (ne_of_gt (hpos v h)) (hv v)
  have hinv : (G z).IsInvertible :=
    CovariantDerivative.metric_isInvertible G
      (RicciFlow.RicciFlow.metricBilin (G z)) hnondeg (fun _ _ ↦ rfl)
  symm
  apply hinv.inverse_apply_eq.mpr
  ext w
  exact (chartMetric_transported_gradient g p f hz hf w).symm

/-- A smooth local metric extension transports the intrinsic Hessian to the
ordinary second derivative with its Christoffel correction. -/
theorem hessianAt_eq_blended_chart_hessian
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (p : M)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : tsupport χ ⊆ (extChartAt I p).target)
    (hχ0 : ∀ q, 0 ≤ χ q) (hχ1 : ∀ q, χ q ≤ 1)
    {z : E} (hz : z ∈ (extChartAt I p).target)
    (hone : ∀ᶠ q in 𝓝 z, χ q = 1)
    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (v w : E) :
    let H := CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p
    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
      fderiv ℝ (fderiv ℝ u) z v w -
        fderiv ℝ u z (RicciFlow.RicciFlow.christoffelClosedOp H z v w) := by
  intro H u D
  have hpos (q : E) (hq : q ≠ 0) : 0 < innerSL ℝ q q := by
    simpa only [innerSL_apply_apply] using (real_inner_self_pos.mpr hq)
  have hsupp : ∀ q, χ q ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) q).IsInvertible := by
    intro q hq
    exact isInvertible_mfderivWithin_extChartAt_symm
      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hq)))
  have hH : ContDiff ℝ 1 H :=
    CovariantDerivative.contDiff_blendedChartMetric χ (innerSL ℝ) g.inner p
      (m := 1) (by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top) hχ hχsupp (g.contMDiff_inner.of_le (by norm_num))
  have hinv (q : E) : (H q).IsInvertible :=
    CovariantDerivative.metric_isInvertible H
      (CovariantDerivative.chartBilin χ (innerSL ℝ) g.inner p q)
      (CovariantDerivative.chartBilin_nondegenerate χ (innerSL ℝ) hpos g.inner
        (fun y v hv ↦ g.inner_pos y hv) p hχ0 hχ1 hsupp q) (fun _ _ ↦ rfl)
  have hsym (q a b : E) : H q a b = H q b a :=
    CovariantDerivative.blendedChartMetric_symm χ (innerSL ℝ)
      (fun a b : E ↦ real_inner_comm b a)
      g.inner (fun y a b ↦ g.inner_symm y a b) p q a b
  have hu : ContDiff ℝ 2 u :=
    ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
  let S := CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f)
  have heq : S =ᶠ[𝓝 z] RicciFlow.RicciFlow.coordGradient H u := by
    filter_upwards [hone, (isOpen_extChartAt_target p).mem_nhds hz] with q hq hqt
    have hg := transported_gradient_eq_coordGradient g p f hqt
      (hf.contMDiffAt.mdifferentiableAt two_ne_zero)
    have hHq : H q = CovariantDerivative.chartMetric g.inner p q :=
      CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
        χ (innerSL ℝ) g.inner p hq
    simpa only [RicciFlow.RicciFlow.coordGradient, hHq, S, u] using hg
  have hbridge :=
    LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
      g χ (innerSL ℝ) hpos p hχ0 hχ1 hsupp (hH.differentiable one_ne_zero)
      (fun a b : E ↦ real_inner_comm b a)
      ((extChartAt I p).map_target hz)
      (by simpa only [(extChartAt I p).right_inv hz] using hone)
      (show MDiffAtTangentField (g.gradient f) ((extChartAt I p).symm z) from
        g.mdifferentiableAt_gradient hf.contMDiffAt) (D v)
  dsimp only [CovariantDerivative.chartTransportedLeviCivitaValueAt,
    CovariantDerivative.chartTransportedLeviCivitaModelValue] at hbridge
  rw [(extChartAt I p).right_inv hz] at hbridge
  have hCD := congrArg (fun L : E →L[ℝ] E ↦ L v)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz)
  change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z)) (D v) = v at hCD
  have hbridge' : D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) =
      (LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
        ((extChartAt I p).symm z) (D v) :=
    (congrArg (fun a ↦ D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos
      g.inner (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) a)) hCD).symm.trans hbridge
  have hmodel :
      (CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
        (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v =
      fderiv ℝ (RicciFlow.RicciFlow.coordGradient H u) z v +
        RicciFlow.RicciFlow.christoffelClosedOp H z v
          (RicciFlow.RicciFlow.coordGradient H u z) := by
    rw [CovariantDerivative.chartLeviCivita, CovariantDerivative.modelLeviCivita_apply,
      ← RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt H _ _ (fun _ _ ↦ rfl)]
    rw [heq.fderiv_eq, heq.self_of_nhds]
  have hresult := RicciFlow.RicciFlow.g_covariantDeriv_coordGradient_eq_covariantHessian'
    H (hH.differentiable one_ne_zero z) hsym hinv hu v w
  rw [← RicciFlow.RicciFlow.covariantHessianForm_eq_covariantHessian H hsym hinv u z v w,
    RicciFlow.RicciFlow.covariantHessianForm_apply] at hresult
  rw [ClosedSmoothRiemannianMetric.hessianAt]
  change g.inner ((extChartAt I p).symm z)
    ((LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
      ((extChartAt I p).symm z) (D v)) (D w) = _
  rw [← hbridge']
  change CovariantDerivative.chartMetric g.inner p z
    ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) w = _
  rw [hmodel, ← CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    χ (innerSL ℝ) g.inner p hone.self_of_nhds]
  exact hresult

/-- The intrinsic Hessian in a genuine chart has the ordinary second derivative
and the connection of the genuine chart metric. -/
theorem hessianAt_eq_chart_derivatives
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (p : M)
    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {z : E} (hz : z ∈ (extChartAt I p).target) (v w : E) :
    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
      fderiv ℝ (fderiv ℝ u) z v w - fderiv ℝ u z
        (RicciFlow.RicciFlow.christoffelClosedOp
          (CovariantDerivative.chartMetric g.inner p) z v w) := by
  obtain ⟨χ, hχ, hχsupp, hone, hbounds⟩ :=
    ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
      (isCompact_singleton (x := z)) (isOpen_extChartAt_target p)
      (singleton_subset_iff.mpr hz)
  have heq : CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p =ᶠ[𝓝 z]
      CovariantDerivative.chartMetric g.inner p := by
    filter_upwards [hone z (mem_singleton z)] with q hq
    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      χ (innerSL ℝ) g.inner p hq
  have h := hessianAt_eq_blended_chart_hessian g p χ hχ hχsupp
    (fun q ↦ (hbounds q).1) (fun q ↦ (hbounds q).2) hz
    (hone z (mem_singleton z)) f hs hf v w
  dsimp only at h ⊢
  simpa only [RicciFlow.RicciFlow.christoffelClosedOp_apply,
    CovariantDerivative.christoffelFunctional, heq.self_of_nhds, heq.fderiv_eq] using h

/-- Coordinates of a raised covector are its inverse-matrix contraction. -/
theorem inverse_apply_coord
    (G : ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
    (hG : G.IsInvertible) (hs : ∀ v w, G v w = G w v)
    (q : ClosedSmoothModel 3 →L[ℝ] ℝ) (k : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord k (G.inverse q) =
      ∑ m, DeTurckPrincipalSecondJet.inverseEntries G k m *
        q (EuclideanSpace.basisFun (Fin 3) ℝ m) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let r := G.inverse (LinearMap.toContinuousLinearMap (b.coord k))
  have hp := DeTurckPrincipalIdentity.inverse_pairing_symm G hG hs
    (LinearMap.toContinuousLinearMap (b.coord k)) q
  change b.coord k (G.inverse q) = q r at hp
  rw [hp]
  have hr := congrArg q (b.sum_repr r)
  calc
    q r = ∑ m, b.repr r m * q (b m) := by
      simpa only [map_sum, map_smul, smul_eq_mul] using hr.symm
    _ = _ := by
      rw [DeTurckPrincipalIdentity.inverseEntries_eq_coordinates G hG]
      rfl

/-- The closed Christoffel operator has the standard inverse-Gram coordinates. -/
theorem christoffelClosedOp_coord
    (G : ClosedSmoothModel 3 → ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
    (z : ClosedSmoothModel 3) (hG : (G z).IsInvertible)
    (hs : ∀ v w, G z v w = G z w v) (hd : DifferentiableAt ℝ G z)
    (k i j : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord k
      (RicciFlow.RicciFlow.christoffelClosedOp G z
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      (1 / 2 : ℝ) * ∑ m, DeTurckPrincipalSecondJet.inverseEntries (G z) k m *
        (coordinateDirectionalDerivative (fun q ↦ G q
            (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ m)) i z +
         coordinateDirectionalDerivative (fun q ↦ G q
            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ m)) j z -
         coordinateDirectionalDerivative (fun q ↦ G q
            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) m z) := by
  have hderiv (a b v : ClosedSmoothModel 3) :
      fderiv ℝ (fun q ↦ G q a b) z v = fderiv ℝ G z v a b := by
    have h := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const a z)).clm_apply
      (hasFDerivAt_const b z)
    simpa using congrArg (fun L : ClosedSmoothModel 3 →L[ℝ] ℝ ↦ L v) h.fderiv
  rw [RicciFlow.RicciFlow.christoffelClosedOp_apply, inverse_apply_coord (G z) hG hs]
  simp only [LinearMap.coe_toContinuousLinearMap', CovariantDerivative.christoffelFunctional,
    coordinateDirectionalDerivative, ← EuclideanSpace.basisFun_apply, hderiv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  dsimp
  ring

section Three
variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
  [ChartedSpace (ClosedSmoothModel 3) M₃]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
local notation "I₃" => closedSmoothModelWithCorners 3
local notation "E₃" => ClosedSmoothModel 3

/-- The intrinsic Hessian entries in the inverse-chart frame have the standard
coordinate second-derivative and Christoffel formula. -/
theorem hessianAt_eq_coordinate_hessian
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (f : M₃ → ℝ) (hs : tsupport f ⊆ (extChartAt I₃ p).source)
    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f)
    {z : E₃} (hz : z ∈ (extChartAt I₃ p).target) (i j : Fin 3) :
    let G := inverseChartPullbackGramMatrixField g p
    let a : E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
    let Γ := fun y k i j ↦ (1 / 2 : ℝ) * ∑ m, a y k m *
      (coordinateDirectionalDerivative (fun q ↦ G q j m) i y +
       coordinateDirectionalDerivative (fun q ↦ G q i m) j y -
       coordinateDirectionalDerivative (fun q ↦ G q i j) m y)
    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p f
    let D := mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ p).symm (range I₃) z
    g.hessianAt f ((extChartAt I₃ p).symm z)
      (D (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (D (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      coordinateSecondDerivative u i j z - ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z := by
  intro G a Γ u D
  let H := CovariantDerivative.chartMetric g.inner p
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hd : DifferentiableAt ℝ H z :=
    (deTurckChartMetric_contDiffAt_two_of_mem_target g p hz).differentiableAt two_ne_zero
  have hpos (v : E₃) (hv : v ≠ 0) : 0 < H z v v :=
    CovariantDerivative.chartMetric_posDef g.inner (fun y v hv ↦ g.inner_pos y hv) p
      (isInvertible_mfderivWithin_extChartAt_symm hz) hv
  have hnondeg : (RicciFlow.RicciFlow.metricBilin (H z)).Nondegenerate := by
    constructor
    · intro v hv
      by_contra h
      exact (ne_of_gt (hpos v h)) (hv v)
    · intro v hv
      by_contra h
      exact (ne_of_gt (hpos v h)) (hv v)
  have hinv : (H z).IsInvertible := CovariantDerivative.metric_isInvertible H
    (RicciFlow.RicciFlow.metricBilin (H z)) hnondeg (fun _ _ ↦ rfl)
  have hcoord (k : Fin 3) : b.coord k
      (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = Γ z k i j :=
    christoffelClosedOp_coord H z hinv
      (CovariantDerivative.chartMetric_symm g.inner (fun y v w ↦ g.inner_symm y v w) p z) hd k i j
  have hu : ContDiff ℝ 2 u := ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
  have hsecond : coordinateSecondDerivative u i j z = fderiv ℝ (fderiv ℝ u) z (b i) (b j) := by
    have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z
    have h := hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (b j) z)
    have hh := congrArg (fun L : E₃ →L[ℝ] ℝ ↦ L (b i)) h.fderiv
    simpa [coordinateSecondDerivative, coordinateDirectionalDerivative, b,
      EuclideanSpace.basisFun_apply] using hh
  have hcorrect : fderiv ℝ u z
      (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) =
      ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z := by
    have h := congrArg (fderiv ℝ u z)
      (b.sum_repr (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)))
    have hexp : fderiv ℝ u z (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) =
        ∑ k, b.coord k (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) *
          fderiv ℝ u z (b k) := by
      simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply] using h.symm
    simp_rw [hcoord] at hexp
    simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      coordinateDirectionalDerivative] using hexp
  rw [hessianAt_eq_chart_derivatives g p f hs hf hz]
  change fderiv ℝ (fderiv ℝ u) z (b i) (b j) - fderiv ℝ u z
    (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = _
  rw [← hsecond, hcorrect]

/-- The intrinsic scalar Laplacian equals the standard Christoffel-coordinate
formula on each shrunk chart region. -/
theorem laplacianAt_eq_christoffelCoordinateLaplacian
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (V : Set M₃) (hV : closure V ⊆ (extChartAt I₃ p).source)
    (φ : M₃ → ℝ) (hφ : tsupport φ ⊆ V)
    (hf : ContMDiff I₃ 𝓘(ℝ) 2 φ)
    (z : (extChartAt I₃ p).target) (hz : (z : E₃) ∈ (extChartAt I₃ p) '' V) :
    let G := inverseChartPullbackGramMatrixField g p
    let a : E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
    let Γ := fun y j k l ↦ (1 / 2 : ℝ) * ∑ m, a y j m *
      (coordinateDirectionalDerivative (fun q ↦ G q l m) k y +
       coordinateDirectionalDerivative (fun q ↦ G q k m) l y -
       coordinateDirectionalDerivative (fun q ↦ G q k l) m y)
    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
      christoffelCoordinateLaplacian a Γ
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z := by
  intro G a Γ
  have hs : tsupport φ ⊆ (extChartAt I₃ p).source :=
    hφ.trans (subset_closure.trans hV)
  have hzt : (z : E₃) ∈ (extChartAt I₃ p).target := by
    obtain ⟨x, hx, hzx⟩ := hz
    rw [← hzx]
    exact (extChartAt I₃ p).map_source (hV (subset_closure hx))
  rw [laplacianAt_eq_chart_hessian g φ p z]
  unfold christoffelCoordinateLaplacian
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun t : ℝ ↦ a z i j * t)
    (hessianAt_eq_coordinate_hessian g p φ hs hf hzt i j)

end Three

/-- Restricting the genuine chart domain restricts the Riemannian chart measure. -/
theorem restrictedChart_measure
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {U : Set E}
    (hU : MeasurableSet U) (hsub : U ⊆ (extChartAt I p).target) :
    HausdorffChartDensityEquality g U
      (fun z ↦ inverseExtendedChartParametrization (n := n) p (Set.inclusion hsub z))
      ((extChartAt I p).symm '' U)
      (fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z)) := by
  let ψ := inverseExtendedChartParametrization (n := n) p
  let ι := Set.inclusion hsub
  let μ := rawHausdorffCoordinateDensityMeasure (extChartAt I p).target
    (inverseChartPullbackVolumeDensity g p)
  have hψ : MeasurableEmbedding ψ :=
    (inverseExtendedChartParametrization_isEmbedding (n := n) p).measurableEmbedding
      (by rw [range_inverseExtendedChartParametrization]; exact (isOpen_extChartAt_source p).measurableSet)
  have hmap := map_rawHausdorffCoordinateDensityMeasure_inclusion
    (isOpen_extChartAt_target p).measurableSet hU hsub (inverseChartPullbackVolumeDensity g p)
  have hres := hψ.restrict_map μ (ψ '' range ι)
  rw [preimage_image_eq _ hψ.injective] at hres
  have himage : ψ '' range ι = (extChartAt I p).symm '' U := by
    ext x
    constructor
    · rintro ⟨q, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨ι ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  have hsource : ψ '' range ι ⊆ (extChartAt I p).source := by
    rintro x ⟨z, _, rfl⟩
    exact (extChartAt I p).map_target z.2
  change Measure.map (ψ ∘ ι) _ = _
  rw [← Measure.map_map hψ.measurable (measurable_inclusion hsub), hmap, ← hres]
  have hfull : Measure.map ψ μ = (volumeMeasure g).restrict (extChartAt I p).source :=
    ClosedLaplacianStokesProducer.openChart_measure g p
  rw [hfull, Measure.restrict_restrict_of_subset hsource, himage]

/-- The genuine density remains integrable on a measurable subdomain of a chart. -/
theorem restrictedChart_density_integrable
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {U : Set E}
    (hU : MeasurableSet U) (hsub : U ⊆ (extChartAt I p).target) :
    Integrable (fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z))
      (coordinateLebesgueMeasure U) := by
  let δ := fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z)
  have hcont : Continuous δ := (continuous_inverseChartPullbackVolumeDensity g p).comp
    (continuous_inclusion hsub)
  have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
  have hmeas : Measurable (fun z : U ↦ inverseExtendedChartParametrization (n := n) p
      (Set.inclusion hsub z)) :=
    (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable.comp
    (measurable_inclusion hsub)
  have hmass := congrArg (fun μ : Measure M ↦ μ univ) (restrictedChart_measure g p hU hsub)
  dsimp only at hmass
  rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hmass
  have hfinite : ∫⁻ z, ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) * δ z)
      ∂(coordinateLebesgueMeasure U) ≠ (⊤ : ℝ≥0∞) := by
    rw [rawHausdorffCoordinateDensityMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hmass
    rw [hmass]
    letI := volumeMeasure_isFiniteMeasure g
    exact measure_ne_top (volumeMeasure g) _
  have hint := (lintegral_ofReal_ne_top_iff_integrable
    (hcont.const_mul (rawHausdorffLebesgueScale n : ℝ)).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ mul_nonneg hscale.le
      (inverseChartPullbackVolumeDensity_pos g p (Set.inclusion hsub z)).le)).mp hfinite
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint

/-- Zero extension does not enlarge the coordinate support beyond the image
of the manifold support. -/
theorem coordinateScalar_tsupport_subset_image [CompactSpace M]
    (p : M) (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source) :
    tsupport (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) ⊆
      (extChartAt I p) '' tsupport f := by
  have hcompact : IsCompact ((extChartAt I p) '' tsupport f) :=
    (isClosed_tsupport f).isCompact.image_of_continuousOn ((continuousOn_extChartAt p).mono hs)
  apply closure_minimal _ hcompact.isClosed
  intro z hz
  by_cases hzt : z ∈ (extChartAt I p).target
  · refine ⟨(extChartAt I p).symm z, ?_, (extChartAt I p).right_inv hzt⟩
    apply subset_tsupport
    simpa only [Function.mem_support, ClosedLaplacianStokesProducer.coordinateScalar,
      indicator_of_mem hzt] using hz
  · exact False.elim (hz (indicator_of_notMem hzt _))

/-- A continuous coordinate divergence on a smaller open region suffices
for continuity of the localized intrinsic Laplacian. -/
theorem laplacian_continuous_of_restricted_coordinate_divergence
    (g : ClosedSmoothRiemannianMetric n M) (p : M) (V : Set M)
    (hV : IsOpen V) (hVs : V ⊆ (extChartAt I p).source)
    (f : M → ℝ) (hs : tsupport f ⊆ V) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (w D : E → ℝ) (hw : Continuous w) (hD : Continuous D)
    (hpos : ∀ z ∈ (extChartAt I p) '' V, 0 < w z)
    (hcoord : ∀ z : (extChartAt I p).target, (z : E) ∈ (extChartAt I p) '' V →
      w z * g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) = D z) :
    Continuous (fun x ↦ g.laplacianAt f x) := by
  have hformula (x : M) (hx : x ∈ V) :
      g.laplacianAt f x = D (extChartAt I p x) / w (extChartAt I p x) := by
    let z : (extChartAt I p).target := ⟨extChartAt I p x, (extChartAt I p).map_source (hVs hx)⟩
    have hinv : inverseExtendedChartParametrization (n := n) p z = x :=
      (extChartAt I p).left_inv (hVs hx)
    have hz : (z : E) ∈ (extChartAt I p) '' V := ⟨x, hx, rfl⟩
    apply (eq_div_iff (hpos z hz).ne').mpr
    simpa only [hinv, mul_comm] using hcoord z hz
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ V
  · have hc := (continuousOn_extChartAt p x (hVs hx)).continuousAt
      ((isOpen_extChartAt_source p).mem_nhds (hVs hx))
    have hquot := (hD.continuousAt.div hw.continuousAt
      (hpos _ ⟨x, hx, rfl⟩).ne').comp hc
    apply hquot.congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hformula y hy
  · have hxt : x ∉ tsupport f := fun h ↦ hx (hs h)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
    calc
      g.laplacianAt f y = g.laplacianAt (fun _ : M ↦ (0 : ℝ)) y :=
        g.laplacianAt_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
          (g.mdifferentiableAt_gradient hf.contMDiffAt)
          (g.mdifferentiableAt_gradient contMDiffAt_const)
      _ = 0 := g.laplacianAt_const 0 y

/-- The Stokes geometry can use the coordinate images of a shrunk open cover. -/
def geometry_of_shrunk_coordinate_coefficients
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (V : Fin C.chartCount → Set M) (hV : ∀ i, IsOpen (V i))
    (hVs : ∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source)
    (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ) (hρ : ρ.IsSubordinate V)
    (w : Fin C.chartCount → E → ℝ)
    (a : Fin C.chartCount → E → Fin n → Fin n → ℝ)
    (Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ)
    (hw : ∀ i, ContDiff ℝ 1 (w i))
    (ha : ∀ i j k, ContDiff ℝ 1 (fun z ↦ a i z j k))
    (hweight : ∀ i (z : (extChartAt I (C.anchor i)).target),
      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i →
      w i z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g (C.anchor i) z)
    (hcompat : ∀ i (z : (extChartAt I (C.anchor i)).target),
      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i → ∀ j,
      (∑ k, fderiv ℝ (fun y ↦ w i y * a i y k j) z (EuclideanSpace.single k (1 : ℝ))) =
        w i z * (-(∑ k, ∑ l, a i z k l * Γ i z j k l)))
    (hcoord : ∀ i (z : (extChartAt I (C.anchor i)).target),
      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i →
      g.laplacianAt (fun x ↦ ρ i x * f x)
        (inverseExtendedChartParametrization (n := n) (C.anchor i) z) =
      christoffelCoordinateLaplacian (a i) (Γ i)
        (ClosedLaplacianStokesProducer.coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)) z) :
    FiniteSubordinateHausdorffLaplacianGeometry g f := by
  let U := fun i ↦ (extChartAt I (C.anchor i)) '' V i
  have hVs' (i) : V i ⊆ (extChartAt I (C.anchor i)).source := subset_closure.trans (hVs i)
  have hsub (i) : U i ⊆ (extChartAt I (C.anchor i)).target :=
    image_subset_iff.mpr fun _ hx ↦ (extChartAt I (C.anchor i)).map_source (hVs' i hx)
  have hU (i) : MeasurableSet (U i) := by
    have heq : U i = Subtype.val ''
        (inverseExtendedChartParametrization (n := n) (C.anchor i) ⁻¹' V i) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨extChartAt I (C.anchor i) x, (extChartAt I (C.anchor i)).map_source (hVs' i hx)⟩, ?_, rfl⟩
        change (extChartAt I (C.anchor i)).symm (extChartAt I (C.anchor i) x) ∈ V i
        rwa [(extChartAt I (C.anchor i)).left_inv (hVs' i hx)]
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(extChartAt I (C.anchor i)).symm z, hz, (extChartAt I (C.anchor i)).right_inv z.2⟩
    rw [heq]
    exact (MeasurableEmbedding.subtype_coe (isOpen_extChartAt_target (C.anchor i)).measurableSet).measurableSet_image.mpr
      ((inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable
        (hV i).measurableSet)
  have himage (i) : (extChartAt I (C.anchor i)).symm '' U i = V i := by
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      rwa [(extChartAt I (C.anchor i)).left_inv (hVs' i hy)]
    · intro hx
      exact ⟨extChartAt I (C.anchor i) x, ⟨x, hx, rfl⟩,
        (extChartAt I (C.anchor i)).left_inv (hVs' i hx)⟩
  have hsV (i) : tsupport (fun x ↦ ρ i x * f x) ⊆ V i := tsupport_mul_subset_left.trans (hρ i)
  have hs (i) : tsupport (fun x ↦ ρ i x * f x) ⊆ (extChartAt I (C.anchor i)).source :=
    (hsV i).trans (hVs' i)
  have htwo : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hlocal (i) : ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
    ((ρ i).contMDiff.of_le htwo).mul hf
  let u := fun i ↦ ClosedLaplacianStokesProducer.coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)
  have hu (i) : ContDiff ℝ 2 (u i) :=
    ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two (C.anchor i) _ (hs i) (hlocal i)
  have hcontinuous (i) : Continuous (fun x ↦ g.laplacianAt (fun y ↦ ρ i y * f y) x) := by
    let F := coordinateMetricFluxComponent (w i) (a i) (u i)
    have hF (k) : ContDiff ℝ 1 (F k) := coordinateMetricFluxComponent_contDiff_one (hw i) (ha i) (hu i) k
    apply laplacian_continuous_of_restricted_coordinate_divergence g (C.anchor i) (V i)
      (hV i) (hVs' i) _ (hsV i) (hlocal i) (w i) (euclideanCoordinateDivergence F) (hw i).continuous
    · exact continuous_finsetSum _ fun k _ ↦ ((hF k).continuous_fderiv one_ne_zero).clm_apply continuous_const
    · intro z hz
      rw [hweight i ⟨z, hsub i hz⟩ hz]
      have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
        exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
          (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
      exact mul_pos hscale (inverseChartPullbackVolumeDensity_pos g (C.anchor i) ⟨z, hsub i hz⟩)
    · intro z hz
      have hdiv := euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
        (contractedChristoffel := fun y j ↦ -(∑ k, ∑ l, a i y k l * Γ i y j k l))
        ((hw i).differentiable one_ne_zero z)
        (fun j k ↦ (ha i j k).differentiable one_ne_zero z)
        (fun j ↦ (coordinateDirectionalDerivative_contDiff_one (hu i) j).differentiable one_ne_zero z)
        (hcompat i z hz)
      rw [contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
        (a i) (Γ i) (fun y j ↦ -(∑ k, ∑ l, a i y k l * Γ i y j k l)) (u i) z (fun _ ↦ rfl)] at hdiv
      rw [hcoord i z hz]
      exact hdiv.symm
  exact {
    chartCount := C.chartCount
    coordinateDomain := U
    coordinateDomain_measurable := hU
    inverseChart := fun i z ↦ inverseExtendedChartParametrization (n := n) (C.anchor i) (Set.inclusion (hsub i) z)
    inverseChart_measurable := fun i ↦
      (inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable.comp (measurable_inclusion (hsub i))
    chartRegion := V
    chartRegion_isOpen := hV
    density := fun i z ↦ inverseChartPullbackVolumeDensity g (C.anchor i) (Set.inclusion (hsub i) z)
    density_nonneg := fun i ↦ Eventually.of_forall fun z ↦ (inverseChartPullbackVolumeDensity_pos g (C.anchor i) (Set.inclusion (hsub i) z)).le
    density_integrable := fun i ↦ restrictedChart_density_integrable g (C.anchor i) (hU i) (hsub i)
    chartMeasure := fun i ↦ by
      have h := restrictedChart_measure g (C.anchor i) (hU i) (hsub i)
      rwa [himage i] at h
    partition := ρ
    partition_subordinate := hρ
    f_contMDiff_two := hf
    coordinateRepresentative := u
    coordinateRepresentative_eq := fun i z ↦ indicator_of_mem (hsub i z.2) _
    coordinateRepresentative_contDiff_two := hu
    coordinateRepresentative_hasCompactSupport := fun i ↦
      (ClosedLaplacianStokesProducer.coordinateScalar_support (C.anchor i) _ (hs i)).1
    coordinateRepresentative_tsupport_subset_coordinateDomain := fun i ↦
      (coordinateScalar_tsupport_subset_image (C.anchor i) _ (hs i)).trans (image_mono (hsV i))
    weight := w
    weight_contDiff_one := hw
    weight_eq_density := fun i z ↦ hweight i (Set.inclusion (hsub i) z) z.2
    inverseMetric := a
    inverseMetric_contDiff_one := ha
    christoffel := Γ
    contractedChristoffel := fun i z j ↦ -(∑ k, ∑ l, a i z k l * Γ i z j k l)
    contractedChristoffel_eq := fun _ _ _ ↦ rfl
    density_inverseMetric_compatibility := fun i z ↦ hcompat i (Set.inclusion (hsub i) z) z.2
    intrinsicCoordinateLaplacian_eq := fun i z ↦ hcoord i (Set.inclusion (hsub i) z) z.2
    localizedLaplacian_aestronglyMeasurable := fun i ↦ (hcontinuous i).aestronglyMeasurable }

section StokesThree
variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
  [ChartedSpace (ClosedSmoothModel 3) M₃]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
local notation "I₃" => closedSmoothModelWithCorners 3
local notation "E₃" => ClosedSmoothModel 3

/-- On a closed smooth three-manifold the Laplacian of a C² scalar is
integrable and its integral is zero. -/
theorem closedLaplacianStokes_of_contMDiff_two
    (g : ClosedSmoothRiemannianMetric 3 M₃) (f : M₃ → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    ClosedLaplacianStokes g f := by
  letI : SecondCountableTopology M₃ := ChartedSpace.secondCountable_of_sigmaCompact E₃ M₃
  let C := compactFiniteExtendedChartCover (n := 3) (M := M₃)
  obtain ⟨V, ρ, w, a, _hcover, hV, hVs, _hcompact, hρ, hw, ha, hwe, hae⟩ :=
    ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_cover_global_coefficients g C
  let G := fun i ↦ inverseChartPullbackGramMatrixField g (C.anchor i)
  let A : Fin C.chartCount → E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun i z ↦ (G i z)⁻¹
  let Γ := fun i z j k l ↦ (1 / 2 : ℝ) * ∑ m, A i z j m *
    (coordinateDirectionalDerivative (fun y ↦ G i y l m) k z +
     coordinateDirectionalDerivative (fun y ↦ G i y k m) l z -
     coordinateDirectionalDerivative (fun y ↦ G i y k l) m z)
  have hle1 : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hle2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  apply (geometry_of_shrunk_coordinate_coefficients g f hf C V hV hVs ρ hρ w a Γ
    (fun i ↦ (hw i).of_le hle1) (fun i j k ↦ (ha i j k).of_le hle1) ?_ ?_ ?_).closedLaplacianStokes
  · intro i z hz
    rw [(hwe i z (image_mono subset_closure hz)).self_of_nhds]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g (C.anchor i)).2 z
  · intro i z hz j
    exact ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq
      g (C.anchor i) (w i) (a i) z z.2
      (hwe i z (image_mono subset_closure hz)) (hae i z (image_mono subset_closure hz)) j
  · intro i z hz
    have hlocal : ContMDiff I₃ 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
      ((ρ i).contMDiff.of_le hle2).mul hf
    have h := laplacianAt_eq_christoffelCoordinateLaplacian g (C.anchor i) (V i) (hVs i)
      (fun x ↦ ρ i x * f x) (tsupport_mul_subset_left.trans (hρ i)) hlocal z hz
    change g.laplacianAt (fun x ↦ ρ i x * f x)
      (inverseExtendedChartParametrization (n := 3) (C.anchor i) z) =
      christoffelCoordinateLaplacian (A i) (Γ i)
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) (C.anchor i) (fun x ↦ ρ i x * f x)) z at h
    rw [h]
    unfold christoffelCoordinateLaplacian
    have hval : a i z = A i z := (hae i z (image_mono subset_closure hz)).self_of_nhds
    rw [hval]

/-- Joint C³ metric entries supply the scalar C² input along a forward
normalized Ricci flow. -/
theorem closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M₃)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M₃, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x) := by
  intro t ht
  apply closedLaplacianStokes_of_contMDiff_two
  intro x
  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow (hFlow t ht)
    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three (hJoint t y)) x

end StokesThree

end Poincare.IntrinsicLaplacianCoordinateForm
