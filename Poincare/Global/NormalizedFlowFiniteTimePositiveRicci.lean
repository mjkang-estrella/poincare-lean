import Poincare.Global.NormalizedFlowEnergyConcentration
import Poincare.Global.ScalarVariation
import Poincare.CurvatureConditions

/-!
# A finite normalized-flow slice with positive Ricci curvature

Uniformly small traceless-Ricci energy is already available along an escaping
sequence of normalized-flow times.  This file converts that analytic endpoint
into a finite-time geometric statement in dimension three.

The conversion is quantitative.  If scalar curvature is bounded below by
`rho > 0` and `|Ric°|² < (rho / 6)²`, then every Ricci eigenvalue is
strictly larger than both `rho / 6` and `R / 6`.  Consequently Ricci is
positive definite and the scalar-normalized Ricci quotient is at most `1/2`.

No limiting metric, convergence theorem, or sphere-recognition input is used.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

namespace PinchingAlgebra

/--
For a diagonal three-dimensional Ricci operator, a scalar lower bound and a
small traceless part force a quantitative lower bound on every eigenvalue.

The second floor is the scale-invariant Hamilton pinching floor `lambda_i >
R / 6`; the first records the absolute positive lower bound inherited from
`R >= rho`.
-/
theorem diagonal_eigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
    {rho a b c : ℝ} (hrho : 0 < rho)
    (hscalar : rho ≤ diagonalScalar3 a b c)
    (htraceless :
      diagonalTracelessRicciNormSq3 a b c < (rho / 6) ^ 2) :
    (rho / 6 < a ∧ diagonalScalar3 a b c / 6 < a) ∧
      (rho / 6 < b ∧ diagonalScalar3 a b c / 6 < b) ∧
        (rho / 6 < c ∧ diagonalScalar3 a b c / 6 < c) := by
  let R : ℝ := diagonalScalar3 a b c
  have hR : rho ≤ R := by simpa [R] using hscalar
  have hrho6 : 0 < rho / 6 := div_pos hrho (by norm_num)
  have hdecomp :
      diagonalTracelessRicciNormSq3 a b c =
        (a - R / 3) ^ 2 + (b - R / 3) ^ 2 + (c - R / 3) ^ 2 := by
    simp [R, diagonalTracelessRicciNormSq3, diagonalRicciNormSq3,
      diagonalScalar3]
    ring
  have hsmall :
      (a - R / 3) ^ 2 + (b - R / 3) ^ 2 + (c - R / 3) ^ 2 <
        (rho / 6) ^ 2 := by
    simpa only [hdecomp] using htraceless
  have lower_of_component
      {x y z : ℝ}
      (hsum : (x - R / 3) ^ 2 + (y - R / 3) ^ 2 + (z - R / 3) ^ 2 <
        (rho / 6) ^ 2) :
      rho / 6 < x ∧ R / 6 < x := by
    have hy : 0 ≤ (y - R / 3) ^ 2 := sq_nonneg _
    have hz : 0 ≤ (z - R / 3) ^ 2 := sq_nonneg _
    have hxdev : (x - R / 3) ^ 2 < (rho / 6) ^ 2 := by
      nlinarith
    have hxabs : R / 3 - rho / 6 < x := by
      by_contra hnot
      have hxle : x ≤ R / 3 - rho / 6 := le_of_not_gt hnot
      have hfirst : 0 ≤ R / 3 - x - rho / 6 := by linarith
      have hsecond : 0 ≤ R / 3 - x + rho / 6 := by linarith
      have hprod :
          0 ≤ (R / 3 - x - rho / 6) * (R / 3 - x + rho / 6) :=
        mul_nonneg hfirst hsecond
      nlinarith [hprod]
    constructor
    · nlinarith
    · nlinarith
  refine ⟨lower_of_component hsmall, ?_, ?_⟩
  · have hb := lower_of_component
      (x := b) (y := a) (z := c) ?_
    · exact hb
    · nlinarith [hsmall]
  · have hc := lower_of_component
      (x := c) (y := a) (z := b) ?_
    · exact hc
    · nlinarith [hsmall]

end PinchingAlgebra

section PointwisePositiveRicci

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "TM" => (TangentSpace I : M → Type _)

/--
The invariant form of the diagonal estimate: every eigenvalue in every Ricci
eigenbasis has both an absolute and a scalar-relative positive floor.
-/
theorem ClosedSmoothRiemannianMetric.ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {rho : ℝ} (hrho : 0 < rho) {x : M}
    (hscalar : rho ≤ g.scalarAt x)
    (htraceless : g.tracelessRicciNormSqAt x < (rho / 6) ^ 2)
    (b : Module.Basis (Fin 3) ℝ (TM x)) (μ : Fin 3 → ℝ)
    (hEig : ∀ i : Fin 3, g.ricciEndoAt x (b i) = μ i • b i) :
    ∀ i : Fin 3, rho / 6 < μ i ∧ g.scalarAt x / 6 < μ i := by
  have hR :
      g.scalarAt x =
        PinchingAlgebra.diagonalScalar3 (μ 0) (μ 1) (μ 2) := by
    rw [g.scalarAt_eq_sum_eigenvalues_of_ricciEndoAt_eigenbasis b μ hEig]
    simp [Fin.sum_univ_three, PinchingAlgebra.diagonalScalar3]
  have hT :
      g.tracelessRicciNormSqAt x =
        PinchingAlgebra.diagonalTracelessRicciNormSq3 (μ 0) (μ 1) (μ 2) :=
    g.tracelessRicciNormSqAt_eq_diagonal_of_ricciEndoAt_eigenbasis
      rfl b μ hEig
  have hfloor :=
    PinchingAlgebra.diagonal_eigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
      (a := μ 0) (b := μ 1) (c := μ 2) hrho
        (by simpa only [hR] using hscalar)
        (by simpa only [hT] using htraceless)
  intro i
  fin_cases i
  · simpa [← hR] using hfloor.1
  · simpa [← hR] using hfloor.2.1
  · simpa [← hR] using hfloor.2.2

/--
The same hypotheses imply the existing scalar-normalized pinching estimate
`|Ric|² / R² ≤ 1/2`.
-/
theorem ClosedSmoothRiemannianMetric.pinchingQuotientAt_le_one_half_of_scalar_lower_of_traceless_lt
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {rho : ℝ} (hrho : 0 < rho) {x : M}
    (hscalar : rho ≤ g.scalarAt x)
    (htraceless : g.tracelessRicciNormSqAt x < (rho / 6) ^ 2) :
    g.pinchingQuotientAt x ≤ 1 / 2 := by
  have hRpos : 0 < g.scalarAt x := hrho.trans_le hscalar
  have hpin :
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (μ : Fin 3 → ℝ),
        (∀ i : Fin 3, g.ricciEndoAt x (b i) = μ i • b i) →
          ∀ i : Fin 3, (1 / 6 : ℝ) * g.scalarAt x ≤ μ i := by
    intro b μ hEig i
    have hi :=
      g.ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
        hrho hscalar htraceless b μ hEig i
    nlinarith [hi.2]
  have hq := g.pinchingQuotientAt_le_of_eigenvalue_pinched
    rfl (ε := (1 / 6 : ℝ)) hRpos hpin
  norm_num at hq ⊢
  exact hq

/--
The quantitative eigenvalue floor makes the genuine Ricci bilinear form
positive definite, expressed through the repository's existing curvature
predicate.
-/
theorem ClosedSmoothRiemannianMetric.hasPosRicciAt_of_scalar_lower_of_traceless_lt
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {rho : ℝ} (hrho : 0 < rho) {x : M}
    (hscalar : rho ≤ g.scalarAt x)
    (htraceless : g.tracelessRicciNormSqAt x < (rho / 6) ^ 2) :
    CovariantDerivative.HasPosRicciAt g.leviCivita x := by
  letI : RiemannianBundle (tangentBundle (n := 3) (M := M)) :=
    g.toRiemannianBundle
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel 3))
  let A : TM x →ₗ[ℝ] TM x := g.ricciEndoAt x
  have hsym : A.IsSymmetric := by
    intro u w
    rw [ClosedSmoothRiemannianMetric.fiber_inner_eq (g := g) x]
    rw [ClosedSmoothRiemannianMetric.fiber_inner_eq (g := g) x]
    exact g.ricciEndoAt_selfAdjoint x u w
  have hdim : Module.finrank ℝ (TM x) = 3 := by
    simpa using
      ClosedSmoothRiemannianMetric.finrank_tangentSpace_eq
        (n := 3) (M := M) x
  let e : OrthonormalBasis (Fin 3) ℝ (TM x) := hsym.eigenvectorBasis hdim
  let μ : Fin 3 → ℝ := hsym.eigenvalues hdim
  have hEig : ∀ i : Fin 3, g.ricciEndoAt x (e.toBasis i) = μ i • e.toBasis i := by
    intro i
    exact hsym.apply_eigenvectorBasis hdim i
  have hμ : ∀ i : Fin 3, rho / 6 < μ i := by
    intro i
    exact
      (g.ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
        hrho hscalar htraceless e.toBasis μ hEig i).1
  intro u hu
  change 0 < g.ricciAt x u u
  rw [← g.inner_ricciEndoAt x u u]
  rw [← ClosedSmoothRiemannianMetric.fiber_inner_eq (g := g) x]
  change 0 < inner ℝ (A u) u
  have hinner :
      inner ℝ (A u) u =
        ∑ i : Fin 3, μ i * (e.repr u i) ^ 2 := by
    have hEigA : ∀ i : Fin 3, A (e i) = μ i • e i := hEig
    nth_rw 1 [← e.sum_repr u]
    rw [map_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, hEigA i]
    simp only [inner_smul_left, e.repr_apply_apply, smul_smul,
      starRingEnd_apply, star_trivial]
    ring
  rw [hinner]
  have hsumSq : ∑ i : Fin 3, (e.repr u i) ^ 2 = ‖u‖ ^ 2 := by
    simpa [e.repr_apply_apply] using e.sum_sq_inner_right u
  have hnormSq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hweighted :
      (rho / 6) * (∑ i : Fin 3, (e.repr u i) ^ 2) ≤
        ∑ i : Fin 3, μ i * (e.repr u i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (hμ i).le (sq_nonneg _)
  have hpositive : 0 < (rho / 6) * (∑ i : Fin 3, (e.repr u i) ^ 2) := by
    rw [hsumSq]
    exact mul_pos (div_pos hrho (by norm_num)) hnormSq
  exact hpositive.trans_le hweighted

end PointwisePositiveRicci

section FiniteNormalizedFlowTime

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Finite absolute normalized-flow dissipation, uniform concentration inputs,
and one preserved positive scalar lower bound produce a single finite
nonnegative time at which Ricci is globally positive and quantitatively
one-sixth pinched.
-/
theorem exists_finite_normalizedFlow_time_global_positiveRicci_of_finiteAbsoluteDissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {L rho : ℝ} (hrho : 0 < rho)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hUniformLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) L)
    (hUniformNoncollapse : UniformClosedRiemannianBallVolumeLower gt)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x) :
    ∃ t : ℝ, 0 ≤ t ∧
      (∀ x : M,
        (∀ (b : Module.Basis (Fin 3) ℝ
            (TangentSpace (closedSmoothModelWithCorners 3) x))
            (μ : Fin 3 → ℝ),
          (∀ i : Fin 3, (gt t).ricciEndoAt x (b i) = μ i • b i) →
            ∀ i : Fin 3,
              rho / 6 < μ i ∧ (gt t).scalarAt x / 6 < μ i) ∧
        CovariantDerivative.HasPosRicciAt (gt t).leviCivita x ∧
        (gt t).pinchingQuotientAt x ≤ 1 / 2) := by
  obtain ⟨sample, hsample, _hEnergyZero, hsmall⟩ :=
    exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation hUniformLipschitz hUniformNoncollapse
  have hthreshold : 0 < (rho / 6) ^ 2 :=
    sq_pos_of_pos (div_pos hrho (by norm_num))
  have hsmallEventually :
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (sample i)).tracelessRicciNormSqAt x < (rho / 6) ^ 2 :=
    hsmall ((rho / 6) ^ 2) hthreshold
  have htimeEventually : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hsample.eventually (eventually_ge_atTop 0)
  obtain ⟨i, htime, htr⟩ := (htimeEventually.and hsmallEventually).exists
  refine ⟨sample i, htime, ?_⟩
  intro x
  have hscalar := hScalarLower (sample i) htime x
  refine ⟨?_, ?_, ?_⟩
  · intro b μ hEig j
    exact
      (gt (sample i)).ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
        hrho hscalar (htr x) b μ hEig j
  · exact
      (gt (sample i)).hasPosRicciAt_of_scalar_lower_of_traceless_lt
        hrho hscalar (htr x)
  · exact
      (gt (sample i)).pinchingQuotientAt_le_one_half_of_scalar_lower_of_traceless_lt
        hrho hscalar (htr x)

/-- Common-scale cubic noncollapse supplies the ball-volume input in the
finite-time positive-Ricci theorem. -/
theorem exists_finite_normalizedFlow_time_global_positiveRicci_of_finiteAbsoluteDissipation_of_cubicNoncollapse
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {L kappa r0 rho : ℝ} (hrho : 0 < rho)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hUniformLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) L)
    (hUniformNoncollapse :
      UniformClosedRiemannianCubicNoncollapse gt kappa r0)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x) :
    ∃ t : ℝ, 0 ≤ t ∧
      (∀ x : M,
        (∀ (b : Module.Basis (Fin 3) ℝ
            (TangentSpace (closedSmoothModelWithCorners 3) x))
            (μ : Fin 3 → ℝ),
          (∀ i : Fin 3, (gt t).ricciEndoAt x (b i) = μ i • b i) →
            ∀ i : Fin 3,
              rho / 6 < μ i ∧ (gt t).scalarAt x / 6 < μ i) ∧
        CovariantDerivative.HasPosRicciAt (gt t).leviCivita x ∧
        (gt t).pinchingQuotientAt x ≤ 1 / 2) :=
  exists_finite_normalizedFlow_time_global_positiveRicci_of_finiteAbsoluteDissipation
    gt hrho hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hUniformLipschitz
      (uniformClosedRiemannianBallVolumeLower_of_cubicNoncollapse
        gt hUniformNoncollapse)
      hScalarLower

end FiniteNormalizedFlowTime

end Poincare
