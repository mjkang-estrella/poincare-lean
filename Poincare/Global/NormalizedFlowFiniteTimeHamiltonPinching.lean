import Poincare.Global.NormalizedFlowFiniteTimePositiveRicci
import Poincare.Global.ScalarEvolution

/-!
# Feeding a finite normalized-flow slice into Hamilton pinching

The compactness-free concentration theorem produces a finite slice on which
the traceless Ricci tensor is uniformly small.  This file chooses the slice
with a slightly stronger quantitative threshold: if
`|Ric°|² < (rho / 12)²` and `R >= rho > 0`, every Ricci eigenvalue is
strictly larger than `R / 4`.

That `1/4` initial floor is deliberately stronger than mere positive Ricci.
Hamilton's existing quotient maximum principle transports it to the positive
floor

`lambda_i >= (2 * (1/4) - 1/3) R = R / 6`.

The transported `1/6` floor is then exactly an admissible, proof-generated
input to the existing improved traceless-pinching maximum principle.  All PDE
evolution and regularity assumptions remain explicit.  No convergence or
sphere-recognition conclusion appears here.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

namespace PinchingAlgebra

/-- A `rho / 12` traceless bound and `R >= rho` force the relative Ricci
eigenvalue floor `lambda_i > R / 4`. -/
theorem diagonal_eigenvalue_one_fourth_floor_of_scalar_lower_of_traceless_lt
    {rho a b c : ℝ} (hrho : 0 < rho)
    (hscalar : rho ≤ diagonalScalar3 a b c)
    (htraceless :
      diagonalTracelessRicciNormSq3 a b c < (rho / 12) ^ 2) :
    diagonalScalar3 a b c / 4 < a ∧
      diagonalScalar3 a b c / 4 < b ∧
        diagonalScalar3 a b c / 4 < c := by
  let R : ℝ := diagonalScalar3 a b c
  have hR : rho ≤ R := by simpa [R] using hscalar
  have hrho12 : 0 < rho / 12 := div_pos hrho (by norm_num)
  have hdecomp :
      diagonalTracelessRicciNormSq3 a b c =
        (a - R / 3) ^ 2 + (b - R / 3) ^ 2 + (c - R / 3) ^ 2 := by
    simp [R, diagonalTracelessRicciNormSq3, diagonalRicciNormSq3,
      diagonalScalar3]
    ring
  have hsmall :
      (a - R / 3) ^ 2 + (b - R / 3) ^ 2 + (c - R / 3) ^ 2 <
        (rho / 12) ^ 2 := by
    simpa only [hdecomp] using htraceless
  have lower_of_component
      {x y z : ℝ}
      (hsum : (x - R / 3) ^ 2 + (y - R / 3) ^ 2 + (z - R / 3) ^ 2 <
        (rho / 12) ^ 2) :
      R / 4 < x := by
    have hy : 0 ≤ (y - R / 3) ^ 2 := sq_nonneg _
    have hz : 0 ≤ (z - R / 3) ^ 2 := sq_nonneg _
    have hxdev : (x - R / 3) ^ 2 < (rho / 12) ^ 2 := by
      nlinarith
    by_contra hnot
    have hxle : x ≤ R / 4 := le_of_not_gt hnot
    have hfirst : 0 ≤ R / 3 - x - rho / 12 := by
      nlinarith
    have hsecond : 0 ≤ R / 3 - x + rho / 12 := by
      nlinarith
    have hprod :
        0 ≤ (R / 3 - x - rho / 12) * (R / 3 - x + rho / 12) :=
      mul_nonneg hfirst hsecond
    nlinarith [hprod]
  refine ⟨lower_of_component hsmall, ?_, ?_⟩
  · apply lower_of_component (x := b) (y := a) (z := c)
    nlinarith [hsmall]
  · apply lower_of_component (x := c) (y := a) (z := b)
    nlinarith [hsmall]

end PinchingAlgebra

section PinchingPayloads

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "TM" => (TangentSpace I : M → Type _)

/-- A global relative lower floor for all Ricci-endomorphism eigenvalues. -/
def GlobalRicciEigenvalueFloor3
    (g : ClosedSmoothRiemannianMetric 3 M) (ε : ℝ)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] : Prop :=
  ∀ x : M, ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (μ : Fin 3 → ℝ),
    (∀ i : Fin 3, g.ricciEndoAt x (b i) = μ i • b i) →
      ∀ i : Fin 3, ε * g.scalarAt x ≤ μ i

/-- The existing positive-Ricci predicate, required at every point. -/
def GlobalPositiveRicci3
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] : Prop :=
  ∀ x : M, CovariantDerivative.HasPosRicciAt g.leviCivita x

/-- A global scalar-normalized Ricci quotient bound. -/
def GlobalPinchingQuotientBound3
    (g : ClosedSmoothRiemannianMetric 3 M) (κ : ℝ)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] : Prop :=
  ∀ x : M, g.pinchingQuotientAt x ≤ κ

/-- The invariant metric version of the `R/4` diagonal floor. -/
theorem ClosedSmoothRiemannianMetric.globalRicciEigenvalueFloor_one_fourth_of_scalar_lower_of_traceless_lt
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {rho : ℝ} (hrho : 0 < rho)
    (hscalar : ∀ x : M, rho ≤ g.scalarAt x)
    (htraceless : ∀ x : M,
      g.tracelessRicciNormSqAt x < (rho / 12) ^ 2) :
    GlobalRicciEigenvalueFloor3 g (1 / 4) := by
  intro x b μ hEig i
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
    PinchingAlgebra.diagonal_eigenvalue_one_fourth_floor_of_scalar_lower_of_traceless_lt
      (a := μ 0) (b := μ 1) (c := μ 2) hrho
        (by simpa only [hR] using hscalar x)
        (by simpa only [hT] using htraceless x)
  have hi : g.scalarAt x / 4 < μ i := by
    fin_cases i
    · simpa [← hR] using hfloor.1
    · simpa [← hR] using hfloor.2.1
    · simpa [← hR] using hfloor.2.2
  nlinarith

/-- The `R/4` eigenvalue floor gives the initial quotient bound `Q ≤ 3/8`. -/
theorem ClosedSmoothRiemannianMetric.globalPinchingQuotientBound_three_eighths_of_globalRicciEigenvalueFloor_one_fourth
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hRpos : ∀ x : M, 0 < g.scalarAt x)
    (hfloor : GlobalRicciEigenvalueFloor3 g (1 / 4)) :
    GlobalPinchingQuotientBound3 g (3 / 8) := by
  intro x
  have hq := g.pinchingQuotientAt_le_of_eigenvalue_pinched
    rfl (ε := (1 / 4 : ℝ)) (hRpos x) (hfloor x)
  norm_num at hq ⊢
  exact hq

end PinchingPayloads

section StrongFiniteSlice

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Choosing the concentration threshold `(rho/12)²` produces a finite slice
whose eigenvalue floor is strong enough to remain positive after Hamilton's
explicit floor-transport loss.
-/
theorem exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation
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
      GlobalRicciEigenvalueFloor3 (gt t) (1 / 4) ∧
      GlobalPositiveRicci3 (gt t) ∧
      GlobalPinchingQuotientBound3 (gt t) (3 / 8) := by
  obtain ⟨sample, hsample, _hEnergyZero, hsmall⟩ :=
    exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation hUniformLipschitz hUniformNoncollapse
  have hthreshold : 0 < (rho / 12) ^ 2 :=
    sq_pos_of_pos (div_pos hrho (by norm_num))
  have hsmallEventually :
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (sample i)).tracelessRicciNormSqAt x < (rho / 12) ^ 2 :=
    hsmall ((rho / 12) ^ 2) hthreshold
  have htimeEventually : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hsample.eventually (eventually_ge_atTop 0)
  obtain ⟨i, htime, htr⟩ := (htimeEventually.and hsmallEventually).exists
  have hscalar : ∀ x : M, rho ≤ (gt (sample i)).scalarAt x :=
    hScalarLower (sample i) htime
  have hfloor : GlobalRicciEigenvalueFloor3 (gt (sample i)) (1 / 4) :=
    (gt (sample i)).globalRicciEigenvalueFloor_one_fourth_of_scalar_lower_of_traceless_lt
      hrho hscalar htr
  have hRpos : ∀ x : M, 0 < (gt (sample i)).scalarAt x :=
    fun x ↦ hrho.trans_le (hscalar x)
  have hpositive : GlobalPositiveRicci3 (gt (sample i)) := by
    intro x
    apply (gt (sample i)).hasPosRicciAt_of_scalar_lower_of_traceless_lt
      hrho (hscalar x)
    have hsmallSq : (rho / 12) ^ 2 < (rho / 6) ^ 2 := by
      nlinarith [sq_pos_of_pos (div_pos hrho (by norm_num : (0 : ℝ) < 12))]
    exact (htr x).trans hsmallSq
  have hquotient : GlobalPinchingQuotientBound3 (gt (sample i)) (3 / 8) :=
    (gt (sample i)).globalPinchingQuotientBound_three_eighths_of_globalRicciEigenvalueFloor_one_fourth
      hRpos hfloor
  exact ⟨sample i, htime, hfloor, hpositive, hquotient⟩

end StrongFiniteSlice

section HamiltonConsumer

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "TM" => (TangentSpace I : M → Type _)

/--
An `R/4` initial floor supplies Hamilton's initial-data premise.  His ordinary
pinching theorem then preserves the quotient maximum and transports the
eigenvalue floor to `R/6`; that proof-generated floor, rather than a repeated
hypothesis, feeds the improved traceless-pinching theorem.
-/
theorem hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 T delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hT0 : 0 ≤ T)
    (hdeltaNonneg : 0 ≤ delta)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (1 / 6))
    (hInitFloor : GlobalRicciEigenvalueFloor3 (gt t0) (1 / 4))
    (hRpos : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      0 < (gt (t0 + tau)).scalarAt x)
    (hQCont :
      Continuous ↿(fun tau (x : M) ↦
        (gt (t0 + tau)).pinchingQuotientAt x))
    (hQTwo : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).pinchingQuotientAt y) x)
    (hQEvol : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t0 + tau) x
          ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont :
      Continuous ↿(fun tau (x : M) ↦
        (gt (t0 + tau)).tracelessPinchingAt x delta))
    (hTQTwo : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).tracelessPinchingAt y delta) x)
    (hTQEvol : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + tau) x delta
          ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x)) :
    (∀ tau ∈ Icc (0 : ℝ) T,
      pinchingMaximumTrack gt t0 tau ≤ pinchingMaximumTrack gt t0 0) ∧
    (∀ tau ∈ Icc (0 : ℝ) T,
      GlobalRicciEigenvalueFloor3 (gt (t0 + tau)) (1 / 6)) ∧
    (∀ tau ∈ Icc (0 : ℝ) T,
      tracelessPinchingMaximumTrack gt t0 delta tau ≤
        tracelessPinchingMaximumTrack gt t0 delta 0) := by
  have hordinary :
      ∀ tau ∈ Icc (0 : ℝ) T,
        pinchingMaximumTrack gt t0 tau ≤ pinchingMaximumTrack gt t0 0 :=
    hamilton_pinching_preserved
      (gt := gt) (t₀ := t0) (T := T)
      rfl hT0 hQCont hQTwo hQEvol
  have htransportRaw :=
    hamilton_eigenvalue_pinching_floor_preserved
      (gt := gt) (t₀ := t0) (T := T) (ε := (1 / 4 : ℝ))
      rfl (by norm_num) hT0 hQCont hQTwo hQEvol hRpos hInitFloor
  have htransport :
      ∀ tau ∈ Icc (0 : ℝ) T,
        GlobalRicciEigenvalueFloor3 (gt (t0 + tau)) (1 / 6) := by
    intro tau htau x b μ hEig i
    have hi := htransportRaw tau htau x b μ hEig i
    norm_num at hi ⊢
    exact hi
  have himproved :
      ∀ tau ∈ Icc (0 : ℝ) T,
        tracelessPinchingMaximumTrack gt t0 delta tau ≤
          tracelessPinchingMaximumTrack gt t0 delta 0 :=
    hamilton_pinching_improvement
      (gt := gt) (t₀ := t0) (T := T)
      (ε := (1 / 6 : ℝ)) (δ := delta)
      rfl hT0 (by norm_num) (by norm_num) hdeltaNonneg hdeltaAdm
      hTQCont hTQTwo hTQEvol htransport
  exact ⟨hordinary, htransport, himproved⟩

end HamiltonConsumer

section FiniteSliceToHamiltonTrack

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/--
End-to-end finite-time Hamilton consumer.

The concentration argument chooses `t0 >= 0` with an `R/4` initial
eigenvalue floor and `Q <= 3/8`.  The explicit quotient evolution and
regularity hypotheses on every forward slab then produce, on the selected
slab, ordinary quotient preservation, the positive transported `R/6`
eigenvalue floor, and improved traceless-pinching preservation.
-/
theorem exists_finite_normalizedFlow_time_with_forward_hamilton_pinching_of_finiteAbsoluteDissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {L rho T delta : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho) (hT0 : 0 ≤ T)
    (hdeltaNonneg : 0 ≤ delta)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (1 / 6))
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
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t0 : ℝ, 0 ≤ t0 →
      Continuous ↿(fun tau (x : M) ↦
        (gt (t0 + tau)).pinchingQuotientAt x))
    (hQTwo : ∀ t0 : ℝ, 0 ≤ t0 →
      ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
        ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ (gt (t0 + tau)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t0 : ℝ, 0 ≤ t0 →
      ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
        ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
          gt (t0 + tau) x
            ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t0 : ℝ, 0 ≤ t0 →
      Continuous ↿(fun tau (x : M) ↦
        (gt (t0 + tau)).tracelessPinchingAt x delta))
    (hTQTwo : ∀ t0 : ℝ, 0 ≤ t0 →
      ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
        ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ (gt (t0 + tau)).tracelessPinchingAt y delta) x)
    (hTQEvol : ∀ t0 : ℝ, 0 ≤ t0 →
      ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
        ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
          gt (t0 + tau) x delta
            ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x)) :
    ∃ t0 : ℝ, 0 ≤ t0 ∧
      GlobalRicciEigenvalueFloor3 (gt t0) (1 / 4) ∧
      GlobalPositiveRicci3 (gt t0) ∧
      GlobalPinchingQuotientBound3 (gt t0) (3 / 8) ∧
      (∀ tau ∈ Icc (0 : ℝ) T,
        pinchingMaximumTrack gt t0 tau ≤ pinchingMaximumTrack gt t0 0) ∧
      (∀ tau ∈ Icc (0 : ℝ) T,
        GlobalRicciEigenvalueFloor3 (gt (t0 + tau)) (1 / 6)) ∧
      (∀ tau ∈ Icc (0 : ℝ) T,
        tracelessPinchingMaximumTrack gt t0 delta tau ≤
          tracelessPinchingMaximumTrack gt t0 delta 0) := by
  obtain ⟨t0, ht0, hfloor, hpositive, hquotient⟩ :=
    exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation
      gt hrho hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation hUniformLipschitz hUniformNoncollapse hScalarLower
  have hRpos : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      0 < (gt (t0 + tau)).scalarAt x := by
    intro tau htau x
    exact hrho.trans_le
      (hScalarLower (t0 + tau) (add_nonneg ht0 htau.1) x)
  obtain ⟨hordinary, htransport, himproved⟩ :=
    hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor
      gt hT0 hdeltaNonneg hdeltaAdm hfloor hRpos
        (hQCont t0 ht0) (hQTwo t0 ht0) (hQEvol t0 ht0)
        (hTQCont t0 ht0) (hTQTwo t0 ht0) (hTQEvol t0 ht0)
  exact
    ⟨t0, ht0, hfloor, hpositive, hquotient,
      hordinary, htransport, himproved⟩

end FiniteSliceToHamiltonTrack

end Poincare
