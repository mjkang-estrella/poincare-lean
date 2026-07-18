import Poincare.Global.DeTurckBUCUniformSolutionEquivariance
import Poincare.Global.DeTurckBUCReconstructedPathInteriorRegularity
import Poincare.Global.ParabolicMinimumContinuousOn

/-!
# Parabolic uniqueness boundary for reconstructed `BUC` chart overlaps

The classical-core and interior-regularity layers identify the positive-time
derivative of a reconstructed coordinate coefficient with the concrete
Ricci--DeTurck coordinate right-hand side.  That right-hand side is already
proved covariant under preferred-chart transitions.  These facts do not by
themselves identify two independently selected chart solutions: one still
needs the parabolic maximum-principle estimate for their difference.

This file isolates that estimate exactly.  For two compact-time `BUC` paths,
let `rho(t)` be the uniform norm of their difference.  The missing parabolic
input is the upper-right-slope inequality

`D⁺ rho(t) <= C * rho(t)`.

It is stated in the `liminf` form consumed by Mathlib's sharp Gronwall
theorem, so no differentiability of the supremum norm is assumed.  Zero
initial difference and this estimate force equality of the paths.  The final
theorem specializes the result to transported affine uniform solutions.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction Manifold ContDiff

namespace Poincare

section GeometricOverlapRateCancellation

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Pointwise cancellation of the apparent chart-transition commutator in the
classical Ricci--DeTurck equation.  Once two scalar coefficient paths have
the geometric rates in their respective preferred charts, covariance of the
full coordinate right-hand side makes the derivative of their transported
difference exactly zero.

This is the part of overlap uniqueness supplied by coordinate-RHS covariance
and classical interior regularity.  It is only a pointwise scalar statement;
turning it into a uniform-norm maximum-principle estimate is a separate
parabolic input.
-/
theorem deTurckChartTransition_metricRateDifference_hasDerivAt_zero
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (v w : E) (source target : ℝ → ℝ)
    (hsource : HasDerivAt source
      (deTurckChartMetricEvolutionBilin gt bg anchor₁ t z v w) t)
    (htarget : HasDerivAt target
      (deTurckChartMetricEvolutionBilin gt bg anchor₂ t
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w)) t) :
    HasDerivAt (fun r ↦ target r - source r) 0 t := by
  have hcov := deTurckChartMetricEvolutionBilin_chartTransitionDeriv
    gt bg t anchor₁ anchor₂ hz hy v w
  have hdiff := htarget.sub hsource
  rw [hcov] at hdiff
  simpa only [sub_self] using hdiff

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/--
Automatic-classical specialization of
`deTurckChartTransition_metricRateDifference_hasDerivAt_zero`.  Local `C²`
coefficient data identify each reconstructed positive-time derivative with
the Ricci--DeTurck right-hand side.  Tensorial covariance then cancels those
two rates after transporting the target evaluation.

The common geometric family `gt` in the hypotheses is essential: this result
does not yet identify two independently reconstructed metrics with one
another.  Its conclusion is the strongest pointwise cancellation available
before a tensor maximum principle or a classical-to-mild overlap theorem.
-/
theorem ofShiftedBackground_transitionMetricValueDifference_hasDerivAt_zero_of_contDiffAt_two
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData (F := CoordinateTwoTensor E) K₂)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT₁ : b ≤
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan
        K₁ : ℝ))
    (hbT₂ : b ≤
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan
        K₂ : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (v w : E)
    (hstateC2₁ : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformInteriorState
          K₁ u₀₁ t) y) z)
    (hbackgroundC2₁ : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt D₁.background y) z)
    (hremainder₁ :
      coordinateMetricValue
          (D₁.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformInteriorState
                K₁ u₀₁ t + D₁.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor₁ t z v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformInteriorState
                K₁ u₀₁ t + D₁.background) z v w +
          coordinateMetricLaplacianValue D₁.background z v w)
    (hstateC2₂ : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformInteriorState
          K₂ u₀₂ t) y)
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
    (hbackgroundC2₂ : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt D₂.background y)
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
    (hremainder₂ :
      coordinateMetricValue
          (D₂.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformInteriorState
                K₂ u₀₂ t + D₂.background))
          (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) =
        deTurckChartMetricEvolutionBilin gt bg anchor₂ t
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformInteriorState
                K₂ u₀₂ t + D₂.background)
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) +
          coordinateMetricLaplacianValue D₂.background
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w)) :
    let A₁ :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁
    let A₂ :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂
    HasDerivAt
      (fun r : ℝ ↦
        coordinateMetricValue
            (A₂.reconstructedMetricCoefficient K₂ u₀₂
              (Set.projIcc 0 (A₂.uniformLifespan K₂ : ℝ)
                (A₂.uniformLifespan K₂).property r))
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) -
          coordinateMetricValue
            (A₁.reconstructedMetricCoefficient K₁ u₀₁
              (Set.projIcc 0 (A₁.uniformLifespan K₁ : ℝ)
                (A₁.uniformLifespan K₁).property r)) z v w)
      0 t := by
  dsimp only
  apply deTurckChartTransition_metricRateDifference_hasDerivAt_zero
    gt bg t anchor₁ anchor₂ hz hy v w
  · exact
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_contDiffAt_two
          D₁ K₁ u₀₁ hc hca hab hbT₁ hα0 hα1 ht gt bg anchor₁ z v w
          hstateC2₁ hbackgroundC2₁ hremainder₁
  · exact
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_contDiffAt_two
          D₂ K₂ u₀₂ hc hca hab hbT₂ hα0 hα1 ht gt bg anchor₂
          (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w)
          hstateC2₂ hbackgroundC2₂ hremainder₂

end GeometricOverlapRateCancellation

section CompactParabolicEnergyUniqueness

universe u

variable {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]

/--
The exact compact tensor-energy maximum-principle reduction needed for
Ricci--DeTurck overlap uniqueness.  A nonnegative energy which starts at zero
and satisfies

`partial_t energy <= lap energy + c * energy`

on the positive-time slab vanishes identically.  The abstract Laplacian
hypotheses are precisely those used by the slab-local compact minimum
principle: sign reversal, invariance under constants, and nonnegativity at a
minimum of `-energy`.

No derivative is required at time zero.  This matches reconstructed mild
solutions, whose automatic classical regularity is only available for
positive time.
-/
theorem compact_parabolic_energy_eq_zero_of_subsolution_Ioc
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {energy energy' : ℝ → M → ℝ} {c : ℝ → M → ℝ}
    {T C : ℝ} (hT : 0 ≤ T)
    (hc : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M, c t x ≤ C)
    (henergy_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      0 ≤ energy t x)
    (henergy_cont : ContinuousOn (Function.uncurry energy)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (henergy_deriv : ∀ x : M, ∀ t ∈ Set.Ioc (0 : ℝ) T,
      HasDerivAt (fun s ↦ energy s x) (energy' t x) t)
    (hlap_neg : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M,
      lap t (fun y ↦ -energy t y) x = -lap t (energy t) x)
    (hlap_add_const : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      lap t (fun y ↦ -energy t y + k) x =
        lap t (fun y ↦ -energy t y) x)
    (hsubsolution : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M,
      energy' t x ≤ lap t (energy t) x + c t x * energy t x)
    (hmin_lap : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M,
      IsMinOn (fun y ↦ -energy t y) Set.univ x →
        0 ≤ lap t (fun y ↦ -energy t y) x)
    (hzero : ∀ x : M, energy 0 x = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, energy t x = 0 := by
  have hnegative_nonneg :
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, 0 ≤ -energy t x := by
    apply closed_parabolic_min_principle_var_Ioc_continuousOn
      (M := M) (lap := lap)
      (u := fun t x ↦ -energy t x)
      (u' := fun t x ↦ -energy' t x) (c := c) hT hc
    · exact henergy_cont.neg
    · intro x t ht
      exact (henergy_deriv x t ht).neg
    · exact hlap_add_const
    · intro t ht x
      rw [hlap_neg t ht x]
      have hsub := hsubsolution t ht x
      linarith
    · exact hmin_lap
    · intro x
      rw [hzero x]
      show (0 : ℝ) ≤ -0
      norm_num
  intro t ht x
  exact le_antisymm (neg_nonneg.mp (hnegative_nonneg t ht x))
    (henergy_nonneg t ht x)

/--
Interior-time version of the compact energy uniqueness theorem.  All
differential and elliptic hypotheses are needed only on `(0,T)`, exactly where
automatic classical regularity of a compact-time mild solution is available.
The result on the terminal slice follows from slab continuity.
-/
theorem compact_parabolic_energy_eq_zero_of_subsolution_Ioo
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {energy energy' : ℝ → M → ℝ} {c : ℝ → M → ℝ}
    {T C : ℝ} (hT : 0 ≤ T)
    (hc : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, c t x ≤ C)
    (henergy_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      0 ≤ energy t x)
    (henergy_cont : ContinuousOn (Function.uncurry energy)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (henergy_deriv : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s ↦ energy s x) (energy' t x) t)
    (hlap_neg : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      lap t (fun y ↦ -energy t y) x = -lap t (energy t) x)
    (hlap_add_const : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      lap t (fun y ↦ -energy t y + k) x =
        lap t (fun y ↦ -energy t y) x)
    (hsubsolution : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      energy' t x ≤ lap t (energy t) x + c t x * energy t x)
    (hmin_lap : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      IsMinOn (fun y ↦ -energy t y) Set.univ x →
        0 ≤ lap t (fun y ↦ -energy t y) x)
    (hzero : ∀ x : M, energy 0 x = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, energy t x = 0 := by
  have hinterior : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      energy s x = 0 := by
    intro s hs x
    let R : ℝ := (s + T) / 2
    have hs0 : 0 < s := hs.1
    have hsT : s < T := hs.2
    have hR0 : 0 ≤ R := by
      dsimp only [R]
      linarith
    have hRT : R < T := by
      dsimp only [R]
      linarith
    have hsR : s ≤ R := by
      dsimp only [R]
      linarith
    have hvanish := compact_parabolic_energy_eq_zero_of_subsolution_Ioc
      (M := M) (T := R) hR0
      (fun t ht y ↦ hc t ⟨ht.1, lt_of_le_of_lt ht.2 hRT⟩ y)
      (fun t ht y ↦ henergy_nonneg t
        ⟨ht.1, ht.2.trans (le_of_lt hRT)⟩ y)
      (henergy_cont.mono (by
        rintro p ⟨hp, hpuniv⟩
        exact ⟨⟨hp.1, hp.2.trans (le_of_lt hRT)⟩, hpuniv⟩))
      (fun y t ht ↦ henergy_deriv y t
        ⟨ht.1, lt_of_le_of_lt ht.2 hRT⟩)
      (fun t ht y ↦ hlap_neg t
        ⟨ht.1, lt_of_le_of_lt ht.2 hRT⟩ y)
      (fun t ht k y ↦ hlap_add_const t
        ⟨ht.1, lt_of_le_of_lt ht.2 hRT⟩ k y)
      (fun t ht y ↦ hsubsolution t
        ⟨ht.1, lt_of_le_of_lt ht.2 hRT⟩ y)
      (fun t ht y hmin ↦ hmin_lap t
        ⟨ht.1, lt_of_le_of_lt ht.2 hRT⟩ y hmin)
      hzero
    exact hvanish s ⟨le_of_lt hs.1, hsR⟩ x
  intro t ht x
  by_cases htzero : t = 0
  · subst t
    exact hzero x
  by_cases htend : t = T
  · subst t
    have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm htzero)
    have hcurve : ContinuousOn (fun s ↦ energy s x)
        (Set.Icc (0 : ℝ) T) := by
      refine henergy_cont.comp
        (continuous_id.prodMk continuous_const).continuousOn ?_
      intro s hs
      exact ⟨hs, Set.mem_univ x⟩
    letI : NeBot (nhdsWithin T (Set.Ioo (0 : ℝ) T)) :=
      right_nhdsWithin_Ioo_neBot hTpos
    have hlimit : Tendsto (fun s ↦ energy s x)
        (nhdsWithin T (Set.Ioo (0 : ℝ) T)) (nhds (energy T x)) :=
      (hcurve T ⟨hT, le_rfl⟩).mono Set.Ioo_subset_Icc_self
    have heq : (fun s ↦ energy s x) =ᶠ[
        nhdsWithin T (Set.Ioo (0 : ℝ) T)] (fun _ ↦ 0) :=
      Filter.eventuallyEq_of_mem self_mem_nhdsWithin
        (fun s hs ↦ hinterior s hs x)
    exact tendsto_nhds_unique hlimit (tendsto_const_nhds.congr' heq.symm)
  · exact hinterior t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero),
        lt_of_le_of_ne ht.2 htend⟩ x

end CompactParabolicEnergyUniqueness

section AbstractParabolicDifference

variable {X : Type*}
variable [NormedAddCommGroup X]

/-- Uniform-norm difference of two compact-time paths, extended to all real
times by projection to their common compact interval. -/
def duhamelPathDifferenceNorm (T : ℝ≥0)
    (u v : DuhamelPath T X) (t : ℝ) : ℝ :=
  ‖u (Set.projIcc 0 (T : ℝ) T.property t) -
    v (Set.projIcc 0 (T : ℝ) T.property t)‖

/--
The exact upper-right-slope estimate supplied by a parabolic maximum
principle for the difference of two solutions.  This is a `liminf`-slope
statement, not a derivative of the norm, because the uniform norm need not be
differentiable at a maximizing coefficient.
-/
def HasParabolicDuhamelDifferenceSlopeBound
    (T : ℝ≥0) (C : ℝ) (u v : DuhamelPath T X) : Prop :=
  ∀ t ∈ Set.Ico (0 : ℝ) (T : ℝ), ∀ r : ℝ,
    C * duhamelPathDifferenceNorm T u v t < r →
      ∃ᶠ s in nhdsWithin t (Set.Ioi t),
        (s - t)⁻¹ *
          (duhamelPathDifferenceNorm T u v s -
            duhamelPathDifferenceNorm T u v t) < r

/-- The projected uniform difference norm is continuous. -/
theorem continuous_duhamelPathDifferenceNorm
    (T : ℝ≥0) (u v : DuhamelPath T X) :
    Continuous (duhamelPathDifferenceNorm T u v) := by
  apply continuous_norm.comp
  exact
    (u.continuous.comp (continuous_projIcc (h := T.property))).sub
      (v.continuous.comp (continuous_projIcc (h := T.property)))

/--
Parabolic overlap uniqueness from the exact maximum-principle slope bound.
This is the non-circular comparison theorem: its hypotheses mention neither a
chosen fixed-point equality nor covariance of either selected solution.
-/
theorem duhamelPaths_eq_of_parabolicDifferenceSlopeBound
    (T : ℝ≥0) (C : ℝ) (u v : DuhamelPath T X)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)))
    (hslope : HasParabolicDuhamelDifferenceSlopeBound T C u v) :
    u = v := by
  let rho : ℝ → ℝ := duhamelPathDifferenceNorm T u v
  have hrhoContinuous : ContinuousOn rho (Set.Icc (0 : ℝ) (T : ℝ)) :=
    (continuous_duhamelPathDifferenceNorm T u v).continuousOn
  have hrhoZero : rho 0 ≤ 0 := by
    have hproj : Set.projIcc 0 (T : ℝ) T.property 0 =
        (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) := by
      exact Set.projIcc_of_mem T.property ⟨le_rfl, T.property⟩
    simp only [rho, duhamelPathDifferenceNorm, hproj, hzero, sub_self,
      norm_zero, le_refl]
  have hrhoBound : ∀ t ∈ Set.Ico (0 : ℝ) (T : ℝ),
      C * rho t ≤ C * rho t + 0 := by
    intro t _ht
    rw [add_zero]
  have hgronwall : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      rho t ≤ gronwallBound 0 C 0 (t - 0) := by
    exact le_gronwallBound_of_liminf_deriv_right_le
      hrhoContinuous (by simpa only [rho] using hslope) hrhoZero hrhoBound
  apply ContinuousMap.ext
  intro t
  have hrhoNonneg : 0 ≤ rho (t : ℝ) := by
    exact norm_nonneg _
  have hrhoNonpos : rho (t : ℝ) ≤ 0 := by
    simpa only [gronwallBound_ε0_δ0] using hgronwall (t : ℝ) t.property
  have hrhoEq : rho (t : ℝ) = 0 := le_antisymm hrhoNonpos hrhoNonneg
  have hproj : Set.projIcc 0 (T : ℝ) T.property (t : ℝ) = t := by
    exact Set.projIcc_of_mem T.property t.property
  have hnorm : ‖u t - v t‖ = 0 := by
    simpa only [rho, duhamelPathDifferenceNorm, hproj] using hrhoEq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Equality gives the parabolic slope bound with any reaction constant.  This
small converse lets a stronger tensor-energy certificate feed every existing
slope-based overlap consumer. -/
theorem hasParabolicDuhamelDifferenceSlopeBound_of_eq
    (T : ℝ≥0) (C : ℝ) (u v : DuhamelPath T X) (h : u = v) :
    HasParabolicDuhamelDifferenceSlopeBound T C u v := by
  subst v
  intro t _ht r hr
  have hrpos : 0 < r := by
    simpa only [duhamelPathDifferenceNorm, sub_self, norm_zero, mul_zero] using hr
  exact (Filter.Eventually.of_forall (fun s ↦ by
    simpa only [duhamelPathDifferenceNorm, sub_self, norm_zero, sub_zero,
      mul_zero] using hrpos)).frequently

end AbstractParabolicDifference

section CompactParabolicDuhamelDifferenceEnergy

universe u

variable {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
variable {X : Type*} [NormedAddCommGroup X]

/--
A complete, non-circular compact tensor-energy certificate for equality of two
compact-time paths.  The only problem-specific analytic field is
`subsolution`; all other fields are continuity, positivity, Laplacian
structure, initial matching, and the statement that zero energy detects
equality of the two coefficients.
-/
structure CompactParabolicDuhamelDifferenceEnergyData
    (T : ℝ≥0) (u v : DuhamelPath T X) where
  lap : ℝ → (M → ℝ) → M → ℝ
  energy : ℝ → M → ℝ
  energyRate : ℝ → M → ℝ
  reaction : ℝ → M → ℝ
  reactionBound : ℝ
  reaction_le : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
    reaction t x ≤ reactionBound
  energy_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ x : M,
    0 ≤ energy t x
  energy_continuousOn : ContinuousOn (Function.uncurry energy)
    (Set.Icc (0 : ℝ) (T : ℝ) ×ˢ (Set.univ : Set M))
  energy_hasDerivAt : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
    HasDerivAt (fun s ↦ energy s x) (energyRate t x) t
  lap_neg : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
    lap t (fun y ↦ -energy t y) x = -lap t (energy t) x
  lap_add_const : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ k : ℝ, ∀ x : M,
    lap t (fun y ↦ -energy t y + k) x =
      lap t (fun y ↦ -energy t y) x
  subsolution : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
    energyRate t x ≤ lap t (energy t) x + reaction t x * energy t x
  lap_nonneg_at_negative_energy_min :
    ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      IsMinOn (fun y ↦ -energy t y) Set.univ x →
        0 ≤ lap t (fun y ↦ -energy t y) x
  energy_zero : ∀ x : M, energy 0 x = 0
  zero_energy_detects : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
    (∀ x : M, energy (t : ℝ) x = 0) → u t = v t

/-- A compact tensor-energy subsolution certificate identifies the two paths.
This is the maximum-principle route behind the more abstract uniform-slope
criterion. -/
theorem duhamelPaths_eq_of_compactParabolicDifferenceEnergy
    (T : ℝ≥0) (u v : DuhamelPath T X)
    (D : CompactParabolicDuhamelDifferenceEnergyData
      (M := M) T u v) :
    u = v := by
  have henergyZero := compact_parabolic_energy_eq_zero_of_subsolution_Ioo
    (M := M) T.property D.reaction_le D.energy_nonneg D.energy_continuousOn
    D.energy_hasDerivAt D.lap_neg D.lap_add_const D.subsolution
    D.lap_nonneg_at_negative_energy_min D.energy_zero
  apply ContinuousMap.ext
  intro t
  exact D.zero_energy_detects t (henergyZero (t : ℝ) t.property)

end CompactParabolicDuhamelDifferenceEnergy

section PointwiseTensorDifferenceEnergy

universe uX uV

variable {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
variable {X : Type uX} {V : Type uV}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Banach-valued difference of two compact-time paths, extended to all real
times by projection to the common interval. -/
def extendedDuhamelPathDifference (T : ℝ≥0)
    (u v : DuhamelPath T X) (t : ℝ) : X :=
  u (Set.projIcc 0 (T : ℝ) T.property t) -
    v (Set.projIcc 0 (T : ℝ) T.property t)

omit [NormedSpace ℝ X] in
/-- The extended Banach-valued path difference is continuous. -/
theorem continuous_extendedDuhamelPathDifference
    (T : ℝ≥0) (u v : DuhamelPath T X) :
    Continuous (extendedDuhamelPathDifference T u v) := by
  exact
    (u.continuous.comp (continuous_projIcc (h := T.property))).sub
      (v.continuous.comp (continuous_projIcc (h := T.property)))

/-- Classical interior derivatives of the two coefficient paths automatically
give the Banach-valued rate required by the pointwise tensor-energy
constructor. -/
theorem extendedDuhamelPathDifference_hasDerivAt_of_pathRates
    (T : ℝ≥0) (u v : DuhamelPath T X) (t : ℝ) (uRate vRate : X)
    (hu : HasDerivAt
      (fun s ↦ u (Set.projIcc 0 (T : ℝ) T.property s)) uRate t)
    (hv : HasDerivAt
      (fun s ↦ v (Set.projIcc 0 (T : ℝ) T.property s)) vRate t) :
    HasDerivAt (extendedDuhamelPathDifference T u v) (uRate - vRate) t := by
  simpa only [extendedDuhamelPathDifference] using hu.sub hv

/-- A time-independent continuous linear chart transport carries the source
classical rate to the transported path rate.  Combined with automatic
interior regularity in each chart, this discharges the `hpathRate` premise of
the pointwise energy constructor. -/
theorem extended_cast_mapDuhamelPathDifference_hasDerivAt_of_pathRates
    {S T : ℝ≥0} (hT : S = T) (L : X →L[ℝ] X)
    (u : DuhamelPath S X) (v : DuhamelPath T X)
    (t : ℝ) (uRate vRate : X)
    (hu : HasDerivAt
      (fun s ↦ u (Set.projIcc 0 (S : ℝ) S.property s)) uRate t)
    (hv : HasDerivAt
      (fun s ↦ v (Set.projIcc 0 (T : ℝ) T.property s)) vRate t) :
    HasDerivAt
      (extendedDuhamelPathDifference T
        (castDuhamelPath hT (mapDuhamelPath S L u)) v)
      (L uRate - vRate) t := by
  cases hT
  apply extendedDuhamelPathDifference_hasDerivAt_of_pathRates
  · have h := L.hasFDerivAt.comp_hasDerivAt t hu
    simpa only [castDuhamelPath_rfl, mapDuhamelPath_apply,
      Function.comp_apply] using h
  · exact hv

/-- Evaluate a path difference as a pointwise tensor field on a compact
spatial domain. -/
def pointwiseDuhamelDifferenceTensor
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (u v : DuhamelPath T X) (t : ℝ) (x : M) : V :=
  evaluation x (extendedDuhamelPathDifference T u v t)

omit [CompactSpace M] [Nonempty M] in
/-- Continuous pointwise evaluations turn a continuous compact-time path
difference into a jointly continuous spacetime tensor field. -/
theorem continuous_uncurry_pointwiseDuhamelDifferenceTensor
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (hevaluation : Continuous evaluation) (u v : DuhamelPath T X) :
    Continuous (Function.uncurry
      (pointwiseDuhamelDifferenceTensor T evaluation u v)) := by
  change Continuous (fun p : ℝ × M ↦
    evaluation p.2 (extendedDuhamelPathDifference T u v p.1))
  exact (hevaluation.comp continuous_snd).clm_apply
    ((continuous_extendedDuhamelPathDifference T u v).comp continuous_fst)

/-- Structural properties of the scalar spatial Laplacian needed by the
compact maximum principle.  These are automatic for any linear elliptic
Laplacian: negation, constant invariance, and the minimum sign. -/
structure CompactParabolicScalarLaplacianData (T : ℝ≥0) where
  lap : ℝ → (M → ℝ) → M → ℝ
  map_neg : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ f : M → ℝ, ∀ x : M,
    lap t (fun y ↦ -f y) x = -lap t f x
  add_const : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ f : M → ℝ,
    ∀ k : ℝ, ∀ x : M, lap t (fun y ↦ f y + k) x = lap t f x
  nonneg_at_min : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ f : M → ℝ,
    ∀ x : M, IsMinOn f Set.univ x → 0 ≤ lap t f x

/--
Energy-specific scalar Laplacian data.  Unlike
`CompactParabolicScalarLaplacianData`, this record asks for linearity and the
minimum sign only on the squared pointwise difference actually consumed by
the maximum principle.  This is the directly geometric interface: the sign
law for a Riemannian Laplacian requires spatial `C²` regularity of this energy,
not an unrealistically universal regularity statement for every function.
-/
structure CompactParabolicPointwiseDifferenceEnergyLaplacianData
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (u v : DuhamelPath T X) where
  lap : ℝ → (M → ℝ) → M → ℝ
  map_neg_energy : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
    lap t
        (fun y ↦
          -‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x =
      -lap t
        (fun y ↦
          ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x
  add_const_neg_energy : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
    ∀ k : ℝ, ∀ x : M,
    lap t
        (fun y ↦
          -‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2 + k) x =
      lap t
        (fun y ↦
          -‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x
  nonneg_at_negative_energy_min :
    ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      IsMinOn
          (fun y ↦
            -‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2)
          Set.univ x →
        0 ≤ lap t
          (fun y ↦
            -‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x

/-- The pointwise squared-difference subsolution for a specified scalar
spatial Laplacian. -/
def HasPointwiseTensorDifferenceEnergySubsolutionForLaplacian
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (u v : DuhamelPath T X) (pathRate : ℝ → X)
    (lap : ℝ → (M → ℝ) → M → ℝ)
    (reaction : ℝ → M → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
    2 * ⟪pointwiseDuhamelDifferenceTensor T evaluation u v t x,
        evaluation x (pathRate t)⟫_ℝ ≤
      lap t
          (fun y ↦
            ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x +
        reaction t x *
          ‖pointwiseDuhamelDifferenceTensor T evaluation u v t x‖ ^ 2

/--
The narrow Ricci--DeTurck PDE input left after classical time regularity and
pointwise tensor assembly: the squared difference tensor satisfies the
Bochner-type scalar subsolution inequality.  Every other maximum-principle
premise is constructed automatically below.
-/
def HasPointwiseTensorDifferenceEnergySubsolution
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (u v : DuhamelPath T X) (pathRate : ℝ → X)
    (L : CompactParabolicScalarLaplacianData (M := M) T)
    (reaction : ℝ → M → ℝ) : Prop :=
  HasPointwiseTensorDifferenceEnergySubsolutionForLaplacian
    T evaluation u v pathRate L.lap reaction

/-- A lower-order tensor term bounded by `B * |h|` contributes at most
`2 * B * |h|²` to the energy rate. -/
theorem two_mul_real_inner_le_of_norm_le_mul
    (h lower : V) (B : ℝ) (hlower : ‖lower‖ ≤ B * ‖h‖) :
    2 * ⟪h, lower⟫_ℝ ≤ (2 * B) * ‖h‖ ^ 2 := by
  calc
    2 * ⟪h, lower⟫_ℝ ≤ 2 * (‖h‖ * ‖lower‖) := by
      gcongr
      exact real_inner_le_norm h lower
    _ ≤ 2 * (‖h‖ * (B * ‖h‖)) := by
      gcongr
    _ = (2 * B) * ‖h‖ ^ 2 := by ring

omit [TopologicalSpace M] [CompactSpace M] [Nonempty M] in
/--
Derive the full pointwise energy subsolution from a principal Bochner bound
and an explicit lower-order coefficient bound.  For Ricci--DeTurck overlap
uniqueness, `principalEnergy` is the strongly parabolic/Bochner estimate;
`lowerNorm` is the finite coefficient estimate for the linearized remainder.
-/
theorem hasPointwiseTensorDifferenceEnergySubsolutionForLaplacian_of_principal_lowerOrder
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (u v : DuhamelPath T X) (pathRate : ℝ → X)
    (lap : ℝ → (M → ℝ) → M → ℝ)
    (principal lower : ℝ → M → V) (lowerBound : ℝ → M → ℝ)
    (hrate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      evaluation x (pathRate t) = principal t x + lower t x)
    (hprincipalEnergy : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      2 * ⟪pointwiseDuhamelDifferenceTensor T evaluation u v t x,
          principal t x⟫_ℝ ≤
        lap t
          (fun y ↦
            ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x)
    (hlowerNorm : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      ‖lower t x‖ ≤ lowerBound t x *
        ‖pointwiseDuhamelDifferenceTensor T evaluation u v t x‖) :
    HasPointwiseTensorDifferenceEnergySubsolutionForLaplacian
      T evaluation u v pathRate lap
      (fun t x ↦ 2 * lowerBound t x) := by
  intro t ht x
  rw [hrate t ht x, inner_add_right]
  have hprincipal := hprincipalEnergy t ht x
  have hlower := two_mul_real_inner_le_of_norm_le_mul
    (pointwiseDuhamelDifferenceTensor T evaluation u v t x)
    (lower t x) (lowerBound t x) (hlowerNorm t ht x)
  linarith

omit [TopologicalSpace M] [CompactSpace M] [Nonempty M] in
/-- Universal-Laplacian specialization of the principal/lower-order
subsolution estimate. -/
theorem hasPointwiseTensorDifferenceEnergySubsolution_of_principal_lowerOrder
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (u v : DuhamelPath T X) (pathRate : ℝ → X)
    (L : CompactParabolicScalarLaplacianData (M := M) T)
    (principal lower : ℝ → M → V) (lowerBound : ℝ → M → ℝ)
    (hrate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      evaluation x (pathRate t) = principal t x + lower t x)
    (hprincipalEnergy : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      2 * ⟪pointwiseDuhamelDifferenceTensor T evaluation u v t x,
          principal t x⟫_ℝ ≤
        L.lap t
          (fun y ↦
            ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x)
    (hlowerNorm : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      ‖lower t x‖ ≤ lowerBound t x *
        ‖pointwiseDuhamelDifferenceTensor T evaluation u v t x‖) :
    HasPointwiseTensorDifferenceEnergySubsolution T evaluation u v pathRate L
      (fun t x ↦ 2 * lowerBound t x) :=
  hasPointwiseTensorDifferenceEnergySubsolutionForLaplacian_of_principal_lowerOrder
    T evaluation u v pathRate L.lap principal lower lowerBound hrate
      hprincipalEnergy hlowerNorm

/--
Construct the full compact parabolic energy certificate from an actual
pointwise difference tensor.  Joint continuity, energy nonnegativity, the
energy derivative, initial vanishing, and coefficient detection are all
derived.  The sole Ricci--DeTurck-specific analytic hypothesis is
`HasPointwiseTensorDifferenceEnergySubsolution`.
-/
def compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_energyLaplacian_jointContinuous
    (T : ℝ≥0) (u v : DuhamelPath T X)
    (evaluation : M → X →L[ℝ] V)
    (hpointwiseContinuous : Continuous
      (Function.uncurry
        (pointwiseDuhamelDifferenceTensor T evaluation u v)))
    (hseparates : ∀ f : X, (∀ x : M, evaluation x f = 0) → f = 0)
    (pathRate : ℝ → X)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (L : CompactParabolicPointwiseDifferenceEnergyLaplacianData
      T evaluation u v)
    (reaction : ℝ → M → ℝ) (C : ℝ)
    (hreaction : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      reaction t x ≤ C)
    (hsubsolution : HasPointwiseTensorDifferenceEnergySubsolutionForLaplacian
      T evaluation u v pathRate L.lap reaction)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))) :
    CompactParabolicDuhamelDifferenceEnergyData (M := M) T u v where
  lap := L.lap
  energy := fun t x ↦
    ‖pointwiseDuhamelDifferenceTensor T evaluation u v t x‖ ^ 2
  energyRate := fun t x ↦
    2 * ⟪pointwiseDuhamelDifferenceTensor T evaluation u v t x,
      evaluation x (pathRate t)⟫_ℝ
  reaction := reaction
  reactionBound := C
  reaction_le := hreaction
  energy_nonneg := by
    intro t _ht x
    exact sq_nonneg _
  energy_continuousOn := by
    exact (hpointwiseContinuous.norm.pow 2).continuousOn
  energy_hasDerivAt := by
    intro x t ht
    have hpointwise : HasDerivAt
        (fun s ↦ pointwiseDuhamelDifferenceTensor T evaluation u v s x)
        (evaluation x (pathRate t)) t := by
      have h := (evaluation x).hasFDerivAt.comp_hasDerivAt t
        (hpathRate t ht)
      simpa only [pointwiseDuhamelDifferenceTensor, Function.comp_apply] using h
    exact hpointwise.norm_sq
  lap_neg := by
    intro t ht x
    exact L.map_neg_energy t ht x
  lap_add_const := by
    intro t ht k x
    exact L.add_const_neg_energy t ht k x
  subsolution := hsubsolution
  lap_nonneg_at_negative_energy_min := by
    intro t ht x hmin
    exact L.nonneg_at_negative_energy_min t ht x hmin
  energy_zero := by
    intro x
    simp [pointwiseDuhamelDifferenceTensor,
      extendedDuhamelPathDifference, hzero]
  zero_energy_detects := by
    intro t henergy
    apply sub_eq_zero.mp
    apply hseparates
    intro x
    have hproj : Set.projIcc 0 (T : ℝ) T.property (t : ℝ) = t :=
      Set.projIcc_of_mem T.property t.property
    have hsquare : ‖evaluation x (u t - v t)‖ ^ 2 = 0 := by
      simpa only [pointwiseDuhamelDifferenceTensor,
        extendedDuhamelPathDifference, hproj] using henergy x
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-- Universal-Laplacian convenience form of the joint-continuity constructor.
It restricts the universal structural laws to the single squared-difference
energy used by the maximum principle. -/
def compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_jointContinuous
    (T : ℝ≥0) (u v : DuhamelPath T X)
    (evaluation : M → X →L[ℝ] V)
    (hpointwiseContinuous : Continuous
      (Function.uncurry
        (pointwiseDuhamelDifferenceTensor T evaluation u v)))
    (hseparates : ∀ f : X, (∀ x : M, evaluation x f = 0) → f = 0)
    (pathRate : ℝ → X)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (L : CompactParabolicScalarLaplacianData (M := M) T)
    (reaction : ℝ → M → ℝ) (C : ℝ)
    (hreaction : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      reaction t x ≤ C)
    (hsubsolution : HasPointwiseTensorDifferenceEnergySubsolution
      T evaluation u v pathRate L reaction)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))) :
    CompactParabolicDuhamelDifferenceEnergyData (M := M) T u v :=
  compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_energyLaplacian_jointContinuous
    T u v evaluation hpointwiseContinuous hseparates pathRate hpathRate
    { lap := L.lap
      map_neg_energy := by
        intro t ht x
        exact L.map_neg t ht _ x
      add_const_neg_energy := by
        intro t ht k x
        exact L.add_const t ht _ k x
      nonneg_at_negative_energy_min := by
        intro t ht x hmin
        exact L.nonneg_at_min t ht _ x hmin }
    reaction C hreaction hsubsolution hzero

/--
Convenience form of the pointwise tensor-energy constructor when the family
of evaluation operators itself is continuous in operator norm.  The more
general `..._jointContinuous` theorem above is the appropriate interface for
ordinary point evaluation on a uniform function space: those evaluation
operators need not vary continuously in operator norm even though the
resulting spacetime tensor field is jointly continuous.
-/
def compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor
    (T : ℝ≥0) (u v : DuhamelPath T X)
    (evaluation : M → X →L[ℝ] V) (hevaluation : Continuous evaluation)
    (hseparates : ∀ f : X, (∀ x : M, evaluation x f = 0) → f = 0)
    (pathRate : ℝ → X)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (L : CompactParabolicScalarLaplacianData (M := M) T)
    (reaction : ℝ → M → ℝ) (C : ℝ)
    (hreaction : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      reaction t x ≤ C)
    (hsubsolution : HasPointwiseTensorDifferenceEnergySubsolution
      T evaluation u v pathRate L reaction)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))) :
    CompactParabolicDuhamelDifferenceEnergyData (M := M) T u v :=
  compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_jointContinuous
    T u v evaluation
    (continuous_uncurry_pointwiseDuhamelDifferenceTensor
      T evaluation hevaluation u v)
    hseparates pathRate hpathRate L reaction C hreaction hsubsolution hzero

/--
Energy-specific-Laplacian explicit-coefficient constructor for the compact
overlap energy package.  It automatically generates every certificate field
from joint continuity, pointwise detection, the interior Banach rate, initial
equality, explicit lower-order bounds, and the single principal Bochner
inequality.
-/
def compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_principal_lowerOrder_energyLaplacian_jointContinuous
    (T : ℝ≥0) (u v : DuhamelPath T X)
    (evaluation : M → X →L[ℝ] V)
    (hpointwiseContinuous : Continuous
      (Function.uncurry
        (pointwiseDuhamelDifferenceTensor T evaluation u v)))
    (hseparates : ∀ f : X, (∀ x : M, evaluation x f = 0) → f = 0)
    (pathRate : ℝ → X)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (L : CompactParabolicPointwiseDifferenceEnergyLaplacianData
      T evaluation u v)
    (principal lower : ℝ → M → V) (lowerBound : ℝ → M → ℝ)
    (B : ℝ)
    (hlowerBound : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      lowerBound t x ≤ B)
    (hrate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      evaluation x (pathRate t) = principal t x + lower t x)
    (hprincipalEnergy : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      2 * ⟪pointwiseDuhamelDifferenceTensor T evaluation u v t x,
          principal t x⟫_ℝ ≤
        L.lap t
          (fun y ↦
            ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x)
    (hlowerNorm : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      ‖lower t x‖ ≤ lowerBound t x *
        ‖pointwiseDuhamelDifferenceTensor T evaluation u v t x‖)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))) :
    CompactParabolicDuhamelDifferenceEnergyData (M := M) T u v :=
  compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_energyLaplacian_jointContinuous
    T u v evaluation hpointwiseContinuous hseparates pathRate hpathRate L
    (fun t x ↦ 2 * lowerBound t x) (2 * B)
    (by
      intro t ht x
      linarith [hlowerBound t ht x])
    (hasPointwiseTensorDifferenceEnergySubsolutionForLaplacian_of_principal_lowerOrder
      T evaluation u v pathRate L.lap principal lower lowerBound hrate
      hprincipalEnergy hlowerNorm)
    hzero

/--
Explicit-coefficient constructor for the compact overlap energy package.  The
lower-order Ricci--DeTurck difference is bounded by `lowerBound * |h|`, with a
uniform bound `B`; the resulting reaction constant is exactly `2 * B`.

After the classical pointwise rate decomposition is known, the only
second-order PDE premise is `hprincipalEnergy`, the principal Bochner
inequality.  All remaining fields of
`CompactParabolicDuhamelDifferenceEnergyData` are generated here.
-/
def compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_principal_lowerOrder_jointContinuous
    (T : ℝ≥0) (u v : DuhamelPath T X)
    (evaluation : M → X →L[ℝ] V)
    (hpointwiseContinuous : Continuous
      (Function.uncurry
        (pointwiseDuhamelDifferenceTensor T evaluation u v)))
    (hseparates : ∀ f : X, (∀ x : M, evaluation x f = 0) → f = 0)
    (pathRate : ℝ → X)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (L : CompactParabolicScalarLaplacianData (M := M) T)
    (principal lower : ℝ → M → V) (lowerBound : ℝ → M → ℝ)
    (B : ℝ)
    (hlowerBound : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      lowerBound t x ≤ B)
    (hrate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      evaluation x (pathRate t) = principal t x + lower t x)
    (hprincipalEnergy : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      2 * ⟪pointwiseDuhamelDifferenceTensor T evaluation u v t x,
          principal t x⟫_ℝ ≤
        L.lap t
          (fun y ↦
            ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x)
    (hlowerNorm : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      ‖lower t x‖ ≤ lowerBound t x *
        ‖pointwiseDuhamelDifferenceTensor T evaluation u v t x‖)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))) :
    CompactParabolicDuhamelDifferenceEnergyData (M := M) T u v :=
  compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_jointContinuous
    T u v evaluation hpointwiseContinuous hseparates pathRate hpathRate L
    (fun t x ↦ 2 * lowerBound t x) (2 * B)
    (by
      intro t ht x
      linarith [hlowerBound t ht x])
    (hasPointwiseTensorDifferenceEnergySubsolution_of_principal_lowerOrder
      T evaluation u v pathRate L principal lower lowerBound hrate
      hprincipalEnergy hlowerNorm)
    hzero

/-- Operator-family-continuous convenience form of the explicit-coefficient
pointwise energy constructor. -/
def compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_principal_lowerOrder
    (T : ℝ≥0) (u v : DuhamelPath T X)
    (evaluation : M → X →L[ℝ] V) (hevaluation : Continuous evaluation)
    (hseparates : ∀ f : X, (∀ x : M, evaluation x f = 0) → f = 0)
    (pathRate : ℝ → X)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (L : CompactParabolicScalarLaplacianData (M := M) T)
    (principal lower : ℝ → M → V) (lowerBound : ℝ → M → ℝ)
    (B : ℝ)
    (hlowerBound : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      lowerBound t x ≤ B)
    (hrate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      evaluation x (pathRate t) = principal t x + lower t x)
    (hprincipalEnergy : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      2 * ⟪pointwiseDuhamelDifferenceTensor T evaluation u v t x,
          principal t x⟫_ℝ ≤
        L.lap t
          (fun y ↦
            ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x)
    (hlowerNorm : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      ‖lower t x‖ ≤ lowerBound t x *
        ‖pointwiseDuhamelDifferenceTensor T evaluation u v t x‖)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))) :
    CompactParabolicDuhamelDifferenceEnergyData (M := M) T u v :=
  compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_principal_lowerOrder_jointContinuous
    T u v evaluation
    (continuous_uncurry_pointwiseDuhamelDifferenceTensor
      T evaluation hevaluation u v)
    hseparates pathRate hpathRate L principal lower lowerBound B
    hlowerBound hrate hprincipalEnergy hlowerNorm hzero

end PointwiseTensorDifferenceEnergy

section RiemannianPointwiseDifferenceEnergyLaplacian

open Bundle FiberBundle

universe uM uX' uV'

variable {n : ℕ} {M : Type uM}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [CompactSpace M] [Nonempty M]
variable {X : Type uX'} {V : Type uV'}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local notation "I" => closedSmoothModelWithCorners n

/--
The actual closed-manifold scalar Laplacian supplies the energy-specific
Laplacian package once the squared pointwise difference is spatially `C²` at
every strict interior time.  Negation, constant invariance, and the sign at a
global minimum are all proved here from the existing Riemannian Laplacian
calculus.
-/
def closedRiemannianPointwiseDifferenceEnergyLaplacianData
    (T : ℝ≥0) (evaluation : M → X →L[ℝ] V)
    (u v : DuhamelPath T X)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt t).leviCivita 1]
    (henergyC2 : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y ↦
          ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2) x) :
    CompactParabolicPointwiseDifferenceEnergyLaplacianData
      T evaluation u v where
  lap := fun t f x ↦ (gt t).laplacianAt f x
  map_neg_energy := by
    intro t ht x
    let energy : M → ℝ := fun y ↦
      ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2
    have henergy : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 energy y :=
      fun y ↦ henergyC2 t ht y
    have hneg : (fun y : M ↦ -energy y) = (-1 : ℝ) • energy := by
      funext y
      simp
    change (gt t).laplacianAt (fun y : M ↦ -energy y) x =
      -(gt t).laplacianAt energy x
    rw [hneg, (gt t).laplacianAt_const_smul'
      (c := -1) (f := energy) (x := x) henergy]
    ring
  add_const_neg_energy := by
    intro t ht k x
    let energy : M → ℝ := fun y ↦
      ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2
    let negEnergy : M → ℝ := fun y ↦ -energy y
    have henergy : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 energy y :=
      fun y ↦ henergyC2 t ht y
    have hnegEnergy : ∀ y : M,
        ContMDiffAt I 𝓘(ℝ) 2 negEnergy y :=
      fun y ↦ (henergy y).neg
    have hconst : ∀ y : M,
        ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ k) y :=
      fun _ ↦ contMDiffAt_const
    change (gt t).laplacianAt (fun y : M ↦ negEnergy y + k) x =
      (gt t).laplacianAt negEnergy x
    rw [show (fun y : M ↦ negEnergy y + k) =
        negEnergy + fun _ : M ↦ k by rfl]
    rw [(gt t).laplacianAt_add'
      (f := negEnergy) (h := fun _ : M ↦ k) (x := x)
      hnegEnergy hconst]
    rw [(gt t).laplacianAt_const k x]
    ring
  nonneg_at_negative_energy_min := by
    intro t ht x hmin
    let energy : M → ℝ := fun y ↦
      ‖pointwiseDuhamelDifferenceTensor T evaluation u v t y‖ ^ 2
    let negEnergy : M → ℝ := fun y ↦ -energy y
    have hnegEnergy : ContMDiffAt I 𝓘(ℝ) 2 negEnergy x :=
      (henergyC2 t ht x).neg
    apply laplacianAt_nonneg_of_isLocalMin
      (g := gt t) (f := negEnergy) (x := x) hnegEnergy
      ((gt t).mdifferentiableAt_gradient hnegEnergy)
    exact hmin.isLocalMin Filter.univ_mem

end RiemannianPointwiseDifferenceEnergyLaplacian

section MildPicardResidualEstimate

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/--
Quantitative stability of the canonical controlled mild solution against an
arbitrary path in the same orbit ball.  The error is exactly the path's
Picard residual.  This is the estimate supplied by heat-semigroup contraction
and the existing local Lipschitz bound; no PDE maximum principle is used.
-/
theorem dist_semilinearHeatBUCUniformLocalSolution_le_picardResidual
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (w : DuhamelPath (semilinearHeatBUCUniformLifespan data K) BUC)
    (hw : w ∈ Metric.closedBall
      (heatLinearBUCPath (semilinearHeatBUCUniformLifespan data K)
        (u₀ : BUC)) (1 : ℝ)) :
    dist w (semilinearHeatBUCUniformLocalSolution K N data u₀) ≤
      (1 -
        ((semilinearHeatBUCUniformLifespan data K *
          semilinearHeatBUCUniformBallLipschitzConstant data K 1 : ℝ≥0) : ℝ))⁻¹ *
        dist
          (semilinearHeatBUCPicard
            (semilinearHeatBUCUniformLifespan data K)
            (u₀ : BUC) N data.continuous w) w := by
  let T := semilinearHeatBUCUniformLifespan data K
  let q : ℝ≥0 := T * semilinearHeatBUCUniformBallLipschitzConstant data K 1
  let v := semilinearHeatBUCUniformLocalSolution K N data u₀
  let Phi := semilinearHeatBUCPicard T (u₀ : BUC) N data.continuous
  have hwZero : w ∈ Metric.closedBall
      (constantDuhamelPathGeneric T (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) :=
    mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
      (E := E) (F := F) T K 1 (u₀ : BUC) u₀.property hw
  have hvZero : v ∈ Metric.closedBall
      (constantDuhamelPathGeneric T (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) := by
    exact semilinearHeatBUCUniformLocalSolution_mem_zero_ball
      (E := E) (F := F) K N data u₀
  have hvFixed : Phi v = v := by
    exact semilinearHeatBUCUniformLocalSolution_isFixedPt
      (E := E) (F := F) K N data u₀
  have hcontract : dist (Phi w) (Phi v) ≤ (q : ℝ) * dist w v := by
    apply (ContinuousMap.dist_le (mul_nonneg q.property dist_nonneg)).mpr
    intro t
    rw [dist_eq_norm]
    rw [dist_eq_norm w v]
    simpa only [Phi, q, T] using
      (norm_semilinearHeatBUCPicard_sub_le_uniform_zero_ball
        (E := E) (F := F) T K 1 N data (u₀ : BUC) w v hwZero hvZero t)
  have htotal : dist w v ≤ dist (Phi w) w + (q : ℝ) * dist w v := by
    calc
      dist w v ≤ dist w (Phi w) + dist (Phi w) v := dist_triangle _ _ _
      _ = dist (Phi w) w + dist (Phi w) (Phi v) := by
        rw [dist_comm w (Phi w), hvFixed]
      _ ≤ dist (Phi w) w + (q : ℝ) * dist w v :=
        add_le_add le_rfl hcontract
  have hq : (q : ℝ) < 1 := by
    exact_mod_cast semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one data K
  have hden : 0 < 1 - (q : ℝ) := sub_pos.mpr hq
  change dist w v ≤ (1 - (q : ℝ))⁻¹ * dist (Phi w) w
  rw [le_inv_mul_iff₀ hden]
  nlinarith [dist_nonneg (x := Phi w) (y := w)]

universe u

/-- A compact tensor-energy certificate against the canonical mild solution
cancels the candidate's full Picard commutator.  This is the precise bridge
from the PDE maximum-principle route back to the fixed-point route. -/
theorem semilinearHeatBUCPicardResidual_eq_zero_of_compactParabolicDifferenceEnergy
    {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (w : DuhamelPath (semilinearHeatBUCUniformLifespan data K) BUC)
    (D : CompactParabolicDuhamelDifferenceEnergyData (M := M)
      (semilinearHeatBUCUniformLifespan data K) w
      (semilinearHeatBUCUniformLocalSolution K N data u₀)) :
    semilinearHeatBUCPicard (semilinearHeatBUCUniformLifespan data K)
        (u₀ : BUC) N data.continuous w - w = 0 := by
  have hw : w = semilinearHeatBUCUniformLocalSolution K N data u₀ :=
    duhamelPaths_eq_of_compactParabolicDifferenceEnergy
      (semilinearHeatBUCUniformLifespan data K) w
      (semilinearHeatBUCUniformLocalSolution K N data u₀) D
  rw [hw, semilinearHeatBUCUniformLocalSolution_isFixedPt, sub_self]

end MildPicardResidualEstimate

section TransportedParabolicDifference

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Compare a transported source path with a target path on the target time
interval. -/
def transportedDuhamelPathDifferenceNorm
    {S T : ℝ≥0} (hT : S = T) (L : X →L[ℝ] X)
    (u : DuhamelPath S X) (v : DuhamelPath T X) (t : ℝ) : ℝ :=
  duhamelPathDifferenceNorm T
    (castDuhamelPath hT (mapDuhamelPath S L u)) v t

/-- Maximum-principle slope estimate for a transported source path and a
target path. -/
def HasTransportedParabolicDuhamelDifferenceSlopeBound
    {S T : ℝ≥0} (hT : S = T) (C : ℝ) (L : X →L[ℝ] X)
    (u : DuhamelPath S X) (v : DuhamelPath T X) : Prop :=
  HasParabolicDuhamelDifferenceSlopeBound T C
    (castDuhamelPath hT (mapDuhamelPath S L u)) v

/-- Transported compact-time paths agree once their initial values agree and
their uniform difference satisfies the parabolic slope estimate. -/
theorem cast_mapDuhamelPath_eq_of_parabolicDifferenceSlopeBound
    {S T : ℝ≥0} (hT : S = T) (C : ℝ) (L : X →L[ℝ] X)
    (u : DuhamelPath S X) (v : DuhamelPath T X)
    (hzero :
      castDuhamelPath hT (mapDuhamelPath S L u)
          (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)))
    (hslope : HasTransportedParabolicDuhamelDifferenceSlopeBound
      hT C L u v) :
    castDuhamelPath hT (mapDuhamelPath S L u) = v := by
  exact duhamelPaths_eq_of_parabolicDifferenceSlopeBound
    T C _ _ hzero hslope

universe u

/-- Existence of a compact tensor-energy certificate for a transported path
difference.  Packaging the large analytic record behind this proposition keeps
chart-indexed interfaces elaboration-stable. -/
def HasTransportedCompactParabolicDuhamelDifferenceEnergy
    {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    {S T : ℝ≥0} (hT : S = T) (L : X →L[ℝ] X)
    (u : DuhamelPath S X) (v : DuhamelPath T X) : Prop :=
  Nonempty (CompactParabolicDuhamelDifferenceEnergyData (M := M) T
    (castDuhamelPath hT (mapDuhamelPath S L u)) v)

/-- A compact tensor-energy subsolution for the transported difference gives
transported path equality directly. -/
theorem cast_mapDuhamelPath_eq_of_compactParabolicDifferenceEnergy
    {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    {S T : ℝ≥0} (hT : S = T) (L : X →L[ℝ] X)
    (u : DuhamelPath S X) (v : DuhamelPath T X)
    (D : CompactParabolicDuhamelDifferenceEnergyData (M := M) T
      (castDuhamelPath hT (mapDuhamelPath S L u)) v) :
    castDuhamelPath hT (mapDuhamelPath S L u) = v :=
  duhamelPaths_eq_of_compactParabolicDifferenceEnergy T _ _ D

/-- The compact tensor-energy route discharges the exact uniform-slope
interface consumed by the chartwise covariance layer. -/
theorem hasTransportedParabolicDuhamelDifferenceSlopeBound_of_compactEnergy
    {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    {S T : ℝ≥0} (hT : S = T) (C : ℝ) (L : X →L[ℝ] X)
    (u : DuhamelPath S X) (v : DuhamelPath T X)
    (D : CompactParabolicDuhamelDifferenceEnergyData (M := M) T
      (castDuhamelPath hT (mapDuhamelPath S L u)) v) :
    HasTransportedParabolicDuhamelDifferenceSlopeBound hT C L u v := by
  exact hasParabolicDuhamelDifferenceSlopeBound_of_eq T C _ _
    (cast_mapDuhamelPath_eq_of_compactParabolicDifferenceEnergy hT L u v D)

end TransportedParabolicDifference

section AffineUniformSolutionParabolicUniqueness

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- A canonical affine solution transported to a prescribed equal compact
time interval. -/
abbrev castMapAffineUniformSolution
    {iota kappa : Type*}
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (L : BUC →L[ℝ] BUC) (T : ℝ≥0) (hT : D.uniformLifespan K = T) :
    DuhamelPath T BUC :=
  castDuhamelPath hT
    (mapDuhamelPath (D.uniformLifespan K) L (D.uniformSolution K u₀))

/-- Canonical positive-time Banach rate of an affine uniform solution. -/
def affineUniformSolutionInteriorRate
    {iota kappa : Type*}
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : ℝ) : BUC :=
  semilinearHeatBUCInteriorGeneratorValue
      (E := E) (F := F) (D.uniformLifespan K) (u₀ : BUC)
      D.nonlinearity (D.uniformSolution K u₀) t +
    semilinearHeatBUCProjectedForcing (D.uniformLifespan K)
      D.nonlinearity (D.uniformSolution K u₀) t

/-- Interior rate of a transported source affine solution minus the target
affine solution. -/
abbrev affineUniformSolutionsInteriorRateDifference
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC) (t : ℝ) : BUC :=
  L (affineUniformSolutionInteriorRate D₁ K₁ u₀₁ t) -
    affineUniformSolutionInteriorRate D₂ K₂ u₀₂ t

/-- Automatic classicality at every strict interior time, with no caller
chosen auxiliary window. -/
theorem affineUniformSolution_hasDerivAt_interior_automatic
    {iota kappa : Type*}
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (D.uniformLifespan K : ℝ)) :
    HasDerivAt
      (fun r ↦ D.uniformSolution K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property r))
      (affineUniformSolutionInteriorRate D K u₀ t) t := by
  have ht0 : 0 < t := ht.1
  have htT : t < (D.uniformLifespan K : ℝ) := ht.2
  have hwindow :=
    AffineRecenteredDeTurckShapedBUCRemainderData.uniformSolution_hasDerivAt_interior
      D K u₀ (c := t / 4) (a := t / 2)
      (b := (D.uniformLifespan K : ℝ)) (α := (1 / 2 : ℝ))
      (by linarith) (by linarith) (by linarith) le_rfl
      (by norm_num) (by norm_num)
  simpa only [affineUniformSolutionInteriorRate] using
    hwindow t ⟨by linarith, htT⟩

/-- The transported difference of two canonical affine solutions has its
Banach-valued classical rate automatically on the strict common interior. -/
theorem extended_cast_map_affineUniformSolutions_hasDerivAt_interior_automatic
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)) :
    HasDerivAt
      (extendedDuhamelPathDifference (D₂.uniformLifespan K₂)
        (castDuhamelPath hT
          (mapDuhamelPath (D₁.uniformLifespan K₁) L
            (D₁.uniformSolution K₁ u₀₁)))
        (D₂.uniformSolution K₂ u₀₂))
      (L (affineUniformSolutionInteriorRate D₁ K₁ u₀₁ t) -
        affineUniformSolutionInteriorRate D₂ K₂ u₀₂ t) t := by
  apply extended_cast_mapDuhamelPathDifference_hasDerivAt_of_pathRates
    hT L (D₁.uniformSolution K₁ u₀₁)
      (D₂.uniformSolution K₂ u₀₂)
  · apply affineUniformSolution_hasDerivAt_interior_automatic
    exact ⟨ht.1, by simpa only [hT] using ht.2⟩
  · exact affineUniformSolution_hasDerivAt_interior_automatic
      D₂ K₂ u₀₂ ht

/-- Alias-stable form of the automatic transported affine difference rate. -/
theorem extended_castMapAffineUniformSolutions_hasDerivAt_interior_automatic
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)) :
    HasDerivAt
      (extendedDuhamelPathDifference (D₂.uniformLifespan K₂)
        (castMapAffineUniformSolution D₁ K₁ u₀₁ L
          (D₂.uniformLifespan K₂) hT)
        (D₂.uniformSolution K₂ u₀₂))
      (affineUniformSolutionsInteriorRateDifference
        D₁ D₂ K₁ K₂ u₀₁ u₀₂ L t) t := by
  simpa only [castMapAffineUniformSolution,
    affineUniformSolutionsInteriorRateDifference] using
    (extended_cast_map_affineUniformSolutions_hasDerivAt_interior_automatic
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ L hT ht)

/-- Transporting the affine initial coefficient identifies the zero-time
values of the two canonical compact-time solution paths. -/
theorem cast_map_affineUniformSolutions_zero_eq
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC) = (u₀₂ : BUC)) :
    castDuhamelPath hT
        (mapDuhamelPath (D₁.uniformLifespan K₁) L
          (D₁.uniformSolution K₁ u₀₁))
        (⟨0, ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩⟩ :
          Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)) =
      D₂.uniformSolution K₂ u₀₂
        (⟨0, ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩⟩ :
          Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)) := by
  let t₁ : Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ) :=
    Set.projIcc 0 (D₁.uniformLifespan K₁ : ℝ)
      (D₁.uniformLifespan K₁).property 0
  have htzero : castDuhamelTime hT t₁ =
      Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
        (D₂.uniformLifespan K₂).property 0 := by
    exact castDuhamelTime_projIcc hT 0
  have hsourceZero : D₁.uniformSolution K₁ u₀₁ t₁ =
      (u₀₁ : BUC) := by
    rw [show t₁ =
        (⟨0, ⟨le_rfl, (D₁.uniformLifespan K₁).property⟩⟩ :
          Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ)) by
      exact Set.projIcc_of_mem (D₁.uniformLifespan K₁).property
        ⟨le_rfl, (D₁.uniformLifespan K₁).property⟩]
    exact D₁.uniformSolution_zero K₁ u₀₁
  rw [D₂.uniformSolution_zero]
  rw [show
      (⟨0, ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩⟩ :
        Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)) =
        Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
          (D₂.uniformLifespan K₂).property 0 by
    exact (Set.projIcc_of_mem (D₂.uniformLifespan K₂).property
      ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩).symm]
  rw [← htzero, castDuhamelPath_apply_castDuhamelTime,
    mapDuhamelPath_apply, hsourceZero, hinit]

universe v

set_option maxHeartbeats 800000 in
/--
Automatic compact tensor-energy package for two transported affine uniform
solutions.  Interior time differentiability is discharged by the affine
solver.  After initial equality, joint continuity, and pointwise
detection, the remaining analytic hypotheses are exactly an explicit
principal/lower-order decomposition, the principal Bochner inequality, and a
uniform bound for the lower-order coefficient.

This theorem deliberately accepts joint continuity of the evaluated
spacetime difference instead of operator-norm continuity of `evaluation`;
ordinary point-evaluation families on `BUC` generally satisfy only the former.
-/
def compactParabolicDuhamelDifferenceEnergyData_of_affineUniformSolutions_principal_lowerOrder
    {M : Type v} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (transport : BUC →L[ℝ] BUC)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (hzero :
      castMapAffineUniformSolution D₁ K₁ u₀₁ transport
          (D₂.uniformLifespan K₂) hT
          (⟨0, ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩⟩ :
            Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)) =
        D₂.uniformSolution K₂ u₀₂
          (⟨0, ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩⟩ :
            Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)))
    (evaluation : M → BUC →L[ℝ] V)
    (hpointwiseContinuous : Continuous
      (Function.uncurry (pointwiseDuhamelDifferenceTensor
        (D₂.uniformLifespan K₂) evaluation
        (castMapAffineUniformSolution D₁ K₁ u₀₁ transport
          (D₂.uniformLifespan K₂) hT)
        (D₂.uniformSolution K₂ u₀₂))))
    (hseparates : ∀ f : BUC, (∀ x : M, evaluation x f = 0) → f = 0)
    (laplacian : CompactParabolicScalarLaplacianData (M := M)
      (D₂.uniformLifespan K₂))
    (principal lower : ℝ → M → V) (lowerBound : ℝ → M → ℝ)
    (B : ℝ)
    (hlowerBound : ∀ t ∈ Set.Ioo (0 : ℝ)
        (D₂.uniformLifespan K₂ : ℝ), ∀ x : M,
      lowerBound t x ≤ B)
    (hrate : ∀ t ∈ Set.Ioo (0 : ℝ)
        (D₂.uniformLifespan K₂ : ℝ), ∀ x : M,
      evaluation x
          (affineUniformSolutionsInteriorRateDifference
            D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport t) =
        principal t x + lower t x)
    (hprincipalEnergy : ∀ t ∈ Set.Ioo (0 : ℝ)
        (D₂.uniformLifespan K₂ : ℝ), ∀ x : M,
      2 * ⟪pointwiseDuhamelDifferenceTensor
            (D₂.uniformLifespan K₂) evaluation
            (castMapAffineUniformSolution D₁ K₁ u₀₁ transport
              (D₂.uniformLifespan K₂) hT)
            (D₂.uniformSolution K₂ u₀₂) t x,
          principal t x⟫_ℝ ≤
        laplacian.lap t
          (fun y ↦
            ‖pointwiseDuhamelDifferenceTensor
              (D₂.uniformLifespan K₂) evaluation
              (castMapAffineUniformSolution D₁ K₁ u₀₁ transport
                (D₂.uniformLifespan K₂) hT)
              (D₂.uniformSolution K₂ u₀₂) t y‖ ^ 2) x)
    (hlowerNorm : ∀ t ∈ Set.Ioo (0 : ℝ)
        (D₂.uniformLifespan K₂ : ℝ), ∀ x : M,
      ‖lower t x‖ ≤ lowerBound t x *
        ‖pointwiseDuhamelDifferenceTensor
          (D₂.uniformLifespan K₂) evaluation
          (castMapAffineUniformSolution D₁ K₁ u₀₁ transport
            (D₂.uniformLifespan K₂) hT)
          (D₂.uniformSolution K₂ u₀₂) t x‖) :
    CompactParabolicDuhamelDifferenceEnergyData (M := M)
      (D₂.uniformLifespan K₂)
      (castMapAffineUniformSolution D₁ K₁ u₀₁ transport
        (D₂.uniformLifespan K₂) hT)
      (D₂.uniformSolution K₂ u₀₂) :=
  compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_principal_lowerOrder_jointContinuous
    (D₂.uniformLifespan K₂)
    (castMapAffineUniformSolution D₁ K₁ u₀₁ transport
      (D₂.uniformLifespan K₂) hT)
    (D₂.uniformSolution K₂ u₀₂)
    evaluation hpointwiseContinuous hseparates
    (affineUniformSolutionsInteriorRateDifference
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport)
    (by
      intro t ht
      exact
        extended_castMapAffineUniformSolutions_hasDerivAt_interior_automatic
          D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport hT ht)
    laplacian principal lower lowerBound B hlowerBound hrate
    hprincipalEnergy hlowerNorm hzero

/-- Orbit equivariance and a norm-nonexpanding coefficient transport put the
transported canonical source solution inside the target uniqueness ball. -/
theorem cast_map_affineUniformSolution_mem_target_orbit_ball
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC) (hL : ‖L‖ ≤ 1)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (horbit :
      mapDuhamelPath (D₁.uniformLifespan K₁) L
          (heatLinearBUCPath (D₁.uniformLifespan K₁) (u₀₁ : BUC)) =
        heatLinearBUCPath (D₁.uniformLifespan K₁) (u₀₂ : BUC)) :
    castDuhamelPath hT
        (mapDuhamelPath (D₁.uniformLifespan K₁) L
          (D₁.uniformSolution K₁ u₀₁)) ∈
      Metric.closedBall
        (heatLinearBUCPath (D₂.uniformLifespan K₂) (u₀₂ : BUC))
        (1 : ℝ) := by
  let S := D₁.uniformLifespan K₁
  let T := D₂.uniformLifespan K₂
  let source := D₁.uniformSolution K₁ u₀₁
  let transported := mapDuhamelPath S L source
  have hsourceBall : source ∈ Metric.closedBall
      (heatLinearBUCPath S (u₀₁ : BUC)) (1 : ℝ) := by
    exact semilinearHeatBUCUniformLocalSolution_mem_orbit_ball
      (E := E) (F := F) K₁ D₁.nonlinearity D₁.localData u₀₁
  have htransportedBall : transported ∈ Metric.closedBall
      (heatLinearBUCPath S (u₀₂ : BUC)) (1 : ℝ) := by
    rw [Metric.mem_closedBall, ← horbit]
    exact (dist_mapDuhamelPath_le_of_norm_le_one S L hL source
      (heatLinearBUCPath S (u₀₁ : BUC))).trans
        (by simpa [Metric.mem_closedBall] using hsourceBall)
  have hcastCenter : castDuhamelPath hT
      (heatLinearBUCPath S (u₀₂ : BUC)) =
        heatLinearBUCPath T (u₀₂ : BUC) :=
    castDuhamelPath_heatLinearBUCPath hT (u₀₂ : BUC)
  rw [← hcastCenter]
  exact (castDuhamelPath_mem_closedBall_iff hT transported
    (heatLinearBUCPath S (u₀₂ : BUC)) 1).2 htransportedBall

/--
The precise parabolic-uniqueness replacement for Picard equivariance.  To
identify two canonical affine solutions it suffices to transport the initial
datum and prove the upper-right-slope estimate for the uniform difference of
the two resulting solution paths.
-/
theorem affineUniformSolutions_cast_map_eq_of_parabolicDifferenceSlopeBound
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC) = (u₀₂ : BUC))
    (C : ℝ)
    (hslope : HasTransportedParabolicDuhamelDifferenceSlopeBound
      hT C L (D₁.uniformSolution K₁ u₀₁)
        (D₂.uniformSolution K₂ u₀₂)) :
    castDuhamelPath hT
        (mapDuhamelPath (D₁.uniformLifespan K₁) L
          (D₁.uniformSolution K₁ u₀₁)) =
      D₂.uniformSolution K₂ u₀₂ := by
  apply cast_mapDuhamelPath_eq_of_parabolicDifferenceSlopeBound
    hT C L (D₁.uniformSolution K₁ u₀₁)
      (D₂.uniformSolution K₂ u₀₂)
  · let t₁ : Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ) :=
      Set.projIcc 0 (D₁.uniformLifespan K₁ : ℝ)
        (D₁.uniformLifespan K₁).property 0
    have htzero : castDuhamelTime hT t₁ =
        Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
          (D₂.uniformLifespan K₂).property 0 := by
      exact castDuhamelTime_projIcc hT 0
    have hsourceZero : D₁.uniformSolution K₁ u₀₁ t₁ =
        (u₀₁ : BUC) := by
      rw [show t₁ =
          (⟨0, ⟨le_rfl, (D₁.uniformLifespan K₁).property⟩⟩ :
            Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ)) by
        exact Set.projIcc_of_mem (D₁.uniformLifespan K₁).property
          ⟨le_rfl, (D₁.uniformLifespan K₁).property⟩]
      exact D₁.uniformSolution_zero K₁ u₀₁
    rw [D₂.uniformSolution_zero]
    rw [show
        (⟨0, ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩⟩ :
          Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ)) =
          Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
            (D₂.uniformLifespan K₂).property 0 by
      exact (Set.projIcc_of_mem (D₂.uniformLifespan K₂).property
        ⟨le_rfl, (D₂.uniformLifespan K₂).property⟩).symm]
    rw [← htzero, castDuhamelPath_apply_castDuhamelTime,
      mapDuhamelPath_apply, hsourceZero, hinit]
  · exact hslope

end AffineUniformSolutionParabolicUniqueness

section CoordinateMetricParabolicUniqueness

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Scalar covariance of the projected uniform-solution summands follows
from the parabolic difference estimate, with no Picard-equivariance premise. -/
theorem coordinateMetricValue_projectedUniformSolutions_eq_of_parabolicDifferenceSlopeBound
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (L : BUC₂ →L[ℝ] BUC₂)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC₂) = (u₀₂ : BUC₂))
    (C : ℝ)
    (hslope : HasTransportedParabolicDuhamelDifferenceSlopeBound
      hT C L (D₁.uniformSolution K₁ u₀₁)
        (D₂.uniformSolution K₂ u₀₂))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (L f) x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : ℝ,
      coordinateMetricValue
          (D₂.uniformSolution K₂ u₀₂
            (Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
              (D₂.uniformLifespan K₂).property t))
          x₂ v₂ w₂ =
        coordinateMetricValue
          (D₁.uniformSolution K₁ u₀₁
            (Set.projIcc 0 (D₁.uniformLifespan K₁ : ℝ)
              (D₁.uniformLifespan K₁).property t))
          x₁ v₁ w₁ := by
  have hpath :=
    affineUniformSolutions_cast_map_eq_of_parabolicDifferenceSlopeBound
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ L hT hinit C hslope
  intro t
  let t₁ : Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ) :=
    Set.projIcc 0 (D₁.uniformLifespan K₁ : ℝ)
      (D₁.uniformLifespan K₁).property t
  have ht := congrArg (fun u ↦ u (castDuhamelTime hT t₁)) hpath
  simp only [castDuhamelPath_apply_castDuhamelTime, mapDuhamelPath_apply] at ht
  have htcast : castDuhamelTime hT t₁ =
      Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
        (D₂.uniformLifespan K₂).property t := by
    exact castDuhamelTime_projIcc hT t
  rw [← htcast, ← ht]
  exact heval (D₁.uniformSolution K₁ u₀₁ t₁)

end CoordinateMetricParabolicUniqueness

section ReconstructedCoordinateSolutionParabolicUniqueness

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Manifold-chart specialization: the exact parabolic difference estimate
discharges the reconstructed fixed-point-summand covariance premise. -/
theorem reconstructedCoordinateSolutionPath_value_eq_of_parabolicDifferenceSlopeBound
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (L : BUC₂ →L[ℝ] BUC₂)
    (hT :
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        D₁).uniformLifespan K₁ =
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        D₂).uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC₂) = (u₀₂ : BUC₂))
    (C : ℝ)
    (hslope : HasTransportedParabolicDuhamelDifferenceSlopeBound
      hT C L
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
          D₁).uniformSolution K₁ u₀₁)
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
          D₂).uniformSolution K₂ u₀₂))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (L f) x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : ℝ,
      coordinateMetricValue
          (reconstructedCoordinateSolutionPath D₂ K₂ u₀₂ t)
          x₂ v₂ w₂ =
        coordinateMetricValue
          (reconstructedCoordinateSolutionPath D₁ K₁ u₀₁ t)
          x₁ v₁ w₁ := by
  simpa only [reconstructedCoordinateSolutionPath] using
    (coordinateMetricValue_projectedUniformSolutions_eq_of_parabolicDifferenceSlopeBound
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁)
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂)
      K₁ K₂ u₀₁ u₀₂ L hT hinit C hslope
      x₁ x₂ v₁ w₁ v₂ w₂ heval)

end ReconstructedCoordinateSolutionParabolicUniqueness

section ChartwiseOverlapParabolicUniqueness

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

/--
Chart-indexed package of the one genuinely new parabolic comparison input.
All fields except `difference_slope` are algebraic compatibility data.  The
last field is exactly the maximum-principle estimate not supplied by the
current classical-core/interior-regularity API.
-/
structure ChartwiseBUCOverlapParabolicUniquenessData
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K) where
  transport : M → M → BUC₂ →L[ℝ] BUC₂
  uniformLifespan_eq : ∀ anchor₁ anchor₂,
    (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₁)).uniformLifespan K =
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₂)).uniformLifespan K
  initial_eq : ∀ anchor₁ anchor₂,
    transport anchor₁ anchor₂ (u₀ anchor₁ : BUC₂) =
      (u₀ anchor₂ : BUC₂)
  slopeConstant : M → M → ℝ
  difference_slope : ∀ anchor₁ anchor₂,
    HasTransportedParabolicDuhamelDifferenceSlopeBound
      (uniformLifespan_eq anchor₁ anchor₂)
      (slopeConstant anchor₁ anchor₂)
      (transport anchor₁ anchor₂)
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₁)).uniformSolution K (u₀ anchor₁))
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₂)).uniformSolution K (u₀ anchor₂))

/-- Common shorthand for the shifted affine lifespan in one chart. -/
def chartwiseShiftedBUCUniformLifespan
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0) (anchor : M) : ℝ≥0 :=
  (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
    (D anchor)).uniformLifespan K

/-- Common shorthand for the shifted affine canonical path in one chart. -/
noncomputable def chartwiseShiftedBUCUniformSolution
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K)
    (anchor : M) :
    DuhamelPath (chartwiseShiftedBUCUniformLifespan D K anchor) BUC₂ :=
  (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
    (D anchor)).uniformSolution K (u₀ anchor)

/-- A source chart's canonical path transported to the target chart lifespan. -/
noncomputable def chartwiseTransportedShiftedBUCUniformSolution
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K)
    (transport : M → M → BUC₂ →L[ℝ] BUC₂)
    (anchor₁ anchor₂ : M)
    (hT : chartwiseShiftedBUCUniformLifespan D K anchor₁ =
      chartwiseShiftedBUCUniformLifespan D K anchor₂) :
    DuhamelPath (chartwiseShiftedBUCUniformLifespan D K anchor₂) BUC₂ :=
  castDuhamelPath hT
    (mapDuhamelPath (chartwiseShiftedBUCUniformLifespan D K anchor₁)
      (transport anchor₁ anchor₂)
      (chartwiseShiftedBUCUniformSolution D K u₀ anchor₁))

/--
Chart-indexed compact tensor-energy replacement for the abstract slope field.
The energy certificate is strictly stronger: the slab maximum principle first
identifies each transported pair of paths, and that equality then supplies the
uniform liminf slope bound used by the existing covariance pipeline.
-/
structure ChartwiseBUCOverlapParabolicEnergyData
    [CompactSpace M] [Nonempty M]
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K) where
  transport : M → M → BUC₂ →L[ℝ] BUC₂
  uniformLifespan_eq : ∀ anchor₁ anchor₂,
    chartwiseShiftedBUCUniformLifespan D K anchor₁ =
      chartwiseShiftedBUCUniformLifespan D K anchor₂
  initial_eq : ∀ anchor₁ anchor₂,
    transport anchor₁ anchor₂ (u₀ anchor₁ : BUC₂) =
      (u₀ anchor₂ : BUC₂)
  difference_energy : ∀ anchor₁ anchor₂,
    HasTransportedCompactParabolicDuhamelDifferenceEnergy (M := M)
      (uniformLifespan_eq anchor₁ anchor₂)
      (transport anchor₁ anchor₂)
      (chartwiseShiftedBUCUniformSolution D K u₀ anchor₁)
      (chartwiseShiftedBUCUniformSolution D K u₀ anchor₂)

/-- Forget a compact tensor-energy certificate to the exact slope package
consumed by chartwise inverse-gauge covariance. -/
def ChartwiseBUCOverlapParabolicEnergyData.toSlopeData
    [CompactSpace M] [Nonempty M]
    {iota kappa : Type*}
    {D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa}
    {K : ℝ≥0}
    {u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K}
    (H : ChartwiseBUCOverlapParabolicEnergyData D K u₀) :
    ChartwiseBUCOverlapParabolicUniquenessData D K u₀ where
  transport := H.transport
  uniformLifespan_eq := H.uniformLifespan_eq
  initial_eq := H.initial_eq
  slopeConstant := fun _ _ ↦ 0
  difference_slope := by
    intro anchor₁ anchor₂
    let energyData := Classical.choice (H.difference_energy anchor₁ anchor₂)
    exact
      hasTransportedParabolicDuhamelDifferenceSlopeBound_of_compactEnergy
        (H.uniformLifespan_eq anchor₁ anchor₂) 0
        (H.transport anchor₁ anchor₂)
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
          (D anchor₁)).uniformSolution K (u₀ anchor₁))
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
          (D anchor₂)).uniformSolution K (u₀ anchor₂))
        energyData

/--
The global reconstructed inverse-gauge spacetime coefficient is chart
covariant once the exact overlap maximum-principle estimate is available.
Thus coordinate-RHS covariance and endpoint ODE covariance reduce the
remaining chart-independence boundary to `difference_slope`; covariance of a
selected solution is not assumed.
-/
theorem chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_background_and_parabolicDifferenceSlope
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (H : ChartwiseBUCOverlapParabolicUniquenessData D K u₀)
    (hPhi : ∀ t anchor z,
      HasFDerivAt (Phi anchor t) (DPhi anchor t z) z)
    (hendpointTarget : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      Phi anchor₁ t z ∈ (extChartAt I anchor₁).target)
    (hendpointSource : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      (extChartAt I anchor₁).symm (Phi anchor₁ t z) ∈
        (extChartAt I anchor₂).source)
    (hcompat : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      (Phi anchor₂ t ∘
          GeodesicTransport.chartTransition anchor₁ anchor₂) =ᶠ[nhds z]
        (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘
          Phi anchor₁ t))
    (hbackground : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ a b : E,
        coordinateMetricValue (D anchor₂).background
            (GeodesicTransport.chartTransition anchor₁ anchor₂
              (Phi anchor₁ t z))
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) b) =
          coordinateMetricValue (D anchor₁).background
            (Phi anchor₁ t z) a b)
    (htransportEvaluation : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ a b : E, ∀ f : BUC₂,
        coordinateMetricValue (H.transport anchor₁ anchor₂ f)
            (GeodesicTransport.chartTransition anchor₁ anchor₂
              (Phi anchor₁ t z))
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) b) =
          coordinateMetricValue f (Phi anchor₁ t z) a b) :
    ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ a b : E,
        chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z b) =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₁ z a b := by
  apply chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_and_backgroundSolution
    D K u₀ Phi DPhi hPhi hendpointTarget hendpointSource hcompat hbackground
  intro t anchor₁ anchor₂ z hz hy a b
  exact reconstructedCoordinateSolutionPath_value_eq_of_parabolicDifferenceSlopeBound
    (D anchor₁) (D anchor₂) K K (u₀ anchor₁) (u₀ anchor₂)
    (H.transport anchor₁ anchor₂)
    (H.uniformLifespan_eq anchor₁ anchor₂)
    (H.initial_eq anchor₁ anchor₂)
    (H.slopeConstant anchor₁ anchor₂)
    (H.difference_slope anchor₁ anchor₂)
    (Phi anchor₁ t z)
    (GeodesicTransport.chartTransition anchor₁ anchor₂
      (Phi anchor₁ t z))
    a b
    (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
      (Phi anchor₁ t z) a)
    (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
      (Phi anchor₁ t z) b)
    (htransportEvaluation t anchor₁ anchor₂ z hz hy a b) t

end ChartwiseOverlapParabolicUniqueness

end Poincare
