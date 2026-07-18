import Poincare.Global.DeTurckBUCOverlapParabolicUniqueness
import Poincare.Global.DeTurckBUCInteriorCoefficientIdentification
import Poincare.Global.DeTurckBUCJointSpacetimeMetricAssembly

/-!
# Quasilinear difference energy for reconstructed DeTurck metrics

This file crosses the first concrete part of the parabolic uniqueness
boundary.  It defines the intrinsic difference of two closed metric families,
identifies its chart entries with differences of reconstructed joint entries,
and subtracts the proved one-solution Ricci--DeTurck coefficient split.  The
result is the exact pointwise decomposition

`difference rate = flat Laplace principal difference + lower-order difference`.

The final sections prove the scalar Bochner inequality for every contraction
of the intrinsic difference tensor and extract uniform bounds for continuous
lower-order coefficients on compact spacetime tracks.
-/

noncomputable section

open Bornology Bundle FiberBundle Filter Set Function
open scoped Manifold ContDiff NNReal Topology Interval InnerProductSpace
  BoundedContinuousFunction

namespace Poincare

section IntrinsicDifferenceTensor

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual intrinsic covariant two-tensor difference of two closed metrics. -/
def closedMetricDifferenceTensorAt
    (g₁ g₂ : ClosedSmoothRiemannianMetric n M) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  g₁.inner x - g₂.inner x

@[simp] theorem closedMetricDifferenceTensorAt_apply
    (g₁ g₂ : ClosedSmoothRiemannianMetric n M) (x : M)
    (v w : TM x) :
    closedMetricDifferenceTensorAt g₁ g₂ x v w =
      g₁.inner x v w - g₂.inner x v w :=
  rfl

/-- A preferred-chart scalar entry of the intrinsic difference tensor. -/
def closedMetricDifferenceChartValue
    (g₁ g₂ : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (z v w : E) : ℝ :=
  CovariantDerivative.chartMetric g₁.inner anchor z v w -
    CovariantDerivative.chartMetric g₂.inner anchor z v w

/-- Realization of two joint chart coefficient families identifies the actual
intrinsic difference entry with their pointwise difference. -/
theorem closedMetricDifferenceChartValue_eq_of_jointEntry_realization
    (g₁ g₂ : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (z v w : E) (G₁ G₂ : E → E →L[ℝ] E →L[ℝ] ℝ)
    (h₁ : CovariantDerivative.chartMetric g₁.inner anchor z = G₁ z)
    (h₂ : CovariantDerivative.chartMetric g₂.inner anchor z = G₂ z) :
    closedMetricDifferenceChartValue g₁ g₂ anchor z v w =
      G₁ z v w - G₂ z v w := by
  simp only [closedMetricDifferenceChartValue, h₁, h₂]

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Specialization to the assembled inverse-gauge spacetime entries.  Thus the
difference used by the energy method is the chart representation of an actual
intrinsic tensor, rather than a formal difference of unrelated coefficients. -/
theorem closedMetricDifferenceChartValue_eq_chartwiseReconstructedEntries
    (D₁ : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) iota₁ kappa₁)
    (D₂ : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₂)
    (Phi₁ Phi₂ : M → ℝ → E → E)
    (DPhi₁ DPhi₂ : M → ℝ → E → E →L[ℝ] E)
    (r₁ r₂ : ℝ → ClosedSmoothRiemannianMetric n M)
    (hrealize₁ : ∀ t anchor z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (r₁ t).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D₁ K₁ u₀₁ Phi₁ DPhi₁ t anchor z)
    (hrealize₂ : ∀ t anchor z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (r₂ t).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D₂ K₂ u₀₂ Phi₂ DPhi₂ t anchor z)
    (t : ℝ) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) (v w : E) :
    closedMetricDifferenceChartValue (r₁ t) (r₂ t) anchor z v w =
      chartwiseReconstructedInverseGaugeMetricSpacetime
          D₁ K₁ u₀₁ Phi₁ DPhi₁ t anchor z v w -
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D₂ K₂ u₀₂ Phi₂ DPhi₂ t anchor z v w := by
  exact closedMetricDifferenceChartValue_eq_of_jointEntry_realization
    (r₁ t) (r₂ t) anchor z v w
    (chartwiseReconstructedInverseGaugeMetricSpacetime
      D₁ K₁ u₀₁ Phi₁ DPhi₁ t anchor)
    (chartwiseReconstructedInverseGaugeMetricSpacetime
      D₂ K₂ u₀₂ Phi₂ DPhi₂ t anchor)
    (hrealize₁ t anchor z hz) (hrealize₂ t anchor z hz)

/-- The time-dependent intrinsic metric difference. -/
def closedMetricFamilyDifferenceTensorAt
    (g₁ g₂ : ℝ → ClosedSmoothRiemannianMetric n M)
    (t : ℝ) (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  closedMetricDifferenceTensorAt (g₁ t) (g₂ t) x

end IntrinsicDifferenceTensor

section QuasilinearRateSplit

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The flat principal coefficient of one reconstructed perturbation: the
coordinate Laplacian of the full metric minus that of its fixed background. -/
def deTurckChartFlatPrincipalValue
    (full background : CoordinateBUCTensor E) (z v w : E) : ℝ :=
  coordinateMetricLaplacianValue full z v w -
    coordinateMetricLaplacianValue background z v w

/-- The principal part in the difference of two reconstructed coefficients. -/
def deTurckChartFlatPrincipalDifferenceValue
    (full₁ background₁ full₂ background₂ : CoordinateBUCTensor E)
    (z v w : E) : ℝ :=
  deTurckChartFlatPrincipalValue full₁ background₁ z v w -
    deTurckChartFlatPrincipalValue full₂ background₂ z v w

/-- The remaining coefficient in the difference of two Ricci--DeTurck
equations after removing the two flat heat principal parts. -/
def deTurckChartLowerOrderDifferenceValue
    (gt₁ gt₂ : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg₁ bg₂ : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t : ℝ) (z : E) (hz : z ∈ (extChartAt I anchor).target)
    (full₁ background₁ full₂ background₂ : CoordinateBUCTensor E)
    (v w : E) : ℝ :=
  deTurckChartPrincipalRemovedCoefficientValue gt₁ bg₁ anchor t z hz
      full₁ background₁ v w -
    deTurckChartPrincipalRemovedCoefficientValue gt₂ bg₂ anchor t z hz
      full₂ background₂ v w

/-- Subtracting the two proved one-solution coefficient identities gives the
exact common-chart quasilinear rate decomposition. -/
theorem deTurckChartMetricEvolution_difference_eq_flatPrincipal_add_lowerOrder
    (gt₁ gt₂ : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg₁ bg₂ : ClosedSmoothRiemannianMetric n M) (anchor y : M) (t : ℝ)
    (hy : y ∈ (extChartAt I anchor).source)
    (hcutoff : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfield₁ : DeTurckVectorFieldRegularAt gt₁ bg₁ t)
    (hfield₂ : DeTurckVectorFieldRegularAt gt₂ bg₂ t)
    (full₁ background₁ full₂ background₂ : CoordinateBUCTensor E)
    (v w : E) :
    deTurckChartMetricEvolutionBilin gt₁ bg₁ anchor t
          (extChartAt I anchor y) v w -
        deTurckChartMetricEvolutionBilin gt₂ bg₂ anchor t
          (extChartAt I anchor y) v w =
      deTurckChartFlatPrincipalDifferenceValue
          full₁ background₁ full₂ background₂
          (extChartAt I anchor y) v w +
        deTurckChartLowerOrderDifferenceValue gt₁ gt₂ bg₁ bg₂
          anchor t (extChartAt I anchor y)
          ((extChartAt I anchor).map_source hy)
          full₁ background₁ full₂ background₂ v w := by
  have h₁ :=
    deTurckChartMetricEvolution_sub_laplacian_eq_principalRemovedCoefficientValue
      gt₁ bg₁ anchor y t hy hcutoff hfield₁
      full₁ background₁ v w
  have h₂ :=
    deTurckChartMetricEvolution_sub_laplacian_eq_principalRemovedCoefficientValue
      gt₂ bg₂ anchor y t hy hcutoff hfield₂
      full₂ background₂ v w
  unfold deTurckChartFlatPrincipalDifferenceValue
    deTurckChartFlatPrincipalValue deTurckChartLowerOrderDifferenceValue
  linarith

/-- If the two intrinsic chart entries have their genuine Ricci--DeTurck
rates, then the scalar contraction of their actual metric-difference tensor
has exactly the principal/lower-order rate displayed above. -/
theorem closedMetricDifferenceChartValue_hasDerivAt_flatPrincipal_add_lowerOrder
    (gt₁ gt₂ : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg₁ bg₂ : ClosedSmoothRiemannianMetric n M) (anchor y : M) (t : ℝ)
    (hy : y ∈ (extChartAt I anchor).source)
    (hcutoff : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfield₁ : DeTurckVectorFieldRegularAt gt₁ bg₁ t)
    (hfield₂ : DeTurckVectorFieldRegularAt gt₂ bg₂ t)
    (full₁ background₁ full₂ background₂ : CoordinateBUCTensor E)
    (v w : E)
    (hrate₁ : HasDerivAt
      (fun s ↦ CovariantDerivative.chartMetric (gt₁ s).inner anchor
        (extChartAt I anchor y) v w)
      (deTurckChartMetricEvolutionBilin gt₁ bg₁ anchor t
        (extChartAt I anchor y) v w) t)
    (hrate₂ : HasDerivAt
      (fun s ↦ CovariantDerivative.chartMetric (gt₂ s).inner anchor
        (extChartAt I anchor y) v w)
      (deTurckChartMetricEvolutionBilin gt₂ bg₂ anchor t
        (extChartAt I anchor y) v w) t) :
    HasDerivAt
      (fun s ↦ closedMetricDifferenceChartValue
        (gt₁ s) (gt₂ s) anchor (extChartAt I anchor y) v w)
      (deTurckChartFlatPrincipalDifferenceValue
          full₁ background₁ full₂ background₂
          (extChartAt I anchor y) v w +
        deTurckChartLowerOrderDifferenceValue gt₁ gt₂ bg₁ bg₂
          anchor t (extChartAt I anchor y)
          ((extChartAt I anchor).map_source hy)
          full₁ background₁ full₂ background₂ v w) t := by
  have hrate := hrate₁.sub hrate₂
  rw [deTurckChartMetricEvolution_difference_eq_flatPrincipal_add_lowerOrder
    gt₁ gt₂ bg₁ bg₂ anchor y t hy hcutoff hfield₁ hfield₂
    full₁ background₁ full₂ background₂ v w] at hrate
  simpa only [closedMetricDifferenceChartValue] using hrate

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- The canonical positive-time reconstructed slopes satisfy the preceding
principal/lower-order difference decomposition without any additional rate
hypothesis.  Both rates are first identified with their genuine Ricci--DeTurck
right-hand sides by interior coefficient identification. -/
theorem reconstructedInteriorSlope_difference_eq_flatPrincipal_add_lowerOrder
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₂)
    {t : ℝ} (ht₀ : 0 < t)
    (htT₁ : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan
        K₁ : ℝ))
    (htT₂ : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan
        K₂ : ℝ))
    (gt₁ gt₂ : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg₁ bg₂ : ClosedSmoothRiemannianMetric n M) (anchor y : M)
    (hy : y ∈ (extChartAt I anchor).source)
    (hcutoff : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfield₁ : DeTurckVectorFieldRegularAt gt₁ bg₁ t)
    (hfield₂ : DeTurckVectorFieldRegularAt gt₂ bg₂ t)
    (hfullGerm₁ :
      (fun z ↦ coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformInteriorState
              K₁ u₀₁ t + D₁.background) z) =ᶠ[nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric (gt₁ t).inner anchor)
    (hfullGerm₂ :
      (fun z ↦ coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformInteriorState
              K₂ u₀₂ t + D₂.background) z) =ᶠ[nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric (gt₂ t).inner anchor)
    (hbackgroundGerm₁ :
      (fun z ↦ coordinateBilinearFormAt D₁.background z) =ᶠ[nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric bg₁.inner anchor)
    (hbackgroundGerm₂ :
      (fun z ↦ coordinateBilinearFormAt D₂.background z) =ᶠ[nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric bg₂.inner anchor)
    (hremainder₁ : ∀ v w : E,
      coordinateMetricValue
          (D₁.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformInteriorState
                K₁ u₀₁ t + D₁.background))
          (extChartAt I anchor y) v w =
        deTurckChartMetricEvolutionBilin gt₁ bg₁ anchor t
            (extChartAt I anchor y) v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformInteriorState
                K₁ u₀₁ t + D₁.background)
            (extChartAt I anchor y) v w +
          coordinateMetricLaplacianValue D₁.background
            (extChartAt I anchor y) v w)
    (hremainder₂ : ∀ v w : E,
      coordinateMetricValue
          (D₂.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformInteriorState
                K₂ u₀₂ t + D₂.background))
          (extChartAt I anchor y) v w =
        deTurckChartMetricEvolutionBilin gt₂ bg₂ anchor t
            (extChartAt I anchor y) v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformInteriorState
                K₂ u₀₂ t + D₂.background)
            (extChartAt I anchor y) v w +
          coordinateMetricLaplacianValue D₂.background
            (extChartAt I anchor y) v w)
    (v w : E) :
    let A₁ :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁
    let A₂ :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂
    coordinateMetricValue
        (A₁.uniformInteriorGeneratorValue K₁ u₀₁ t +
          D₁.base.nonlinearity
            (A₁.uniformInteriorState K₁ u₀₁ t + D₁.background))
        (extChartAt I anchor y) v w -
      coordinateMetricValue
        (A₂.uniformInteriorGeneratorValue K₂ u₀₂ t +
          D₂.base.nonlinearity
            (A₂.uniformInteriorState K₂ u₀₂ t + D₂.background))
        (extChartAt I anchor y) v w =
      deTurckChartFlatPrincipalDifferenceValue
        (A₁.uniformInteriorState K₁ u₀₁ t + D₁.background)
        D₁.background
        (A₂.uniformInteriorState K₂ u₀₂ t + D₂.background)
        D₂.background (extChartAt I anchor y) v w +
      deTurckChartLowerOrderDifferenceValue gt₁ gt₂ bg₁ bg₂
        anchor t (extChartAt I anchor y)
        ((extChartAt I anchor).map_source hy)
        (A₁.uniformInteriorState K₁ u₀₁ t + D₁.background)
        D₁.background
        (A₂.uniformInteriorState K₂ u₀₂ t + D₂.background)
        D₂.background v w := by
  dsimp only
  have hslope₁ :=
    coordinateBilinearFormAt_reconstructedInteriorSlope_eq_deTurckChartMetricEvolutionBilin_of_germs
      D₁ K₁ u₀₁ ht₀ htT₁ gt₁ bg₁ anchor
      ((extChartAt I anchor).map_source hy)
      hfullGerm₁ hbackgroundGerm₁ hremainder₁
  have hslope₂ :=
    coordinateBilinearFormAt_reconstructedInteriorSlope_eq_deTurckChartMetricEvolutionBilin_of_germs
      D₂ K₂ u₀₂ ht₀ htT₂ gt₂ bg₂ anchor
      ((extChartAt I anchor).map_source hy)
      hfullGerm₂ hbackgroundGerm₂ hremainder₂
  have hslope₁' := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B v w) hslope₁
  have hslope₂' := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B v w) hslope₂
  dsimp only at hslope₁' hslope₂'
  rw [coordinateBilinearFormAt_apply] at hslope₁' hslope₂'
  rw [hslope₁', hslope₂']
  exact deTurckChartMetricEvolution_difference_eq_flatPrincipal_add_lowerOrder
    gt₁ gt₂ bg₁ bg₂ anchor y t hy hcutoff hfield₁ hfield₂
    _ _ _ _ v w

end QuasilinearRateSplit

section PrincipalBochner

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Scalar Bochner control for a Laplace principal part.  The discarded term
is twice the nonnegative squared gradient norm. -/
theorem two_mul_value_mul_laplacianAt_le_laplacianAt_sq
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (f : M → ℝ)
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y) (x : M) :
    2 * f x * g.laplacianAt f x ≤
      g.laplacianAt (fun y ↦ f y ^ 2) x := by
  rw [g.laplacianAt_sq hf]
  have hgrad : 0 ≤
      g.inner x (g.gradientAt f x) (g.gradientAt f x) :=
    g.inner_nonneg x (g.gradientAt f x)
  linarith

/-- Bochner control specialized to any scalar contraction of the actual
intrinsic difference tensor against two tangent vector fields. -/
theorem closedMetricDifferenceTensor_contraction_principal_bochner
    (g g₁ g₂ : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (V W : ∀ x : M, TM x)
    (hC2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun x ↦ closedMetricDifferenceTensorAt g₁ g₂ x (V x) (W x)) y)
    (x : M) :
    2 * closedMetricDifferenceTensorAt g₁ g₂ x (V x) (W x) *
        g.laplacianAt
          (fun y ↦ closedMetricDifferenceTensorAt g₁ g₂ y (V y) (W y)) x ≤
      g.laplacianAt
        (fun y ↦
          (closedMetricDifferenceTensorAt g₁ g₂ y (V y) (W y)) ^ 2) x := by
  exact two_mul_value_mul_laplacianAt_le_laplacianAt_sq g _ hC2 x

end PrincipalBochner

section CompactTrackBounds

universe u v

variable {M : Type u} {V : Type v}
variable [TopologicalSpace M] [CompactSpace M]
variable [NormedAddCommGroup V]

/-- Joint continuity on a compact closed spacetime track gives one uniform
nonnegative norm bound. -/
theorem exists_nonnegative_uniform_norm_bound_on_compact_parabolic_track
    (T : ℝ) (f : ℝ → M → V)
    (hf : ContinuousOn (Function.uncurry f)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, ‖f t x‖ ≤ B := by
  let K : Set (ℝ × M) :=
    Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hnorm : ContinuousOn (fun p : ℝ × M ↦ ‖f p.1 p.2‖) K := by
    simpa only [Function.uncurry_apply_pair] using hf.norm
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x
  have hmem : ‖f t x‖ ∈ (fun p : ℝ × M ↦ ‖f p.1 p.2‖) '' K :=
    mem_image_of_mem _ (show (t, x) ∈ K from ⟨ht, Set.mem_univ x⟩)
  exact (hC hmem).trans (le_max_left _ _)

/-- Scalar absolute-value form used for lower-order coefficients. -/
theorem exists_nonnegative_uniform_abs_bound_on_compact_parabolic_track
    (T : ℝ) (c : ℝ → M → ℝ)
    (hc : ContinuousOn (Function.uncurry c)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, |c t x| ≤ B := by
  simpa only [Real.norm_eq_abs] using
    exists_nonnegative_uniform_norm_bound_on_compact_parabolic_track T c hc

/-- A continuous scalar coefficient multiplying the metric difference has the
uniform linear lower-order estimate required by the energy argument. -/
theorem exists_uniform_linear_lowerOrder_bound_on_compact_parabolic_track
    (T : ℝ) (c h : ℝ → M → ℝ)
    (hc : ContinuousOn (Function.uncurry c)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
        ‖c t x * h t x‖ ≤ B * ‖h t x‖ := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_nonnegative_uniform_abs_bound_on_compact_parabolic_track T c hc
  refine ⟨B, hB0, ?_⟩
  intro t ht x
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB t ht x) (norm_nonneg _)

end CompactTrackBounds

end Poincare
