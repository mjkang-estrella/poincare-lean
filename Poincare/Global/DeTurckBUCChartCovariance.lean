import Poincare.Global.DeTurckBUCMetricReconstruction
import Poincare.Global.DeTurckChartIndependentPullback

/-!
# Chart-covariant evaluation of reconstructed `BUC` metric coefficients

`DeTurckBUCMetricReconstruction` produces a Banach-valued path of positive
coordinate metric coefficients.  This file connects that output to the
coordinate tensors used by the geometric Ricci--DeTurck development.

The bridge has three concrete parts:

* the Riesz-operator coefficient at a point is promoted to an actual
  continuous bilinear form;
* pointwise metric evaluation commutes with the Banach-valued one-sided time
  derivative supplied by the fixed-point theorem;
* the concrete coordinate right-hand side `-2 Ric + L_W g` is proved to
  transform through the derivative of an honest preferred-chart transition.

Consequently, an explicit identification of the analytic right-hand side in
one chart gives the scalar initial evolution in every overlapping preferred
chart.  No chart-covariance predicate is assumed in that conclusion.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction Manifold ContDiff

namespace Poincare

section BUCEvaluation

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The continuous bilinear form represented by a Riesz-operator `BUC`
coefficient at one spatial point. -/
def coordinateBilinearFormAt (g : CoordinateBUCTensor E) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp (g.1 x)

@[simp]
theorem coordinateBilinearFormAt_apply
    (g : CoordinateBUCTensor E) (x v w : E) :
    coordinateBilinearFormAt g x v w = coordinateMetricValue g x v w := by
  rfl

/-- Evaluation of one `BUC` coefficient on fixed spatial and tangent data is
a linear functional. -/
def coordinateMetricEvaluationLinearMap (x v w : E) :
    CoordinateBUCTensor E →ₗ[ℝ] ℝ where
  toFun g := coordinateMetricValue g x v w
  map_add' g h := coordinateMetricValue_add g h x v w
  map_smul' c g := by
    change ⟪c • (g.1 x) v, w⟫_ℝ = c * coordinateMetricValue g x v w
    rw [real_inner_smul_left]
    rfl

/-- The pointwise metric-evaluation functional is continuous in the uniform
`BUC` norm. -/
def coordinateMetricEvaluationCLM (x v w : E) :
    CoordinateBUCTensor E →L[ℝ] ℝ :=
  LinearMap.mkContinuous (coordinateMetricEvaluationLinearMap x v w)
    (‖v‖ * ‖w‖) (fun g ↦ by
      change |coordinateMetricValue g x v w| ≤ (‖v‖ * ‖w‖) * ‖g‖
      calc
        |coordinateMetricValue g x v w| ≤ ‖g‖ * ‖v‖ * ‖w‖ :=
          abs_coordinateMetricValue_le (E := E) g x v w
        _ = (‖v‖ * ‖w‖) * ‖g‖ := by ring)

@[simp]
theorem coordinateMetricEvaluationCLM_apply
    (x v w : E) (g : CoordinateBUCTensor E) :
    coordinateMetricEvaluationCLM x v w g =
      coordinateMetricValue g x v w :=
  rfl

/-- A Banach-valued time derivative of `BUC` metric coefficients may be
evaluated at fixed spatial and tangent data. -/
theorem HasDerivWithinAt.coordinateMetricValue
    {g : ℝ → CoordinateBUCTensor E} {g' : CoordinateBUCTensor E}
    {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt g g' s t)
    (x v w : E) :
    HasDerivWithinAt
      (fun τ ↦ coordinateMetricValue (g τ) x v w)
      (coordinateMetricValue g' x v w) s t := by
  let L := coordinateMetricEvaluationCLM x v w
  have hcomp := L.hasFDerivAt.comp_hasDerivWithinAt t h
  simpa [L, Function.comp_def] using hcomp

variable {iota kappa : Type*}

/-- Scalar form of the exact initial evolution of a reconstructed coefficient
with the natural shifted-background forcing. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (x v w : E) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    HasDerivWithinAt
      (fun t : ℝ ↦ coordinateMetricValue
        (A.reconstructedMetricCoefficient K u₀
          (Set.projIcc 0 (A.uniformLifespan K : ℝ)
            (A.uniformLifespan K).property t)) x v w)
      (coordinateMetricValue
        (Au₀ + D.base.nonlinearity
          ((u₀ : CoordinateBUCTensor E) + D.background)) x v w)
      (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  exact HasDerivWithinAt.coordinateMetricValue
    (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground_reconstructedMetricCoefficient_hasDerivWithinAt_zero
      D K u₀ Au₀ hu₀) x v w

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Coordinate covariance of the reconstructed metric is inherited from the
background coefficient and the fixed-point perturbation separately.  This is
the algebraic assembly lemma used when two chartwise solvers have already
been related on an overlap; covariance of their sum is a theorem, not an
additional solver hypothesis. -/
theorem reconstructedMetricValue_eq_of_background_and_solution
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₂)
    (t₁ : Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ))
    (t₂ : Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (hbackground :
      coordinateMetricValue D₂.recentered.background x₂ v₂ w₂ =
        coordinateMetricValue D₁.recentered.background x₁ v₁ w₁)
    (hsolution :
      coordinateMetricValue (D₂.uniformSolution K₂ u₀₂ t₂) x₂ v₂ w₂ =
        coordinateMetricValue (D₁.uniformSolution K₁ u₀₁ t₁) x₁ v₁ w₁) :
    coordinateMetricValue
        (D₂.reconstructedMetricCoefficient K₂ u₀₂ t₂) x₂ v₂ w₂ =
      coordinateMetricValue
        (D₁.reconstructedMetricCoefficient K₁ u₀₁ t₁) x₁ v₁ w₁ := by
  simp only [AffineRecenteredDeTurckShapedBUCRemainderData.reconstructedMetricCoefficient,
    coordinateMetricValue_add]
  rw [hbackground, hsolution]

/-- Filter-local path form of reconstructed-metric overlap assembly.  If the
background and fixed-point scalar coefficients agree eventually along two
time parametrizations, then their reconstructed metric coefficients agree on
the same filter.  In particular this applies to `nhdsWithin 0 s`, which is the
germ consumed by forward coordinate-flow congruence theorems. -/
theorem reconstructedMetricValue_eventuallyEq_of_background_and_solution
    {l : Filter ℝ}
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₂)
    (t₁ : ℝ → Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ))
    (t₂ : ℝ → Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (hbackground :
      (fun _ : ℝ ↦ coordinateMetricValue
        D₂.recentered.background x₂ v₂ w₂) =ᶠ[l]
      (fun _ : ℝ ↦ coordinateMetricValue
        D₁.recentered.background x₁ v₁ w₁))
    (hsolution :
      (fun t : ℝ ↦ coordinateMetricValue
        (D₂.uniformSolution K₂ u₀₂ (t₂ t)) x₂ v₂ w₂) =ᶠ[l]
      (fun t : ℝ ↦ coordinateMetricValue
        (D₁.uniformSolution K₁ u₀₁ (t₁ t)) x₁ v₁ w₁)) :
    (fun t : ℝ ↦ coordinateMetricValue
      (D₂.reconstructedMetricCoefficient K₂ u₀₂ (t₂ t)) x₂ v₂ w₂) =ᶠ[l]
    (fun t : ℝ ↦ coordinateMetricValue
      (D₁.reconstructedMetricCoefficient K₁ u₀₁ (t₁ t)) x₁ v₁ w₁) := by
  filter_upwards [hbackground, hsolution] with t hbg hsol
  exact reconstructedMetricValue_eq_of_background_and_solution
    D₁ D₂ K₁ K₂ u₀₁ u₀₂ (t₁ t) (t₂ t)
      x₁ x₂ v₁ w₁ v₂ w₂ hbg hsol

/-- Time-dependent-point form of reconstructed-metric overlap assembly.  This
is the form needed after composing both coordinate metrics with inverse gauge
paths: the evaluation points and transported tangent vectors may all vary with
the real path parameter. -/
theorem reconstructedMetricValue_eventuallyEq_of_background_and_solution_timeDependent
    {l : Filter ℝ}
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₂)
    (t₁ : ℝ → Set.Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ))
    (t₂ : ℝ → Set.Icc (0 : ℝ) (D₂.uniformLifespan K₂ : ℝ))
    (x₁ x₂ v₁ w₁ v₂ w₂ : ℝ → E)
    (hbackground :
      (fun t : ℝ ↦ coordinateMetricValue
        D₂.recentered.background (x₂ t) (v₂ t) (w₂ t)) =ᶠ[l]
      (fun t : ℝ ↦ coordinateMetricValue
        D₁.recentered.background (x₁ t) (v₁ t) (w₁ t)))
    (hsolution :
      (fun t : ℝ ↦ coordinateMetricValue
        (D₂.uniformSolution K₂ u₀₂ (t₂ t)) (x₂ t) (v₂ t) (w₂ t)) =ᶠ[l]
      (fun t : ℝ ↦ coordinateMetricValue
        (D₁.uniformSolution K₁ u₀₁ (t₁ t)) (x₁ t) (v₁ t) (w₁ t))) :
    (fun t : ℝ ↦ coordinateMetricValue
      (D₂.reconstructedMetricCoefficient K₂ u₀₂ (t₂ t))
        (x₂ t) (v₂ t) (w₂ t)) =ᶠ[l]
    (fun t : ℝ ↦ coordinateMetricValue
      (D₁.reconstructedMetricCoefficient K₁ u₀₁ (t₁ t))
        (x₁ t) (v₁ t) (w₁ t)) := by
  filter_upwards [hbackground, hsolution] with t hbg hsol
  exact reconstructedMetricValue_eq_of_background_and_solution
    D₁ D₂ K₁ K₂ u₀₁ u₀₂ (t₁ t) (t₂ t)
      (x₁ t) (x₂ t) (v₁ t) (w₁ t) (v₂ t) (w₂ t) hbg hsol

end BUCEvaluation

section GeometricChartCovariance

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The full concrete Ricci--DeTurck coordinate right-hand side is a genuine
covariant two-tensor under an honest preferred-chart transition. -/
theorem deTurckChartMetricEvolutionBilin_chartTransitionDeriv
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (v w : E) :
    deTurckChartMetricEvolutionBilin gt bg anchor₂ t
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) =
      deTurckChartMetricEvolutionBilin gt bg anchor₁ t z v w := by
  have hRicci := deTurckChartRicciBilin_chartTransitionDeriv
    gt t anchor₁ anchor₂ hz hy v w
  have hLie := chartBilinearTensor_chartTransitionDeriv
    (B := fun y ↦
      lieDerivMetricBilinAt (gt t) (deTurckVectorField gt bg t) y)
    anchor₁ anchor₂ hz hy v w
  simp only [deTurckChartMetricEvolutionBilin,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [hRicci]
  change (-2 : ℝ) * deTurckChartRicciBilin gt anchor₁ t z v w +
      deTurckChartLieBilin gt bg anchor₂ t
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) = _
  rw [show deTurckChartLieBilin gt bg anchor₂ t
      (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
      (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
      (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) =
        deTurckChartLieBilin gt bg anchor₁ t z v w by
    simpa [deTurckChartLieBilin] using hLie]

variable {iota kappa : Type*}

/-- If the explicit analytic coefficient `A u₀ + N(u₀ + c)` is identified
with the concrete Ricci--DeTurck coordinate form at one point, the
reconstructed `BUC` coefficient has exactly that scalar initial derivative.

The premise is deliberately an equality of displayed coefficients, rather
than a packaged "solves Ricci--DeTurck" predicate.  This isolates the genuine
remaining PDE identification: the heat generator plus assembled
nonlinearity must be computed to be `-2 Ric + L_W g`. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_deTurckChartRHS
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (z v w : E)
    (hidentify :
      coordinateMetricValue
          (Au₀ + D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    HasDerivWithinAt
      (fun t : ℝ ↦ coordinateMetricValue
        (A.reconstructedMetricCoefficient K u₀
          (Set.projIcc 0 (A.uniformLifespan K : ℝ)
            (A.uniformLifespan K).property t)) z v w)
      (deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w)
      (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  rw [← hidentify]
  exact reconstructedMetricValue_hasDerivWithinAt_zero
    D K u₀ Au₀ hu₀ z v w

/-- The one-chart analytic identification automatically gives the same
initial scalar evolution rate in every overlapping preferred chart.  The
second-chart rate is obtained from the intrinsic tensoriality of
`-2 Ric + L_W g`; no second coordinate-RHS identification and no abstract
covariance premise are assumed. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (v w : E)
    (hidentify :
      coordinateMetricValue
          (Au₀ + D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor₁ 0 z v w) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    HasDerivWithinAt
      (fun t : ℝ ↦ coordinateMetricValue
        (A.reconstructedMetricCoefficient K u₀
          (Set.projIcc 0 (A.uniformLifespan K : ℝ)
            (A.uniformLifespan K).property t)) z v w)
      (deTurckChartMetricEvolutionBilin gt bg anchor₂ 0
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w))
      (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  rw [deTurckChartMetricEvolutionBilin_chartTransitionDeriv
    gt bg 0 anchor₁ anchor₂ hz hy v w]
  exact reconstructedMetricValue_hasDerivWithinAt_zero_eq_deTurckChartRHS
    D K u₀ Au₀ hu₀ gt bg anchor₁ z v w hidentify

/-- Bilinear-form version of the two-chart bridge.  A single explicit
operator identity in the first chart supplies the transported initial
evolution theorem simultaneously for every pair of coordinate vectors. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_bilinearForm_eq
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (hidentify :
      coordinateBilinearFormAt
          (Au₀ + D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) z =
        deTurckChartMetricEvolutionBilin gt bg anchor₁ 0 z) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∀ v w : E,
      HasDerivWithinAt
        (fun t : ℝ ↦ coordinateMetricValue
          (A.reconstructedMetricCoefficient K u₀
            (Set.projIcc 0 (A.uniformLifespan K : ℝ)
              (A.uniformLifespan K).property t)) z v w)
        (deTurckChartMetricEvolutionBilin gt bg anchor₂ 0
          (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w))
        (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  dsimp only
  intro v w
  apply reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS
    (D := D) (K := K) (u₀ := u₀) (Au₀ := Au₀) (hu₀ := hu₀)
    (gt := gt) (bg := bg)
    (anchor₁ := anchor₁) (anchor₂ := anchor₂) (z := z)
    (hz := hz) (hy := hy) (v := v) (w := w)
  have h := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B v w) hidentify
  simpa only [coordinateBilinearFormAt_apply] using h

end GeometricChartCovariance

end Poincare
