import Poincare.Global.DeTurckBUCChartCovariance
import Poincare.Global.DeTurckBUCGeneratorLocality
import Poincare.Global.DeTurckBUCMovingEvaluation
import Poincare.Global.MetricFlowJointCurvatureRegularity
import Poincare.Global.DeTurckCoordinateJointRegularity
import Poincare.Global.DeTurckCoordinateJointRegularityOverlap

/-!
# Inverse-gauge Ricci evolution for the reconstructed `BUC` metric

The fixed-point construction now produces a positive path of coordinate
metric coefficients and identifies its initial derivative at every fixed
coordinate point with the concrete Ricci--DeTurck right-hand side.  Passing
to Ricci flow requires evaluating that coefficient along the moving inverse
gauge and differentiating its two moving tangent slots.

This file proves the one-sided pullback calculus needed at the initial time,
constructs the actual inverse-function-theorem germ, and packages the
resulting local Ricci evolution.  The only additional analytic premise is
displayed explicitly: moving the spatial evaluation point along the inverse
gauge contributes the negative chart-advection term.  This is precisely the
spatial differentiability statement not available from `BUC` regularity
alone; the Ricci--DeTurck right-hand-side identification itself is consumed
from the reconstructed solver.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction Manifold ContDiff

namespace Poincare

section OneSidedPullbackCalculus

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Product and chain rule for a pulled bilinear form, relative to an
arbitrary one-sided or constrained time set. -/
theorem hasDerivWithinAt_pullbackBilinearApply
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    {s : Set ℝ} {t₀ : ℝ} {A' : E →L[ℝ] E →L[ℝ] ℝ}
    {D' : E →L[ℝ] E}
    (hA : HasDerivWithinAt A A' s t₀)
    (hD : HasDerivWithinAt D D' s t₀)
    (u v : E) :
    HasDerivWithinAt (pullbackBilinearApply A D u v)
      (A' (D t₀ u) (D t₀ v) +
        A t₀ (D' u) (D t₀ v) +
        A t₀ (D t₀ u) (D' v)) s t₀ := by
  have hDu : HasDerivWithinAt (fun t : ℝ ↦ D t u) (D' u) s t₀ := by
    simpa using hD.clm_apply
      (hasDerivWithinAt_const (x := t₀) (s := s) u)
  have hDv : HasDerivWithinAt (fun t : ℝ ↦ D t v) (D' v) s t₀ := by
    simpa using hD.clm_apply
      (hasDerivWithinAt_const (x := t₀) (s := s) v)
  have hAu : HasDerivWithinAt (fun t : ℝ ↦ A t (D t u))
      (A' (D t₀ u) + A t₀ (D' u)) s t₀ :=
    hA.clm_apply hDu
  have h := hAu.clm_apply hDv
  simpa [pullbackBilinearApply, ContinuousLinearMap.add_apply, add_assoc] using h

/-- One-sided DeTurck cancellation, including curvature conjugacy and the
Ricci trace.  This is the constrained-time counterpart of the two-sided
pullback theorem used by the smooth chart family. -/
theorem hasDerivWithinAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    (e : E ≃L[ℝ] E)
    (curvSource curvTarget : E → E → (E →ₗ[ℝ] E))
    {s : Set ℝ} {t₀ : ℝ}
    (hA : HasDerivWithinAt A (H - adv) s t₀)
    (hD : HasDerivWithinAt D (-(DW.comp (D t₀))) s t₀)
    (hA₀ : A t₀ = G)
    (hD₀ : D t₀ = e.toContinuousLinearMap)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (hRicciTarget : ∀ u v : E,
      R (e u) (e v) =
        LinearMap.trace ℝ E (curvTarget (e u) (e v)))
    (hcurv : ∀ u v w : E,
      curvTarget (e u) (e v) (e w) = e (curvSource u v w))
    (u v : E) :
    HasDerivWithinAt (pullbackBilinearApply A D u v)
      ((-2 : ℝ) * LinearMap.trace ℝ E (curvSource u v)) s t₀ := by
  have hpull := hasDerivWithinAt_pullbackBilinearApply A D hA hD u v
  refine hpull.congr_deriv ?_
  have htrace := ricciTrace_natural_of_curvature_intertwining
    e.toLinearEquiv curvSource curvTarget hcurv u v
  rw [hA₀]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, map_neg]
  rw [hDeTurck]
  have hDu : D t₀ u = e u := by rw [hD₀]; rfl
  have hDv : D t₀ v = e v := by rw [hD₀]; rfl
  have htrace' : LinearMap.trace ℝ E (curvTarget (e u) (e v)) =
      LinearMap.trace ℝ E (curvSource u v) := by
    simpa using htrace
  rw [hDu, hDv, hRicciTarget, htrace']
  ring

end OneSidedPullbackCalculus

section InteriorTimeProjection

/-- Strict interior points do not see the canonical projection onto a closed
time interval: its real value agrees locally with the identity. -/
theorem eventually_coe_projIcc_eq_self_of_mem_Ioo
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Ioo a b) :
    (fun s : ℝ ↦ (Set.projIcc a b hab s : ℝ)) =ᶠ[𝓝 t]
      (fun s : ℝ ↦ s) := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  simp [Set.coe_projIcc, max_eq_right hs.1.le, min_eq_right hs.2.le]

/-- A derivative relative to a closed interval is an ordinary two-sided
derivative at every strict interior point. -/
theorem hasDerivAt_of_hasDerivWithinAt_Icc_of_mem_Ioo
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {a b t : ℝ}
    (h : HasDerivWithinAt f f' (Set.Icc a b) t)
    (ht : t ∈ Set.Ioo a b) :
    HasDerivAt f f' t :=
  h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end InteriorTimeProjection

section BilinearBUCEvaluation

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {ι κ : Type*}

/-- The reconstructed positive coefficient path, extended from its forward
existence interval by the canonical projection onto that interval. -/
def reconstructedCoordinateMetricPath
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (t : ℝ) : CoordinateBUCTensor E :=
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  A.reconstructedMetricCoefficient K u₀
    (Set.projIcc 0 (A.uniformLifespan K : ℝ)
      (A.uniformLifespan K).property t)

/-- The projected real-time path starts at the prescribed background plus
initial perturbation. -/
@[simp] theorem reconstructedCoordinateMetricPath_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K) :
    reconstructedCoordinateMetricPath D K u₀ 0 =
      D.background + (u₀ : CoordinateBUCTensor E) := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  change A.reconstructedMetricCoefficient K u₀
      (Set.projIcc 0 (A.uniformLifespan K : ℝ)
        (A.uniformLifespan K).property 0) = _
  rw [show Set.projIcc 0 (A.uniformLifespan K : ℝ)
      (A.uniformLifespan K).property 0 =
        (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
          Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ)) by
    ext
    simp]
  exact A.reconstructedMetricCoefficient_zero K u₀

/-- At a genuine time in the reconstructed lifespan, the projected path is
the underlying fixed-point coefficient evaluated at that same time.  This is
the pointwise form of the fact that `projIcc` is invisible in the interior. -/
theorem reconstructedCoordinateMetricPath_eq_of_mem_Icc
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    {t : ℝ}
    (ht : t ∈ Set.Icc 0
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) :
    reconstructedCoordinateMetricPath D K u₀ t =
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).reconstructedMetricCoefficient
        K u₀ ⟨t, ht⟩ := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  change A.reconstructedMetricCoefficient K u₀
      (Set.projIcc 0 (A.uniformLifespan K : ℝ)
        (A.uniformLifespan K).property t) =
    A.reconstructedMetricCoefficient K u₀ ⟨t, ht⟩
  apply congrArg (A.reconstructedMetricCoefficient K u₀)
  apply Subtype.ext
  simp only [Set.coe_projIcc]
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- The reconstructed coefficient path has an ordinary two-sided derivative
at every strict interior time whenever its fixed-point orbit has the expected
derivative relative to the closed lifespan.  In particular, this theorem
cannot be applied at the initial endpoint `t = 0`. -/
theorem reconstructedCoordinateMetricPath_hasDerivAt_of_interior
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    {t : ℝ} {g' : CoordinateBUCTensor E}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ))
    (hderiv : HasDerivWithinAt
      (reconstructedCoordinateMetricPath D K u₀) g'
      (Set.Icc 0
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) t) :
    HasDerivAt (reconstructedCoordinateMetricPath D K u₀) g' t :=
  hasDerivAt_of_hasDerivWithinAt_Icc_of_mem_Ioo hderiv ⟨ht₀, htT⟩

/-- The analytic reconstruction supplies only this constrained, forward
derivative at its initial endpoint.  It is intentionally stated separately
from the interior `HasDerivAt` bridge above: unless the displayed rate
vanishes, the projected path is not two-sided differentiable at `t = 0`. -/
theorem reconstructedCoordinateMetricPath_hasDerivWithinAt_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (E := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀) :
    HasDerivWithinAt
      (reconstructedCoordinateMetricPath D K u₀)
      (Au₀ + D.base.nonlinearity
        ((u₀ : CoordinateBUCTensor E) + D.background))
      (Set.Icc 0
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) 0 := by
  simpa only [reconstructedCoordinateMetricPath] using
    (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground_reconstructedMetricCoefficient_hasDerivWithinAt_zero
        D K u₀ Au₀ hu₀)

/-- Any hypothetical ordinary derivative of the projected reconstruction at
the initial endpoint must be zero, because the projection makes the path
constant on the entire negative half-line.  Combined with the preceding
forward derivative theorem, this records the precise obstruction to an
endpoint `HasDerivAt` whenever the Ricci--DeTurck rate is nonzero. -/
theorem reconstructedCoordinateMetricPath_hasDerivAt_zero_deriv_eq_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    {g' : CoordinateBUCTensor E}
    (hderiv : HasDerivAt
      (reconstructedCoordinateMetricPath D K u₀) g' 0) :
    g' = 0 := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  have hleft : HasDerivWithinAt
      (reconstructedCoordinateMetricPath D K u₀) 0 (Set.Iic 0) 0 := by
    refine (hasDerivWithinAt_const
      (x := (0 : ℝ)) (s := Set.Iic 0)
      (c := reconstructedCoordinateMetricPath D K u₀ 0)).congr_of_mem ?_
        Set.self_mem_Iic
    intro s hs
    change A.reconstructedMetricCoefficient K u₀
        (Set.projIcc 0 (A.uniformLifespan K : ℝ)
          (A.uniformLifespan K).property s) =
      A.reconstructedMetricCoefficient K u₀
        (Set.projIcc 0 (A.uniformLifespan K : ℝ)
          (A.uniformLifespan K).property 0)
    apply congrArg (A.reconstructedMetricCoefficient K u₀)
    apply Subtype.ext
    have hs₀ : s ≤ 0 := hs
    have hsT : s ≤ (A.uniformLifespan K : ℝ) :=
      hs₀.trans (A.uniformLifespan K).property
    simp only [Set.coe_projIcc]
    rw [min_eq_right hsT, max_eq_left hs₀]
    simp
  exact ((uniqueDiffOn_Iic (0 : ℝ)).uniqueDiffWithinAt
    Set.self_mem_Iic).eq_deriv (Set.Iic 0)
      hderiv.hasDerivWithinAt hleft

/-- If the actual forward Ricci--DeTurck rate at zero is nonzero, the
canonically projected reconstructed path is not ordinarily differentiable at
zero.  Thus an endpoint scalar-evolution argument must use a separate smooth
extension; it cannot obtain two-sided regularity from `projIcc`. -/
theorem not_differentiableAt_reconstructedCoordinateMetricPath_zero_of_rate_ne_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (E := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (hrate : Au₀ + D.base.nonlinearity
      ((u₀ : CoordinateBUCTensor E) + D.background) ≠ 0) :
    ¬ DifferentiableAt ℝ (reconstructedCoordinateMetricPath D K u₀) 0 := by
  intro hdiff
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  have hT : (0 : ℝ) < (A.uniformLifespan K : ℝ) := by
    exact_mod_cast A.uniformLifespan_pos K
  have hforward :=
    reconstructedCoordinateMetricPath_hasDerivWithinAt_zero
      D K u₀ Au₀ hu₀
  have hzeroDeriv : deriv (reconstructedCoordinateMetricPath D K u₀) 0 = 0 :=
    reconstructedCoordinateMetricPath_hasDerivAt_zero_deriv_eq_zero
      D K u₀ hdiff.hasDerivAt
  have hzero : HasDerivAt
      (reconstructedCoordinateMetricPath D K u₀) 0 0 :=
    hdiff.hasDerivAt.congr_deriv hzeroDeriv
  have huniq : UniqueDiffWithinAt ℝ
      (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ⟨le_rfl, hT.le⟩
  have heq : (0 : CoordinateBUCTensor E) =
      Au₀ + D.base.nonlinearity
        ((u₀ : CoordinateBUCTensor E) + D.background) :=
    huniq.eq_deriv (Set.Icc 0 (A.uniformLifespan K : ℝ))
      hzero.hasDerivWithinAt hforward
  exact hrate heq.symm

/-- Pull the reconstructed coordinate coefficient through a moving
coordinate endpoint and its variational differential. -/
def reconstructedInverseGaugeMetric
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E) (t : ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  pullbackBilinearForm
    (coordinateBilinearFormAt
      (reconstructedCoordinateMetricPath D K u₀ t) (phi t)) (J t)

@[simp] theorem reconstructedInverseGaugeMetric_apply
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E) (t : ℝ) (u v : E) :
    reconstructedInverseGaugeMetric D K u₀ phi J t u v =
      coordinateMetricValue (reconstructedCoordinateMetricPath D K u₀ t)
        (phi t) (J t u) (J t v) :=
  rfl

/-- At the initial time, any identification of the reconstructed coordinate
coefficient is preserved exactly by the inverse-gauge pullback. -/
theorem reconstructedInverseGaugeMetric_zero_eq_pullback
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : coordinateBilinearFormAt
        (D.background + (u₀ : CoordinateBUCTensor E)) (phi 0) = G) :
    reconstructedInverseGaugeMetric D K u₀ phi J 0 =
      pullbackBilinearForm G (J 0) := by
  simp only [reconstructedInverseGaugeMetric,
    reconstructedCoordinateMetricPath_zero]
  rw [hG]

/-- Actual overlap-germ assembly for inverse-gauge reconstructed metrics.
The spatial evaluation point and both tangent slots may move with time, and
`S₁`, `S₂` transport the fixed source vectors into the two chart sources.
It therefore applies directly to `phi`, its variational differential `J`,
and the preferred-chart tangent equivalence. -/
theorem reconstructedInverseGaugeMetric_eventuallyEq_of_background_and_solution
    {ι₁ κ₁ ι₂ κ₂ : Type*} {l : Filter ℝ}
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι₁ κ₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι₂ κ₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K₂)
    (phi₁ phi₂ : ℝ → E) (J₁ J₂ : ℝ → E →L[ℝ] E)
    (S₁ S₂ : E →L[ℝ] E)
    (hbackground : ∀ u v : E, Filter.EventuallyEq l
      (fun t ↦ coordinateMetricValue D₂.background
        (phi₂ t) (J₂ t (S₂ u)) (J₂ t (S₂ v)))
      (fun t ↦ coordinateMetricValue D₁.background
        (phi₁ t) (J₁ t (S₁ u)) (J₁ t (S₁ v))))
    (hsolution : ∀ u v : E, Filter.EventuallyEq l
      (fun t ↦ coordinateMetricValue
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformSolution
          K₂ u₀₂
          (Set.projIcc 0
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan K₂ : ℝ)
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan K₂).property t))
        (phi₂ t) (J₂ t (S₂ u)) (J₂ t (S₂ v)))
      (fun t ↦ coordinateMetricValue
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformSolution
          K₁ u₀₁
          (Set.projIcc 0
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan K₁ : ℝ)
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan K₁).property t))
        (phi₁ t) (J₁ t (S₁ u)) (J₁ t (S₁ v)))) :
    ∀ u v : E, Filter.EventuallyEq l
      (fun t ↦ reconstructedInverseGaugeMetric D₂ K₂ u₀₂ phi₂ J₂ t
        (S₂ u) (S₂ v))
      (fun t ↦ reconstructedInverseGaugeMetric D₁ K₁ u₀₁ phi₁ J₁ t
        (S₁ u) (S₁ v)) := by
  intro u v
  filter_upwards [hbackground u v, hsolution u v] with t hbg hsol
  let A₁ :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁
  let A₂ :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂
  change coordinateMetricValue
      (A₂.reconstructedMetricCoefficient K₂ u₀₂
        (Set.projIcc 0 (A₂.uniformLifespan K₂ : ℝ)
          (A₂.uniformLifespan K₂).property t))
      (phi₂ t) (J₂ t (S₂ u)) (J₂ t (S₂ v)) =
    coordinateMetricValue
      (A₁.reconstructedMetricCoefficient K₁ u₀₁
        (Set.projIcc 0 (A₁.uniformLifespan K₁ : ℝ)
          (A₁.uniformLifespan K₁).property t))
      (phi₁ t) (J₁ t (S₁ u)) (J₁ t (S₁ v))
  exact reconstructedMetricValue_eq_of_background_and_solution
    A₁ A₂ K₁ K₂ u₀₁ u₀₂
    (Set.projIcc 0 (A₁.uniformLifespan K₁ : ℝ)
      (A₁.uniformLifespan K₁).property t)
    (Set.projIcc 0 (A₂.uniformLifespan K₂ : ℝ)
      (A₂.uniformLifespan K₂).property t)
    (phi₁ t) (phi₂ t)
    (J₁ t (S₁ u)) (J₁ t (S₁ v))
    (J₂ t (S₂ u)) (J₂ t (S₂ v))
    hbg hsol

/-- Symmetry of a reconstructed coordinate coefficient is preserved by the
inverse-gauge pullback. -/
theorem reconstructedInverseGaugeMetric_symm
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E) (t : ℝ)
    (hsymm : IsSymmetricCoordinateTensorCoefficient
      (reconstructedCoordinateMetricPath D K u₀ t)) (u v : E) :
    reconstructedInverseGaugeMetric D K u₀ phi J t u v =
      reconstructedInverseGaugeMetric D K u₀ phi J t v u := by
  simpa only [reconstructedInverseGaugeMetric_apply] using
    hsymm (phi t) (J t u) (J t v)

/-- A uniformly positive reconstructed coefficient remains positive after
pullback in every direction not killed by the variational differential. -/
theorem reconstructedInverseGaugeMetric_pos
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E) (t : ℝ) {μ : ℝ}
    (hpos : IsUniformlyPositiveCoordinateMetric μ
      (reconstructedCoordinateMetricPath D K u₀ t))
    {u : E} (hJu : J t u ≠ 0) :
    0 < reconstructedInverseGaugeMetric D K u₀ phi J t u u := by
  have hnorm : 0 < ‖J t u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hJu)
  calc
    0 < μ * ‖J t u‖ ^ 2 := mul_pos hpos.margin_pos hnorm
    _ ≤ coordinateMetricValue (reconstructedCoordinateMetricPath D K u₀ t)
        (phi t) (J t u) (J t u) := hpos.lower_bound (phi t) (J t u)
    _ = reconstructedInverseGaugeMetric D K u₀ phi J t u u := by
      rw [reconstructedInverseGaugeMetric_apply]

/-- The ordinary coordinate definition of a positive-definite symmetric
bilinear form. -/
def IsPositiveDefiniteCoordinateBilinearForm
    (g : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  (∀ u v : E, g u v = g v u) ∧
    ∀ u : E, u ≠ 0 → 0 < g u u

/-- An invertible gauge differential turns every uniformly positive
reconstructed coefficient into a genuine positive-definite coordinate
metric at the pulled point. -/
theorem reconstructedInverseGaugeMetric_isPositiveDefinite
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (E := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E) (t : ℝ) {μ : ℝ}
    (hpos : IsUniformlyPositiveCoordinateMetric μ
      (reconstructedCoordinateMetricPath D K u₀ t))
    (hJinv : (J t).IsInvertible) :
    IsPositiveDefiniteCoordinateBilinearForm
      (reconstructedInverseGaugeMetric D K u₀ phi J t) := by
  constructor
  · exact reconstructedInverseGaugeMetric_symm
      D K u₀ phi J t hpos.symmetric
  · intro u hu
    apply reconstructedInverseGaugeMetric_pos D K u₀ phi J t hpos
    rcases hJinv with ⟨e, he⟩
    intro hzero
    have heu : e u = 0 := by
      change (e : E →L[ℝ] E) u = 0
      rw [he]
      exact hzero
    exact hu (e.injective (by simpa using heu))

/-- Forward, pointwise coordinate Ricci evolution expressed through a
curvature endomorphism whose trace is the source Ricci tensor. -/
def IsForwardCoordinateRicciFlowAt
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (curv : E → E → (E →ₗ[ℝ] E)) (s : Set ℝ) (t₀ : ℝ) : Prop :=
  ∀ u v : E, HasDerivWithinAt (fun t ↦ g t u v)
    ((-2 : ℝ) * LinearMap.trace ℝ E (curv u v)) s t₀

/-- The two-sided coordinate Ricci equation.  This is separated from the
forward predicate because the reconstructed `BUC` orbit is canonically
defined only on a nonnegative lifespan. -/
def IsCoordinateRicciFlowAt
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (curv : E → E → (E →ₗ[ℝ] E)) (t₀ : ℝ) : Prop :=
  ∀ u v : E, HasDerivAt (fun t ↦ g t u v)
    ((-2 : ℝ) * LinearMap.trace ℝ E (curv u v)) t₀

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Two-sided coordinate Ricci evolution depends only on the ordinary time
germ of the metric path.  This is the local assembly principle used when an
inverse-gauge reconstruction is identified near an interior time with one
chart of a global smooth metric family. -/
theorem IsCoordinateRicciFlowAt.congr_of_eventuallyEq
    {g h : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {curv : E → E → (E →ₗ[ℝ] E)} {t₀ : ℝ}
    (hflow : IsCoordinateRicciFlowAt g curv t₀)
    (hgh : ∀ u v : E, Filter.EventuallyEq (nhds t₀)
      (fun t ↦ h t u v) (fun t ↦ g t u v)) :
    IsCoordinateRicciFlowAt h curv t₀ := by
  intro u v
  exact (hflow u v).congr_of_eventuallyEq (hgh u v)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The two-sided coordinate Ricci equation already supplies the coordinate
analogue of global `TimeDifferentiableAt`; no extra time-regularity witness is
needed after the forward-to-two-sided bridge has been applied. -/
theorem IsCoordinateRicciFlowAt.differentiableAt
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {curv : E → E → (E →ₗ[ℝ] E)} {t₀ : ℝ}
    (hflow : IsCoordinateRicciFlowAt g curv t₀) (u v : E) :
    DifferentiableAt ℝ (fun t ↦ g t u v) t₀ :=
  (hflow u v).differentiableAt

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A forward coordinate Ricci equation on a closed interval is automatically
the ordinary two-sided coordinate equation at every strict interior time.
This is the geometric counterpart of the `projIcc` interior bridge. -/
theorem IsForwardCoordinateRicciFlowAt.to_isCoordinateRicciFlowAt_of_mem_Ioo
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {curv : E → E → (E →ₗ[ℝ] E)} {a b t : ℝ}
    (hflow : IsForwardCoordinateRicciFlowAt g curv (Set.Icc a b) t)
    (ht : t ∈ Set.Ioo a b) :
    IsCoordinateRicciFlowAt g curv t := by
  intro u v
  exact hasDerivAt_of_hasDerivWithinAt_Icc_of_mem_Ioo (hflow u v) ht

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Forward coordinate Ricci evolution depends only on the constrained-time
germ of the metric path.  This is the exact overlap principle needed after
two chartwise reconstructed solvers have been proved to represent the same
pulled coefficient family. -/
theorem IsForwardCoordinateRicciFlowAt.congr_of_eventuallyEq
    {g h : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {curv : E → E → (E →ₗ[ℝ] E)} {s : Set ℝ} {t₀ : ℝ}
    (hflow : IsForwardCoordinateRicciFlowAt g curv s t₀)
    (ht₀ : t₀ ∈ s)
    (hgh : ∀ u v : E,
      Filter.EventuallyEq (nhdsWithin t₀ s)
        (fun t ↦ h t u v) (fun t ↦ g t u v)) :
    IsForwardCoordinateRicciFlowAt h curv s t₀ := by
  intro u v
  exact (hflow u v).congr_of_eventuallyEq (hgh u v)
    ((hgh u v).self_of_nhdsWithin ht₀)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Metric-germ transport through a fixed tangent map.  Combined with
`IsForwardCoordinateRicciFlowAt.chartTransition`, this converts the
chart-independent curvature rate into the full forward evolution of a
second chartwise metric path once the two reconstructed pullbacks agree on
their constrained-time germ. -/
theorem IsForwardCoordinateRicciFlowAt.pullback_congr_of_eventuallyEq
    {g h : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {curv : E → E → (E →ₗ[ℝ] E)} {s : Set ℝ} {t₀ : ℝ}
    (hflow : IsForwardCoordinateRicciFlowAt g curv s t₀)
    (ht₀ : t₀ ∈ s) (S : E →L[ℝ] E)
    (hgh : ∀ u v : E,
      Filter.EventuallyEq (nhdsWithin t₀ s)
        (fun t ↦ h t (S u) (S v)) (fun t ↦ g t u v)) :
    IsForwardCoordinateRicciFlowAt
      (fun t ↦ pullbackBilinearForm (h t) S) curv s t₀ := by
  apply hflow.congr_of_eventuallyEq ht₀
  intro u v
  simpa only [pullbackBilinearForm_apply] using hgh u v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A forward coordinate Ricci equation determines the ordinary two-sided
derivative whenever an independently assembled metric family is known to be
time-differentiable there.  Thus the missing passage from the `BUC` output to
the closed Ricci-flow wrapper is isolated to genuine time regularity and
smooth manifold assembly, rather than any further DeTurck cancellation. -/
theorem IsForwardCoordinateRicciFlowAt.to_isCoordinateRicciFlowAt
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {curv : E → E → (E →ₗ[ℝ] E)} {s : Set ℝ} {t₀ : ℝ}
    (hflow : IsForwardCoordinateRicciFlowAt g curv s t₀)
    (huniq : UniqueDiffWithinAt ℝ s t₀)
    (hdiff : ∀ u v : E, DifferentiableAt ℝ (fun t ↦ g t u v) t₀) :
    IsCoordinateRicciFlowAt g curv t₀ := by
  intro u v
  let rate := (-2 : ℝ) * LinearMap.trace ℝ E (curv u v)
  have hfull : HasDerivWithinAt (fun t ↦ g t u v)
      (deriv (fun t ↦ g t u v) t₀) s t₀ :=
    (hdiff u v).hasDerivAt.hasDerivWithinAt
  have hrate : deriv (fun t ↦ g t u v) t₀ = rate :=
    (hfull.derivWithin huniq).symm.trans
      ((hflow u v).derivWithin huniq)
  exact (hdiff u v).hasDerivAt.congr_deriv hrate

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Specialization of the two-sided regularity bridge to the positive
lifespan produced by the reconstructed solver. -/
theorem IsForwardCoordinateRicciFlowAt.to_isCoordinateRicciFlowAt_Icc_zero
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {curv : E → E → (E →ₗ[ℝ] E)} {T : ℝ}
    (hT : 0 < T)
    (hflow : IsForwardCoordinateRicciFlowAt g curv (Set.Icc 0 T) 0)
    (hdiff : ∀ u v : E, DifferentiableAt ℝ (fun t ↦ g t u v) 0) :
    IsCoordinateRicciFlowAt g curv 0 :=
  hflow.to_isCoordinateRicciFlowAt
    ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ⟨le_rfl, hT.le⟩) hdiff

end BilinearBUCEvaluation

section ReconstructedLocalRicciEvolution

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/-- A two-sided coordinate Ricci equation for the genuine chart coefficients
of an assembled smooth metric family supplies `TimeDifferentiableAt` in the
intrinsic tangent fiber.  This is the cheap projection from the reconstruction
output to the global time-regularity input of scalar evolution. -/
theorem IsCoordinateRicciFlowAt.timeDifferentiableAt_of_chartMetric
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source) {t₀ : ℝ}
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsCoordinateRicciFlowAt
      (fun t ↦ CovariantDerivative.chartMetric (gt t).inner anchor
        (extChartAt I anchor y)) curv t₀) :
    TimeDifferentiableAt gt t₀ y := by
  intro v w
  let p := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y v
  let q := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y w
  have hcoord := hflow.differentiableAt p q
  have heq :
      (fun t ↦ CovariantDerivative.chartMetric (gt t).inner anchor
        (extChartAt I anchor y) p q) =
      (fun t ↦ (gt t).inner y v w) := by
    funext t
    exact CovariantDerivative.chartMetric_apply_chart
      (gt t).inner anchor hy v w
  rw [← heq]
  exact hcoord

omit [T2Space M] in
/-- Interior specialization for a forward chartwise Ricci equation.  At a
strict interior time the closed interval is a neighborhood, so the forward
equation is two-sided and hence supplies intrinsic `TimeDifferentiableAt`.
The theorem deliberately has no endpoint specialization. -/
theorem IsForwardCoordinateRicciFlowAt.timeDifferentiableAt_of_chartMetric_interior
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source) {a b t : ℝ}
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsForwardCoordinateRicciFlowAt
      (fun s ↦ CovariantDerivative.chartMetric (gt s).inner anchor
        (extChartAt I anchor y)) curv (Set.Icc a b) t)
    (ht : t ∈ Set.Ioo a b) :
    TimeDifferentiableAt gt t y :=
  IsCoordinateRicciFlowAt.timeDifferentiableAt_of_chartMetric
    gt anchor hy curv (hflow.to_isCoordinateRicciFlowAt_of_mem_Ioo ht)

omit [T2Space M] in
/-- Self-chart specialization at every point.  Thus a globally assembled
family of two-sided coordinate solutions discharges the minimal scalar
evolution interface's global `TimeDifferentiableAt` input. -/
theorem global_timeDifferentiableAt_of_selfChart_coordinateRicciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (curv : M → E → E → (E →ₗ[ℝ] E))
    (hflow : ∀ y : M, IsCoordinateRicciFlowAt
      (fun t ↦ CovariantDerivative.chartMetric (gt t).inner y
        (extChartAt I y y)) (curv y) t₀) :
    ∀ y : M, TimeDifferentiableAt gt t₀ y := by
  intro y
  exact IsCoordinateRicciFlowAt.timeDifferentiableAt_of_chartMetric
    gt y (mem_extChartAt_source y) (curv y) (hflow y)

variable {ι κ : Type*}

omit [T2Space M] in
/-- At a strict positive interior time, Banach-valued differentiability of
the reconstructed coordinate coefficient and a genuine metric-germ
realization imply intrinsic pointwise time differentiability.  The
`0 < t < uniformLifespan` hypotheses are essential: they are exactly what
turns the derivative relative to the closed lifespan into a two-sided one. -/
theorem timeDifferentiableAt_of_reconstructedCoordinateMetricPath_interior
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    {t : ℝ} {g' : CoordinateBUCTensor E}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ))
    (hderiv : HasDerivWithinAt
      (reconstructedCoordinateMetricPath D K u₀) g'
      (Set.Icc 0
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) t)
    (hmetric : Filter.EventuallyEq (nhds t)
      (fun s : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ s)
        (extChartAt I anchor y))
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (gt s).inner anchor (extChartAt I anchor y))) :
    TimeDifferentiableAt gt t y := by
  have hpath : HasDerivAt
      (reconstructedCoordinateMetricPath D K u₀) g' t :=
    reconstructedCoordinateMetricPath_hasDerivAt_of_interior
      D K u₀ ht₀ htT hderiv
  intro v w
  let p : E := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y v
  let q : E := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y w
  have hcoordinateDeriv : HasDerivAt
      (fun s : ℝ ↦ coordinateMetricValue
        (reconstructedCoordinateMetricPath D K u₀ s)
        (extChartAt I anchor y) p q)
      (coordinateMetricValue g' (extChartAt I anchor y) p q) t :=
    (Poincare.HasDerivWithinAt.coordinateMetricValue
      (s := Set.univ) hpath.hasDerivWithinAt
      (extChartAt I anchor y) p q).hasDerivAt Filter.univ_mem
  have hcoordinate : DifferentiableAt ℝ
      (fun s : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ s)
        (extChartAt I anchor y) p q) t := by
    simpa only [coordinateBilinearFormAt_apply] using
      hcoordinateDeriv.differentiableAt
  have hmetricValue : Filter.EventuallyEq (nhds t)
      (fun s : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ s)
        (extChartAt I anchor y) p q)
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (gt s).inner anchor (extChartAt I anchor y) p q) := by
    filter_upwards [hmetric] with s hs
    exact congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B p q) hs
  have hchart : DifferentiableAt ℝ
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (gt s).inner anchor (extChartAt I anchor y) p q) t :=
    hcoordinate.congr_of_eventuallyEq hmetricValue.symm
  have heq :
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (gt s).inner anchor (extChartAt I anchor y) p q) =
      (fun s : ℝ ↦ (gt s).inner y v w) := by
    funext s
    exact CovariantDerivative.chartMetric_apply_chart
      (gt s).inner anchor hy v w
  rw [heq] at hchart
  exact hchart

/-- A forward Ricci-trace evolution proved in one preferred chart has the
identical rate in every overlapping preferred chart.  The endpoint-map germ
compatibility differentiates to the required variational conjugacy; no
abstract covariance premise is used. -/
theorem IsForwardCoordinateRicciFlowAt.chartTransition
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (anchor₁ anchor₂ : M) {Phi₁ Phi₂ : E → E} {z : E}
    {D₁ D₂ : E →L[ℝ] E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (hz' : Phi₁ z ∈ (extChartAt I anchor₁).target)
    (hy' : (extChartAt I anchor₁).symm (Phi₁ z) ∈
      (extChartAt I anchor₂).source)
    (hz₂' : GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z) ∈
      (extChartAt I anchor₂).target)
    (hPhi₁ : HasFDerivAt Phi₁ D₁ z)
    (hPhi₂ : HasFDerivAt Phi₂ D₂
      (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
    (hcompat :
      (Phi₂ ∘ GeodesicTransport.chartTransition anchor₁ anchor₂) =ᶠ[𝓝 z]
        (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘ Phi₁))
    (e₁ e₂ : E ≃L[ℝ] E)
    (he₁ : (e₁ : E →L[ℝ] E) = D₁)
    (he₂ : (e₂ : E →L[ℝ] E) = D₂)
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (s : Set ℝ) (t₀ : ℝ)
    (hflow : IsForwardCoordinateRicciFlowAt g
      (pullbackCurvatureEnd e₁
        (chartRicciCurvatureEndAt (gt t) anchor₁ (Phi₁ z) hz')) s t₀) :
    let S := chartTransitionTangentEquiv anchor₁ anchor₂ z hz hy
    IsForwardCoordinateRicciFlowAt g
      (fun u v ↦ pullbackCurvatureEnd e₂
        (chartRicciCurvatureEndAt (gt t) anchor₂
          (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z)) hz₂')
        (S u) (S v)) s t₀ := by
  dsimp only
  intro u v
  have htrace := inverseGaugeRicciTrace_chartTransition_eq
    gt t anchor₁ anchor₂ hz hy hz' hy' hz₂'
    hPhi₁ hPhi₂ hcompat e₁ e₂ he₁ he₂ u v
  rw [htrace]
  exact hflow u v

/-- Full two-chart forward Ricci evolution from an actual overlap germ of
the two metric paths.  Curvature transport is proved from the endpoint-map
germ and chart geometry; `hmetric` is the sole remaining chartwise solver
compatibility premise and is stated directly on `nhdsWithin t₀ s`. -/
theorem IsForwardCoordinateRicciFlowAt.chartTransition_of_metricGerm
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (anchor₁ anchor₂ : M) {Phi₁ Phi₂ : E → E} {z : E}
    {D₁ D₂ : E →L[ℝ] E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (hz' : Phi₁ z ∈ (extChartAt I anchor₁).target)
    (hy' : (extChartAt I anchor₁).symm (Phi₁ z) ∈
      (extChartAt I anchor₂).source)
    (hz₂' : GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z) ∈
      (extChartAt I anchor₂).target)
    (hPhi₁ : HasFDerivAt Phi₁ D₁ z)
    (hPhi₂ : HasFDerivAt Phi₂ D₂
      (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
    (hcompat : Filter.EventuallyEq (nhds z)
      (Phi₂ ∘ GeodesicTransport.chartTransition anchor₁ anchor₂)
      (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘ Phi₁))
    (e₁ e₂ : E ≃L[ℝ] E)
    (he₁ : (e₁ : E →L[ℝ] E) = D₁)
    (he₂ : (e₂ : E →L[ℝ] E) = D₂)
    (g₁ g₂ : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (s : Set ℝ) (t₀ : ℝ) (ht₀ : t₀ ∈ s)
    (hmetric :
      let S := chartTransitionTangentEquiv anchor₁ anchor₂ z hz hy
      ∀ u v : E, Filter.EventuallyEq (nhdsWithin t₀ s)
        (fun r ↦ g₂ r (S u) (S v)) (fun r ↦ g₁ r u v))
    (hflow : IsForwardCoordinateRicciFlowAt g₁
      (pullbackCurvatureEnd e₁
        (chartRicciCurvatureEndAt (gt t) anchor₁ (Phi₁ z) hz')) s t₀) :
    let S := chartTransitionTangentEquiv anchor₁ anchor₂ z hz hy
    IsForwardCoordinateRicciFlowAt
      (fun r ↦ pullbackBilinearForm (g₂ r) (S : E →L[ℝ] E))
      (fun u v ↦ pullbackCurvatureEnd e₂
        (chartRicciCurvatureEndAt (gt t) anchor₂
          (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z)) hz₂')
        (S u) (S v)) s t₀ := by
  dsimp only at hmetric ⊢
  have htransport := IsForwardCoordinateRicciFlowAt.chartTransition
    gt t anchor₁ anchor₂ hz hy hz' hy' hz₂'
      hPhi₁ hPhi₂ hcompat e₁ e₂ he₁ he₂ g₁ s t₀ hflow
  dsimp only at htransport
  exact htransport.pullback_congr_of_eventuallyEq ht₀
    (chartTransitionTangentEquiv anchor₁ anchor₂ z hz hy) hmetric

/-- Joint `C²` regularity of the concrete coordinate DeTurck field makes
its spatial derivative jointly `C¹`.  The latter is definitionally the
field `deTurckChartFieldDerivativeAt` used by the variational ODE. -/
theorem deTurckChartFieldDerivativeAt_jointContDiffAt_one_of_coordinateField_jointContDiffAt_two
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t₀ : ℝ) (z₀ : E)
    (hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z)) (t₀, z₀)) :
    ContDiffAt ℝ 1 (Function.uncurry
      (fun t z ↦ deTurckChartFieldDerivativeAt gt bg anchor t z))
      (t₀, z₀) := by
  have h :=
    contDiffAt_spatial_fderiv_of_joint_contDiffAt_two_vector
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z) t₀ z₀ hW
  simpa [Function.uncurry, deTurckChartFieldDerivativeAt] using h

/-- Joint `C¹` regularity of the concrete coordinate DeTurck field constructs
the inverse-gauge trajectory and its variational differential at the initial
time.  The derivatives may be restricted to any time set because the ODE
solver supplies ordinary two-sided derivatives on an open interval. -/
theorem exists_inverseDeTurckChartGauge_initial_variational_data
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z₀ : E)
    (hW : ContDiffAt ℝ 1 (Function.uncurry
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z)) (0, z₀))
    (hDW : ContDiffAt ℝ 1 (Function.uncurry
      (fun t z ↦ deTurckChartFieldDerivativeAt gt bg anchor t z))
      (0, z₀))
    (s : Set ℝ) :
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi 0 = z₀ ∧
        J 0 = ContinuousLinearMap.id ℝ E ∧
        HasDerivWithinAt phi
          (inverseDeTurckChartCoordinateField gt bg anchor 0 (phi 0)) s 0 ∧
        HasDerivWithinAt J
          (-(deTurckChartFieldDerivativeAt gt bg anchor 0 (phi 0)).comp
            (J 0)) s 0 ∧
        (J 0).IsInvertible := by
  let W : ℝ → E → E := fun t z ↦
    chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z
  let DW : ℝ → E → E →L[ℝ] E := fun t z ↦
    deTurckChartFieldDerivativeAt gt bg anchor t z
  rcases exists_local_inverseGauge_with_variationalEquation_of_contDiffAt
      W DW 0 z₀ (by simpa [W] using hW) (by simpa [DW] using hDW) with
    ⟨ε, hε, phi, J, hphi₀, hJ₀, hODE⟩
  have hzero : (0 : ℝ) ∈ Set.Ioo (0 - ε) (0 + ε) := by
    constructor <;> linarith
  have hODE₀ := hODE 0 hzero
  refine ⟨phi, J, hphi₀, hJ₀, ?_, ?_, ?_⟩
  · simpa [W, inverseDeTurckChartCoordinateField] using
      hODE₀.1.hasDerivWithinAt
  · simpa [DW] using hODE₀.2.hasDerivWithinAt
  · rw [hJ₀]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩

/-- Joint `C¹` regularity at an arbitrary physical time constructs the local
inverse DeTurck trajectory and its variational differential based at that
time.  This is the time-translated form of the initial-data theorem and is
the entry point needed for interior reconstructed-flow evolution. -/
theorem exists_inverseDeTurckChartGauge_variational_data_at
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t₀ : ℝ) (z₀ : E)
    (hW : ContDiffAt ℝ 1 (Function.uncurry
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z)) (t₀, z₀))
    (hDW : ContDiffAt ℝ 1 (Function.uncurry
      (fun t z ↦ deTurckChartFieldDerivativeAt gt bg anchor t z))
      (t₀, z₀))
    (s : Set ℝ) :
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi t₀ = z₀ ∧
        J t₀ = ContinuousLinearMap.id ℝ E ∧
        HasDerivWithinAt phi
          (inverseDeTurckChartCoordinateField gt bg anchor t₀ (phi t₀))
          s t₀ ∧
        HasDerivWithinAt J
          (-(deTurckChartFieldDerivativeAt gt bg anchor t₀ (phi t₀)).comp
            (J t₀)) s t₀ ∧
        (J t₀).IsInvertible := by
  let W : ℝ → E → E := fun t z ↦
    chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z
  let DW : ℝ → E → E →L[ℝ] E := fun t z ↦
    deTurckChartFieldDerivativeAt gt bg anchor t z
  rcases exists_local_inverseGauge_with_variationalEquation_of_contDiffAt
      W DW t₀ z₀ (by simpa [W] using hW) (by simpa [DW] using hDW) with
    ⟨ε, hε, phi, J, hphi₀, hJ₀, hODE⟩
  have ht₀mem : t₀ ∈ Set.Ioo (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith
  have hODE₀ := hODE t₀ ht₀mem
  refine ⟨phi, J, hphi₀, hJ₀, ?_, ?_, ?_⟩
  · simpa [W, inverseDeTurckChartCoordinateField] using
      hODE₀.1.hasDerivWithinAt
  · simpa [DW] using hODE₀.2.hasDerivWithinAt
  · rw [hJ₀]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩

/-- Exact moving-base chain rule still needed beyond the `BUC` fixed-point
output.  The temporal term is the already-proved Banach derivative
`A u₀ + N (u₀ + c)`; the additional term is precisely negative DeTurck
advection from following the inverse-gauge trajectory.  The expression is
bilinear-form valued, so it also supplies the uniform control needed when
the tangent slots move. -/
def HasReconstructedInverseGaugeAdvectionAtZero
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) : Prop :=
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  let s := Set.Icc 0 (A.uniformLifespan K : ℝ)
  HasDerivWithinAt
    (fun t : ℝ ↦ coordinateBilinearFormAt
      (reconstructedCoordinateMetricPath D K u₀ t) (phi t))
    (coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity
          ((u₀ : CoordinateBUCTensor E) + D.background)) (phi 0) -
      deTurckChartMetricAdvectionAt gt bg anchor 0 (phi 0)) s 0

set_option synthInstance.maxHeartbeats 1000000 in
/-- An honest initial metric germ and the inverse DeTurck coordinate velocity
derive the moving-base advection identity required by the pullback argument.
Thus the formerly packaged `hbase` premise is ordinary chain rule data, not
an additional Ricci--DeTurck equation. -/
theorem hasReconstructedInverseGaugeAdvectionAtZero_of_metric_germ_and_velocity
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      («E» := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E)
    (hz : phi 0 ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) z') =ᶠ[nhds (phi 0)]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hphi : HasDerivWithinAt phi
      (inverseDeTurckChartCoordinateField gt bg anchor 0 (phi 0))
      (Set.Icc 0
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) 0) :
    HasReconstructedInverseGaugeAdvectionAtZero
      D K u₀ Au₀ gt bg anchor phi := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  let s := Set.Icc 0 (A.uniformLifespan K : ℝ)
  change HasDerivWithinAt
    (fun t : ℝ ↦ coordinateBilinearFormAt
      (reconstructedCoordinateMetricPath D K u₀ t) (phi t))
    (coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity
          ((u₀ : CoordinateBUCTensor E) + D.background)) (phi 0) -
      deTurckChartMetricAdvectionAt gt bg anchor 0 (phi 0)) s 0
  have hg : HasDerivWithinAt
      (reconstructedCoordinateMetricPath D K u₀)
      (Au₀ + D.base.nonlinearity
        ((u₀ : CoordinateBUCTensor E) + D.background)) s 0 := by
    simpa only [A, s] using
      reconstructedCoordinateMetricPath_hasDerivWithinAt_zero
        D K u₀ Au₀ hu₀
  have hgerm₀ :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ 0) z') =ᶠ[nhds (phi 0)]
        CovariantDerivative.chartMetric (gt 0).inner anchor := by
    rw [reconstructedCoordinateMetricPath_zero D K u₀,
      add_comm D.background (u₀ : CoordinateBUCTensor E)]
    exact hfullGerm
  have hchartC2 :=
    deTurckChartMetric_contDiffAt_two_of_mem_target
      (gt 0) anchor hz
  have hchartD : HasFDerivAt
      (CovariantDerivative.chartMetric (gt 0).inner anchor)
      (fderiv ℝ (CovariantDerivative.chartMetric (gt 0).inner anchor)
        (phi 0)) (phi 0) :=
    (hchartC2.differentiableAt (by norm_num)).hasFDerivAt
  have hspace : HasFDerivAt
      (fun z' ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ 0) z')
      (fderiv ℝ (CovariantDerivative.chartMetric (gt 0).inner anchor)
        (phi 0)) (phi 0) :=
    hchartD.congr_of_eventuallyEq hgerm₀
  have hmoving :=
    hasDerivWithinAt_coordinateBilinearFormAt_moving
      (g := reconstructedCoordinateMetricPath D K u₀)
      (g' := Au₀ + D.base.nonlinearity
        ((u₀ : CoordinateBUCTensor E) + D.background))
      (phi := phi)
      (phi' := inverseDeTurckChartCoordinateField gt bg anchor 0 (phi 0))
      (s := s) (t₀ := 0)
      (D := fderiv ℝ
        (CovariantDerivative.chartMetric (gt 0).inner anchor) (phi 0))
      hg (by simpa only [A, s] using hphi) hspace
  have hspatial :
      (fderiv ℝ (CovariantDerivative.chartMetric (gt 0).inner anchor)
        (phi 0))
          (inverseDeTurckChartCoordinateField gt bg anchor 0 (phi 0)) =
        -deTurckChartMetricAdvectionAt gt bg anchor 0 (phi 0) := by
    simp only [inverseDeTurckChartCoordinateField,
      deTurckChartMetricAdvectionAt, map_neg]
  rw [hspatial] at hmoving
  simpa only [sub_eq_add_neg] using hmoving

set_option synthInstance.maxHeartbeats 1000000 in
/-- At an arbitrary time, an honest derivative of the reconstructed `BUC`
coefficient, a spatial metric germ, and the inverse DeTurck coordinate
velocity give the full moving-base derivative.  This is the two-sided
interior-time counterpart of
`hasReconstructedInverseGaugeAdvectionAtZero_of_metric_germ_and_velocity`.

Unlike the endpoint statement, no generator-domain hypothesis appears here:
the caller supplies the ordinary Banach-valued derivative available at a
strict interior time. -/
theorem hasReconstructedInverseGaugeAdvectionAt_of_metric_germ_and_velocity
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) {t : ℝ} {g' : CoordinateBUCTensor E}
    (hg : HasDerivAt (reconstructedCoordinateMetricPath D K u₀) g' t)
    (hz : phi t ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) z') =ᶠ[nhds (phi t)]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hphi : HasDerivAt phi
      (inverseDeTurckChartCoordinateField gt bg anchor t (phi t)) t) :
    HasDerivAt
      (fun s : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ s) (phi s))
      (coordinateBilinearFormAt g' (phi t) -
        deTurckChartMetricAdvectionAt gt bg anchor t (phi t)) t := by
  have hchartC2 :=
    deTurckChartMetric_contDiffAt_two_of_mem_target
      (gt t) anchor hz
  have hchartD : HasFDerivAt
      (CovariantDerivative.chartMetric (gt t).inner anchor)
      (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
        (phi t)) (phi t) :=
    (hchartC2.differentiableAt (by norm_num)).hasFDerivAt
  have hspace : HasFDerivAt
      (fun z' ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ t) z')
      (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
        (phi t)) (phi t) :=
    hchartD.congr_of_eventuallyEq hfullGerm
  have hmovingWithin :=
    hasDerivWithinAt_coordinateBilinearFormAt_moving
      (g := reconstructedCoordinateMetricPath D K u₀)
      (g' := g')
      (phi := phi)
      (phi' := inverseDeTurckChartCoordinateField gt bg anchor t (phi t))
      (s := Set.univ) (t₀ := t)
      (D := fderiv ℝ
        (CovariantDerivative.chartMetric (gt t).inner anchor) (phi t))
      hg.hasDerivWithinAt hphi.hasDerivWithinAt hspace
  have hmoving : HasDerivAt
      (fun s : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ s) (phi s))
      (coordinateBilinearFormAt g' (phi t) +
        (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
          (phi t))
          (inverseDeTurckChartCoordinateField gt bg anchor t (phi t))) t := by
    unfold HasDerivWithinAt at hmovingWithin
    unfold HasDerivAt
    simpa only [nhdsWithin_univ] using hmovingWithin
  have hspatial :
      (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
        (phi t))
          (inverseDeTurckChartCoordinateField gt bg anchor t (phi t)) =
        -deTurckChartMetricAdvectionAt gt bg anchor t (phi t) := by
    simp only [inverseDeTurckChartCoordinateField,
      deTurckChartMetricAdvectionAt, map_neg]
  rw [hspatial] at hmoving
  simpa only [sub_eq_add_neg] using hmoving

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A two-sided reconstructed coefficient derivative at an arbitrary time
produces a genuine coordinate Ricci-flow germ after inverse DeTurck pullback.

The theorem constructs the local coordinate diffeomorphism rather than
assuming one.  Its remaining analytic inputs are exactly an ordinary
Banach-valued coefficient derivative, the spatial metric germ identifying
that coefficient with `gt t`, and the pointwise Ricci--DeTurck right-hand
side.  At strict positive times these are the data exported by the interior
classicality layer. -/
theorem exists_reconstructed_coordinateLocalDiffeomorphGerm_with_RicciFlowAt
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (Phi : E → E) (x : E)
    (hphi_t : phi t = extChartAt I anchor y)
    (hPhi_t : Phi x = phi t)
    {g' : CoordinateBUCTensor E}
    (hg : HasDerivAt (reconstructedCoordinateMetricPath D K u₀) g' t)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) z') =ᶠ[nhds (phi t)]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hidentifyRHS :
      coordinateBilinearFormAt g' (phi t) =
        deTurckChartMetricEvolutionBilin gt bg anchor t (phi t))
    (hphi : HasDerivAt phi
      (inverseDeTurckChartCoordinateField gt bg anchor t (phi t)) t)
    (hJ : HasDerivAt J
      (-(deTurckChartFieldDerivativeAt gt bg anchor t (phi t)).comp (J t)) t)
    (hJinv : (J t).IsInvertible)
    (hPhiC1 : ContDiffAt ℝ 1 Phi x)
    (hPhiD : HasFDerivAt Phi (J t) x)
    (hreg : DeTurckVectorFieldRegularAt gt bg t) :
    ∃ G : CoordinateLocalDiffeomorphGerm Phi x (J t),
      G.localHomeomorph x = phi t ∧
        reconstructedInverseGaugeMetric D K u₀ phi J t =
          pullbackBilinearForm
            (CovariantDerivative.chartMetric (gt t).inner anchor (phi t))
            (G.tangentEquiv : E →L[ℝ] E) ∧
        IsCoordinateRicciFlowAt
          (reconstructedInverseGaugeMetric D K u₀ phi J)
          (pullbackCurvatureEnd G.tangentEquiv
            (chartRicciCurvatureEndAt (gt t) anchor (phi t)
              (by
                simpa [hphi_t] using
                  (extChartAt I anchor).map_source hy))) t := by
  rcases exists_coordinateLocalDiffeomorphGerm_of_variational_data
      Phi x (J t) hPhiC1 hPhiD hJinv with
    ⟨e, he, U, hUcoe, hxU, hPhiTarget, hUderiv, hUinvDeriv,
      _hUC1, _hUinvC1, hleft, hright⟩
  let G : CoordinateLocalDiffeomorphGerm Phi x (J t) :=
    { tangentEquiv := e
      tangentEquiv_coe := he
      localHomeomorph := U
      localHomeomorph_coe := hUcoe
      mem_source := hxU
      image_mem_target := hPhiTarget
      forward_fderiv := hUderiv
      inverse_fderiv := hUinvDeriv
      eventually_left_inverse := hleft
      eventually_right_inverse := hright }
  have hz : phi t ∈ (extChartAt I anchor).target := by
    simpa [hphi_t] using (extChartAt I anchor).map_source hy
  let C := chartRicciCurvatureEndAt (gt t) anchor (phi t) hz
  have hmetric :
      coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) (phi t) =
        CovariantDerivative.chartMetric (gt t).inner anchor (phi t) :=
    hfullGerm.self_of_nhds
  have hmoving : HasDerivAt
      (fun s : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ s) (phi s))
      (deTurckChartMetricEvolutionBilin gt bg anchor t (phi t) -
        deTurckChartMetricAdvectionAt gt bg anchor t (phi t)) t := by
    have h :=
      hasReconstructedInverseGaugeAdvectionAt_of_metric_germ_and_velocity
        D K u₀ gt bg anchor phi hg hz hfullGerm hphi
    rw [hidentifyRHS] at h
    exact h
  have hDeTurck : ∀ p q : E,
      deTurckChartMetricEvolutionBilin gt bg anchor t (phi t) p q =
        (-2 : ℝ) * deTurckChartRicciBilin gt anchor t (phi t) p q +
          deTurckChartMetricAdvectionAt gt bg anchor t (phi t) p q +
          coordinateBilinearFormAt
              (reconstructedCoordinateMetricPath D K u₀ t) (phi t)
              (deTurckChartFieldDerivativeAt gt bg anchor t (phi t) p) q +
          coordinateBilinearFormAt
              (reconstructedCoordinateMetricPath D K u₀ t) (phi t) p
              (deTurckChartFieldDerivativeAt gt bg anchor t (phi t) q) := by
    intro p q
    simp only [deTurckChartMetricEvolutionBilin,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    have hmetric' := hmetric
    rw [hphi_t] at hmetric'
    rw [hphi_t,
      deTurckChartLieBilin_apply_chart_eq_advection_add_DW_slots
        gt bg anchor t hy hχone hreg p q,
      ← hmetric']
    ring
  have hrate : IsCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J)
      (pullbackCurvatureEnd e C) t := by
    intro p q
    have hpull :=
      hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace
        (fun s : ℝ ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ s) (phi s))
        J
        (coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) (phi t))
        (deTurckChartMetricEvolutionBilin gt bg anchor t (phi t))
        (deTurckChartMetricAdvectionAt gt bg anchor t (phi t))
        (deTurckChartRicciBilin gt anchor t (phi t))
        (deTurckChartFieldDerivativeAt gt bg anchor t (phi t))
        e (pullbackCurvatureEnd e C) C hmoving hJ rfl he.symm hDeTurck
        (fun a b ↦ deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
          gt anchor t (phi t) hz (e a) (e b))
        (curvature_natural_pullbackCurvatureEnd e C) p q
    simpa [reconstructedInverseGaugeMetric,
      reconstructedInverseGaugeMetric_apply] using hpull
  have hpulled :
      reconstructedInverseGaugeMetric D K u₀ phi J t =
        pullbackBilinearForm
          (CovariantDerivative.chartMetric (gt t).inner anchor (phi t))
          (G.tangentEquiv : E →L[ℝ] E) := by
    simp only [reconstructedInverseGaugeMetric]
    rw [hmetric]
    exact congrArg
      (pullbackBilinearForm
        (CovariantDerivative.chartMetric (gt t).inner anchor (phi t)))
      G.tangentEquiv_coe.symm
  refine ⟨G, ?_, hpulled, ?_⟩
  · change U x = phi t
    rw [congrFun hUcoe x, hPhi_t]
  · dsimp [G]
    exact hrate

/-- The complete theorem-bearing local output obtained by composing the
positive reconstructed `BUC` metric with an actual inverse-gauge germ.

The analytic coefficient identity is the remaining Ricci--DeTurck RHS
identification.  `hbase` is the spatial chain rule unavailable in the `BUC`
norm: its temporal term is the solver derivative and its moving-base term is
negative advection.  All Lie-term
cancellation, curvature pullback, Ricci contraction, positivity, and the
inverse-function-theorem germ are proved in the conclusion. -/
theorem exists_reconstructed_coordinateLocalDiffeomorphGerm_with_forwardRicciFlowAt
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      («E» := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (μ : ℝ)
    (hbackground : IsUniformlyPositiveCoordinateMetric μ D.background)
    (hsolutionSymmetric :
      ∀ t : Set.Icc (0 : ℝ)
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ),
        IsSymmetricCoordinateTensorCoefficient
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformSolution K u₀ t))
    (hsmall : ((K + 1 : ℝ≥0) : ℝ) < μ)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (Phi : E → E) (x : E)
    (hphi₀ : phi 0 = extChartAt I anchor y)
    (hPhi₀ : Phi x = phi 0)
    (hreg : DeTurckVectorFieldRegularAt gt bg 0)
    (hidentifyInitial :
      coordinateBilinearFormAt
          (D.background + (u₀ : CoordinateBUCTensor E)) (phi 0) =
        CovariantDerivative.chartMetric (gt 0).inner anchor (phi 0))
    (hidentifyRHS :
      coordinateBilinearFormAt
          (Au₀ + D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) (phi 0) =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 (phi 0))
    (hbase : HasReconstructedInverseGaugeAdvectionAtZero
      D K u₀ Au₀ gt bg anchor phi)
    (hJ : HasDerivWithinAt J
      (-(deTurckChartFieldDerivativeAt gt bg anchor 0 (phi 0)).comp (J 0))
      (Set.Icc 0
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) 0)
    (hJinv : (J 0).IsInvertible)
    (hPhiC1 : ContDiffAt ℝ 1 Phi x)
    (hPhiD : HasFDerivAt Phi (J 0) x) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∃ G : CoordinateLocalDiffeomorphGerm Phi x (J 0),
      0 < A.uniformLifespan K ∧
        A.reconstructedMetricCoefficient K u₀
            (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
              Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ)) =
          D.background + (u₀ : CoordinateBUCTensor E) ∧
        (∀ t : Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ),
          IsUniformlyPositiveCoordinateMetric
            (μ - ((K + 1 : ℝ≥0) : ℝ))
            (A.reconstructedMetricCoefficient K u₀ t)) ∧
        G.localHomeomorph x = phi 0 ∧
        reconstructedInverseGaugeMetric D K u₀ phi J 0 =
          pullbackBilinearForm
            (CovariantDerivative.chartMetric (gt 0).inner anchor (phi 0))
            (G.tangentEquiv : E →L[ℝ] E) ∧
        IsPositiveDefiniteCoordinateBilinearForm
          (reconstructedInverseGaugeMetric D K u₀ phi J 0) ∧
        IsForwardCoordinateRicciFlowAt
          (reconstructedInverseGaugeMetric D K u₀ phi J)
          (pullbackCurvatureEnd G.tangentEquiv
            (chartRicciCurvatureEndAt (gt 0) anchor (phi 0)
              (by simpa [hphi₀] using (extChartAt I anchor).map_source hy)))
          (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  dsimp only
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  let s := Set.Icc 0 (A.uniformLifespan K : ℝ)
  have hpositive :=
    AffineRecenteredDeTurckShapedBUCRemainderData.exists_positive_reconstructedMetricCoefficient_evolution
      D K u₀ Au₀ hu₀ μ hbackground hsolutionSymmetric hsmall
  dsimp only at hpositive
  rcases hpositive with ⟨hT, hzero, hpos, _hsolverDerivative⟩
  rcases exists_coordinateLocalDiffeomorphGerm_of_variational_data
      Phi x (J 0) hPhiC1 hPhiD hJinv with
    ⟨e, he, U, hUcoe, hxU, hPhiTarget, hUderiv, hUinvDeriv,
      _hUC1, _hUinvC1, hleft, hright⟩
  let G : CoordinateLocalDiffeomorphGerm Phi x (J 0) :=
    { tangentEquiv := e
      tangentEquiv_coe := he
      localHomeomorph := U
      localHomeomorph_coe := hUcoe
      mem_source := hxU
      image_mem_target := hPhiTarget
      forward_fderiv := hUderiv
      inverse_fderiv := hUinvDeriv
      eventually_left_inverse := hleft
      eventually_right_inverse := hright }
  have hz : phi 0 ∈ (extChartAt I anchor).target := by
    simpa [hphi₀] using (extChartAt I anchor).map_source hy
  let C := chartRicciCurvatureEndAt (gt 0) anchor (phi 0) hz
  have hmoving : HasDerivWithinAt
      (fun t : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ t) (phi t))
      (deTurckChartMetricEvolutionBilin gt bg anchor 0 (phi 0) -
        deTurckChartMetricAdvectionAt gt bg anchor 0 (phi 0)) s 0 := by
    have hbase' := hbase
    change HasDerivWithinAt
      (fun t : ℝ ↦ coordinateBilinearFormAt
        (reconstructedCoordinateMetricPath D K u₀ t) (phi t))
      (coordinateBilinearFormAt
          (Au₀ + D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) (phi 0) -
        deTurckChartMetricAdvectionAt gt bg anchor 0 (phi 0)) s 0 at hbase'
    rw [hidentifyRHS] at hbase'
    exact hbase'
  have hmetric0 :
      coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ 0) (phi 0) =
        CovariantDerivative.chartMetric (gt 0).inner anchor (phi 0) := by
    rw [reconstructedCoordinateMetricPath_zero D K u₀]
    exact hidentifyInitial
  have hDeTurck : ∀ p q : E,
      deTurckChartMetricEvolutionBilin gt bg anchor 0 (phi 0) p q =
        (-2 : ℝ) * deTurckChartRicciBilin gt anchor 0 (phi 0) p q +
          deTurckChartMetricAdvectionAt gt bg anchor 0 (phi 0) p q +
          coordinateBilinearFormAt
              (reconstructedCoordinateMetricPath D K u₀ 0) (phi 0)
              (deTurckChartFieldDerivativeAt gt bg anchor 0 (phi 0) p) q +
          coordinateBilinearFormAt
              (reconstructedCoordinateMetricPath D K u₀ 0) (phi 0) p
              (deTurckChartFieldDerivativeAt gt bg anchor 0 (phi 0) q) := by
    intro p q
    simp only [deTurckChartMetricEvolutionBilin,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    have hmetric0' := hmetric0
    rw [hphi₀] at hmetric0'
    rw [hphi₀,
      deTurckChartLieBilin_apply_chart_eq_advection_add_DW_slots
        gt bg anchor 0 hy hχone hreg p q,
      ← hmetric0']
    ring
  have hrate : IsForwardCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J)
      (pullbackCurvatureEnd e C) s 0 := by
    intro p q
    have hpull :=
      hasDerivWithinAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace
        (fun t : ℝ ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) (phi t))
        J
        (coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ 0) (phi 0))
        (deTurckChartMetricEvolutionBilin gt bg anchor 0 (phi 0))
        (deTurckChartMetricAdvectionAt gt bg anchor 0 (phi 0))
        (deTurckChartRicciBilin gt anchor 0 (phi 0))
        (deTurckChartFieldDerivativeAt gt bg anchor 0 (phi 0))
        e (pullbackCurvatureEnd e C) C hmoving hJ rfl he.symm hDeTurck
        (fun a b ↦ deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
          gt anchor 0 (phi 0) hz (e a) (e b))
        (curvature_natural_pullbackCurvatureEnd e C) p q
    simpa [reconstructedInverseGaugeMetric,
      reconstructedInverseGaugeMetric_apply] using hpull
  have hposInitial : IsUniformlyPositiveCoordinateMetric
      (μ - ((K + 1 : ℝ≥0) : ℝ))
      (reconstructedCoordinateMetricPath D K u₀ 0) := by
    rw [reconstructedCoordinateMetricPath_zero D K u₀, ← hzero]
    exact hpos
      (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
        Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ))
  have hpulledPositive : IsPositiveDefiniteCoordinateBilinearForm
      (reconstructedInverseGaugeMetric D K u₀ phi J 0) :=
    reconstructedInverseGaugeMetric_isPositiveDefinite
      D K u₀ phi J 0 hposInitial hJinv
  have hpulledInitial :
      reconstructedInverseGaugeMetric D K u₀ phi J 0 =
        pullbackBilinearForm
          (CovariantDerivative.chartMetric (gt 0).inner anchor (phi 0))
          (G.tangentEquiv : E →L[ℝ] E) := by
    have h := reconstructedInverseGaugeMetric_zero_eq_pullback
      D K u₀ phi J
      (CovariantDerivative.chartMetric (gt 0).inner anchor (phi 0))
      hidentifyInitial
    rw [← he] at h
    simpa [G] using h
  refine ⟨G, hT, hzero, hpos, ?_, hpulledInitial, hpulledPositive, ?_⟩
  · change U x = phi 0
    rw [congrFun hUcoe x, hPhi₀]
  · dsimp [G]
    exact hrate

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Local metric germs and the lower-order coefficient formula discharge both
pointwise Ricci--DeTurck coefficient-identification premises in the inverse
gauge construction.  The moving-base advection identity is now derived from
the ordinary inverse-gauge coordinate velocity `hphi`; no separate `hbase`
premise remains. -/
theorem exists_reconstructed_coordinateLocalDiffeomorphGerm_with_forwardRicciFlowAt_of_generator_domain_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      («E» := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (μ : ℝ)
    (hbackground : IsUniformlyPositiveCoordinateMetric μ D.background)
    (hsolutionSymmetric :
      ∀ t : Set.Icc (0 : ℝ)
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ),
        IsSymmetricCoordinateTensorCoefficient
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformSolution K u₀ t))
    (hsmall : ((K + 1 : ℝ≥0) : ℝ) < μ)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (Phi : E → E) (x : E)
    (hphi₀ : phi 0 = extChartAt I anchor y)
    (hPhi₀ : Phi x = phi 0)
    (hreg : DeTurckVectorFieldRegularAt gt bg 0)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) z') =ᶠ[nhds (phi 0)]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[nhds (phi 0)]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) (phi 0) v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 (phi 0) v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background) (phi 0) v w +
          coordinateMetricLaplacianValue D.background (phi 0) v w)
    (hphi : HasDerivWithinAt phi
      (inverseDeTurckChartCoordinateField gt bg anchor 0 (phi 0))
      (Set.Icc 0
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) 0)
    (hJ : HasDerivWithinAt J
      (-(deTurckChartFieldDerivativeAt gt bg anchor 0 (phi 0)).comp (J 0))
      (Set.Icc 0
        ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ)) 0)
    (hJinv : (J 0).IsInvertible)
    (hPhiC1 : ContDiffAt ℝ 1 Phi x)
    (hPhiD : HasFDerivAt Phi (J 0) x) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∃ G : CoordinateLocalDiffeomorphGerm Phi x (J 0),
      0 < A.uniformLifespan K ∧
        A.reconstructedMetricCoefficient K u₀
            (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
              Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ)) =
          D.background + (u₀ : CoordinateBUCTensor E) ∧
        (∀ t : Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ),
          IsUniformlyPositiveCoordinateMetric
            (μ - ((K + 1 : ℝ≥0) : ℝ))
            (A.reconstructedMetricCoefficient K u₀ t)) ∧
        G.localHomeomorph x = phi 0 ∧
        reconstructedInverseGaugeMetric D K u₀ phi J 0 =
          pullbackBilinearForm
            (CovariantDerivative.chartMetric (gt 0).inner anchor (phi 0))
            (G.tangentEquiv : E →L[ℝ] E) ∧
        IsPositiveDefiniteCoordinateBilinearForm
          (reconstructedInverseGaugeMetric D K u₀ phi J 0) ∧
        IsForwardCoordinateRicciFlowAt
          (reconstructedInverseGaugeMetric D K u₀ phi J)
          (pullbackCurvatureEnd G.tangentEquiv
            (chartRicciCurvatureEndAt (gt 0) anchor (phi 0)
              (by simpa [hphi₀] using (extChartAt I anchor).map_source hy)))
          (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  have hz : phi 0 ∈ (extChartAt I anchor).target := by
    simpa [hphi₀] using (extChartAt I anchor).map_source hy
  have hbase : HasReconstructedInverseGaugeAdvectionAtZero
      D K u₀ Au₀ gt bg anchor phi :=
    hasReconstructedInverseGaugeAdvectionAtZero_of_metric_germ_and_velocity
      D K u₀ Au₀ hu₀ gt bg anchor phi hz hfullGerm hphi
  have hidentifyInitial :
      coordinateBilinearFormAt
          (D.background + (u₀ : CoordinateBUCTensor E)) (phi 0) =
        CovariantDerivative.chartMetric (gt 0).inner anchor (phi 0) := by
    rw [add_comm D.background (u₀ : CoordinateBUCTensor E)]
    exact hfullGerm.eq_of_nhds
  have hidentifyRHS :
      coordinateBilinearFormAt
          (Au₀ + D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) (phi 0) =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 (phi 0) := by
    exact
      coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_generator_domain_and_metric_germs
        D (u₀ : CoordinateBUCTensor E) Au₀ hu₀ gt bg anchor hz
        hfullGerm hbackgroundGerm hremainder
  exact
    exists_reconstructed_coordinateLocalDiffeomorphGerm_with_forwardRicciFlowAt
      D K u₀ Au₀ hu₀ μ hbackground hsolutionSymmetric hsmall
      gt bg anchor hy hχone phi J Phi x hphi₀ hPhi₀ hreg
      hidentifyInitial hidentifyRHS hbase hJ hJinv hPhiC1 hPhiD

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Point-local joint `C²` regularity of the concrete DeTurck coordinate field now
constructs all inverse-gauge ODE data consumed by the reconstructed solver.
At the initial time the endpoint map is the identity, so its local
diffeomorphism germ and derivative require no separate smooth-dependence
premise. -/
theorem exists_reconstructed_inverseDeTurckGauge_with_forwardRicciFlowAt_of_generator_domain_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      («E» := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (μ : ℝ)
    (hbackground : IsUniformlyPositiveCoordinateMetric μ D.background)
    (hsolutionSymmetric :
      ∀ t : Set.Icc (0 : ℝ)
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ),
        IsSymmetricCoordinateTensorCoefficient
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformSolution K u₀ t))
    (hsmall : ((K + 1 : ℝ≥0) : ℝ) < μ)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hreg : DeTurckVectorFieldRegularAt gt bg 0)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) z') =ᶠ[
            nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[
          nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background))
          (extChartAt I anchor y) v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0
            (extChartAt I anchor y) v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background)
            (extChartAt I anchor y) v w +
          coordinateMetricLaplacianValue D.background
            (extChartAt I anchor y) v w)
    (hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z))
      (0, extChartAt I anchor y)) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi 0 = extChartAt I anchor y ∧
        J 0 = ContinuousLinearMap.id ℝ E ∧
        ∃ G : CoordinateLocalDiffeomorphGerm
            (fun z : E ↦ z) (extChartAt I anchor y) (J 0),
          0 < A.uniformLifespan K ∧
            A.reconstructedMetricCoefficient K u₀
                (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
                  Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ)) =
              D.background + (u₀ : CoordinateBUCTensor E) ∧
            (∀ t : Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ),
              IsUniformlyPositiveCoordinateMetric
                (μ - ((K + 1 : ℝ≥0) : ℝ))
                (A.reconstructedMetricCoefficient K u₀ t)) ∧
            G.localHomeomorph (extChartAt I anchor y) =
                extChartAt I anchor y ∧
            reconstructedInverseGaugeMetric D K u₀ phi J 0 =
              pullbackBilinearForm
                (CovariantDerivative.chartMetric (gt 0).inner anchor
                  (extChartAt I anchor y))
                (G.tangentEquiv : E →L[ℝ] E) ∧
            IsPositiveDefiniteCoordinateBilinearForm
              (reconstructedInverseGaugeMetric D K u₀ phi J 0) ∧
            IsForwardCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric D K u₀ phi J)
              (pullbackCurvatureEnd G.tangentEquiv
                (chartRicciCurvatureEndAt (gt 0) anchor
                  (extChartAt I anchor y)
                  ((extChartAt I anchor).map_source hy)))
              (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  dsimp only
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  let s := Set.Icc 0 (A.uniformLifespan K : ℝ)
  have hWone : ContDiffAt ℝ 1 (Function.uncurry
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z))
      (0, extChartAt I anchor y) :=
    hW.of_le (by norm_num)
  have hDWone : ContDiffAt ℝ 1 (Function.uncurry
      (fun t z ↦ deTurckChartFieldDerivativeAt gt bg anchor t z))
      (0, extChartAt I anchor y) :=
    deTurckChartFieldDerivativeAt_jointContDiffAt_one_of_coordinateField_jointContDiffAt_two
      gt bg anchor 0 (extChartAt I anchor y) hW
  rcases exists_inverseDeTurckChartGauge_initial_variational_data
      gt bg anchor (extChartAt I anchor y) hWone hDWone s with
    ⟨phi, J, hphi₀, hJ₀, hphi, hJ, hJinv⟩
  have hfullGerm' :
      (fun z' ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) z') =ᶠ[nhds (phi 0)]
        CovariantDerivative.chartMetric (gt 0).inner anchor := by
    rw [hphi₀]
    exact hfullGerm
  have hbackgroundGerm' :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[nhds (phi 0)]
        CovariantDerivative.chartMetric bg.inner anchor := by
    rw [hphi₀]
    exact hbackgroundGerm
  have hremainder' : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) (phi 0) v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 (phi 0) v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background) (phi 0) v w +
          coordinateMetricLaplacianValue D.background (phi 0) v w := by
    intro v w
    rw [hphi₀]
    exact hremainder v w
  have hPhi₀ : (fun z : E ↦ z) (extChartAt I anchor y) = phi 0 := by
    exact hphi₀.symm
  have hPhiD : HasFDerivAt (fun z : E ↦ z) (J 0)
      (extChartAt I anchor y) := by
    rw [hJ₀]
    exact hasFDerivAt_id (x := extChartAt I anchor y)
  have hresult :=
    exists_reconstructed_coordinateLocalDiffeomorphGerm_with_forwardRicciFlowAt_of_generator_domain_and_metric_germs
      D K u₀ Au₀ hu₀ μ hbackground hsolutionSymmetric hsmall
      gt bg anchor hy hχone phi J (fun z : E ↦ z)
      (extChartAt I anchor y) hphi₀ hPhi₀ hreg
      hfullGerm' hbackgroundGerm' hremainder'
      (by simpa only [A, s] using hphi)
      (by simpa only [A, s] using hJ) hJinv contDiffAt_id hPhiD
  rcases hresult with
    ⟨G, hT, hzero, hpos, hG, hmetric, hpositive, hflow⟩
  refine ⟨phi, J, hphi₀, hJ₀, G, hT, hzero, hpos, ?_, ?_,
    hpositive, ?_⟩
  · simpa only [hphi₀] using hG
  · simpa only [hphi₀] using hmetric
  · have hzphi : phi 0 ∈ (extChartAt I anchor).target := by
      simpa only [hphi₀] using (extChartAt I anchor).map_source hy
    have hcurv :
        chartRicciCurvatureEndAt (gt 0) anchor (phi 0) hzphi =
          chartRicciCurvatureEndAt (gt 0) anchor
            (extChartAt I anchor y)
            ((extChartAt I anchor).map_source hy) := by
      exact chartRicciCurvatureEndAt_congr
        (gt 0) anchor hzphi ((extChartAt I anchor).map_source hy) hphi₀
    simpa only [hcurv] using hflow

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Joint `C³` metric-entry regularity centered at `y` supplies the joint
`C²` DeTurck coordinate-field regularity in any preferred chart containing
`y`.  Together with the unconditional time-slice regularity of the concrete
DeTurck field, this removes both analytic regularity premises from the
arbitrary-point inverse-gauge construction. -/
theorem exists_reconstructed_inverseDeTurckGauge_with_forwardRicciFlowAt_of_metricEntriesJointContDiffAt_of_mem_source
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      («E» := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (μ : ℝ)
    (hbackground : IsUniformlyPositiveCoordinateMetric μ D.background)
    (hsolutionSymmetric :
      ∀ t : Set.Icc (0 : ℝ)
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ),
        IsSymmetricCoordinateTensorCoefficient
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformSolution K u₀ t))
    (hsmall : ((K + 1 : ℝ≥0) : ℝ) < μ)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hJoint : MetricEntriesJointContDiffAt gt 0 y 3)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) z') =ᶠ[
            nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[
          nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background))
          (extChartAt I anchor y) v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0
            (extChartAt I anchor y) v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background)
            (extChartAt I anchor y) v w +
          coordinateMetricLaplacianValue D.background
            (extChartAt I anchor y) v w) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi 0 = extChartAt I anchor y ∧
        J 0 = ContinuousLinearMap.id ℝ E ∧
        ∃ G : CoordinateLocalDiffeomorphGerm
            (fun z : E ↦ z) (extChartAt I anchor y) (J 0),
          0 < A.uniformLifespan K ∧
            A.reconstructedMetricCoefficient K u₀
                (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
                  Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ)) =
              D.background + (u₀ : CoordinateBUCTensor E) ∧
            (∀ t : Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ),
              IsUniformlyPositiveCoordinateMetric
                (μ - ((K + 1 : ℝ≥0) : ℝ))
                (A.reconstructedMetricCoefficient K u₀ t)) ∧
            G.localHomeomorph (extChartAt I anchor y) =
                extChartAt I anchor y ∧
            reconstructedInverseGaugeMetric D K u₀ phi J 0 =
              pullbackBilinearForm
                (CovariantDerivative.chartMetric (gt 0).inner anchor
                  (extChartAt I anchor y))
                (G.tangentEquiv : E →L[ℝ] E) ∧
            IsPositiveDefiniteCoordinateBilinearForm
              (reconstructedInverseGaugeMetric D K u₀ phi J 0) ∧
            IsForwardCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric D K u₀ phi J)
              (pullbackCurvatureEnd G.tangentEquiv
                (chartRicciCurvatureEndAt (gt 0) anchor
                  (extChartAt I anchor y)
                  ((extChartAt I anchor).map_source hy)))
              (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  have hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z))
      (0, extChartAt I anchor y) :=
    DeTurckCoordinateJointRegularityOverlap.deTurckChartCoordinateField_jointContDiffAt_two_of_metricEntries_of_mem_source
      (gt := gt) (bg := bg) (t₀ := 0) (anchor := anchor) (y := y) hy hJoint
  exact
    exists_reconstructed_inverseDeTurckGauge_with_forwardRicciFlowAt_of_generator_domain_and_metric_germs
      D K u₀ Au₀ hu₀ μ hbackground hsolutionSymmetric hsmall
      gt bg anchor (y := y) hy hχone
      (deTurckVectorFieldRegularAt_holds gt bg 0)
      hfullGerm hbackgroundGerm hremainder hW

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- At the preferred-chart anchor, joint `C³` metric-entry regularity supplies
all DeTurck-field regularity needed by the inverse-gauge construction.
Consequently neither the time-slice `DeTurckVectorFieldRegularAt` package nor
the coordinate-field joint `C²` premise is required at this entry point. -/
theorem exists_reconstructed_inverseDeTurckGauge_with_forwardRicciFlowAt_of_metricEntriesJointContDiffAt
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      («E» := E) (F := CoordinateTwoTensor E)
      (u₀ : CoordinateBUCTensor E) Au₀)
    (μ : ℝ)
    (hbackground : IsUniformlyPositiveCoordinateMetric μ D.background)
    (hsolutionSymmetric :
      ∀ t : Set.Icc (0 : ℝ)
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ),
        IsSymmetricCoordinateTensorCoefficient
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformSolution K u₀ t))
    (hsmall : ((K + 1 : ℝ≥0) : ℝ) < μ)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M)
    (hJoint : MetricEntriesJointContDiffAt gt 0 anchor 3)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) z') =ᶠ[
            nhds (extChartAt I anchor anchor)]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[
          nhds (extChartAt I anchor anchor)]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background))
          (extChartAt I anchor anchor) v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0
            (extChartAt I anchor anchor) v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background)
            (extChartAt I anchor anchor) v w +
          coordinateMetricLaplacianValue D.background
            (extChartAt I anchor anchor) v w) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi 0 = extChartAt I anchor anchor ∧
        J 0 = ContinuousLinearMap.id ℝ E ∧
        ∃ G : CoordinateLocalDiffeomorphGerm
            (fun z : E ↦ z) (extChartAt I anchor anchor) (J 0),
          0 < A.uniformLifespan K ∧
            A.reconstructedMetricCoefficient K u₀
                (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
                  Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ)) =
              D.background + (u₀ : CoordinateBUCTensor E) ∧
            (∀ t : Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ),
              IsUniformlyPositiveCoordinateMetric
                (μ - ((K + 1 : ℝ≥0) : ℝ))
                (A.reconstructedMetricCoefficient K u₀ t)) ∧
            G.localHomeomorph (extChartAt I anchor anchor) =
                extChartAt I anchor anchor ∧
            reconstructedInverseGaugeMetric D K u₀ phi J 0 =
              pullbackBilinearForm
                (CovariantDerivative.chartMetric (gt 0).inner anchor
                  (extChartAt I anchor anchor))
                (G.tangentEquiv : E →L[ℝ] E) ∧
            IsPositiveDefiniteCoordinateBilinearForm
              (reconstructedInverseGaugeMetric D K u₀ phi J 0) ∧
            IsForwardCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric D K u₀ phi J)
              (pullbackCurvatureEnd G.tangentEquiv
                (chartRicciCurvatureEndAt (gt 0) anchor
                  (extChartAt I anchor anchor)
                  ((extChartAt I anchor).map_source
                    (mem_extChartAt_source anchor))))
              (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  have hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun t z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg t) z))
      (0, extChartAt I anchor anchor) :=
    DeTurckCoordinateJointRegularity.deTurckChartCoordinateField_jointContDiffAt_two_of_metricEntries
      (bg := bg) hJoint
  exact
    exists_reconstructed_inverseDeTurckGauge_with_forwardRicciFlowAt_of_generator_domain_and_metric_germs
      D K u₀ Au₀ hu₀ μ hbackground hsolutionSymmetric hsmall
      gt bg anchor (y := anchor) (mem_extChartAt_source anchor)
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) anchor)
      (deTurckVectorFieldRegularAt_holds gt bg 0)
      hfullGerm hbackgroundGerm hremainder hW

end ReconstructedLocalRicciEvolution

end Poincare
