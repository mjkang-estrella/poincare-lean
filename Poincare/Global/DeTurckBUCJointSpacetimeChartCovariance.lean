import Poincare.Global.DeTurckBUCJointSpacetimeMetricAssembly

/-!
# Chart covariance of reconstructed inverse-gauge spacetime coefficients

The endpoint maps of inverse DeTurck flows agree across a preferred-chart
overlap.  Differentiating that germ conjugates their spatial differentials.
This file feeds the conjugacy into the bilinear pullback and reduces covariance
of the reconstructed inverse-gauge metric to covariance of the underlying
reconstructed coordinate coefficient.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The fixed-point (non-background) summand of the projected reconstructed
coordinate metric path. -/
def reconstructedCoordinateSolutionPath
    {ι κ : Type*}
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (t : ℝ) : CoordinateBUCTensor E :=
  let A := AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  A.uniformSolution K u₀
    (Set.projIcc 0 (A.uniformLifespan K : ℝ)
      (A.uniformLifespan K).property t)

/-- Covariance of the background and fixed-point summands separately implies
covariance of the full reconstructed coordinate coefficient. -/
theorem reconstructedCoordinateMetricPath_value_eq_of_backgroundAndSolution
    {ι₁ κ₁ ι₂ κ₂ : Type*}
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι₁ κ₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι₂ κ₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₂)
    (t : ℝ) (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (hbackground : coordinateMetricValue D₂.background x₂ v₂ w₂ =
      coordinateMetricValue D₁.background x₁ v₁ w₁)
    (hsolution : coordinateMetricValue
        (reconstructedCoordinateSolutionPath D₂ K₂ u₀₂ t) x₂ v₂ w₂ =
      coordinateMetricValue
        (reconstructedCoordinateSolutionPath D₁ K₁ u₀₁ t) x₁ v₁ w₁) :
    coordinateMetricValue (reconstructedCoordinateMetricPath D₂ K₂ u₀₂ t)
        x₂ v₂ w₂ =
      coordinateMetricValue (reconstructedCoordinateMetricPath D₁ K₁ u₀₁ t)
        x₁ v₁ w₁ := by
  let A₁ :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁
  let A₂ :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂
  change coordinateMetricValue
      (A₂.reconstructedMetricCoefficient K₂ u₀₂
        (Set.projIcc 0 (A₂.uniformLifespan K₂ : ℝ)
          (A₂.uniformLifespan K₂).property t)) x₂ v₂ w₂ =
    coordinateMetricValue
      (A₁.reconstructedMetricCoefficient K₁ u₀₁
        (Set.projIcc 0 (A₁.uniformLifespan K₁ : ℝ)
          (A₁.uniformLifespan K₁).property t)) x₁ v₁ w₁
  apply reconstructedMetricValue_eq_of_background_and_solution
    A₁ A₂ K₁ K₂ u₀₁ u₀₂
    (Set.projIcc 0 (A₁.uniformLifespan K₁ : ℝ)
      (A₁.uniformLifespan K₁).property t)
    (Set.projIcc 0 (A₂.uniformLifespan K₂ : ℝ)
      (A₂.uniformLifespan K₂).property t)
    x₁ x₂ v₁ w₁ v₂ w₂ hbackground
  simpa only [reconstructedCoordinateSolutionPath, A₁, A₂] using hsolution

/--
Pointwise covariance of the reconstructed inverse-gauge pullback.  Endpoint
compatibility supplies the derivative conjugacy automatically, so the only
coefficient input is covariance of the reconstructed coordinate metric at the
flow endpoint.
-/
theorem reconstructedInverseGaugeMetricSpacetime_chartTransition_eq_of_endpointGerm
    {ι₁ κ₁ ι₂ κ₂ : Type*}
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι₁ κ₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι₂ κ₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₁)
    (u₀₂ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K₂)
    (Phi₁ Phi₂ : ℝ → E → E)
    (DPhi₁ DPhi₂ : ℝ → E → E →L[ℝ] E)
    (anchor₁ anchor₂ : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (hz' : Phi₁ t z ∈ (extChartAt I anchor₁).target)
    (hy' : (extChartAt I anchor₁).symm (Phi₁ t z) ∈
      (extChartAt I anchor₂).source)
    (hPhi₁ : HasFDerivAt (Phi₁ t) (DPhi₁ t z) z)
    (hPhi₂ : HasFDerivAt (Phi₂ t)
      (DPhi₂ t (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
      (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
    (hcompat :
      (Phi₂ t ∘ GeodesicTransport.chartTransition anchor₁ anchor₂) =ᶠ[nhds z]
        (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘ Phi₁ t))
    (hcoefficient : ∀ a b : E,
      coordinateMetricValue (reconstructedCoordinateMetricPath D₂ K₂ u₀₂ t)
          (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ t z))
          (GeodesicTransport.chartTransitionDeriv
            anchor₁ anchor₂ (Phi₁ t z) a)
          (GeodesicTransport.chartTransitionDeriv
            anchor₁ anchor₂ (Phi₁ t z) b) =
        coordinateMetricValue (reconstructedCoordinateMetricPath D₁ K₁ u₀₁ t)
          (Phi₁ t z) a b)
    (u v : E) :
    reconstructedInverseGaugeMetricSpacetime D₂ K₂ u₀₂ Phi₂ DPhi₂
        (t, GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
      reconstructedInverseGaugeMetricSpacetime D₁ K₁ u₀₁ Phi₁ DPhi₁
        (t, z) u v := by
  have hoverlap :
      z ∈ ((extChartAt I anchor₁).symm ≫ extChartAt I anchor₂).source := by
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using
      And.intro hz hy
  have hoverlap' :
      Phi₁ t z ∈
        ((extChartAt I anchor₁).symm ≫ extChartAt I anchor₂).source := by
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using
      And.intro hz' hy'
  have hconj := chartTransition_flow_fderiv_conjugacy
    anchor₁ anchor₂
    (chartTransition_differentiableAt_of_mem_source
      anchor₁ anchor₂ hoverlap)
    hPhi₁ hPhi₂
    (chartTransition_differentiableAt_of_mem_source
      anchor₁ anchor₂ hoverlap')
    hcompat
  have hendpoint := hcompat.self_of_nhds
  change Phi₂ t (GeodesicTransport.chartTransition anchor₁ anchor₂ z) =
    GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ t z) at hendpoint
  have hconj_apply (w : E) :
      DPhi₂ t (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w) =
        GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ (Phi₁ t z)
          (DPhi₁ t z w) := by
    have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hconj
    simpa only [ContinuousLinearMap.comp_apply] using hw
  change coordinateMetricValue (reconstructedCoordinateMetricPath D₂ K₂ u₀₂ t)
      (Phi₂ t (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
      (DPhi₂ t (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u))
      (DPhi₂ t (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)) =
    coordinateMetricValue (reconstructedCoordinateMetricPath D₁ K₁ u₀₁ t)
      (Phi₁ t z) (DPhi₁ t z u) (DPhi₁ t z v)
  rw [hendpoint, hconj_apply u, hconj_apply v]
  exact hcoefficient (DPhi₁ t z u) (DPhi₁ t z v)

/--
Family-level form of
`reconstructedInverseGaugeMetricSpacetime_chartTransition_eq_of_endpointGerm`.
Its conclusion is exactly the `hcov` premise of
`exists_closedSmoothRiemannianMetricFamily_realizing_chartwiseReconstruction`.
The endpoint derivative conjugacy is not an input: it is derived from the
displayed endpoint-map germs.
-/
theorem chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms
    {ι κ : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
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
    (hcoefficient : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ a b : E,
        coordinateMetricValue
            (reconstructedCoordinateMetricPath
              (D anchor₂) K (u₀ anchor₂) t)
            (GeodesicTransport.chartTransition anchor₁ anchor₂
              (Phi anchor₁ t z))
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) b) =
          coordinateMetricValue
            (reconstructedCoordinateMetricPath
              (D anchor₁) K (u₀ anchor₁) t)
            (Phi anchor₁ t z) a b) :
    ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ u v : E,
        chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₁ z u v := by
  intro t anchor₁ anchor₂ z hz hy u v
  exact reconstructedInverseGaugeMetricSpacetime_chartTransition_eq_of_endpointGerm
    (D anchor₁) (D anchor₂) K K (u₀ anchor₁) (u₀ anchor₂)
    (Phi anchor₁) (Phi anchor₂) (DPhi anchor₁) (DPhi anchor₂)
    anchor₁ anchor₂ t hz hy
    (hendpointTarget t anchor₁ anchor₂ z hz hy)
    (hendpointSource t anchor₁ anchor₂ z hz hy)
    (hPhi t anchor₁ z)
    (hPhi t anchor₂
      (GeodesicTransport.chartTransition anchor₁ anchor₂ z))
    (hcompat t anchor₁ anchor₂ z hz hy)
    (hcoefficient t anchor₁ anchor₂ z hz hy) u v

/--
The full chartwise covariance premise follows from endpoint-map germs plus
separate covariance of the background and fixed-point solution summands.  The
sum is assembled by `reconstructedMetricValue_eq_of_background_and_solution`;
no covariance of the already-summed coefficient is assumed.
-/
theorem chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_and_backgroundSolution
    {ι κ : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
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
    (hsolution : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ a b : E,
        coordinateMetricValue
            (reconstructedCoordinateSolutionPath
              (D anchor₂) K (u₀ anchor₂) t)
            (GeodesicTransport.chartTransition anchor₁ anchor₂
              (Phi anchor₁ t z))
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) b) =
          coordinateMetricValue
            (reconstructedCoordinateSolutionPath
              (D anchor₁) K (u₀ anchor₁) t)
            (Phi anchor₁ t z) a b) :
    ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ u v : E,
        chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₁ z u v := by
  apply chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms
    D K u₀ Phi DPhi hPhi hendpointTarget hendpointSource hcompat
  intro t anchor₁ anchor₂ z hz hy a b
  exact reconstructedCoordinateMetricPath_value_eq_of_backgroundAndSolution
    (D anchor₁) (D anchor₂) K K (u₀ anchor₁) (u₀ anchor₂) t
    (Phi anchor₁ t z)
    (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi anchor₁ t z))
    a b
    (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
      (Phi anchor₁ t z) a)
    (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
      (Phi anchor₁ t z) b)
    (hbackground t anchor₁ anchor₂ z hz hy a b)
    (hsolution t anchor₁ anchor₂ z hz hy a b)

end Poincare
