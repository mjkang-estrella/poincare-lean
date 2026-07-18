import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowChristoffelRegularityAssembly

/-!
# Automatic spatial regularity in supplied physical-flow assembly

For a supplied point flow, its spatial differential and spatial second
differential are canonically the first two Frechet derivatives.  Local `C^3`
regularity of the fixed-time endpoint map supplies all derivative premises and
both Schwarz symmetries required by curvature naturality.  Invertibility only
has to be known at the base point: continuity of the differential and openness
of the continuous-linear-equivalence locus propagate it to a neighborhood.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

section ThirdDerivativeSymmetry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The two outer differentiation slots of a local third Frechet derivative
commute. -/
theorem fderiv_third_outer_symm_of_contDiffAt_three
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) (a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x b a c := by
  have hDf : ContDiffAt ℝ 2 (fderiv ℝ f) x :=
    hf.fderiv_right (m := 2) (by norm_num)
  have hsymm := (hDf.isSymmSndFDerivAt (by norm_num)).eq a b
  exact DFunLike.congr_fun hsymm c

/-- The two evaluation slots of a local third Frechet derivative commute.

The Hessian is symmetric throughout a neighborhood supplied by local `C^3`
regularity.  Differentiating that germ equality gives the claimed third-order
symmetry at the base point. -/
theorem fderiv_third_inner_symm_of_contDiffAt_three
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) (a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a c b := by
  have hDtwo : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heval (p q d : E) :
      fderiv ℝ (fun y ↦ fderiv ℝ (fderiv ℝ f) y p q) x d =
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x d p q := by
    have hev : HasFDerivAt
        (fun y ↦ fderiv ℝ (fderiv ℝ f) y p q) _ x :=
      (hDtwo.hasFDerivAt.clm_apply (hasFDerivAt_const p x)).clm_apply
        (hasFDerivAt_const q x)
    rw [hev.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add]
  have hfTwoNear : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y :=
    (hf.of_le (by norm_num)).eventually (by norm_num)
  have hHessianSymm :
      (fun y ↦ fderiv ℝ (fderiv ℝ f) y b c) =ᶠ[nhds x]
        (fun y ↦ fderiv ℝ (fderiv ℝ f) y c b) := by
    filter_upwards [hfTwoNear] with y hy
    exact (hy.isSymmSndFDerivAt (by norm_num)).eq b c
  rw [← heval b c a, ← heval c b a, hHessianSymm.fderiv_eq]

/-- Full third-order Schwarz symmetry in the first and last displayed slots,
obtained from the two adjacent transpositions above. -/
theorem fderiv_third_first_last_symm_of_contDiffAt_three
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) (a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x c b a := by
  calc
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c =
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x b a c :=
      fderiv_third_outer_symm_of_contDiffAt_three hf a b c
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x b c a :=
      fderiv_third_inner_symm_of_contDiffAt_three hf b a c
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x c b a :=
      fderiv_third_outer_symm_of_contDiffAt_three hf b c a

end ThirdDerivativeSymmetry

section CanonicalSpatialDifferentials

variable {n : ℕ} {M : Type u}

local notation "E" => ClosedSmoothModel n

/-- The canonical spatial differential of a supplied point flow. -/
def suppliedPhysicalPointFlowSpatialDifferential
    (Phi : M → ℝ → E → E) : M → ℝ → E → E →L[ℝ] E :=
  fun anchor t z ↦ fderiv ℝ (Phi anchor t) z

/-- The canonical spatial second differential of a supplied point flow. -/
def suppliedPhysicalPointFlowSpatialSecondDifferential
    (Phi : M → ℝ → E → E) (anchor : M) (t : ℝ) :
    E → E →L[ℝ] E →L[ℝ] E :=
  fun z ↦ fderiv ℝ
    (suppliedPhysicalPointFlowSpatialDifferential Phi anchor t) z

end CanonicalSpatialDifferentials

section AutomaticSpatialRegularitySuppliedFlowAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supplied physical-flow assembly with all fixed-time spatial derivative,
symmetry, and nearby-invertibility premises generated from local `C^3`
regularity and invertibility at the base point. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_spatialC3
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y₀ y₁ : M} {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor)).uniformLifespan K : ℝ))
    (hy₀ : y₀ ∈ (extChartAt I anchor).source)
    (hy₁ : y₁ ∈ (extChartAt I anchor).source)
    (hχ₀ : ∀ᶠ z' in nhds (extChartAt I anchor y₀),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hχ₁ : ∀ᶠ z' in nhds (extChartAt I anchor y₁),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hendpoint :
      Phi anchor t (extChartAt I anchor y₀) = extChartAt I anchor y₁)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath
            (D anchor) K (u₀ anchor) t) z') =ᶠ[
            nhds (Phi anchor t (extChartAt I anchor y₀))]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hidentifyRHS :
      coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
              (D anchor)).uniformInteriorGeneratorValue K (u₀ anchor) t +
            (D anchor).base.nonlinearity
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
                  (D anchor)).uniformInteriorState K (u₀ anchor) t +
                (D anchor).background))
          (Phi anchor t (extChartAt I anchor y₀)) =
        deTurckChartMetricEvolutionBilin gt bg anchor t
          (Phi anchor t (extChartAt I anchor y₀)))
    (hPhiTime : HasDerivAt
      (fun s : ℝ ↦ Phi anchor s (extChartAt I anchor y₀))
      (inverseDeTurckChartCoordinateField gt bg anchor t
        (Phi anchor t (extChartAt I anchor y₀))) t)
    (hDPhiTime : HasDerivAt
      (fun s : ℝ ↦ suppliedPhysicalPointFlowSpatialDifferential
        Phi anchor s (extChartAt I anchor y₀))
      (-(deTurckChartFieldDerivativeAt gt bg anchor t
          (Phi anchor t (extChartAt I anchor y₀))).comp
        (suppliedPhysicalPointFlowSpatialDifferential
          Phi anchor t (extChartAt I anchor y₀))) t)
    (hPhiSpatialC3 : ContDiffAt ℝ 3 (Phi anchor t)
      (extChartAt I anchor y₀))
    (hDPhiInv :
      (suppliedPhysicalPointFlowSpatialDifferential
        Phi anchor t (extChartAt I anchor y₀)).IsInvertible)
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi (suppliedPhysicalPointFlowSpatialDifferential Phi)
            s anchor z) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  let z₀ : E := extChartAt I anchor y₀
  let DPhi := suppliedPhysicalPointFlowSpatialDifferential Phi
  let B : E → E →L[ℝ] E →L[ℝ] E :=
    suppliedPhysicalPointFlowSpatialSecondDifferential Phi anchor t
  have hPhiC1 : ContDiffAt ℝ 1 (Phi anchor t) z₀ :=
    hPhiSpatialC3.of_le (by norm_num)
  have hC3Near : ∀ᶠ q in nhds z₀, ContDiffAt ℝ 3 (Phi anchor t) q :=
    hPhiSpatialC3.eventually (by norm_num)
  have hPhiSpaceNear : ∀ᶠ q in nhds z₀,
      HasFDerivAt (Phi anchor t) (DPhi anchor t q) q := by
    filter_upwards [hC3Near] with q hq
    simpa only [DPhi, suppliedPhysicalPointFlowSpatialDifferential] using
      (hq.differentiableAt (by norm_num)).hasFDerivAt
  have hDPhiSpaceNear : ∀ᶠ q in nhds z₀,
      HasFDerivAt (DPhi anchor t) (B q) q := by
    filter_upwards [hC3Near] with q hq
    have hD : ContDiffAt ℝ 2 (fderiv ℝ (Phi anchor t)) q :=
      hq.fderiv_right (m := 2) (by norm_num)
    simpa only [DPhi, B, suppliedPhysicalPointFlowSpatialDifferential,
      suppliedPhysicalPointFlowSpatialSecondDifferential] using
        (hD.differentiableAt (by norm_num)).hasFDerivAt
  have hBSpace : HasFDerivAt B (fderiv ℝ B z₀) z₀ := by
    have hB : ContDiffAt ℝ 1
        (fderiv ℝ (fderiv ℝ (Phi anchor t))) z₀ :=
      (hPhiSpatialC3.fderiv_right (m := 2) (by norm_num)).fderiv_right
        (m := 1) (by norm_num)
    simpa only [DPhi, B, suppliedPhysicalPointFlowSpatialDifferential,
      suppliedPhysicalPointFlowSpatialSecondDifferential] using
        (hB.differentiableAt (by norm_num)).hasFDerivAt
  have hDPhiInvNear : ∀ᶠ q in nhds z₀,
      (DPhi anchor t q).IsInvertible := by
    have hDPhiContinuous : ContinuousAt (DPhi anchor t) z₀ := by
      simpa only [DPhi, suppliedPhysicalPointFlowSpatialDifferential] using
        (hPhiSpatialC3.fderiv_right (m := 2) (by norm_num)).continuousAt
    rcases hDPhiInv with ⟨e, he⟩
    have hopen :
        Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) ∈
          nhds (DPhi anchor t z₀) := by
      rw [show DPhi anchor t z₀ = (e : E →L[ℝ] E) by
        simpa only [DPhi, z₀,
          suppliedPhysicalPointFlowSpatialDifferential] using he.symm]
      exact ContinuousLinearEquiv.nhds e
    filter_upwards [hDPhiContinuous hopen] with q hq
    rcases hq with ⟨eqv, heqv⟩
    exact ⟨eqv, heqv⟩
  have hBsymmNear : ∀ᶠ q in nhds z₀,
      ∀ a b : E, (B q a) b = (B q b) a := by
    filter_upwards [hC3Near] with q hq
    intro a b
    simpa only [B, suppliedPhysicalPointFlowSpatialSecondDifferential,
      suppliedPhysicalPointFlowSpatialDifferential] using
        (hq.isSymmSndFDerivAt (by norm_num)).eq a b
  have hCsymm : ∀ a b c : E,
      ((fderiv ℝ B z₀ a) b) c = ((fderiv ℝ B z₀ c) b) a := by
    intro a b c
    simpa only [B, suppliedPhysicalPointFlowSpatialSecondDifferential,
      suppliedPhysicalPointFlowSpatialDifferential] using
        fderiv_third_first_last_symm_of_contDiffAt_three
          hPhiSpatialC3 a b c
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_automaticChristoffelRegularity
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi DPhi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
        hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime hPhiC1 hrealize
        B hPhiSpaceNear hDPhiSpaceNear hBSpace hDPhiInvNear hBsymmNear hCsymm

end AutomaticSpatialRegularitySuppliedFlowAssembly

end Poincare
