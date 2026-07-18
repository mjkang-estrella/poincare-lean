import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowTimeVariationalAssembly

/-!
# Local inverse-flow data supplies differential invertibility

A differentiable two-sided local inverse germ has inverse Frechet
derivatives.  This turns genuine forward/backward point-flow data into the
`ContinuousLinearMap.IsInvertible` witness used by the inverse-gauge metric
assembly, without retaining a separate algebraic invertibility premise.
-/

noncomputable section

open Bundle FiberBundle Filter Function
open scoped Manifold ContDiff NNReal Topology

universe u v

namespace Poincare

section TwoSidedInverseGermDifferential

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Frechet derivative of a `C^1` map is a continuous linear
equivalence when the map has a `C^1` two-sided local inverse germ.

The proof differentiates the two inverse identities.  It does not use finite
dimensionality. -/
theorem fderiv_isInvertible_of_contDiffAt_one_twoSidedInverseGerm
    (f : E → F) (g : F → E) (x : E)
    (hf : ContDiffAt ℝ 1 f x)
    (hg : ContDiffAt ℝ 1 g (f x))
    (hleft : (fun q ↦ g (f q)) =ᶠ[nhds x] (fun q ↦ q))
    (hright : (fun q ↦ f (g q)) =ᶠ[nhds (f x)] (fun q ↦ q)) :
    (fderiv ℝ f x).IsInvertible := by
  let Df : E →L[ℝ] F := fderiv ℝ f x
  let Dg : F →L[ℝ] E := fderiv ℝ g (f x)
  have hfd : HasFDerivAt f Df x := by
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hgd : HasFDerivAt g Dg (f x) := by
    exact (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hleftValue : g (f x) = x := hleft.self_of_nhds
  have hleftLinear : Dg.comp Df = ContinuousLinearMap.id ℝ E := by
    calc
      Dg.comp Df = fderiv ℝ (fun q ↦ g (f q)) x :=
        (hgd.comp x hfd).fderiv.symm
      _ = fderiv ℝ (fun q : E ↦ q) x := hleft.fderiv_eq
      _ = ContinuousLinearMap.id ℝ E := (hasFDerivAt_id x).fderiv
  have hfdAtImage : HasFDerivAt f Df (g (f x)) := by
    simpa only [hleftValue] using hfd
  have hrightLinear : Df.comp Dg = ContinuousLinearMap.id ℝ F := by
    calc
      Df.comp Dg = fderiv ℝ (fun q ↦ f (g q)) (f x) :=
        (hfdAtImage.comp (f x) hgd).fderiv.symm
      _ = fderiv ℝ (fun q : F ↦ q) (f x) := hright.fderiv_eq
      _ = ContinuousLinearMap.id ℝ F := (hasFDerivAt_id (f x)).fderiv
  have hrightLinearMap :
      Df.toLinearMap.comp Dg.toLinearMap = LinearMap.id := by
    ext w
    have hw := congrArg (fun L : F →L[ℝ] F ↦ L w) hrightLinear
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hw
  have hleftLinearMap :
      Dg.toLinearMap.comp Df.toLinearMap = LinearMap.id := by
    ext z
    have hz := congrArg (fun L : E →L[ℝ] E ↦ L z) hleftLinear
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hz
  let e : E ≃L[ℝ] F :=
    { toLinearEquiv := LinearEquiv.ofLinear
        Df.toLinearMap Dg.toLinearMap hrightLinearMap hleftLinearMap
      continuous_toFun := Df.continuous
      continuous_invFun := Dg.continuous }
  refine ⟨e, ?_⟩
  ext z
  rfl

end TwoSidedInverseGermDifferential

section LocalInverseSuppliedFlowAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supplied physical-flow assembly where a genuine differentiable backward
endpoint germ makes the canonical forward spatial differential invertible.

`Psi` is the backward endpoint map at the selected physical time.  The two
germ identities are the local flow inverse laws at the source and target
coordinates. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_localInverseGerms
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
    (hPhiJointC3 : ContDiffAt ℝ 3
      (Function.uncurry (Phi anchor))
      (t, extChartAt I anchor y₀))
    (hPhiODEGerm :
      (fun q ↦ deriv (fun s ↦ Phi anchor s q) t) =ᶠ[
          nhds (extChartAt I anchor y₀)]
        (fun q ↦ inverseDeTurckChartCoordinateField
          gt bg anchor t (Phi anchor t q)))
    (Psi : E → E)
    (hPsiC1 : ContDiffAt ℝ 1 Psi (extChartAt I anchor y₁))
    (hleft :
      (fun q ↦ Psi (Phi anchor t q)) =ᶠ[
          nhds (extChartAt I anchor y₀)] (fun q ↦ q))
    (hright :
      (fun q ↦ Phi anchor t (Psi q)) =ᶠ[
          nhds (extChartAt I anchor y₁)] (fun q ↦ q))
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi (suppliedPhysicalPointFlowSpatialDifferential Phi)
            s anchor z) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  let z₀ : E := extChartAt I anchor y₀
  have hPhiC1 : ContDiffAt ℝ 1 (Phi anchor t) z₀ := by
    have hpath : ContDiffAt ℝ 1 (fun q : E ↦ (t, q)) z₀ :=
      contDiffAt_const.prodMk contDiffAt_id
    simpa only [Function.uncurry] using
      (hPhiJointC3.of_le (by norm_num)).comp z₀ hpath
  have hPsiC1' : ContDiffAt ℝ 1 Psi (Phi anchor t z₀) := by
    simpa only [z₀, hendpoint] using hPsiC1
  have hright' :
      (fun q ↦ Phi anchor t (Psi q)) =ᶠ[
        nhds (Phi anchor t z₀)] (fun q ↦ q) := by
    simpa only [z₀, hendpoint] using hright
  have hDPhiInv :
      (suppliedPhysicalPointFlowSpatialDifferential
        Phi anchor t z₀).IsInvertible := by
    simpa only [suppliedPhysicalPointFlowSpatialDifferential] using
      fderiv_isInvertible_of_contDiffAt_one_twoSidedInverseGerm
        (Phi anchor t) Psi z₀ hPhiC1 hPsiC1' hleft hright'
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_jointC3_ODEGerm
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
        hendpoint hfullGerm hidentifyRHS hPhiJointC3 hPhiODEGerm
        hDPhiInv hrealize

end LocalInverseSuppliedFlowAssembly

end Poincare
