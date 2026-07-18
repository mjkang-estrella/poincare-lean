import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowInteriorAssembly
import Poincare.Global.LCNaturality
import Poincare.Global.MetricFlowJointScalarTraceZoneBridge

/-!
# Curvature locality for an exactly realized inverse-gauge metric

Exact chartwise realization and the source metric germ imply a genuine local
metric-pullback identity for the supplied endpoint map.  Differentiating that
identity gives the signed Christoffel transition law through the existing
Levi-Civita naturality theorem.

The remaining curvature calculation is isolated below as a first-jet
Christoffel naturality lemma.  Its hypotheses are precisely the value and
first spatial derivative of the signed Christoffel transition; the second- and
third-derivative correction terms cancel by symmetry.  The final theorem
turns this chart-curvature intertwining into equality of the actual
`chartRicciCurvatureEndAt` pullback tensor, before taking any trace.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

section ExactRealizationPullbackGerm

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

/-- Exact chartwise realization, restricted through the source coefficient
germ, is the honest spatial metric-pullback germ for the supplied endpoint map
and variational differential. -/
theorem pullback_chartMetric_eventuallyEq_chartMetric_of_chartwiseRealization_and_sourceGerm
    (rt gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (R : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (anchor : M) (t : ℝ) {z₀ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hPhi : ContinuousAt (Phi anchor t) z₀)
    (hrealize : ∀ z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt t).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          R K u₀ Phi DPhi t anchor z)
    (hsource :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath
            (R anchor) K (u₀ anchor) t) z') =ᶠ[
              nhds (Phi anchor t z₀)]
        CovariantDerivative.chartMetric (gt t).inner anchor) :
    (fun z ↦ pullbackBilinearForm
        (CovariantDerivative.chartMetric (gt t).inner anchor
          (Phi anchor t z))
        (DPhi anchor t z)) =ᶠ[nhds z₀]
      CovariantDerivative.chartMetric (rt t).inner anchor := by
  have htarget : (extChartAt I anchor).target ∈ nhds z₀ :=
    (isOpen_extChartAt_target anchor).mem_nhds hz₀
  have hsourceBase :
      (fun z ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath
            (R anchor) K (u₀ anchor) t)
          (Phi anchor t z)) =ᶠ[nhds z₀]
        (fun z ↦ CovariantDerivative.chartMetric
          (gt t).inner anchor (Phi anchor t z)) :=
    hsource.comp_tendsto hPhi
  filter_upwards [htarget, hsourceBase] with z hz hsourceZ
  rw [hrealize z hz]
  simp only [chartwiseReconstructedInverseGaugeMetricSpacetime,
    reconstructedInverseGaugeMetricSpacetime]
  rw [hsourceZ]

end ExactRealizationPullbackGerm

section ChristoffelFromPullbackGerm

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- A metric-pullback germ gives the signed Christoffel transition law at its
base point.  This composes the existing pullback differentiation theorem with
the existing Levi-Civita uniqueness/naturality theorem. -/
theorem christoffelAt_map_eq_signed_transport_of_metricPullbackGerm
    (G₀ G₁ : E → E →L[ℝ] E →L[ℝ] ℝ)
    (F : E → E) (D : E → E →L[ℝ] E) {z : E}
    (hF : HasFDerivAt F (D z) z)
    (hD : HasFDerivAt D (fderiv ℝ D z) z)
    (hG₀ : HasFDerivAt G₀ (fderiv ℝ G₀ z) z)
    (hG₁ : HasFDerivAt G₁ (fderiv ℝ G₁ (F z)) (F z))
    (hpull : ∀ a b : E,
      (fun q : E ↦ G₁ (F q) (D q a) (D q b)) =ᶠ[nhds z]
        (fun q : E ↦ G₀ q a b))
    (hDinv : (D z).IsInvertible)
    (hD2symm : ∀ a b : E,
      (fderiv ℝ D z a) b = (fderiv ℝ D z b) a)
    (hG₁symm : ∀ a b : E, G₁ (F z) a b = G₁ (F z) b a)
    (b₀ b₁ : LinearMap.BilinForm ℝ E)
    (hb₀ : b₀.Nondegenerate) (hb₁ : b₁.Nondegenerate)
    (hb₀G : ∀ a b : E, b₀ a b = G₀ z a b)
    (hb₁G : ∀ a b : E, b₁ a b = G₁ (F z) a b)
    (u v : E) :
    CovariantDerivative.christoffelAt G₁ (F z) b₁ hb₁
        (D z v) (D z u) =
      D z (CovariantDerivative.christoffelAt G₀ z b₀ hb₀ v u) -
        (fderiv ℝ D z u) v := by
  have hdiff :=
    GeodesicTransport.differentiated_pullback_hdiff_of_eventuallyEq
      G₀ G₁ F D hF hD hG₀ hG₁ hpull
  have hpullAt : ∀ a b : E,
      G₁ (F z) (D z a) (D z b) = G₀ z a b := by
    intro a b
    exact (hpull a b).self_of_nhds
  exact
    GeodesicTransport.christoffelAt_map_eq_signed_transport_of_differentiated_pullback
      G₀ G₁ F D hDinv hD2symm hdiff
        hpullAt
        hG₁symm b₀ b₁ hb₀ hb₁ hb₀G hb₁G u v

end ChristoffelFromPullbackGerm

section DifferentiateChristoffelGerm

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 2000000 in
/-- Differentiating a germwise signed Christoffel transition produces the
first-jet identity consumed by curvature naturality.  `B` is the derivative
field of `D`; its derivative is the third-order correction. -/
theorem differentiated_signedChristoffelFirstJet_of_eventuallyEq
    (Γ₀ Γ₁ : E → E →L[ℝ] E →L[ℝ] E)
    (F : E → E) (D : E → E →L[ℝ] E)
    (B : E → E →L[ℝ] E →L[ℝ] E) {z : E}
    (hF : HasFDerivAt F (D z) z)
    (hD : HasFDerivAt D (B z) z)
    (hB : HasFDerivAt B (fderiv ℝ B z) z)
    (hΓ₀ : HasFDerivAt Γ₀ (fderiv ℝ Γ₀ z) z)
    (hΓ₁ : HasFDerivAt Γ₁ (fderiv ℝ Γ₁ (F z)) (F z))
    (htransition : ∀ a b : E,
      (fun q : E ↦ Γ₁ (F q) (D q a) (D q b)) =ᶠ[nhds z]
        (fun q : E ↦ D q (Γ₀ q a b) - (B q b) a)) :
    ∀ e a b : E,
      (fderiv ℝ Γ₁ (F z) (D z e)) (D z a) (D z b) +
          Γ₁ (F z) ((B z e) a) (D z b) +
          Γ₁ (F z) (D z a) ((B z e) b) =
        (B z e) (Γ₀ z a b) +
          D z ((fderiv ℝ Γ₀ z e) a b) -
          ((fderiv ℝ B z e) b) a := by
  intro e a b
  have hDa : HasFDerivAt (fun q : E ↦ D q a) ((B z).flip a) z := by
    simpa using hD.clm_apply (hasFDerivAt_const (x := z) (c := a))
  have hDb : HasFDerivAt (fun q : E ↦ D q b) ((B z).flip b) z := by
    simpa using hD.clm_apply (hasFDerivAt_const (x := z) (c := b))
  have hΓF : HasFDerivAt (fun q : E ↦ Γ₁ (F q))
      ((fderiv ℝ Γ₁ (F z)).comp (D z)) z := by
    change HasFDerivAt (Γ₁ ∘ F)
      ((fderiv ℝ Γ₁ (F z)).comp (D z)) z
    exact HasFDerivAt.comp (𝕜 := ℝ) (f := F) (f' := D z)
      (g := Γ₁) (g' := fderiv ℝ Γ₁ (F z)) z hΓ₁ hF
  have hΓFDa : HasFDerivAt (fun q : E ↦ Γ₁ (F q) (D q a))
      ((Γ₁ (F z)).comp ((B z).flip a) +
        (((fderiv ℝ Γ₁ (F z)).comp (D z)).flip (D z a))) z := by
    exact HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E →L[ℝ] E) hΓF hDa
  have hleft : HasFDerivAt
      (fun q : E ↦ Γ₁ (F q) (D q a) (D q b))
      ((Γ₁ (F z) (D z a)).comp ((B z).flip b) +
          (((Γ₁ (F z)).comp ((B z).flip a) +
          (((fderiv ℝ Γ₁ (F z)).comp (D z)).flip (D z a))).flip
            (D z b))) z := by
    exact HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E) hΓFDa hDb
  have hΓ₀a : HasFDerivAt (fun q : E ↦ Γ₀ q a)
      ((fderiv ℝ Γ₀ z).flip a) z := by
    simpa using HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E →L[ℝ] E) hΓ₀
        (hasFDerivAt_const (x := z) (c := a))
  have hΓ₀ab : HasFDerivAt (fun q : E ↦ Γ₀ q a b)
      (((fderiv ℝ Γ₀ z).flip a).flip b) z := by
    simpa using HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E) hΓ₀a
        (hasFDerivAt_const (x := z) (c := b))
  have hDΓ₀ : HasFDerivAt (fun q : E ↦ D q (Γ₀ q a b))
      ((D z).comp (((fderiv ℝ Γ₀ z).flip a).flip b) +
        (B z).flip (Γ₀ z a b)) z := by
    exact HasFDerivAt.clm_apply (𝕜 := ℝ) (G := E)
      (H := E) hD hΓ₀ab
  have hBb : HasFDerivAt (fun q : E ↦ B q b)
      ((fderiv ℝ B z).flip b) z := by
    simpa using hB.clm_apply (hasFDerivAt_const (x := z) (c := b))
  have hBba : HasFDerivAt (fun q : E ↦ (B q b) a)
      (((fderiv ℝ B z).flip b).flip a) z := by
    simpa using hBb.clm_apply (hasFDerivAt_const (x := z) (c := a))
  have hright : HasFDerivAt
      (fun q : E ↦ D q (Γ₀ q a b) - (B q b) a)
      (((D z).comp (((fderiv ℝ Γ₀ z).flip a).flip b) +
          (B z).flip (Γ₀ z a b)) -
        ((fderiv ℝ B z).flip b).flip a) z :=
    hDΓ₀.sub hBba
  have hderivEq :
      fderiv ℝ (fun q : E ↦ Γ₁ (F q) (D q a) (D q b)) z e =
        fderiv ℝ (fun q : E ↦ D q (Γ₀ q a b) - (B q b) a) z e := by
    exact congrArg (fun L : E →L[ℝ] E ↦ L e)
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (htransition a b))
  have hleftEval :
      fderiv ℝ (fun q : E ↦ Γ₁ (F q) (D q a) (D q b)) z e =
        Γ₁ (F z) (D z a) ((B z e) b) +
          (Γ₁ (F z) ((B z e) a) (D z b) +
            (fderiv ℝ Γ₁ (F z) (D z e)) (D z a) (D z b)) := by
    rw [hleft.fderiv]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  have hrightEval :
      fderiv ℝ (fun q : E ↦ D q (Γ₀ q a b) - (B q b) a) z e =
        D z ((fderiv ℝ Γ₀ z e) a b) +
          (B z e) (Γ₀ z a b) - ((fderiv ℝ B z e) b) a := by
    rw [hright.fderiv]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply]
  rw [hleftEval, hrightEval] at hderivEq
  simpa [add_assoc, add_comm, add_left_comm] using hderivEq

end DifferentiateChristoffelGerm

section FirstJetCurvatureNaturality

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Curvature naturality from the value and first derivative of the signed
Christoffel transition law.

`B` is the second derivative of the coordinate map and `C` its third
derivative at the base point.  Only the displayed symmetries are used.  This
is the tensorial cancellation missing between the metric-pullback germ and
the Ricci trace; no trace or Ricci-flow equation appears in the statement. -/
theorem chartCurvatureOf_natural_of_signedChristoffelFirstJet
    (Γ₀ Γ₁ : E → E →L[ℝ] E →L[ℝ] E)
    (z₀ z₁ : E) (D : E →L[ℝ] E)
    (B : E → E → E) (C : E → E → E → E)
    (hBsymm : ∀ a b : E, B a b = B b a)
    (hCsymm : ∀ a b c : E, C a b c = C c b a)
    (hΓ : ∀ a b : E,
      Γ₁ z₁ (D a) (D b) = D (Γ₀ z₀ a b) - B b a)
    (hDΓ : ∀ e a b : E,
      (fderiv ℝ Γ₁ z₁ (D e)) (D a) (D b) +
          Γ₁ z₁ (B e a) (D b) + Γ₁ z₁ (D a) (B e b) =
        B e (Γ₀ z₀ a b) + D ((fderiv ℝ Γ₀ z₀ e) a b) - C e b a)
    (u v w : E) :
    chartCurvatureOf Γ₁ z₁ (D u) (D v) (D w) =
      D (chartCurvatureOf Γ₀ z₀ u v w) := by
  have hDu :
      (fderiv ℝ Γ₁ z₁ (D u)) (D v) (D w) =
        B u (Γ₀ z₀ v w) + D ((fderiv ℝ Γ₀ z₀ u) v w) - C u w v -
          Γ₁ z₁ (B u v) (D w) - Γ₁ z₁ (D v) (B u w) := by
    calc
      (fderiv ℝ Γ₁ z₁ (D u)) (D v) (D w) =
          ((fderiv ℝ Γ₁ z₁ (D u)) (D v) (D w) +
              Γ₁ z₁ (B u v) (D w) + Γ₁ z₁ (D v) (B u w)) -
            Γ₁ z₁ (B u v) (D w) - Γ₁ z₁ (D v) (B u w) := by
        abel
      _ = _ := by rw [hDΓ u v w]
  have hDv :
      (fderiv ℝ Γ₁ z₁ (D v)) (D u) (D w) =
        B v (Γ₀ z₀ u w) + D ((fderiv ℝ Γ₀ z₀ v) u w) - C v w u -
          Γ₁ z₁ (B v u) (D w) - Γ₁ z₁ (D u) (B v w) := by
    calc
      (fderiv ℝ Γ₁ z₁ (D v)) (D u) (D w) =
          ((fderiv ℝ Γ₁ z₁ (D v)) (D u) (D w) +
              Γ₁ z₁ (B v u) (D w) + Γ₁ z₁ (D u) (B v w)) -
            Γ₁ z₁ (B v u) (D w) - Γ₁ z₁ (D u) (B v w) := by
        abel
      _ = _ := by rw [hDΓ v u w]
  have hquadUV :
      Γ₁ z₁ (D u) (Γ₁ z₁ (D v) (D w)) =
        D (Γ₀ z₀ u (Γ₀ z₀ v w)) - B (Γ₀ z₀ v w) u -
          Γ₁ z₁ (D u) (B w v) := by
    calc
      Γ₁ z₁ (D u) (Γ₁ z₁ (D v) (D w)) =
          Γ₁ z₁ (D u) (D (Γ₀ z₀ v w) - B w v) := by rw [hΓ v w]
      _ = Γ₁ z₁ (D u) (D (Γ₀ z₀ v w)) -
          Γ₁ z₁ (D u) (B w v) := by rw [map_sub]
      _ = _ := by rw [hΓ u (Γ₀ z₀ v w)]
  have hquadVU :
      Γ₁ z₁ (D v) (Γ₁ z₁ (D u) (D w)) =
        D (Γ₀ z₀ v (Γ₀ z₀ u w)) - B (Γ₀ z₀ u w) v -
          Γ₁ z₁ (D v) (B w u) := by
    calc
      Γ₁ z₁ (D v) (Γ₁ z₁ (D u) (D w)) =
          Γ₁ z₁ (D v) (D (Γ₀ z₀ u w) - B w u) := by rw [hΓ u w]
      _ = Γ₁ z₁ (D v) (D (Γ₀ z₀ u w)) -
          Γ₁ z₁ (D v) (B w u) := by rw [map_sub]
      _ = _ := by rw [hΓ v (Γ₀ z₀ u w)]
  unfold chartCurvatureOf
  rw [hDu, hDv, hquadUV, hquadVU]
  rw [hBsymm u (Γ₀ z₀ v w), hBsymm v (Γ₀ z₀ u w),
    hCsymm u w v, hBsymm u v, hBsymm u w, hBsymm v w]
  simp only [map_add, map_sub]
  abel

/-- Germwise form of the first-jet curvature naturality theorem.  Sufficient
spatial regularity differentiates the signed Christoffel germ automatically;
only the genuine Hessian and third-derivative symmetries remain explicit. -/
theorem chartCurvatureOf_natural_of_signedChristoffelGerm
    (Γ₀ Γ₁ : E → E →L[ℝ] E →L[ℝ] E)
    (F : E → E) (D : E → E →L[ℝ] E)
    (B : E → E →L[ℝ] E →L[ℝ] E) {z : E}
    (hF : HasFDerivAt F (D z) z)
    (hD : HasFDerivAt D (B z) z)
    (hB : HasFDerivAt B (fderiv ℝ B z) z)
    (hΓ₀ : HasFDerivAt Γ₀ (fderiv ℝ Γ₀ z) z)
    (hΓ₁ : HasFDerivAt Γ₁ (fderiv ℝ Γ₁ (F z)) (F z))
    (hBsymm : ∀ a b : E, (B z a) b = (B z b) a)
    (hCsymm : ∀ a b c : E,
      ((fderiv ℝ B z a) b) c = ((fderiv ℝ B z c) b) a)
    (htransition : ∀ a b : E,
      (fun q : E ↦ Γ₁ (F q) (D q a) (D q b)) =ᶠ[nhds z]
        (fun q : E ↦ D q (Γ₀ q a b) - (B q b) a))
    (u v w : E) :
    chartCurvatureOf Γ₁ (F z) (D z u) (D z v) (D z w) =
      D z (chartCurvatureOf Γ₀ z u v w) := by
  apply chartCurvatureOf_natural_of_signedChristoffelFirstJet
    Γ₀ Γ₁ z (F z) (D z)
    (fun a b ↦ (B z a) b)
    (fun a b c ↦ ((fderiv ℝ B z a) b) c)
    hBsymm hCsymm
  · intro a b
    exact (htransition a b).self_of_nhds
  · exact differentiated_signedChristoffelFirstJet_of_eventuallyEq
      Γ₀ Γ₁ F D B hF hD hB hΓ₀ hΓ₁ htransition

end FirstJetCurvatureNaturality

section IntrinsicChartCurvaturePullback

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Direct chart-flow specialization of germwise Christoffel naturality.  Its
conclusion is exactly the `hcurv` input of the tensorial pullback theorem
below. -/
theorem anchorChartCurvatureFlow_natural_of_signedChristoffelGerm
    (rt gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ)
    (F : E → E) (D : E → E →L[ℝ] E)
    (B : E → E →L[ℝ] E →L[ℝ] E) {z : E}
    (hF : HasFDerivAt F (D z) z)
    (hD : HasFDerivAt D (B z) z)
    (hB : HasFDerivAt B (fderiv ℝ B z) z)
    (hΓ₀ : HasFDerivAt (anchorChartChristoffelFieldFlow rt anchor t)
      (fderiv ℝ (anchorChartChristoffelFieldFlow rt anchor t) z) z)
    (hΓ₁ : HasFDerivAt (anchorChartChristoffelFieldFlow gt anchor t)
      (fderiv ℝ (anchorChartChristoffelFieldFlow gt anchor t) (F z)) (F z))
    (hBsymm : ∀ a b : E, (B z a) b = (B z b) a)
    (hCsymm : ∀ a b c : E,
      ((fderiv ℝ B z a) b) c = ((fderiv ℝ B z c) b) a)
    (htransition : ∀ a b : E,
      (fun q : E ↦ anchorChartChristoffelFieldFlow gt anchor t
          (F q) (D q a) (D q b)) =ᶠ[nhds z]
        (fun q : E ↦ D q
            (anchorChartChristoffelFieldFlow rt anchor t q a b) -
          (B q b) a)) :
    ∀ u v w : E,
      anchorChartCurvatureFlow gt anchor t (F z)
          (D z u) (D z v) (D z w) =
        D z (anchorChartCurvatureFlow rt anchor t z u v w) := by
  intro u v w
  simpa only [anchorChartCurvatureFlow] using
    chartCurvatureOf_natural_of_signedChristoffelGerm
      (anchorChartChristoffelFieldFlow rt anchor t)
      (anchorChartChristoffelFieldFlow gt anchor t)
      F D B hF hD hB hΓ₀ hΓ₁ hBsymm hCsymm htransition u v w

/-- A chart-curvature intertwining law is exactly the tensorial statement
needed to identify the pulled source curvature with the actual curvature of
the assembled metric.  Cutoff-one zone bridges convert both chart curvature
expressions to `chartRicciCurvatureEndAt`. -/
theorem pullbackCurvatureEnd_chartRicciCurvatureEndAt_eq_of_chartCurvatureNatural
    (rt gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ) {z₀ z₁ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hz₁ : z₁ ∈ (extChartAt I anchor).target)
    (hχ₀ : ∀ᶠ z in nhds z₀,
      GeodesicTransport.cutoff (n := n) anchor z = 1)
    (hχ₁ : ∀ᶠ z in nhds z₁,
      GeodesicTransport.cutoff (n := n) anchor z = 1)
    (e : E ≃L[ℝ] E)
    (hcurv : ∀ u v w : E,
      anchorChartCurvatureFlow gt anchor t z₁ (e u) (e v) (e w) =
        e (anchorChartCurvatureFlow rt anchor t z₀ u v w)) :
    pullbackCurvatureEnd e
        (chartRicciCurvatureEndAt (gt t) anchor z₁ hz₁) =
      chartRicciCurvatureEndAt (rt t) anchor z₀ hz₀ := by
  funext p q
  apply LinearMap.ext
  intro r
  simp only [pullbackCurvatureEnd_apply]
  have htarget :=
    anchorChartCurvatureFlow_eq_chartRicciCurvatureEndAt_apply_zone
      gt anchor t hz₁ hχ₁ (e r) (e p) (e q)
  have hsource :=
    anchorChartCurvatureFlow_eq_chartRicciCurvatureEndAt_apply_zone
      rt anchor t hz₀ hχ₀ r p q
  calc
    e.symm
        (chartRicciCurvatureEndAt (gt t) anchor z₁ hz₁
          (e p) (e q) (e r)) =
      e.symm (anchorChartCurvatureFlow gt anchor t z₁
        (e r) (e p) (e q)) := by rw [htarget]
    _ = e.symm (e (anchorChartCurvatureFlow rt anchor t z₀ r p q)) := by
      rw [hcurv r p q]
    _ = anchorChartCurvatureFlow rt anchor t z₀ r p q :=
      e.symm_apply_apply _
    _ = chartRicciCurvatureEndAt (rt t) anchor z₀ hz₀ p q r := hsource

/-- Trace-level corollary of the tensorial chart-curvature pullback theorem. -/
theorem trace_pullbackCurvatureEnd_chartRicciCurvatureEndAt_eq_of_chartCurvatureNatural
    (rt gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ) {z₀ z₁ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hz₁ : z₁ ∈ (extChartAt I anchor).target)
    (hχ₀ : ∀ᶠ z in nhds z₀,
      GeodesicTransport.cutoff (n := n) anchor z = 1)
    (hχ₁ : ∀ᶠ z in nhds z₁,
      GeodesicTransport.cutoff (n := n) anchor z = 1)
    (e : E ≃L[ℝ] E)
    (hcurv : ∀ u v w : E,
      anchorChartCurvatureFlow gt anchor t z₁ (e u) (e v) (e w) =
        e (anchorChartCurvatureFlow rt anchor t z₀ u v w))
    (p q : E) :
    LinearMap.trace ℝ E
        (pullbackCurvatureEnd e
          (chartRicciCurvatureEndAt (gt t) anchor z₁ hz₁) p q) =
      LinearMap.trace ℝ E
        (chartRicciCurvatureEndAt (rt t) anchor z₀ hz₀ p q) := by
  rw [pullbackCurvatureEnd_chartRicciCurvatureEndAt_eq_of_chartCurvatureNatural
    rt gt anchor t hz₀ hz₁ hχ₀ hχ₁ e hcurv]

/-- The exact scaled equality consumed by interior Ricci/Hamilton assembly.
Unlike the former explicit `hcurvatureRate` boundary, its only geometric input
is the tensorial chart-curvature naturality law. -/
theorem neg_two_trace_pullbackCurvatureEnd_eq_chartMetric_neg_two_ricci_of_chartCurvatureNatural
    (rt gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ) {z₀ z₁ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hz₁ : z₁ ∈ (extChartAt I anchor).target)
    (hχ₀ : ∀ᶠ z in nhds z₀,
      GeodesicTransport.cutoff (n := n) anchor z = 1)
    (hχ₁ : ∀ᶠ z in nhds z₁,
      GeodesicTransport.cutoff (n := n) anchor z = 1)
    (e : E ≃L[ℝ] E)
    (hcurv : ∀ u v w : E,
      anchorChartCurvatureFlow gt anchor t z₁ (e u) (e v) (e w) =
        e (anchorChartCurvatureFlow rt anchor t z₀ u v w))
    (p q : E) :
    (-2 : ℝ) * LinearMap.trace ℝ E
        (pullbackCurvatureEnd e
          (chartRicciCurvatureEndAt (gt t) anchor z₁ hz₁) p q) =
      CovariantDerivative.chartMetric
        (fun y : M ↦ (-2 : ℝ) • ricciContinuousBilinAt (rt t) y)
        anchor z₀ p q := by
  rw [trace_pullbackCurvatureEnd_chartRicciCurvatureEndAt_eq_of_chartCurvatureNatural
    rt gt anchor t hz₀ hz₁ hχ₀ hχ₁ e hcurv p q]
  rw [← deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
    rt anchor t z₀ hz₀ p q]
  simp only [deTurckChartRicciBilin, CovariantDerivative.chartMetric_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

end IntrinsicChartCurvaturePullback

end Poincare
