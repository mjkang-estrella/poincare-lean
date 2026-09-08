import Poincare.Global.DeTurckPrincipalSecondJet

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100

noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology BigOperators NNReal

namespace Poincare.DeTurckPrincipalIdentity
open DeTurckPrincipalSecondJet DeTurckCoordinateJointRegularity

/-- The Koszul covector constructed directly from a first metric jet. -/
def koszul (J : Jet1) (u v : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (J u v + J v u - (J.flip u).flip v)

/-- The coordinate connection constructed directly from the metric value and first jet. -/
def connection (G : Bilin) (J : Jet1) (u v : E) : E :=
  G.inverse (koszul J v u)

/-- Evaluation of the Koszul covector uses only the three first-jet slots. -/
theorem koszul_apply (J : Jet1) (u v q : E) :
    koszul J u v q = (1 / 2 : ℝ) * (J u v q + J v u q - J q u v) := by
  rfl

section Manifold
universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The actual Christoffel field in the cutoff-one region depends on the first metric jet. -/
theorem christoffel_eq_connection
    (g : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1)
    (u v : E) :
    GeodesicTransport.chartChristoffelField g anchor z u v =
      connection (CovariantDerivative.chartMetric g.inner anchor z)
        (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) u v := by
  let G := CovariantDerivative.chartMetric g.inner anchor
  let B := anchorBlendedMetricFlow (fun _ => g) anchor 0
  have heq : B =ᶠ[nhds z] G := by
    filter_upwards [hcut] with y hy
    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      (GeodesicTransport.cutoff (n := 3) anchor)
      (GeodesicTransport.backgroundMetric (n := 3)) g.inner anchor hy
  have hbase := anchorChartChristoffelFieldOperatorFamily_apply_eq_christoffelClosedOp
    (fun _ : Unit => g) anchor () z u v
  change GeodesicTransport.chartChristoffelField g anchor z u v =
    RicciFlow.RicciFlow.christoffelClosedOp B z v u at hbase
  rw [hbase, RicciFlow.RicciFlow.christoffelClosedOp_apply]
  rw [heq.self_of_nhds]
  unfold connection koszul
  congr 1
  ext q
  simp only [CovariantDerivative.christoffelFunctional, heq.fderiv_eq,
    LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  rfl

/-- The Christoffel derivative splits into a second-jet term and an inverse-metric correction. -/
theorem christoffelDerivative_eq_jets
    (g : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1)
    (a u v : E) :
    let G := CovariantDerivative.chartMetric g.inner anchor
    let J := fderiv ℝ G z
    let H := fderiv ℝ (fderiv ℝ G) z
    fderiv ℝ (GeodesicTransport.chartChristoffelField g anchor) z a u v =
      -(G z).inverse (J a (connection (G z) J u v)) +
        connection (G z) (H a) u v := by
  let G := CovariantDerivative.chartMetric g.inner anchor
  have hG : ContDiffAt ℝ 2 G z :=
    deTurckChartMetric_contDiffAt_two_of_mem_target g anchor hz
  have hJ := (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heval : fderiv ℝ (fun y => fderiv ℝ G y a) z =
      fderiv ℝ (fderiv ℝ G) z a := by
    ext b p q
    have hh := congrArg (fun L : E →L[ℝ] Bilin => L b p q)
      (hJ.hasFDerivAt.clm_apply (hasFDerivAt_const a z)).fderiv
    have hh' : fderiv ℝ (fun y => fderiv ℝ G y a) z b p q =
        fderiv ℝ (fderiv ℝ G) z b a p q := by simpa using hh
    exact hh'.trans
      (congrArg (fun B : Bilin => B p q)
        (hG.isSymmSndFDerivAt (by norm_num) b a))
  have hK (F : E → Bilin) :
      LinearMap.toContinuousLinearMap (CovariantDerivative.christoffelFunctional F z v u) =
        koszul (fderiv ℝ F z) v u := by
    ext q
    rfl
  dsimp only [G] at heval
  dsimp only
  rw [christoffelDerivative_eq_chartMetricSecondJet g anchor z hcut a u v]
  simp only [hK, heval]
  rfl

end Manifold
end Poincare.DeTurckPrincipalIdentity
