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

/-- The contracted connection difference evaluated from the first metric jet. -/
def fieldValue (G : Bilin) (J : Jet1) (B : E →L[ℝ] E →L[ℝ] E) : E :=
  let b := Module.finBasis ℝ E
  ∑ i,
    let r := G.inverse (LinearMap.toContinuousLinearMap (b.coord i))
    connection G J r (b i) - B r (b i)

/-- The second-jet contribution to the derivative of the contracted field. -/
def fieldSecond (G : Bilin) (H : E →L[ℝ] Jet1) (a : E) : E :=
  let b := Module.finBasis ℝ E
  ∑ i, connection G (H a)
    (G.inverse (LinearMap.toContinuousLinearMap (b.coord i))) (b i)

/-- The derivative remainder uses only the first metric jet and fixed background data. -/
def fieldFirst (G : Bilin) (J : Jet1) (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (a : E) : E :=
  let b := Module.finBasis ℝ E
  ∑ i,
    let r := G.inverse (LinearMap.toContinuousLinearMap (b.coord i))
    let dr := -G.inverse (J a r);
    -G.inverse (J a (connection G J r (b i))) + connection G J dr (b i) -
      DB a r (b i) - B dr (b i)

/-- The two second-jet Lie slots before converting the basis contraction to matrix entries. -/
def lieSecondCoordinate (G : Bilin) (H : E →L[ℝ] Jet1) (v w : E) : ℝ :=
  G (fieldSecond G H v) w + G v (fieldSecond G H w)

/-- The Lie remainder, including metric advection, is an explicit first-jet function. -/
def lieFirst (G : Bilin) (J : Jet1) (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (v w : E) : ℝ :=
  J (fieldValue G J B) v w + G (fieldFirst G J B DB v) w +
    G v (fieldFirst G J B DB w)

/-- The second-jet terms in the curvature trace in the landed finite basis. -/
def ricciSecondCoordinate (G : Bilin) (H : E →L[ℝ] Jet1) (v w : E) : ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, b.coord i (connection G (H (b i)) v w - connection G (H v) (b i) w)

/-- The curvature remainder contains only inverse-metric derivatives and connection products. -/
def ricciFirst (G : Bilin) (J : Jet1) (v w : E) : ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, b.coord i
    (-G.inverse (J (b i) (connection G J v w)) +
      G.inverse (J v (connection G J (b i) w)) +
      connection G J (b i) (connection G J v w) -
      connection G J v (connection G J (b i) w))

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

/-- Differentiation of the contracted field includes the motion of the raised covectors. -/
theorem fieldDerivative_eq_raised_derivative
    (g bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z a : E) :
    let B := anchorBlendedMetricFlow (fun _ => g) anchor 0
    let Γ := GeodesicTransport.chartChristoffelField g anchor
    let Γb := GeodesicTransport.chartChristoffelField bg anchor
    let b := Module.finBasis ℝ E
    fderiv ℝ (anchorChartDeTurckContractionFlow (fun _ => g) bg anchor 0) z a =
      ∑ i,
        let r := (B z).inverse (LinearMap.toContinuousLinearMap (b.coord i))
        let dr := -(B z).inverse (fderiv ℝ B z a r)
        fderiv ℝ Γ z a r (b i) + Γ z dr (b i) -
          fderiv ℝ Γb z a r (b i) - Γb z dr (b i) := by
  let B := anchorBlendedMetricFlow (fun _ => g) anchor 0
  let Γ := GeodesicTransport.chartChristoffelField g anchor
  let Γb := GeodesicTransport.chartChristoffelField bg anchor
  let b := Module.finBasis ℝ E
  have hB : DifferentiableAt ℝ B z :=
    ((anchorBlendedMetricFamily_contDiff_four (fun _ : Unit => g) anchor ()).differentiable
      (by norm_num)).differentiableAt
  have hΓ : DifferentiableAt ℝ Γ z :=
    ((GeodesicTransport.chartChristoffelField_contDiff_top g anchor).differentiable
      (by simp)).differentiableAt
  have hΓb : DifferentiableAt ℝ Γb z :=
    ((GeodesicTransport.chartChristoffelField_contDiff_top bg anchor).differentiable
      (by simp)).differentiableAt
  have hr (i) := RicciFlow.RicciFlow.hasFDerivAt_inverse_raise hB
    (Filter.Eventually.of_forall (anchorBlendedMetricFlow_isInvertible (fun _ => g) anchor 0))
    (LinearMap.toContinuousLinearMap (b.coord i))
  have ht (i) := ((hΓ.hasFDerivAt.clm_apply (hr i)).clm_apply
    (hasFDerivAt_const (b i) z)).sub
      ((hΓb.hasFDerivAt.clm_apply (hr i)).clm_apply (hasFDerivAt_const (b i) z))
  have hs := HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => ht i)
  simp only [Pi.sub_apply] at hs
  dsimp only
  change fderiv ℝ (fun y => ∑ i, (Γ y ((B y).inverse
    (LinearMap.toContinuousLinearMap (b.coord i))) (b i) -
    Γb y ((B y).inverse (LinearMap.toContinuousLinearMap (b.coord i))) (b i))) z a = _
  rw [hs.fderiv, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add]
  abel

/-- The full derivative separates into a second-jet contraction and a uniform first-jet remainder. -/
theorem fieldDerivative_eq_jets
    (g bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1)
    (a : E) :
    let G := CovariantDerivative.chartMetric g.inner anchor
    let J := fderiv ℝ G z
    let H := fderiv ℝ (fderiv ℝ G) z
    let B := GeodesicTransport.chartChristoffelField bg anchor
    fderiv ℝ (anchorChartDeTurckContractionFlow (fun _ => g) bg anchor 0) z a =
      fieldSecond (G z) H a + fieldFirst (G z) J (B z) (fderiv ℝ B z) a := by
  let G := CovariantDerivative.chartMetric g.inner anchor
  let Blend := anchorBlendedMetricFlow (fun _ => g) anchor 0
  have heq : Blend =ᶠ[nhds z] G := by
    filter_upwards [hcut] with y hy
    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      (GeodesicTransport.cutoff (n := 3) anchor)
      (GeodesicTransport.backgroundMetric (n := 3)) g.inner anchor hy
  have hval := heq.self_of_nhds
  have hder : fderiv ℝ Blend z = fderiv ℝ G z := heq.fderiv_eq
  dsimp only [Blend, G] at hval hder
  dsimp only
  rw [fieldDerivative_eq_raised_derivative g bg anchor z a]
  dsimp only
  simp only [hval, hder, christoffelDerivative_eq_jets g anchor z hz hcut,
    christoffel_eq_connection g anchor z hcut]
  simp only [fieldSecond, fieldFirst, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  abel

/-- The coordinate field value is the fixed algebraic first-jet contraction. -/
theorem field_eq_value
    (g bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1) :
    anchorChartDeTurckContractionFlow (fun _ => g) bg anchor 0 z =
      fieldValue (CovariantDerivative.chartMetric g.inner anchor z)
        (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z)
        (GeodesicTransport.chartChristoffelField bg anchor z) := by
  have hval : anchorBlendedMetricFlow (fun _ => g) anchor 0 z =
      CovariantDerivative.chartMetric g.inner anchor z :=
    CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      (GeodesicTransport.cutoff (n := 3) anchor)
      (GeodesicTransport.backgroundMetric (n := 3)) g.inner anchor hcut.self_of_nhds
  simp only [anchorChartDeTurckContractionFlow, fieldValue,
    anchorChartChristoffelFieldFlow, hval, christoffel_eq_connection g anchor z hcut]

/-- The actual Lie expression splits into its coordinate second-jet part and explicit first-jet remainder. -/
theorem lie_eq_secondCoordinate_add_first
    (g bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1)
    (v w : E) :
    let G := CovariantDerivative.chartMetric g.inner anchor
    let J := fderiv ℝ G z
    let H := fderiv ℝ (fderiv ℝ G) z
    let B := GeodesicTransport.chartChristoffelField bg anchor
    let W := anchorChartDeTurckContractionFlow (fun _ => g) bg anchor 0
    J (W z) v w + G z (fderiv ℝ W z v) w + G z v (fderiv ℝ W z w) =
      lieSecondCoordinate (G z) H v w + lieFirst (G z) J (B z) (fderiv ℝ B z) v w := by
  dsimp only
  rw [field_eq_value g bg anchor z hcut,
    fieldDerivative_eq_jets g bg anchor z hz hcut v,
    fieldDerivative_eq_jets g bg anchor z hz hcut w]
  simp only [lieSecondCoordinate, lieFirst, map_add, ContinuousLinearMap.add_apply]
  ring

/-- The actual curvature trace splits into its coordinate second-jet part and explicit first-jet remainder. -/
theorem ricci_eq_secondCoordinate_add_first
    (g : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1)
    (v w : E) :
    let G := CovariantDerivative.chartMetric g.inner anchor
    let Γ := GeodesicTransport.chartChristoffelField g anchor
    let b := Module.finBasis ℝ E
    (∑ i, b.coord i
      ((fderiv ℝ Γ z (b i)) v w - (fderiv ℝ Γ z v) (b i) w +
        Γ z (b i) (Γ z v w) - Γ z v (Γ z (b i) w))) =
      ricciSecondCoordinate (G z) (fderiv ℝ (fderiv ℝ G) z) v w +
        ricciFirst (G z) (fderiv ℝ G z) v w := by
  dsimp only
  simp only [christoffelDerivative_eq_jets g anchor z hz hcut,
    christoffel_eq_connection g anchor z hcut,
    ricciSecondCoordinate, ricciFirst, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_add, map_sub, map_neg]
  ring

end Manifold
end Poincare.DeTurckPrincipalIdentity
