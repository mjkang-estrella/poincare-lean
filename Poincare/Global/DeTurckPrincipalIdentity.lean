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

/-- The matrix inverse agrees with the coordinate coefficients of the inverse metric operator. -/
theorem inverseEntries_eq_coordinates (G : Bilin) (hG : G.IsInvertible) :
    inverseEntries G = fun i j => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord j
      (G.inverse (LinearMap.toContinuousLinearMap
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord i))) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  apply Matrix.inv_eq_left_inv
  ext i k
  change (∑ j, b.coord j (G.inverse (LinearMap.toContinuousLinearMap (b.coord i))) *
    G (b j) (b k)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i k
  let r := G.inverse (LinearMap.toContinuousLinearMap (b.coord i))
  have hraise : G r = LinearMap.toContinuousLinearMap (b.coord i) :=
    (hG.inverse_apply_eq.mp rfl).symm
  calc
    _ = G (∑ j, b.repr r j • b j) (b k) := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply, r]
    _ = G r (b k) := by rw [b.sum_repr]
    _ = _ := by
      rw [hraise]
      simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
        Module.Basis.repr_self_apply, Matrix.one_apply]
      simp only [eq_comm]

/-- Symmetry of the inverse metric pairing follows from symmetry of the metric. -/
theorem inverse_pairing_symm (G : Bilin) (hG : G.IsInvertible)
    (hs : ∀ u v, G u v = G v u) (p q : E →L[ℝ] ℝ) :
    p (G.inverse q) = q (G.inverse p) := by
  have hp : G (G.inverse p) = p := (hG.inverse_apply_eq.mp rfl).symm
  have hq : G (G.inverse q) = q := (hG.inverse_apply_eq.mp rfl).symm
  exact (congrArg (fun f : E →L[ℝ] ℝ => f (G.inverse q)) hp).symm.trans
    ((hs _ _).trans (congrArg (fun f : E →L[ℝ] ℝ => f (G.inverse p)) hq))

/-- The landed finite-basis metric contraction is the fixed three-dimensional matrix contraction. -/
theorem contraction_eq_matrix (G T : Bilin) (hG : G.IsInvertible)
    (hs : ∀ u v, G u v = G v u) :
    (∑ i, T (G.inverse (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord i))) ((Module.finBasis ℝ E) i)) =
      ∑ i : Fin 3, ∑ j : Fin 3, inverseEntries G i j * T (basis3 i) (basis3 j) := by
  let b := Module.finBasis ℝ E
  let e := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let F := (G.inverse.comp T.flip).toLinearMap
  have hA : ∀ i j, inverseEntries G i j = inverseEntries G j i := by
    have hm : Matrix.IsSymm (fun i j : Fin 3 => G (basis3 i) (basis3 j)) :=
      Matrix.IsSymm.ext (fun i j => hs (basis3 j) (basis3 i))
    exact fun i j => hm.inv.apply j i
  calc
    _ = ∑ i, b.coord i (F (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (inverse_pairing_symm G hG hs
        (LinearMap.toContinuousLinearMap (b.coord i)) (T.flip (b i))).symm
    _ = LinearMap.trace ℝ E F := RicciFlow.RicciFlow.sum_coord_eq_trace F
    _ = ∑ i, e.coord i (F (e i)) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ e F, Matrix.trace]
      simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
    _ = ∑ i, T (G.inverse (LinearMap.toContinuousLinearMap (e.coord i))) (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact inverse_pairing_symm G hG hs
        (LinearMap.toContinuousLinearMap (e.coord i)) (T.flip (e i))
    _ = ∑ i, ∑ j, inverseEntries G i j * T (basis3 j) (basis3 i) := by
      rw [inverseEntries_eq_coordinates G hG]
      apply Finset.sum_congr rfl
      intro i _
      let r := G.inverse (LinearMap.toContinuousLinearMap (e.coord i))
      change T r (e i) = ∑ j, e.repr r j * T (e j) (e i)
      have hh := congrArg (fun x => T x (e i)) (e.sum_repr r)
      simpa only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul] using hh.symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hA j i]

/-- Finite-dimensional bilinear maps give continuous bilinear maps in the model space. -/
def continuousBilinear (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Bilin :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap.comp L)

/-- The six Lie second-jet terms, bundled in their contracted slots. -/
def lieTensor (H : E →L[ℝ] Jet1) (v w : E) : Bilin :=
  continuousBilinear (LinearMap.mk₂ ℝ
    (fun p q => H v p q w + H v q p w - H v w p q +
      H w p q v + H w q p v - H w v p q)
    (by intros; simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (by intros; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (by intros; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring))

/-- The six Ricci second-jet terms, bundled in their contracted slots. -/
def ricciTensor (H : E →L[ℝ] Jet1) (v w : E) : Bilin :=
  continuousBilinear (LinearMap.mk₂ ℝ
    (fun p q => H p v w q + H p w v q - H p q v w -
      H v p w q - H v w p q + H v q p w)
    (by intros; simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (by intros; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (by intros; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring))

/-- Evaluation of the bundled Lie contraction tensor is its explicit six-term expression. -/
theorem lieTensor_apply (H : E →L[ℝ] Jet1) (v w p q : E) :
    lieTensor H v w p q = H v p q w + H v q p w - H v w p q +
      H w p q v + H w q p v - H w v p q := by
  rfl

/-- Lowering the two Lie slots gives exactly the landed formal Lie second jet. -/
theorem lieSecondCoordinate_eq_lieSecondJet (G : Bilin) (H : E →L[ℝ] Jet1)
    (hG : G.IsInvertible) (hs : ∀ u v, G u v = G v u)
    (hH : ∀ a b p q, H a b p q = H a b q p) (v w : E) :
    lieSecondCoordinate G H v w =
      lieSecondJet (inverseEntries G) (fun a b p q => H a b p q) v w := by
  have hraise (p : E →L[ℝ] ℝ) : G (G.inverse p) = p :=
    (hG.inverse_apply_eq.mp rfl).symm
  calc
    _ = (1 / 2 : ℝ) * ∑ i, lieTensor H v w
        (G.inverse (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
        ((Module.finBasis ℝ E) i) := by
      simp only [lieSecondCoordinate, fieldSecond, map_sum, ContinuousLinearMap.sum_apply,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [connection, hraise]
      rw [hs v]
      simp only [hraise, koszul_apply, lieTensor_apply]
      rw [hH v w ((Module.finBasis ℝ E) i), hH w v ((Module.finBasis ℝ E) i)]
      ring
    _ = _ := by
      rw [contraction_eq_matrix G (lieTensor H v w) hG hs]
      rfl

/-- The curvature second-jet trace is exactly the landed formal Ricci second jet. -/
theorem ricciSecondCoordinate_eq_ricciSecondJet (G : Bilin) (H : E →L[ℝ] Jet1)
    (hG : G.IsInvertible) (hs : ∀ u v, G u v = G v u)
    (hH : ∀ a b p q, H a b p q = H a b q p) (v w : E) :
    ricciSecondCoordinate G H v w =
      ricciSecondJet (inverseEntries G) (fun a b p q => H a b p q) v w := by
  have hA : ∀ i j, inverseEntries G i j = inverseEntries G j i := by
    have hm : Matrix.IsSymm (fun i j : Fin 3 => G (basis3 i) (basis3 j)) :=
      Matrix.IsSymm.ext (fun i j => hs (basis3 j) (basis3 i))
    exact fun i j => hm.inv.apply j i
  calc
    _ = (1 / 2 : ℝ) * ∑ i, (ricciTensor H v w).flip
        (G.inverse (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
        ((Module.finBasis ℝ E) i) := by
      simp only [ricciSecondCoordinate, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [connection, map_sub]
      change (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))
        (G.inverse (koszul (H ((Module.finBasis ℝ E) i)) w v)) -
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))
        (G.inverse (koszul (H v) w ((Module.finBasis ℝ E) i))) = _
      rw [inverse_pairing_symm G hG hs
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))
        (koszul (H ((Module.finBasis ℝ E) i)) w v),
        inverse_pairing_symm G hG hs
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))
        (koszul (H v) w ((Module.finBasis ℝ E) i))]
      simp only [koszul_apply]
      change _ = (1 / 2 : ℝ) *
        (H ((Module.finBasis ℝ E) i) v w _ + H ((Module.finBasis ℝ E) i) w v _ -
          H ((Module.finBasis ℝ E) i) _ v w - H v ((Module.finBasis ℝ E) i) w _ -
          H v w ((Module.finBasis ℝ E) i) _ + H v _ ((Module.finBasis ℝ E) i) w)
      rw [hH ((Module.finBasis ℝ E) i) _ w v, hH v _ w ((Module.finBasis ℝ E) i)]
      ring
    _ = _ := by
      rw [contraction_eq_matrix G (ricciTensor H v w).flip hG hs]
      unfold ricciSecondJet
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hA j i]
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
