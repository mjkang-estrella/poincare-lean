import Poincare.Global.DeTurckChartOverlapCovariance
import Poincare.Global.DeTurckRicciTracePullback
import Poincare.Global.GeodesicReanchorClose
import Poincare.Global.MetricVariation
import Poincare.Global.ChartCurvatureBridge6
import Poincare.Global.ChartCurvatureBridgeZoneClose
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Chart-independent inverse gauge and Ricci-trace pullback

The coordinate variational equation starts at the identity.  This file
shrinks its existence interval so that its solution remains a continuous
linear equivalence, then packages the arbitrary-time Ricci-trace pullback
theorem without requiring callers to choose that equivalence by hand.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace Poincare

section BilinearPullback

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull a continuous bilinear form through a continuous linear map in both
slots.  This is the tensor-valued counterpart of `pullbackBilinearApply`. -/
def pullbackBilinearForm
    (G : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR E G).flip D).comp D

@[simp] theorem pullbackBilinearForm_apply
    (G : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E) (u v : E) :
    pullbackBilinearForm G D u v = G (D u) (D v) :=
  rfl

end BilinearPullback

section CurvaturePullback

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull back a curvature-endomorphism family through a tangent linear
equivalence.  The two curvature slots are pushed forward and the traced slot
is conjugated. -/
noncomputable def pullbackCurvatureEnd
    (e : E ≃L[ℝ] E) (curvTarget : E → E → (E →ₗ[ℝ] E))
    (p q : E) : E →ₗ[ℝ] E :=
  e.symm.toLinearEquiv.toLinearMap.comp
    ((curvTarget (e p) (e q)).comp e.toLinearEquiv.toLinearMap)

@[simp] theorem pullbackCurvatureEnd_apply
    (e : E ≃L[ℝ] E) (curvTarget : E → E → (E →ₗ[ℝ] E))
    (p q r : E) :
    pullbackCurvatureEnd e curvTarget p q r =
      e.symm (curvTarget (e p) (e q) (e r)) :=
  rfl

/-- Curvature is intertwined by the derivative equivalence of the coordinate
germ, by construction of the tensor pullback. -/
theorem curvature_natural_pullbackCurvatureEnd
    (e : E ≃L[ℝ] E) (curvTarget : E → E → (E →ₗ[ℝ] E))
    (p q r : E) :
    curvTarget (e p) (e q) (e r) =
      e (pullbackCurvatureEnd e curvTarget p q r) := by
  simp [pullbackCurvatureEnd]

/-- The corresponding Ricci contraction is invariant under this curvature
pullback. -/
theorem trace_pullbackCurvatureEnd
    (e : E ≃L[ℝ] E) (curvTarget : E → E → (E →ₗ[ℝ] E))
    (p q : E) :
    LinearMap.trace ℝ E (curvTarget (e p) (e q)) =
      LinearMap.trace ℝ E (pullbackCurvatureEnd e curvTarget p q) := by
  exact ricciTrace_natural_of_curvature_intertwining e.toLinearEquiv
    (pullbackCurvatureEnd e curvTarget) curvTarget
    (curvature_natural_pullbackCurvatureEnd e curvTarget) p q

end CurvaturePullback

section ModelLieSplit

variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ F]

/-- For the model Levi-Civita connection, the metric Lie derivative splits
into base-point advection plus the two ordinary derivative slot terms.  This
is the exact coordinate identity used in the DeTurck cancellation. -/
theorem modelLeviCivita_lieDeriv_eq_metricAdvection_add_fderiv_slots
    (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : F → LinearMap.BilinForm ℝ F)
    (hb : ∀ z, (b z).Nondegenerate)
    (hbg : ∀ z p q, b z p q = G z p q)
    (W : F → F) (z p q : F)
    (hGd : DifferentiableAt ℝ G z)
    (hGsymm : ∀ z p q, G z p q = G z q p)
    :
    G z ((CovariantDerivative.modelLeviCivita G b hb) W z p) q +
        G z p ((CovariantDerivative.modelLeviCivita G b hb) W z q) =
      (fderiv ℝ G z (W z)) p q +
        G z (fderiv ℝ W z p) q + G z p (fderiv ℝ W z q) := by
  let Γ : F → F → F := fun u v ↦
    CovariantDerivative.christoffelAt G z (b z) (hb z) u v
  have hΓ₁ : G z (Γ p (W z)) q = (1 / 2 : ℝ) *
      ((fderiv ℝ G z p) (W z) q +
        (fderiv ℝ G z (W z)) p q -
        (fderiv ℝ G z q) p (W z)) := by
    rw [← hbg z]
    exact CovariantDerivative.b_christoffelAt G z (b z) (hb z) p (W z) q
  have hΓ₂ : G z p (Γ q (W z)) = (1 / 2 : ℝ) *
      ((fderiv ℝ G z q) (W z) p +
        (fderiv ℝ G z (W z)) q p -
        (fderiv ℝ G z p) q (W z)) := by
    rw [hGsymm z p]
    rw [← hbg z]
    exact CovariantDerivative.b_christoffelAt G z (b z) (hb z) q (W z) p
  have hsymP := CovariantDerivative.fderiv_metric_symm G hGd
    hGsymm p (W z) q
  have hsymQ := CovariantDerivative.fderiv_metric_symm G hGd
    hGsymm q (W z) p
  have hsymW := CovariantDerivative.fderiv_metric_symm G hGd
    hGsymm (W z) q p
  rw [CovariantDerivative.modelLeviCivita_apply,
    CovariantDerivative.modelLeviCivita_apply]
  simp only [map_add, ContinuousLinearMap.add_apply]
  change
    G z (fderiv ℝ W z p) q + G z (Γ p (W z)) q +
        (G z p (fderiv ℝ W z q) + G z p (Γ q (W z))) = _
  rw [hΓ₁, hΓ₂, hsymP, hsymQ, hsymW]
  ring

/-- The model Levi-Civita derivative is local in its section argument. -/
theorem modelLeviCivita_congr_of_eventuallyEq
    (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : F → LinearMap.BilinForm ℝ F)
    (hb : ∀ z, (b z).Nondegenerate)
    {W W' : F → F} {z : F} (h : W =ᶠ[𝓝 z] W') :
    (CovariantDerivative.modelLeviCivita G b hb) W z =
      (CovariantDerivative.modelLeviCivita G b hb) W' z := by
  ext p
  rw [CovariantDerivative.modelLeviCivita_apply,
    CovariantDerivative.modelLeviCivita_apply, h.self_of_nhds, h.fderiv_eq]

end ModelLieSplit

section ChartLieSplit

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The intrinsic metric Lie derivative as a continuous bilinear form. -/
noncomputable def lieDerivMetricBilinAt
    (g : ClosedSmoothRiemannianMetric n M) (W : ∀ y : M, TM y)
    (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  let nablaW := g.leviCivita W x
  (g.inner x).comp nablaW +
    (ContinuousLinearMap.precompR (TM x) (g.inner x)).flip nablaW

@[simp] theorem lieDerivMetricBilinAt_apply
    (g : ClosedSmoothRiemannianMetric n M) (W : ∀ y : M, TM y)
    (x : M) (u w : TM x) :
    lieDerivMetricBilinAt g W x u w = lieDerivMetricAt g W x u w := by
  simp [lieDerivMetricBilinAt, lieDerivMetricAt]

omit [T2Space M] in
/-- On the genuine anchor-chart image, the coordinate field defined by the
preferred tangent-coordinate cocycle is the same field as inverse-chart
transport.  In particular, its ordinary Fréchet derivative is the derivative
of the actual transported intrinsic field, rather than an auxiliary model
field. -/
theorem chartCoordinateTangentField_apply_chart_eq_transported
    (x₀ : M) (W : ∀ y : M, TM y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) :
    chartCoordinateTangentField x₀ W (extChartAt I x₀ y) =
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ W
        (extChartAt I x₀ y) := by
  rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
    («I» := I) (x₀ := x₀) (σ := W) (y := y) hy]
  simp only [chartCoordinateTangentField]
  rw [(extChartAt I x₀).left_inv hy]
  have hsrc : y ∈ (chartAt E x₀).source := by
    rwa [← extChartAt_source I]
  have hmf := mfderiv_chartAt_eq_tangentCoordChange
    («I» := I) (x := y) (y := x₀) hsrc
  simpa using congrArg (fun L : E →L[ℝ] E ↦ L (W y)) hmf.symm

omit [T2Space M] in
/-- The two concrete coordinate realizations of an intrinsic tangent field
have the same germ at the anchor. -/
theorem chartCoordinateTangentField_eventuallyEq_transported
    (x₀ : M) (W : ∀ y : M, TM y) :
    chartCoordinateTangentField x₀ W =ᶠ[𝓝 (extChartAt I x₀ x₀)]
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ W := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds
      (mem_extChartAt_target x₀)] with z hz
  let y := (extChartAt I x₀).symm z
  have hy : y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hzy : extChartAt I x₀ y = z :=
    (extChartAt I x₀).right_inv hz
  rw [← hzy]
  exact chartCoordinateTangentField_apply_chart_eq_transported x₀ W hy

omit [T2Space M] in
/-- The coordinate cocycle field and inverse-chart transport agree as germs
at every genuine target point, not only at the chart anchor. -/
theorem chartCoordinateTangentField_eventuallyEq_transported_of_mem_target
    (x₀ : M) (W : ∀ y : M, TM y) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    chartCoordinateTangentField x₀ W =ᶠ[𝓝 z]
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ W := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hz] with z' hz'
  let y := (extChartAt I x₀).symm z'
  have hy : y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz'
  have hzy : extChartAt I x₀ y = z' :=
    (extChartAt I x₀).right_inv hz'
  rw [← hzy]
  exact chartCoordinateTangentField_apply_chart_eq_transported x₀ W hy

omit [T2Space M] in
/-- Cutoff-one-locus form of the model Lie split.  It is valid at every point
where the blended connection has the genuine chart metric as its germ. -/
theorem chartLeviCivita_lieDeriv_eq_chartMetricAdvection_add_fderiv_slots_at
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (z : E)
    (hχone : ∀ᶠ z' in 𝓝 z,
      GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (Wc : E → E) (p q : E) :
    CovariantDerivative.chartMetric g.inner x₀ z
          ((GeodesicTransport.chartLeviCivita g x₀) Wc z p) q +
        CovariantDerivative.chartMetric g.inner x₀ z p
          ((GeodesicTransport.chartLeviCivita g x₀) Wc z q) =
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z (Wc z)) p q +
        CovariantDerivative.chartMetric g.inner x₀ z
          (fderiv ℝ Wc z p) q +
        CovariantDerivative.chartMetric g.inner x₀ z p
          (fderiv ℝ Wc z q) := by
  let χ := GeodesicTransport.cutoff (n := n) x₀
  let G₀ := GeodesicTransport.backgroundMetric (n := n)
  let B := CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀
  let C := CovariantDerivative.chartMetric g.inner x₀
  let b := CovariantDerivative.chartBilin χ G₀ g.inner x₀
  let hb : ∀ z, (b z).Nondegenerate :=
    CovariantDerivative.chartBilin_nondegenerate χ G₀
      (GeodesicTransport.backgroundMetric_pos (n := n)) g.inner
      (fun y u hu ↦ g.inner_pos y (v := u) hu) x₀
      (GeodesicTransport.cutoff_nonneg (n := n) x₀)
      (GeodesicTransport.cutoff_le_one (n := n) x₀)
      (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
  have hone_le_top : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) = ((1 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hone_add_one_le_top : (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) + 1 = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg₁ :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun y : M ↦
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le hone_le_top
  have hBd : DifferentiableAt ℝ B z := by
    exact (CovariantDerivative.contDiff_blendedChartMetric χ G₀ g.inner x₀
      hone_add_one_le_top (GeodesicTransport.cutoff_contDiff (n := n) x₀)
      (GeodesicTransport.cutoff_tsupport (n := n) x₀) hg₁).differentiable
        (by norm_num) z
  have hBsymm : ∀ z p q, B z p q = B z q p := by
    intro z p q
    exact CovariantDerivative.blendedChartMetric_symm χ G₀
      (GeodesicTransport.backgroundMetric_symm (n := n)) g.inner
      (fun y v w ↦ g.inner_symm y v w) x₀ z p q
  have hBC : B =ᶠ[𝓝 z] C := by
    filter_upwards [hχone] with z' hz'
    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      χ G₀ g.inner x₀ hz'
  have hmodel :=
    modelLeviCivita_lieDeriv_eq_metricAdvection_add_fderiv_slots
      B b hb (fun _ _ _ ↦ rfl) Wc z p q hBd hBsymm
  change
    B z ((GeodesicTransport.chartLeviCivita g x₀) Wc z p) q +
        B z p ((GeodesicTransport.chartLeviCivita g x₀) Wc z q) = _
    at hmodel
  rw [hBC.self_of_nhds, hBC.fderiv_eq] at hmodel
  exact hmodel

omit [T2Space M] in
/-- The fixed anchor chart has the exact moving-field Lie split for the
unblended chart metric.  The chart connection is globally built from the
cutoff-blended metric, but the cutoff-one germ identifies both its value and
its first derivative with the genuine chart metric at the anchor. -/
theorem chartLeviCivita_lieDeriv_eq_chartMetricAdvection_add_fderiv_slots
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (Wc : E → E) (p q : E) :
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)
          ((GeodesicTransport.chartLeviCivita g x₀) Wc
            (extChartAt I x₀ x₀) p) q +
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)
          p ((GeodesicTransport.chartLeviCivita g x₀) Wc
            (extChartAt I x₀ x₀) q) =
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀)
          (extChartAt I x₀ x₀) (Wc (extChartAt I x₀ x₀))) p q +
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)
          (fderiv ℝ Wc (extChartAt I x₀ x₀) p) q +
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)
          p (fderiv ℝ Wc (extChartAt I x₀ x₀) q) := by
  let χ := GeodesicTransport.cutoff (n := n) x₀
  let G₀ := GeodesicTransport.backgroundMetric (n := n)
  let B := CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀
  let C := CovariantDerivative.chartMetric g.inner x₀
  let b := CovariantDerivative.chartBilin χ G₀ g.inner x₀
  let hb : ∀ z, (b z).Nondegenerate :=
    CovariantDerivative.chartBilin_nondegenerate χ G₀
      (GeodesicTransport.backgroundMetric_pos (n := n)) g.inner
      (fun y u hu ↦ g.inner_pos y (v := u) hu) x₀
      (GeodesicTransport.cutoff_nonneg (n := n) x₀)
      (GeodesicTransport.cutoff_le_one (n := n) x₀)
      (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
  let z₀ := extChartAt I x₀ x₀
  have hone_le_top : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) = ((1 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hone_add_one_le_top : (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) + 1 = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg₁ :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun y : M ↦
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le hone_le_top
  have hBd : DifferentiableAt ℝ B z₀ := by
    exact (CovariantDerivative.contDiff_blendedChartMetric χ G₀ g.inner x₀
      hone_add_one_le_top (GeodesicTransport.cutoff_contDiff (n := n) x₀)
      (GeodesicTransport.cutoff_tsupport (n := n) x₀) hg₁).differentiable
        (by norm_num) z₀
  have hBsymm : ∀ z p q, B z p q = B z q p := by
    intro z p q
    exact CovariantDerivative.blendedChartMetric_symm χ G₀
      (GeodesicTransport.backgroundMetric_symm (n := n)) g.inner
      (fun y v w ↦ g.inner_symm y v w) x₀ z p q
  have hBC : B =ᶠ[𝓝 z₀] C := by
    filter_upwards [GeodesicTransport.cutoff_eventuallyEq_one (n := n) x₀]
      with z hz
    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      χ G₀ g.inner x₀ hz
  have hmodel :=
    modelLeviCivita_lieDeriv_eq_metricAdvection_add_fderiv_slots
      B b hb (fun _ _ _ ↦ rfl) Wc z₀ p q hBd hBsymm
  change
    B z₀ ((GeodesicTransport.chartLeviCivita g x₀) Wc z₀ p) q +
        B z₀ p ((GeodesicTransport.chartLeviCivita g x₀) Wc z₀ q) = _
    at hmodel
  rw [hBC.self_of_nhds, hBC.fderiv_eq] at hmodel
  exact hmodel

/-- At its anchor, the transported model Levi-Civita derivative of a
differentiable intrinsic field is literally the intrinsic Levi-Civita
derivative, under Mathlib's preferred-chart tangent identification. -/
theorem chartLeviCivita_apply_anchor_eq_closed
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (W : ∀ y : M, TM y) (hW : MDiffAtTangentField W x₀) (p : E) :
    (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ W)
        (extChartAt I x₀ x₀) p =
      g.leviCivita W x₀ p := by
  let X : ∀ y : M, TM y := fun _ ↦ p
  have h :=
    ChartCurvatureBridge6.chartTransportedLeviCivitaSection_closed_hom_apply_anchor
      (g := g) (x₀ := x₀) (σ := W) (X := X) hW
  have hleft :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M ↦ g.leviCivita W y (X y))
          (extChartAt I x₀ x₀) =
        g.leviCivita W x₀ p := by
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x₀)
        (σ := fun y : M ↦ g.leviCivita W y (X y))
        (y := x₀) (mem_extChartAt_source x₀)
    rw [mfderiv_extChartAt_self] at happly
    simpa [X] using happly
  have hX :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ X
          (extChartAt I x₀ x₀) = p := by
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x₀) (σ := X)
        (y := x₀) (mem_extChartAt_source x₀)
    rw [mfderiv_extChartAt_self] at happly
    simpa [X] using happly
  rw [hleft, hX] at h
  exact h.symm

/-- The intrinsic metric Lie derivative is exactly the ordinary coordinate
advection-and-two-slot expression for the actual preferred-chart
representative of the moving field. -/
theorem lieDerivMetricAt_eq_chartMetricAdvection_add_fderiv_slots
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (W : ∀ y : M, TM y) (hW : MDiffAtTangentField W x₀) (p q : E) :
    lieDerivMetricAt g W x₀ p q =
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀)
          (extChartAt I x₀ x₀)
          (chartCoordinateTangentField x₀ W (extChartAt I x₀ x₀))) p q +
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)
          (fderiv ℝ (chartCoordinateTangentField x₀ W)
            (extChartAt I x₀ x₀) p) q +
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)
          p (fderiv ℝ (chartCoordinateTangentField x₀ W)
            (extChartAt I x₀ x₀) q) := by
  let Wc := chartCoordinateTangentField x₀ W
  let Wt := CovariantDerivative.chartTransportedLeviCivitaSection x₀ W
  let z₀ := extChartAt I x₀ x₀
  have hcoord : Wc =ᶠ[𝓝 z₀] Wt := by
    simpa [Wc, Wt, z₀] using
      chartCoordinateTangentField_eventuallyEq_transported x₀ W
  have hconn :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z₀ =
        (GeodesicTransport.chartLeviCivita g x₀) Wt z₀ := by
    simpa [GeodesicTransport.chartLeviCivita,
      CovariantDerivative.chartLeviCivita] using
      (modelLeviCivita_congr_of_eventuallyEq
        (G := CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀)
        (b := CovariantDerivative.chartBilin
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀)
        (hb := CovariantDerivative.chartBilin_nondegenerate
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n))
          (GeodesicTransport.backgroundMetric_pos (n := n)) g.inner
          (fun y u hu ↦ g.inner_pos y (v := u) hu) x₀
          (GeodesicTransport.cutoff_nonneg (n := n) x₀)
          (GeodesicTransport.cutoff_le_one (n := n) x₀)
          (GeodesicTransport.cutoff_support_invertible (n := n) x₀))
        hcoord)
  have hconnP :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z₀ p =
        (GeodesicTransport.chartLeviCivita g x₀) Wt z₀ p := by
    exact congrArg (fun L : E →L[ℝ] E ↦ L p) hconn
  have hconnQ :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z₀ q =
        (GeodesicTransport.chartLeviCivita g x₀) Wt z₀ q := by
    exact congrArg (fun L : E →L[ℝ] E ↦ L q) hconn
  have hclosedP := chartLeviCivita_apply_anchor_eq_closed g x₀ W hW p
  have hclosedQ := chartLeviCivita_apply_anchor_eq_closed g x₀ W hW q
  have hLCP :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z₀ p =
        g.leviCivita W x₀ p := hconnP.trans hclosedP
  have hLCQ :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z₀ q =
        g.leviCivita W x₀ q := hconnQ.trans hclosedQ
  have hmetric (a b : E) :
      CovariantDerivative.chartMetric g.inner x₀ z₀ a b =
        g.inner x₀ a b := by
    have h := CovariantDerivative.chartMetric_apply_chart g.inner x₀
      (mem_extChartAt_source x₀) a b
    rw [mfderiv_extChartAt_self] at h
    simpa [z₀] using h
  have hsplit :=
    chartLeviCivita_lieDeriv_eq_chartMetricAdvection_add_fderiv_slots
      g x₀ Wc p q
  change
    CovariantDerivative.chartMetric g.inner x₀ z₀
          ((GeodesicTransport.chartLeviCivita g x₀) Wc z₀ p) q +
        CovariantDerivative.chartMetric g.inner x₀ z₀ p
          ((GeodesicTransport.chartLeviCivita g x₀) Wc z₀ q) = _
    at hsplit
  calc
    lieDerivMetricAt g W x₀ p q =
        CovariantDerivative.chartMetric g.inner x₀ z₀
            ((GeodesicTransport.chartLeviCivita g x₀) Wc z₀ p) q +
          CovariantDerivative.chartMetric g.inner x₀ z₀ p
            ((GeodesicTransport.chartLeviCivita g x₀) Wc z₀ q) := by
              rw [lieDerivMetricAt, hmetric, hmetric, hLCP, hLCQ]
    _ = _ := by simpa [Wc, z₀] using hsplit

/-- Source-point form of the intrinsic Lie split on the full cutoff-one chart
locus.  Constant model directions are realized by canonical manifold
extensions, and the closed/chart Levi-Civita naturality theorem transports
their covariant derivatives exactly. -/
theorem chartMetric_lieDerivBilin_eq_advection_add_fderiv_slots_at
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I x₀ y),
      GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (W : ∀ y : M, TM y) (hW : MDiffAtTangentField W y) (p q : E) :
    CovariantDerivative.chartMetric
        (fun a ↦ lieDerivMetricBilinAt g W a) x₀ (extChartAt I x₀ y) p q =
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀)
          (extChartAt I x₀ y)
          (chartCoordinateTangentField x₀ W (extChartAt I x₀ y))) p q +
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ y)
          (fderiv ℝ (chartCoordinateTangentField x₀ W)
            (extChartAt I x₀ y) p) q +
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ y)
          p (fderiv ℝ (chartCoordinateTangentField x₀ W)
            (extChartAt I x₀ y) q) := by
  let z := extChartAt I x₀ y
  let Wc := chartCoordinateTangentField x₀ W
  let Wt := CovariantDerivative.chartTransportedLeviCivitaSection x₀ W
  let Xp : ∀ a : M, TM a := extend E (x := x₀) p
  let Xq : ∀ a : M, TM a := extend E (x := x₀) q
  have hz : z ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hXp :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ Xp z = p := by
    simpa [Xp, z] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x₀) (y := y) hy p)
  have hXq :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ Xq z = q := by
    simpa [Xq, z] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x₀) (y := y) hy q)
  have hcoord : Wc =ᶠ[𝓝 z] Wt := by
    exact chartCoordinateTangentField_eventuallyEq_transported_of_mem_target
      x₀ W hz
  have hconn :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z =
        (GeodesicTransport.chartLeviCivita g x₀) Wt z := by
    simpa [GeodesicTransport.chartLeviCivita,
      CovariantDerivative.chartLeviCivita] using
      (modelLeviCivita_congr_of_eventuallyEq
        (G := CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀)
        (b := CovariantDerivative.chartBilin
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀)
        (hb := CovariantDerivative.chartBilin_nondegenerate
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n))
          (GeodesicTransport.backgroundMetric_pos (n := n)) g.inner
          (fun a u hu ↦ g.inner_pos a (v := u) hu) x₀
          (GeodesicTransport.cutoff_nonneg (n := n) x₀)
          (GeodesicTransport.cutoff_le_one (n := n) x₀)
          (GeodesicTransport.cutoff_support_invertible (n := n) x₀))
        hcoord)
  have hnatP :=
    ChartCurvatureBridgeZoneClose.chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
      (g := g) (x₀ := x₀) (y := y) hy hχone W Xp hW
  have hnatQ :=
    ChartCurvatureBridgeZoneClose.chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
      (g := g) (x₀ := x₀) (y := y) hy hχone W Xq hW
  have hconnP :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z p =
        (GeodesicTransport.chartLeviCivita g x₀) Wt z p := by
    exact congrArg (fun L : E →L[ℝ] E ↦ L p) hconn
  have hconnQ :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z q =
        (GeodesicTransport.chartLeviCivita g x₀) Wt z q := by
    exact congrArg (fun L : E →L[ℝ] E ↦ L q) hconn
  have hLCP :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z p =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun a : M ↦ g.leviCivita W a (Xp a)) z := by
    calc
      _ = (GeodesicTransport.chartLeviCivita g x₀) Wt z p := hconnP
      _ = _ := by
        rw [hXp] at hnatP
        exact hnatP.symm
  have hLCQ :
      (GeodesicTransport.chartLeviCivita g x₀) Wc z q =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun a : M ↦ g.leviCivita W a (Xq a)) z := by
    calc
      _ = (GeodesicTransport.chartLeviCivita g x₀) Wt z q := hconnQ
      _ = _ := by
        rw [hXq] at hnatQ
        exact hnatQ.symm
  have htermP :=
    CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection
      g.inner x₀ (fun a : M ↦ g.leviCivita W a (Xp a)) Xq hz
  have htermQ :=
    CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection
      g.inner x₀ Xp (fun a : M ↦ g.leviCivita W a (Xq a)) hz
  have hlie :=
    CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection
      (fun a ↦ lieDerivMetricBilinAt g W a) x₀ Xp Xq hz
  have hsplit :=
    chartLeviCivita_lieDeriv_eq_chartMetricAdvection_add_fderiv_slots_at
      g x₀ z (by simpa [z] using hχone) Wc p q
  have hleft :
      CovariantDerivative.chartMetric
          (fun a ↦ lieDerivMetricBilinAt g W a) x₀ z p q =
        CovariantDerivative.chartMetric g.inner x₀ z
            ((GeodesicTransport.chartLeviCivita g x₀) Wc z p) q +
          CovariantDerivative.chartMetric g.inner x₀ z p
            ((GeodesicTransport.chartLeviCivita g x₀) Wc z q) := by
    rw [hLCP, hLCQ]
    rw [hXp, hXq] at hlie
    rw [hXq] at htermP
    rw [hXp] at htermQ
    rw [hlie]
    simpa [z, (extChartAt I x₀).left_inv hy,
      lieDerivMetricBilinAt_apply, lieDerivMetricAt] using
      congrArg₂ (fun a b : ℝ ↦ a + b) htermP.symm htermQ.symm
  rw [hleft]
  simpa [Wc, z] using hsplit

end ChartLieSplit

section ConcreteDeTurckEvolution

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The concrete DeTurck-gauged flow predicate gives the pointwise bilinear
metric evolution equation.  The bump extension removes the test-field
quantifier, while germ locality of the Ricci trace identifies its contraction
with the intrinsic Ricci tensor. -/
theorem isDeTurckGaugedFlowAt_timeDerivAt_eq_neg_two_ricciAt_add_lie
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsDeTurckGaugedFlowAt gt bg t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (v w : TM x) :
    timeDerivAt gt t₀ x v w =
      -2 * (gt t₀).ricciAt x v w +
        lieDerivMetricAt (gt t₀) (deTurckVectorField gt bg t₀) x v w := by
  let Z : ∀ y : M, TM y := bumpExtend (n := n) (M := M) x v
  have hZ : ClosedC2TangentField Z := by
    simpa [Z] using bumpExtend_closedC2TangentField (n := n) (M := M) x v
  have hregZ : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x := by
    exact CovariantDerivative.derivRegularAt_of_contMDiff
      (cov := (gt t₀).leviCivita) hZ x
  have hregExt :
      CovariantDerivative.DerivRegularAt (gt t₀).leviCivita (extend E v) x :=
    hext v
  have hflow' := hflow.flow hZ hregZ w
  have htraceCongr :
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregZ w =
        CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w := by
    exact ricciTraceAt_congr_of_eventuallyEq
      (cov := (gt t₀).leviCivita)
      (Z := Z) (Z' := extend E v) (x := x)
      (by simpa [Z] using (hZ x))
      (FiberBundle.contMDiffAt_extend' (k := 2) I E v)
      hregZ hregExt
      (by simpa [Z] using
        (bumpExtend_eventuallyEq_extend (n := n) (M := M) x v))
      w
  have htrace :
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w =
        (gt t₀).ricciAt x v w := by
    have h :=
      CovariantDerivative.ricciTraceAt_eq_ricciBilinearAt
        (cov := (gt t₀).leviCivita) (Z := extend E v) (x := x)
        (FiberBundle.contMDiffAt_extend' (k := 2) I E v) hregExt w
    calc
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w =
          (gt t₀).ricciAt x w v := by
            simpa [ClosedSmoothRiemannianMetric.ricciAt] using h
      _ = (gt t₀).ricciAt x v w := (gt t₀).ricciAt_symm x w v
  rw [htraceCongr, htrace] at hflow'
  simpa [timeDerivAt, IsDeTurckGaugedFlowAt, Z] using hflow'

/-- The intrinsic Ricci tensor as a continuous bilinear form on a tangent
fiber.  Finite dimensionality upgrades the algebraic Ricci dual map to a
continuous one. -/
noncomputable def ricciContinuousBilinAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    (((LinearMap.toContinuousLinearMap :
        (TM x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TM x →L[ℝ] ℝ)).toLinearMap) ∘ₗ
      CovariantDerivative.ricciDualAt g.leviCivita x)

@[simp] theorem ricciContinuousBilinAt_apply
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    ricciContinuousBilinAt g x u w = g.ricciAt x u w := by
  simp [ricciContinuousBilinAt, ClosedSmoothRiemannianMetric.ricciAt,
    CovariantDerivative.ricciDualAt]

/-- The metric along a coordinate inverse-gauge trajectory, pulled through
its variational differential.  This is an actual continuous bilinear metric
family on the fixed source model space. -/
noncomputable def inverseGaugePulledChartMetric
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E) (t : ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  pullbackBilinearForm
    (CovariantDerivative.chartMetric (gt t).inner anchor (phi t)) (D t)

omit [T2Space M] in
@[simp] theorem inverseGaugePulledChartMetric_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E) (t : ℝ) (u w : E) :
    inverseGaugePulledChartMetric gt anchor phi D t u w =
      pullbackBilinearApply
        (fun s ↦ CovariantDerivative.chartMetric (gt s).inner anchor (phi s))
        D u w t :=
  rfl

omit [T2Space M] in
/-- At an identity-gauge time, the pulled chart metric is the original chart
metric at the trajectory point. -/
theorem inverseGaugePulledChartMetric_at_identity
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E) (t₀ : ℝ)
    (hD₀ : D t₀ = ContinuousLinearMap.id ℝ E) :
    inverseGaugePulledChartMetric gt anchor phi D t₀ =
      CovariantDerivative.chartMetric (gt t₀).inner anchor (phi t₀) := by
  ext u w
  simp [inverseGaugePulledChartMetric, hD₀]

omit [T2Space M] in
/-- If the coordinate trajectory starts at a genuine chart point and its
variational differential starts at the identity, the pulled chart metric
recovers the intrinsic initial metric on chart-pushed tangent vectors. -/
theorem inverseGaugePulledChartMetric_apply_chart_at_identity
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E) (t₀ : ℝ) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hphi₀ : phi t₀ = extChartAt I anchor y)
    (hD₀ : D t₀ = ContinuousLinearMap.id ℝ E)
    (v w : TM y) :
    inverseGaugePulledChartMetric gt anchor phi D t₀
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y w) =
      (gt t₀).inner y v w := by
  rw [inverseGaugePulledChartMetric_at_identity gt anchor phi D t₀ hD₀,
    hphi₀]
  exact CovariantDerivative.chartMetric_apply_chart (gt t₀).inner anchor hy v w

omit [T2Space M] in
/-- Gauge pullback preserves the symmetry of the chart metric. -/
theorem inverseGaugePulledChartMetric_symm
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E) (t : ℝ) (u w : E) :
    inverseGaugePulledChartMetric gt anchor phi D t u w =
      inverseGaugePulledChartMetric gt anchor phi D t w u := by
  exact CovariantDerivative.chartMetric_symm (gt t).inner
    (fun y p q ↦ (gt t).inner_symm y p q) anchor (phi t) (D t u) (D t w)

omit [T2Space M] in
/-- On the inverse-chart target, an invertible gauge differential makes the
pulled chart metric positive definite. -/
theorem inverseGaugePulledChartMetric_posDef
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E) (t : ℝ)
    (hphi : phi t ∈ (extChartAt I anchor).target)
    (hDinv : (D t).IsInvertible) {u : E} (hu : u ≠ 0) :
    0 < inverseGaugePulledChartMetric gt anchor phi D t u u := by
  rcases hDinv with ⟨e, he⟩
  have hDu : D t u ≠ 0 := by
    intro hzero
    have heu : e u = 0 := by
      change (e : E →L[ℝ] E) u = 0
      rw [he]
      exact hzero
    exact hu (e.injective (by simpa using heu))
  exact CovariantDerivative.chartMetric_posDef (gt t).inner
    (fun y p hp ↦ (gt t).inner_pos y hp) anchor
    (isInvertible_mfderivWithin_extChartAt_symm hphi) hDu

omit [T2Space M] in
/-- Consequently the pulled chart metric has trivial left kernel wherever
the coordinate endpoint and its differential define a local gauge map. -/
theorem inverseGaugePulledChartMetric_nondegenerate
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E) (t : ℝ)
    (hphi : phi t ∈ (extChartAt I anchor).target)
    (hDinv : (D t).IsInvertible) (u : E)
    (hu : ∀ w : E, inverseGaugePulledChartMetric gt anchor phi D t u w = 0) :
    u = 0 := by
  by_contra hune
  exact (ne_of_gt (inverseGaugePulledChartMetric_posDef
    gt anchor phi D t hphi hDinv hune)) (hu u)

/-- The concrete Ricci tensor transported to a chart. -/
noncomputable def deTurckChartRicciBilin
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t : ℝ) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  CovariantDerivative.chartMetric
    (fun y ↦ ricciContinuousBilinAt (gt t) y) anchor z

/-- The curvature endomorphism whose trace is the Ricci tensor, with the
project's slot convention `v ↦ R(v,u)w`. -/
noncomputable def ricciCurvatureEndAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TM x) : TM x →ₗ[ℝ] TM x :=
  CovariantDerivative.curvatureEndAt g.leviCivita
    (CovariantDerivative.derivRegularAt_extend g.leviCivita w) u

/-- The actual inverse-chart tangent equivalence at a genuine target point. -/
noncomputable def chartInverseTangentEquiv
    (anchor : M) (z : E) (hz : z ∈ (extChartAt I anchor).target) : E ≃L[ℝ] E :=
  Classical.choose
    (isInvertible_mfderivWithin_extChartAt_symm («I» := I) (x := anchor) hz)

omit [T2Space M] in
theorem chartInverseTangentEquiv_toContinuousLinearMap
    (anchor : M) (z : E) (hz : z ∈ (extChartAt I anchor).target) :
    (chartInverseTangentEquiv anchor z hz : E →L[ℝ] E) =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor).symm)
        (Set.range I) z :=
  Classical.choose_spec
    (isInvertible_mfderivWithin_extChartAt_symm («I» := I) (x := anchor) hz)

omit [T2Space M] in
/-- The derivative of an honest preferred-chart transition is invertible. -/
theorem chartTransitionDeriv_isInvertible
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source) :
    (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z).IsInvertible := by
  rw [GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
    anchor₁ anchor₂ hz hy]
  dsimp [GeodesicTransport.chartTransitionMFDeriv]
  exact (isInvertible_mfderiv_extChartAt hy).comp
    (isInvertible_mfderivWithin_extChartAt_symm hz)

/-- The continuous linear equivalence represented by the derivative of an
honest preferred-chart transition. -/
noncomputable def chartTransitionTangentEquiv
    (anchor₁ anchor₂ : M) (z : E)
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source) : E ≃L[ℝ] E :=
  Classical.choose (chartTransitionDeriv_isInvertible anchor₁ anchor₂ hz hy)

omit [T2Space M] in
theorem chartTransitionTangentEquiv_toContinuousLinearMap
    (anchor₁ anchor₂ : M) (z : E)
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source) :
    (chartTransitionTangentEquiv anchor₁ anchor₂ z hz hy : E →L[ℝ] E) =
      GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z :=
  Classical.choose_spec (chartTransitionDeriv_isInvertible anchor₁ anchor₂ hz hy)

omit [T2Space M] in
/-- Any intrinsic continuous bilinear tensor has compatible representatives
in two honest preferred charts.  The proof uses the actual inverse-chart and
forward-chart differentials, so this applies to the Ricci tensor rather than
only to metrics. -/
theorem chartBilinearTensor_chartTransitionDeriv
    (B : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] ℝ)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (u v : E) :
    CovariantDerivative.chartMetric B anchor₂
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
      CovariantDerivative.chartMetric B anchor₁ z u v := by
  rw [GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
    anchor₁ anchor₂ hz hy]
  have hleft :=
    CovariantDerivative.chartMetric_apply_chart B anchor₂ hy
      ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor₁).symm)
        (Set.range I) z) u)
      ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor₁).symm)
        (Set.range I) z) v)
  simp only [GeodesicTransport.chartTransition,
    GeodesicTransport.chartTransitionMFDeriv]
  change
    CovariantDerivative.chartMetric B anchor₂
        (extChartAt I anchor₂ ((extChartAt I anchor₁).symm z))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I anchor₂)
            ((extChartAt I anchor₁).symm z))
          ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor₁).symm)
              (Set.range I) z) u))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I anchor₂)
            ((extChartAt I anchor₁).symm z))
          ((mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor₁).symm)
              (Set.range I) z) v)) =
      CovariantDerivative.chartMetric B anchor₁ z u v
  rw [hleft]
  rw [CovariantDerivative.chartMetric_apply]

/-- In particular, the concrete chart Ricci tensors agree under the actual
preferred-chart transition differential. -/
theorem deTurckChartRicciBilin_chartTransitionDeriv
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (u v : E) :
    deTurckChartRicciBilin gt anchor₂ t
        (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
      deTurckChartRicciBilin gt anchor₁ t z u v := by
  exact chartBilinearTensor_chartTransitionDeriv
    (fun x ↦ ricciContinuousBilinAt (gt t) x)
    anchor₁ anchor₂ hz hy u v

/-- Intrinsic curvature expressed in a genuine preferred chart. -/
noncomputable def chartRicciCurvatureEndAt
    (g : ClosedSmoothRiemannianMetric n M)
    (anchor : M) (z : E) (hz : z ∈ (extChartAt I anchor).target) :
    E → E → (E →ₗ[ℝ] E) :=
  pullbackCurvatureEnd (chartInverseTangentEquiv anchor z hz)
    (ricciCurvatureEndAt g ((extChartAt I anchor).symm z))

/-- The chart curvature representative is independent of the proof supplied
for target membership and respects equality of its coordinate point. -/
theorem chartRicciCurvatureEndAt_congr
    (g : ClosedSmoothRiemannianMetric n M) (anchor : M)
    {z w : E} (hz : z ∈ (extChartAt I anchor).target)
    (hw : w ∈ (extChartAt I anchor).target) (hzw : z = w) :
    chartRicciCurvatureEndAt g anchor z hz =
      chartRicciCurvatureEndAt g anchor w hw := by
  subst w
  rfl

/-- At every genuine chart point, the chart Ricci tensor is the trace of the
actual inverse-chart pullback of intrinsic curvature. -/
theorem deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ) (z : E)
    (hz : z ∈ (extChartAt I anchor).target) (p q : E) :
    deTurckChartRicciBilin gt anchor t z p q =
      LinearMap.trace ℝ E (chartRicciCurvatureEndAt (gt t) anchor z hz p q) := by
  let e := chartInverseTangentEquiv anchor z hz
  have he : (e : E →L[ℝ] E) =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor).symm)
        (Set.range I) z := by
    exact chartInverseTangentEquiv_toContinuousLinearMap anchor z hz
  have htrace := trace_pullbackCurvatureEnd e
    (ricciCurvatureEndAt (gt t) ((extChartAt I anchor).symm z)) p q
  have hep : e p =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor).symm)
        (Set.range I) z p := by
    change (e : E →L[ℝ] E) p = _
    rw [he]
    rfl
  have heq : e q =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I anchor).symm)
        (Set.range I) z q := by
    change (e : E →L[ℝ] E) q = _
    rw [he]
    rfl
  rw [deTurckChartRicciBilin, CovariantDerivative.chartMetric_apply,
    ricciContinuousBilinAt_apply]
  rw [hep, heq] at htrace
  simpa [chartRicciCurvatureEndAt, e, ricciCurvatureEndAt,
    ClosedSmoothRiemannianMetric.ricciAt,
    CovariantDerivative.ricciBilinearAt,
    CovariantDerivative.ricciTraceAt] using htrace

/-- The Ricci-flow derivative produced by the inverse-gauge pullback is
independent of the preferred chart.  The source vectors are related by the
actual source chart-transition derivative; the variational derivatives are
then conjugate because the two endpoint maps agree as germs. -/
theorem inverseGaugeRicciTrace_chartTransition_eq
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
    (u v : E) :
    let S := chartTransitionTangentEquiv anchor₁ anchor₂ z hz hy
    LinearMap.trace ℝ E
        (pullbackCurvatureEnd e₂
          (chartRicciCurvatureEndAt (gt t) anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z)) hz₂')
          (S u) (S v)) =
      LinearMap.trace ℝ E
        (pullbackCurvatureEnd e₁
          (chartRicciCurvatureEndAt (gt t) anchor₁ (Phi₁ z) hz') u v) := by
  let S := chartTransitionTangentEquiv anchor₁ anchor₂ z hz hy
  let T := chartTransitionTangentEquiv anchor₁ anchor₂ (Phi₁ z) hz' hy'
  have hoverlap :
      z ∈ ((extChartAt I anchor₁).symm ≫ extChartAt I anchor₂).source := by
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using
      And.intro hz hy
  have hoverlap' :
      Phi₁ z ∈
        ((extChartAt I anchor₁).symm ≫ extChartAt I anchor₂).source := by
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using
      And.intro hz' hy'
  have hconj := chartTransition_flow_fderiv_conjugacy
    anchor₁ anchor₂
    (chartTransition_differentiableAt_of_mem_source anchor₁ anchor₂ hoverlap)
    hPhi₁ hPhi₂
    (chartTransition_differentiableAt_of_mem_source anchor₁ anchor₂ hoverlap')
    hcompat
  have hS : (S : E →L[ℝ] E) =
      GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z := by
    exact chartTransitionTangentEquiv_toContinuousLinearMap
      anchor₁ anchor₂ z hz hy
  have hT : (T : E →L[ℝ] E) =
      GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ (Phi₁ z) := by
    exact chartTransitionTangentEquiv_toContinuousLinearMap
      anchor₁ anchor₂ (Phi₁ z) hz' hy'
  have hconj_apply (w : E) : e₂ (S w) = T (e₁ w) := by
    have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hconj
    change (e₂ : E →L[ℝ] E) ((S : E →L[ℝ] E) w) =
      (T : E →L[ℝ] E) ((e₁ : E →L[ℝ] E) w)
    rw [he₁, he₂, hS, hT]
    simpa [ContinuousLinearMap.comp_apply] using hw
  let C₁ := chartRicciCurvatureEndAt (gt t) anchor₁ (Phi₁ z) hz'
  let C₂ := chartRicciCurvatureEndAt (gt t) anchor₂
    (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z)) hz₂'
  change LinearMap.trace ℝ E
      (pullbackCurvatureEnd e₂ C₂ (S u) (S v)) =
    LinearMap.trace ℝ E (pullbackCurvatureEnd e₁ C₁ u v)
  calc
    LinearMap.trace ℝ E (pullbackCurvatureEnd e₂ C₂ (S u) (S v)) =
        LinearMap.trace ℝ E (C₂ (e₂ (S u)) (e₂ (S v))) :=
      (trace_pullbackCurvatureEnd e₂ C₂ (S u) (S v)).symm
    _ = LinearMap.trace ℝ E (C₂ (T (e₁ u)) (T (e₁ v))) := by
      rw [hconj_apply u, hconj_apply v]
    _ = deTurckChartRicciBilin gt anchor₂ t
        (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z))
        (T (e₁ u)) (T (e₁ v)) := by
      symm
      exact deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
        gt anchor₂ t
        (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z))
        hz₂' (T (e₁ u)) (T (e₁ v))
    _ = deTurckChartRicciBilin gt anchor₁ t (Phi₁ z) (e₁ u) (e₁ v) := by
      change deTurckChartRicciBilin gt anchor₂ t
          (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ z))
          ((T : E →L[ℝ] E) (e₁ u)) ((T : E →L[ℝ] E) (e₁ v)) =
        deTurckChartRicciBilin gt anchor₁ t (Phi₁ z) (e₁ u) (e₁ v)
      rw [hT]
      exact deTurckChartRicciBilin_chartTransitionDeriv
        gt t anchor₁ anchor₂ hz' hy' (e₁ u) (e₁ v)
    _ = LinearMap.trace ℝ E (C₁ (e₁ u) (e₁ v)) := by
      exact deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
        gt anchor₁ t (Phi₁ z) hz' (e₁ u) (e₁ v)
    _ = LinearMap.trace ℝ E (pullbackCurvatureEnd e₁ C₁ u v) :=
      trace_pullbackCurvatureEnd e₁ C₁ u v

/-- At a preferred-chart anchor, the transported Ricci tensor is literally
the trace of the corresponding intrinsic curvature endomorphism. -/
theorem deTurckChartRicciBilin_apply_anchor_eq_trace_curvatureEnd
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ) (p q : E) :
    deTurckChartRicciBilin gt anchor t (extChartAt I anchor anchor) p q =
      LinearMap.trace ℝ E (ricciCurvatureEndAt (gt t) anchor p q) := by
  have hchart := CovariantDerivative.chartMetric_apply_chart
    (fun y ↦ ricciContinuousBilinAt (gt t) y) anchor
    (mem_extChartAt_source anchor) p q
  rw [mfderiv_extChartAt_self] at hchart
  simpa [deTurckChartRicciBilin, ricciCurvatureEndAt,
    ricciContinuousBilinAt_apply, ClosedSmoothRiemannianMetric.ricciAt,
    CovariantDerivative.ricciBilinearAt,
    CovariantDerivative.ricciTraceAt] using hchart

/-- The concrete metric Lie derivative transported to a chart. -/
noncomputable def deTurckChartLieBilin
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t : ℝ) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  CovariantDerivative.chartMetric
    (fun y ↦ lieDerivMetricBilinAt (gt t) (deTurckVectorField gt bg t) y)
    anchor z

/-- Base-point advection of the chart metric by the concrete DeTurck field at
an arbitrary model point. -/
noncomputable def deTurckChartMetricAdvectionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (t : ℝ) (z : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor) z
    (chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z)

/-- Ordinary coordinate derivative of the concrete DeTurck field at an
arbitrary model point. -/
noncomputable def deTurckChartFieldDerivativeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (t : ℝ) (z : E) :
    E →L[ℝ] E :=
  fderiv ℝ
    (chartCoordinateTangentField anchor (deTurckVectorField gt bg t)) z

/-- The concrete DeTurck Lie split at every genuine chart point in the
cutoff-one locus. -/
theorem deTurckChartLieBilin_apply_chart_eq_advection_add_DW_slots
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (t : ℝ)
    {y : M} (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hreg : DeTurckVectorFieldRegularAt gt bg t) (p q : E) :
    deTurckChartLieBilin gt bg anchor t (extChartAt I anchor y) p q =
      deTurckChartMetricAdvectionAt gt bg anchor t (extChartAt I anchor y) p q +
        CovariantDerivative.chartMetric (gt t).inner anchor
          (extChartAt I anchor y)
          (deTurckChartFieldDerivativeAt gt bg anchor t
            (extChartAt I anchor y) p) q +
        CovariantDerivative.chartMetric (gt t).inner anchor
          (extChartAt I anchor y) p
          (deTurckChartFieldDerivativeAt gt bg anchor t
            (extChartAt I anchor y) q) := by
  let W := deTurckVectorField gt bg t
  have hreg' : ClosedC2TangentField (n := n) (M := M) W := by
    simpa [W, DeTurckVectorFieldRegularAt] using hreg
  have hW : MDiffAtTangentField W y := by
    simpa [MDiffAtTangentField] using
      (hreg'.contMDiffAt.mdifferentiableAt two_ne_zero)
  simpa [deTurckChartLieBilin, deTurckChartMetricAdvectionAt,
    deTurckChartFieldDerivativeAt, W] using
    (chartMetric_lieDerivBilin_eq_advection_add_fderiv_slots_at
      (gt t) anchor hy hχone W hW p q)

/-- At the anchor, regularity of the concrete DeTurck field discharges the
moving-chart Lie-split obligation with the actual coordinate field and its
ordinary Fréchet derivative. -/
theorem deTurckChartLieBilin_apply_anchor_eq_metricAdvection_add_fderiv_slots
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (t : ℝ)
    (hreg : DeTurckVectorFieldRegularAt gt bg t) (p q : E) :
    deTurckChartLieBilin gt bg anchor t (extChartAt I anchor anchor) p q =
      (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
          (extChartAt I anchor anchor)
          (chartCoordinateTangentField anchor (deTurckVectorField gt bg t)
            (extChartAt I anchor anchor))) p q +
        CovariantDerivative.chartMetric (gt t).inner anchor
          (extChartAt I anchor anchor)
          (fderiv ℝ
            (chartCoordinateTangentField anchor (deTurckVectorField gt bg t))
            (extChartAt I anchor anchor) p) q +
        CovariantDerivative.chartMetric (gt t).inner anchor
          (extChartAt I anchor anchor) p
          (fderiv ℝ
            (chartCoordinateTangentField anchor (deTurckVectorField gt bg t))
            (extChartAt I anchor anchor) q) := by
  let W := deTurckVectorField gt bg t
  have hreg' : ClosedC2TangentField (n := n) (M := M) W := by
    simpa [W, DeTurckVectorFieldRegularAt] using hreg
  have hW : MDiffAtTangentField W anchor := by
    simpa [MDiffAtTangentField] using
      (hreg'.contMDiffAt.mdifferentiableAt two_ne_zero)
  have hchart := CovariantDerivative.chartMetric_apply_chart
    (fun y ↦ lieDerivMetricBilinAt (gt t) W y) anchor
    (mem_extChartAt_source anchor) p q
  rw [mfderiv_extChartAt_self] at hchart
  have hvalue :
      deTurckChartLieBilin gt bg anchor t (extChartAt I anchor anchor) p q =
        lieDerivMetricAt (gt t) W anchor p q := by
    simpa [deTurckChartLieBilin, W] using hchart
  rw [hvalue]
  simpa [W] using
    (lieDerivMetricAt_eq_chartMetricAdvection_add_fderiv_slots
      (gt t) anchor W hW p q)

/-- Base-point advection of the chart metric by the concrete DeTurck field at
the preferred-chart anchor. -/
noncomputable def deTurckChartMetricAdvectionAtAnchor
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (t : ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
    (extChartAt I anchor anchor)
    (chartCoordinateTangentField anchor (deTurckVectorField gt bg t)
      (extChartAt I anchor anchor))

/-- Ordinary coordinate derivative of the concrete DeTurck field at the
preferred-chart anchor. -/
noncomputable def deTurckChartFieldDerivativeAtAnchor
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (t : ℝ) :
    E →L[ℝ] E :=
  fderiv ℝ
    (chartCoordinateTangentField anchor (deTurckVectorField gt bg t))
    (extChartAt I anchor anchor)

/-- Packaged bilinear form of the exact concrete Lie split. -/
theorem deTurckChartLieBilin_apply_anchor_eq_advection_add_DW_slots
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (t : ℝ)
    (hreg : DeTurckVectorFieldRegularAt gt bg t) (p q : E) :
    deTurckChartLieBilin gt bg anchor t (extChartAt I anchor anchor) p q =
      deTurckChartMetricAdvectionAtAnchor gt bg anchor t p q +
        CovariantDerivative.chartMetric (gt t).inner anchor
          (extChartAt I anchor anchor)
          (deTurckChartFieldDerivativeAtAnchor gt bg anchor t p) q +
        CovariantDerivative.chartMetric (gt t).inner anchor
          (extChartAt I anchor anchor) p
          (deTurckChartFieldDerivativeAtAnchor gt bg anchor t q) := by
  simpa [deTurckChartMetricAdvectionAtAnchor,
    deTurckChartFieldDerivativeAtAnchor] using
    deTurckChartLieBilin_apply_anchor_eq_metricAdvection_add_fderiv_slots
      gt bg anchor t hreg p q

/-- The full concrete DeTurck metric-variation bilinear form in a chart. -/
noncomputable def deTurckChartMetricEvolutionBilin
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t : ℝ) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-2 : ℝ) • deTurckChartRicciBilin gt anchor t z +
    deTurckChartLieBilin gt bg anchor t z

/-- On chart-pushed tangent vectors, the concrete chart evolution form is
exactly `-2 Ric + L_W g` intrinsically. -/
theorem deTurckChartMetricEvolutionBilin_apply_chart
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t : ℝ) {y : M} (hy : y ∈ (extChartAt I anchor).source)
    (v w : TM y) :
    deTurckChartMetricEvolutionBilin gt bg anchor t (extChartAt I anchor y)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y w) =
      -2 * (gt t).ricciAt y v w +
        lieDerivMetricAt (gt t) (deTurckVectorField gt bg t) y v w := by
  simp only [deTurckChartMetricEvolutionBilin,
    deTurckChartRicciBilin, deTurckChartLieBilin,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [CovariantDerivative.chartMetric_apply_chart
      (fun q ↦ ricciContinuousBilinAt (gt t) q) anchor hy v w,
    CovariantDerivative.chartMetric_apply_chart
      (fun q ↦ lieDerivMetricBilinAt (gt t) (deTurckVectorField gt bg t) q)
      anchor hy v w]
  simp

/-- The section-tested concrete gauged-flow predicate is therefore an exact
chart-bilinear metric evolution statement on every genuine chart point. -/
theorem isDeTurckGaugedFlowAt_timeDerivAt_eq_chartMetricEvolutionBilin
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    {anchor x : M} (hx : x ∈ (extChartAt I anchor).source)
    (hflow : IsDeTurckGaugedFlowAt gt bg t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (v w : TM x) :
    timeDerivAt gt t₀ x v w =
      deTurckChartMetricEvolutionBilin gt bg anchor t₀ (extChartAt I anchor x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x w) := by
  rw [isDeTurckGaugedFlowAt_timeDerivAt_eq_neg_two_ricciAt_add_lie
    hflow hext v w]
  exact (deTurckChartMetricEvolutionBilin_apply_chart
    gt bg anchor t₀ hx v w).symm

end ConcreteDeTurckEvolution

section VariationalInvertibility

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous operator path which equals the identity at one time remains
invertible on a neighborhood of that time. -/
theorem eventually_isInvertible_of_continuousAt_eq_id
    (D : ℝ → E →L[ℝ] E) {t₀ : ℝ}
    (hD : ContinuousAt D t₀)
    (hD₀ : D t₀ = ContinuousLinearMap.id ℝ E) :
    ∀ᶠ t in 𝓝 t₀, (D t).IsInvertible := by
  have hopen :
      Set.range ((↑) : (E ≃L[ℝ] E) → (E →L[ℝ] E)) ∈
        𝓝 (D t₀) := by
    rw [hD₀]
    simpa using
      (ContinuousLinearEquiv.nhds (ContinuousLinearEquiv.refl ℝ E))
  filter_upwards [hD hopen] with t ht
  rcases ht with ⟨e, he⟩
  exact ⟨e, he⟩

/-- The coordinate inverse-gauge variational solution can be chosen on an
interval where every differential is invertible. -/
theorem exists_local_inverseGauge_with_variationalEquation_isInvertible
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDW : ContDiff ℝ 1 (Function.uncurry DW))
    (t₀ : ℝ) (x₀ : E) :
    ∃ ε > (0 : ℝ), ∃ phi : ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
      phi t₀ = x₀ ∧
        D t₀ = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt phi (-W t (phi t)) t ∧
            HasDerivAt D (-((DW t (phi t)).comp (D t))) t ∧
            (D t).IsInvertible := by
  rcases exists_local_inverseGauge_with_variationalEquation
      W DW hW hDW t₀ x₀ with
    ⟨ε, hε, phi, D, hphi₀, hD₀, hODE⟩
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith
  have hDcont : ContinuousAt D t₀ := (hODE t₀ ht₀).2.continuousAt
  have hinv := eventually_isInvertible_of_continuousAt_eq_id D hDcont hD₀
  rcases Metric.mem_nhds_iff.mp hinv with ⟨δ, hδ, hball⟩
  let η : ℝ := min ε δ / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hmin : 0 < min ε δ := lt_min hε hδ
  have hηε : η < ε := by
    dsimp [η]
    linarith [min_le_left ε δ]
  have hηδ : η < δ := by
    dsimp [η]
    linarith [min_le_right ε δ]
  refine ⟨η, hη, phi, D, hphi₀, hD₀, ?_⟩
  intro t ht
  have htOld : t ∈ Ioo (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith [ht.1, ht.2, hηε]
  have htBall : t ∈ ball t₀ δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2, hηδ]
  exact ⟨(hODE t htOld).1, (hODE t htOld).2, hball htBall⟩

variable [FiniteDimensional ℝ E]

/-- The common initial-point flow can be shrunk so that its identified
Frechet derivative is invertible at every time.  Thus the operator produced
by the variational equation is not merely formal: it is the differential of
the actual endpoint map and remains a linear equivalence. -/
theorem exists_local_inverseGaugePointFlow_variationalIdentification_isInvertible
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDWcont : ContDiff ℝ 1 (Function.uncurry DW))
    (hDW : ∀ t x, HasFDerivAt (W t) (DW t x) x)
    (t₀ : ℝ) (x₀ : E) :
    ∃ T > (0 : ℝ), ∃ r > (0 : ℝ),
      ∃ phi : E → ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
        (∀ x ∈ closedBall x₀ r,
          phi x 0 = x ∧
            ∀ s ∈ Icc (0 : ℝ) T,
              HasDerivWithinAt (phi x) (-W (t₀ + s) (phi x s))
                (Icc (0 : ℝ) T) s) ∧
        D 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ s ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt D
              (-((DW (t₀ + s) (phi x₀ s)).comp (D s)))
              (Icc (0 : ℝ) T) s ∧
            (D s).IsInvertible) ∧
        ∀ s ∈ Icc (0 : ℝ) T,
          HasFDerivAt (fun x : E => phi x s) (D s) x₀ := by
  rcases exists_local_inverseGaugePointFlow_variationalIdentification
      W DW hW hDWcont hDW t₀ x₀ with
    ⟨T, hT, r, hr, phi, D, hphi, hD₀, hDvar, hendpoint⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hDcont : ContinuousWithinAt D (Icc (0 : ℝ) T) 0 :=
    (hDvar 0 hzero).continuousWithinAt
  have hopen :
      Set.range ((↑) : (E ≃L[ℝ] E) → (E →L[ℝ] E)) ∈ 𝓝 (D 0) := by
    rw [hD₀]
    simpa using
      (ContinuousLinearEquiv.nhds (ContinuousLinearEquiv.refl ℝ E))
  have hinvWithin :
      {s : ℝ | (D s).IsInvertible} ∈ 𝓝[Icc (0 : ℝ) T] 0 := by
    have hrange := hDcont hopen
    filter_upwards [hrange] with s hs
    rcases hs with ⟨e, he⟩
    exact ⟨e, he⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hinvWithin with
    ⟨U, hU, hUsub⟩
  rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hball⟩
  let η : ℝ := min T δ / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hηT : η ≤ T := by
    dsimp [η]
    linarith [min_le_left T δ]
  have hηδ : η < δ := by
    dsimp [η]
    linarith [min_le_right T δ, hδ]
  have hsmall : Icc (0 : ℝ) η ⊆ Icc (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hηT⟩
  refine ⟨η, hη, r, hr, phi, D, ?_, hD₀, ?_, ?_⟩
  · intro x hx
    refine ⟨(hphi x hx).1, ?_⟩
    intro s hs
    exact ((hphi x hx).2 s (hsmall hs)).mono hsmall
  · intro s hs
    refine ⟨(hDvar s (hsmall hs)).mono hsmall, ?_⟩
    apply hUsub
    constructor
    · apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_lt]
      constructor <;> linarith [hs.1, hs.2, hηδ]
    · exact hsmall hs
  · intro s hs
    exact hendpoint s (hsmall hs)

end VariationalInvertibility

section CoordinateLocalDiffeomorphism

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An invertible variational differential and `C¹` endpoint regularity produce
an actual local coordinate diffeomorphism germ.  The conclusion includes the
partial homeomorphism, both local inverse laws, and the exact derivatives of
the forward and inverse maps. -/
theorem exists_coordinateLocalDiffeomorphGerm_of_variational_data
    (Phi : E → E) (x : E) (D : E →L[ℝ] E)
    (hPhiC1 : ContDiffAt ℝ 1 Phi x)
    (hPhiD : HasFDerivAt Phi D x)
    (hDinv : D.IsInvertible) :
    ∃ e : E ≃L[ℝ] E, e.toContinuousLinearMap = D ∧
      ∃ U : OpenPartialHomeomorph E E,
        (U : E → E) = Phi ∧
          x ∈ U.source ∧
          Phi x ∈ U.target ∧
          HasFDerivAt U (e : E →L[ℝ] E) x ∧
          HasFDerivAt U.symm (e.symm : E →L[ℝ] E) (Phi x) ∧
          ContDiffAt ℝ 1 U x ∧
          ContDiffAt ℝ 1 U.symm (Phi x) ∧
          (∀ᶠ y in 𝓝 x, U.symm (Phi y) = y) ∧
          (∀ᶠ z in 𝓝 (Phi x), Phi (U.symm z) = z) := by
  rcases hDinv with ⟨e, he⟩
  have hPhiE : HasFDerivAt Phi (e : E →L[ℝ] E) x := by
    simpa [he] using hPhiD
  let hs : HasStrictFDerivAt Phi (e : E →L[ℝ] E) x :=
    hPhiC1.hasStrictFDerivAt' hPhiE (by norm_num)
  let U : OpenPartialHomeomorph E E := hs.toOpenPartialHomeomorph Phi
  have hUcoe : (U : E → E) = Phi := by
    exact hs.toOpenPartialHomeomorph_coe
  have hx : x ∈ U.source := by
    exact hs.mem_toOpenPartialHomeomorph_source
  have hy : Phi x ∈ U.target := by
    exact hs.image_mem_toOpenPartialHomeomorph_target
  have hUinvx : U.symm (Phi x) = x := by
    calc
      U.symm (Phi x) = U.symm (U x) := by
        rw [congrFun hUcoe x]
      _ = x := U.left_inv hx
  have hUderiv : HasFDerivAt U (e : E →L[ℝ] E) x := by
    simpa [hUcoe] using hPhiE
  have hUinvDeriv :
      HasFDerivAt U.symm (e.symm : E →L[ℝ] E) (Phi x) := by
    apply U.hasFDerivAt_symm hy
    rw [hUinvx]
    exact hUderiv
  have hUC1 : ContDiffAt ℝ 1 U x := by
    simpa [hUcoe] using hPhiC1
  have hUinvC1 : ContDiffAt ℝ 1 U.symm (Phi x) := by
    apply U.contDiffAt_symm hy
    · rw [hUinvx]
      exact hUderiv
    · rw [hUinvx]
      exact hUC1
  have hleft : ∀ᶠ y in 𝓝 x, U.symm (Phi y) = y := by
    simpa [hUcoe] using U.eventually_left_inverse hx
  have hright : ∀ᶠ z in 𝓝 (Phi x), Phi (U.symm z) = z := by
    simpa [hUcoe] using U.eventually_right_inverse' hx
  exact ⟨e, he, U, hUcoe, hx, hy, hUderiv, hUinvDeriv, hUC1,
    hUinvC1, hleft, hright⟩

/-- The theorem-bearing data of a local coordinate diffeomorphism germ.  In
particular, this records the actual partial homeomorphism and both inverse
laws, not just an invertibility marker for its derivative. -/
structure CoordinateLocalDiffeomorphGerm
    (Phi : E → E) (x : E) (D : E →L[ℝ] E) where
  tangentEquiv : E ≃L[ℝ] E
  tangentEquiv_coe : (tangentEquiv : E →L[ℝ] E) = D
  localHomeomorph : OpenPartialHomeomorph E E
  localHomeomorph_coe : (localHomeomorph : E → E) = Phi
  mem_source : x ∈ localHomeomorph.source
  image_mem_target : Phi x ∈ localHomeomorph.target
  forward_fderiv :
    HasFDerivAt localHomeomorph (tangentEquiv : E →L[ℝ] E) x
  inverse_fderiv :
    HasFDerivAt localHomeomorph.symm (tangentEquiv.symm : E →L[ℝ] E) (Phi x)
  eventually_left_inverse :
    ∀ᶠ y in 𝓝 x, localHomeomorph.symm (Phi y) = y
  eventually_right_inverse :
    ∀ᶠ z in 𝓝 (Phi x), Phi (localHomeomorph.symm z) = z

end CoordinateLocalDiffeomorphism

section RicciTraceBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Arbitrary-time Ricci-trace pullback cancellation from an invertible gauge
differential.  The continuous-linear-equivalence witness is extracted from
`hDinv`; geometric naturality is requested uniformly for that representation.
-/
theorem hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace_of_isInvertible
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    (curvSource curvTarget : E → E → (E →ₗ[ℝ] E))
    {t₀ : ℝ}
    (hA : HasDerivAt A (H - adv) t₀)
    (hD : HasDerivAt D (-(DW.comp (D t₀))) t₀)
    (hA₀ : A t₀ = G)
    (hDinv : (D t₀).IsInvertible)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (hRicciTarget : ∀ (e : E ≃L[ℝ] E),
      D t₀ = e.toContinuousLinearMap → ∀ u v : E,
        R (e u) (e v) =
          LinearMap.trace ℝ E (curvTarget (e u) (e v)))
    (hcurv : ∀ (e : E ≃L[ℝ] E),
      D t₀ = e.toContinuousLinearMap → ∀ u v w : E,
        curvTarget (e u) (e v) (e w) = e (curvSource u v w))
    (u v : E) :
    HasDerivAt (pullbackBilinearApply A D u v)
      ((-2 : ℝ) * LinearMap.trace ℝ E (curvSource u v)) t₀ := by
  rcases hDinv with ⟨e, he⟩
  have hD₀ : D t₀ = e.toContinuousLinearMap := he.symm
  exact hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace
    A D G H adv R DW e curvSource curvTarget hA hD hA₀ hD₀ hDeTurck
      (hRicciTarget e hD₀) (hcurv e hD₀) u v

variable [CompleteSpace E]

/-- Local inverse-gauge existence with an invertible differential and the
source Ricci-trace pullback derivative available at every time of the shrunken
interval.  The remaining geometric hypotheses are exactly Ricci contraction
in the target coordinates and curvature intertwining by the gauge
differential. -/
theorem exists_local_inverseGauge_with_sourceRicciTraceDerivative
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDW : ContDiff ℝ 1 (Function.uncurry DW))
    (t₀ : ℝ) (x₀ : E) :
    ∃ ε > (0 : ℝ), ∃ phi : ℝ → E, ∃ D : ℝ → E →L[ℝ] E,
      phi t₀ = x₀ ∧
        D t₀ = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt phi (-W t (phi t)) t ∧
            HasDerivAt D (-((DW t (phi t)).comp (D t))) t ∧
            (D t).IsInvertible ∧
            ∀ (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
              (G H adv R : E →L[ℝ] E →L[ℝ] ℝ)
              (curvSource curvTarget : E → E → (E →ₗ[ℝ] E)),
              HasDerivAt A (H - adv) t →
                A t = G →
                (∀ u v : E,
                  H u v =
                    (-2 : ℝ) * R u v + adv u v +
                      G ((DW t (phi t)) u) v +
                        G u ((DW t (phi t)) v)) →
                (∀ (e : E ≃L[ℝ] E),
                  D t = e.toContinuousLinearMap → ∀ u v : E,
                    R (e u) (e v) =
                      LinearMap.trace ℝ E (curvTarget (e u) (e v))) →
                (∀ (e : E ≃L[ℝ] E),
                  D t = e.toContinuousLinearMap → ∀ u v w : E,
                    curvTarget (e u) (e v) (e w) = e (curvSource u v w)) →
                ∀ u v : E,
                  HasDerivAt (pullbackBilinearApply A D u v)
                    ((-2 : ℝ) * LinearMap.trace ℝ E (curvSource u v)) t := by
  rcases exists_local_inverseGauge_with_variationalEquation_isInvertible
      W DW hW hDW t₀ x₀ with
    ⟨ε, hε, phi, D, hphi₀, hD₀, hODE⟩
  refine ⟨ε, hε, phi, D, hphi₀, hD₀, ?_⟩
  intro t ht
  rcases hODE t ht with ⟨hphi, hD, hDinv⟩
  refine ⟨hphi, hD, hDinv, ?_⟩
  intro A G H adv R curvSource curvTarget hA hA₀ hDeTurck
    hRicciTarget hcurv u v
  exact hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace_of_isInvertible
    A D G H adv R (DW t (phi t)) curvSource curvTarget hA hD hA₀ hDinv
      hDeTurck hRicciTarget hcurv u v

end RicciTraceBridge

section ConcreteChartPullbackDerivative

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Concrete chart specialization of the arbitrary-time Ricci-trace
pullback theorem.  The metric path, its value, the Ricci tensor, and the full
DeTurck evolution tensor are no longer caller-selected abstract bilinear
forms.  The two remaining geometric obligations are exposed precisely as the
moving-chart Lie split and curvature naturality. -/
theorem hasDerivAt_inverseGaugePulledChartMetric_eq_neg_two_source_ricciTrace
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E)
    (adv : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    (curvSource curvTarget : E → E → (E →ₗ[ℝ] E))
    {t₀ : ℝ}
    (hA : HasDerivAt
      (fun s ↦ CovariantDerivative.chartMetric (gt s).inner anchor (phi s))
      (deTurckChartMetricEvolutionBilin gt bg anchor t₀ (phi t₀) - adv) t₀)
    (hD : HasDerivAt D (-(DW.comp (D t₀))) t₀)
    (hDinv : (D t₀).IsInvertible)
    (hLieSplit : ∀ p q : E,
      deTurckChartLieBilin gt bg anchor t₀ (phi t₀) p q =
        adv p q +
          CovariantDerivative.chartMetric (gt t₀).inner anchor (phi t₀)
              (DW p) q +
          CovariantDerivative.chartMetric (gt t₀).inner anchor (phi t₀)
              p (DW q))
    (hRicciTarget : ∀ (e : E ≃L[ℝ] E),
      D t₀ = e.toContinuousLinearMap → ∀ p q : E,
        deTurckChartRicciBilin gt anchor t₀ (phi t₀) (e p) (e q) =
          LinearMap.trace ℝ E (curvTarget (e p) (e q)))
    (hcurv : ∀ (e : E ≃L[ℝ] E),
      D t₀ = e.toContinuousLinearMap → ∀ p q r : E,
        curvTarget (e p) (e q) (e r) = e (curvSource p q r))
    (u v : E) :
    HasDerivAt
      (fun s ↦ inverseGaugePulledChartMetric gt anchor phi D s u v)
      ((-2 : ℝ) * LinearMap.trace ℝ E (curvSource u v)) t₀ := by
  let A : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦
    CovariantDerivative.chartMetric (gt s).inner anchor (phi s)
  let G : E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric (gt t₀).inner anchor (phi t₀)
  let H : E →L[ℝ] E →L[ℝ] ℝ :=
    deTurckChartMetricEvolutionBilin gt bg anchor t₀ (phi t₀)
  let R : E →L[ℝ] E →L[ℝ] ℝ :=
    deTurckChartRicciBilin gt anchor t₀ (phi t₀)
  have hDeTurck : ∀ p q : E,
      H p q =
        (-2 : ℝ) * R p q + adv p q +
          G (DW p) q + G p (DW q) := by
    intro p q
    dsimp [H, R, G]
    simp only [deTurckChartMetricEvolutionBilin,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [hLieSplit p q]
    ring
  have hpull :=
    hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace_of_isInvertible
      A D G H adv R DW curvSource curvTarget hA hD rfl hDinv hDeTurck
      hRicciTarget hcurv u v
  simpa [A, inverseGaugePulledChartMetric] using hpull

/-- Concrete local Ricci-flow pullback at any genuine cutoff-one chart point.
This is the overlap-ready form: its target curvature is the actual
inverse-chart transport of the intrinsic curvature at the represented
manifold point. -/
theorem exists_coordinateLocalDiffeomorphGerm_with_inverseGaugeRicciFlowDerivative_at_chartPoint
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E)
    (Phi : E → E) (x : E) {t₀ : ℝ}
    (hphi : phi t₀ = extChartAt I anchor y)
    (hreg : DeTurckVectorFieldRegularAt gt bg t₀)
    (hA : HasDerivAt
      (fun s ↦ CovariantDerivative.chartMetric (gt s).inner anchor (phi s))
      (deTurckChartMetricEvolutionBilin gt bg anchor t₀ (phi t₀) -
        deTurckChartMetricAdvectionAt gt bg anchor t₀
          (extChartAt I anchor y)) t₀)
    (hD : HasDerivAt D
      (-(deTurckChartFieldDerivativeAt gt bg anchor t₀
        (extChartAt I anchor y)).comp (D t₀)) t₀)
    (hDinv : (D t₀).IsInvertible)
    (hPhiC1 : ContDiffAt ℝ 1 Phi x)
    (hPhiD : HasFDerivAt Phi (D t₀) x)
    (u v : E) :
    ∃ e : E ≃L[ℝ] E, e.toContinuousLinearMap = D t₀ ∧
      ∃ U : OpenPartialHomeomorph E E,
        (U : E → E) = Phi ∧
          x ∈ U.source ∧ Phi x ∈ U.target ∧
          HasFDerivAt U (e : E →L[ℝ] E) x ∧
          HasFDerivAt U.symm (e.symm : E →L[ℝ] E) (Phi x) ∧
          (∀ᶠ a in 𝓝 x, U.symm (Phi a) = a) ∧
          (∀ᶠ z in 𝓝 (Phi x), Phi (U.symm z) = z) ∧
          HasDerivAt
            (fun s ↦ inverseGaugePulledChartMetric gt anchor phi D s u v)
            ((-2 : ℝ) * LinearMap.trace ℝ E
              (pullbackCurvatureEnd e
                (chartRicciCurvatureEndAt (gt t₀) anchor
                  (extChartAt I anchor y)
                  ((extChartAt I anchor).map_source hy)) u v)) t₀ := by
  rcases exists_coordinateLocalDiffeomorphGerm_of_variational_data
      Phi x (D t₀) hPhiC1 hPhiD hDinv with
    ⟨e, he, U, hUcoe, hx, hPhix, hUderiv, hUinvDeriv, _hUC1,
      _hUinvC1, hleft, hright⟩
  refine ⟨e, he, U, hUcoe, hx, hPhix, hUderiv, hUinvDeriv,
    hleft, hright, ?_⟩
  apply hasDerivAt_inverseGaugePulledChartMetric_eq_neg_two_source_ricciTrace
    gt bg anchor phi D
    (deTurckChartMetricAdvectionAt gt bg anchor t₀ (extChartAt I anchor y))
    (deTurckChartFieldDerivativeAt gt bg anchor t₀ (extChartAt I anchor y))
    (pullbackCurvatureEnd e
      (chartRicciCurvatureEndAt (gt t₀) anchor (extChartAt I anchor y)
        ((extChartAt I anchor).map_source hy)))
    (chartRicciCurvatureEndAt (gt t₀) anchor (extChartAt I anchor y)
      ((extChartAt I anchor).map_source hy))
    hA hD hDinv
  · intro p q
    rw [hphi]
    exact deTurckChartLieBilin_apply_chart_eq_advection_add_DW_slots
      gt bg anchor t₀ hy hχone hreg p q
  · intro e' he' p q
    rw [hphi]
    exact deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
      gt anchor t₀ (extChartAt I anchor y)
        ((extChartAt I anchor).map_source hy) (e' p) (e' q)
  · intro e' he' p q r
    have heq : e' = e := by
      apply ContinuousLinearEquiv.ext
      funext w
      have hmaps : e'.toContinuousLinearMap = e.toContinuousLinearMap :=
        he'.symm.trans he.symm
      exact congrArg (fun L : E →L[ℝ] E ↦ L w) hmaps
    subst e'
    exact curvature_natural_pullbackCurvatureEnd e
      (chartRicciCurvatureEndAt (gt t₀) anchor (extChartAt I anchor y)
        ((extChartAt I anchor).map_source hy)) p q r

/-- Two overlapping preferred charts produce compatible actual local
diffeomorphism germs and the same inverse-gauge Ricci-flow derivative.

The endpoint maps agree as germs through the genuine chart transition.  The
theorem differentiates that germ identity, conjugates the two variational
differentials, transports the chart Ricci tensor, and returns one scalar
derivative shared by both coordinate pullbacks. -/
theorem exists_chartIndependent_coordinateLocalDiffeomorphGerms_with_inverseGaugeRicciFlowDerivative
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor₁ anchor₂ y : M)
    (hy₁ : y ∈ (extChartAt I anchor₁).source)
    (hy₂ : y ∈ (extChartAt I anchor₂).source)
    (hχone₁ : ∀ᶠ z' in 𝓝 (extChartAt I anchor₁ y),
      GeodesicTransport.cutoff (n := n) anchor₁ z' = 1)
    (hχone₂ : ∀ᶠ z' in 𝓝 (extChartAt I anchor₂ y),
      GeodesicTransport.cutoff (n := n) anchor₂ z' = 1)
    (phi₁ : ℝ → E) (D₁ : ℝ → E →L[ℝ] E) (Phi₁ : E → E)
    (phi₂ : ℝ → E) (D₂ : ℝ → E →L[ℝ] E) (Phi₂ : E → E)
    (x : E) {t₀ : ℝ}
    (hx : x ∈ (extChartAt I anchor₁).target)
    (hx₂ : (extChartAt I anchor₁).symm x ∈
      (extChartAt I anchor₂).source)
    (hPhi₁x : Phi₁ x = extChartAt I anchor₁ y)
    (hphi₁ : phi₁ t₀ = extChartAt I anchor₁ y)
    (hphi₂ : phi₂ t₀ = extChartAt I anchor₂ y)
    (hreg : DeTurckVectorFieldRegularAt gt bg t₀)
    (hA₁ : HasDerivAt
      (fun s ↦ CovariantDerivative.chartMetric (gt s).inner anchor₁ (phi₁ s))
      (deTurckChartMetricEvolutionBilin gt bg anchor₁ t₀ (phi₁ t₀) -
        deTurckChartMetricAdvectionAt gt bg anchor₁ t₀
          (extChartAt I anchor₁ y)) t₀)
    (hD₁ : HasDerivAt D₁
      (-(deTurckChartFieldDerivativeAt gt bg anchor₁ t₀
        (extChartAt I anchor₁ y)).comp (D₁ t₀)) t₀)
    (hA₂ : HasDerivAt
      (fun s ↦ CovariantDerivative.chartMetric (gt s).inner anchor₂ (phi₂ s))
      (deTurckChartMetricEvolutionBilin gt bg anchor₂ t₀ (phi₂ t₀) -
        deTurckChartMetricAdvectionAt gt bg anchor₂ t₀
          (extChartAt I anchor₂ y)) t₀)
    (hD₂ : HasDerivAt D₂
      (-(deTurckChartFieldDerivativeAt gt bg anchor₂ t₀
        (extChartAt I anchor₂ y)).comp (D₂ t₀)) t₀)
    (hDinv₁ : (D₁ t₀).IsInvertible)
    (hDinv₂ : (D₂ t₀).IsInvertible)
    (hPhiC1₁ : ContDiffAt ℝ 1 Phi₁ x)
    (hPhiD₁ : HasFDerivAt Phi₁ (D₁ t₀) x)
    (hPhiC1₂ : ContDiffAt ℝ 1 Phi₂
      (GeodesicTransport.chartTransition anchor₁ anchor₂ x))
    (hPhiD₂ : HasFDerivAt Phi₂ (D₂ t₀)
      (GeodesicTransport.chartTransition anchor₁ anchor₂ x))
    (hcompat :
      (Phi₂ ∘ GeodesicTransport.chartTransition anchor₁ anchor₂) =ᶠ[𝓝 x]
        (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘ Phi₁))
    (u v : E) :
    ∃ G₁ : CoordinateLocalDiffeomorphGerm Phi₁ x (D₁ t₀),
      ∃ G₂ : CoordinateLocalDiffeomorphGerm Phi₂
          (GeodesicTransport.chartTransition anchor₁ anchor₂ x) (D₂ t₀),
        G₁.localHomeomorph x = phi₁ t₀ ∧
          G₂.localHomeomorph
              (GeodesicTransport.chartTransition anchor₁ anchor₂ x) = phi₂ t₀ ∧
          (G₂.localHomeomorph ∘
              GeodesicTransport.chartTransition anchor₁ anchor₂) =ᶠ[𝓝 x]
            (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘
              G₁.localHomeomorph) ∧
          (D₂ t₀).comp
              (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ x) =
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
                (extChartAt I anchor₁ y)).comp (D₁ t₀) ∧
          (fun a ↦ (extChartAt I anchor₁).symm (G₁.localHomeomorph a)) =ᶠ[𝓝 x]
            (fun a ↦ (extChartAt I anchor₂).symm
              (G₂.localHomeomorph
                (GeodesicTransport.chartTransition anchor₁ anchor₂ a))) ∧
          (let S := chartTransitionTangentEquiv anchor₁ anchor₂ x hx hx₂
           let rate := (-2 : ℝ) * LinearMap.trace ℝ E
             (pullbackCurvatureEnd G₁.tangentEquiv
               (chartRicciCurvatureEndAt (gt t₀) anchor₁
                 (extChartAt I anchor₁ y)
                 ((extChartAt I anchor₁).map_source hy₁)) u v)
           HasDerivAt
               (fun s ↦ inverseGaugePulledChartMetric
                 gt anchor₁ phi₁ D₁ s u v) rate t₀ ∧
             HasDerivAt
               (fun s ↦ inverseGaugePulledChartMetric
                 gt anchor₂ phi₂ D₂ s (S u) (S v)) rate t₀) := by
  let S := chartTransitionTangentEquiv anchor₁ anchor₂ x hx hx₂
  rcases
      exists_coordinateLocalDiffeomorphGerm_with_inverseGaugeRicciFlowDerivative_at_chartPoint
        gt bg anchor₁ hy₁ hχone₁ phi₁ D₁ Phi₁ x hphi₁ hreg
        hA₁ hD₁ hDinv₁ hPhiC1₁ hPhiD₁ u v with
    ⟨e₁, he₁, U₁, hU₁coe, hU₁source, hU₁target,
      hU₁deriv, hU₁invDeriv, hU₁left, hU₁right, hrate₁⟩
  rcases
      exists_coordinateLocalDiffeomorphGerm_with_inverseGaugeRicciFlowDerivative_at_chartPoint
        gt bg anchor₂ hy₂ hχone₂ phi₂ D₂ Phi₂
        (GeodesicTransport.chartTransition anchor₁ anchor₂ x) hphi₂ hreg
        hA₂ hD₂ hDinv₂ hPhiC1₂ hPhiD₂ (S u) (S v) with
    ⟨e₂, he₂, U₂, hU₂coe, hU₂source, hU₂target,
      hU₂deriv, hU₂invDeriv, hU₂left, hU₂right, hrate₂⟩
  let G₁ : CoordinateLocalDiffeomorphGerm Phi₁ x (D₁ t₀) :=
    { tangentEquiv := e₁
      tangentEquiv_coe := he₁
      localHomeomorph := U₁
      localHomeomorph_coe := hU₁coe
      mem_source := hU₁source
      image_mem_target := hU₁target
      forward_fderiv := hU₁deriv
      inverse_fderiv := hU₁invDeriv
      eventually_left_inverse := hU₁left
      eventually_right_inverse := hU₁right }
  let G₂ : CoordinateLocalDiffeomorphGerm Phi₂
      (GeodesicTransport.chartTransition anchor₁ anchor₂ x) (D₂ t₀) :=
    { tangentEquiv := e₂
      tangentEquiv_coe := he₂
      localHomeomorph := U₂
      localHomeomorph_coe := hU₂coe
      mem_source := hU₂source
      image_mem_target := hU₂target
      forward_fderiv := hU₂deriv
      inverse_fderiv := hU₂invDeriv
      eventually_left_inverse := hU₂left
      eventually_right_inverse := hU₂right }
  have hz₁' : Phi₁ x ∈ (extChartAt I anchor₁).target := by
    rw [hPhi₁x]
    exact (extChartAt I anchor₁).map_source hy₁
  have hy' : (extChartAt I anchor₁).symm (Phi₁ x) ∈
      (extChartAt I anchor₂).source := by
    rw [hPhi₁x, (extChartAt I anchor₁).left_inv hy₁]
    exact hy₂
  have htargetTransition :
      GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ x) =
        extChartAt I anchor₂ y := by
    rw [hPhi₁x]
    change extChartAt I anchor₂
      ((extChartAt I anchor₁).symm (extChartAt I anchor₁ y)) = _
    rw [(extChartAt I anchor₁).left_inv hy₁]
  have hz₂' : GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ x) ∈
      (extChartAt I anchor₂).target := by
    rw [htargetTransition]
    exact (extChartAt I anchor₂).map_source hy₂
  have htrace := inverseGaugeRicciTrace_chartTransition_eq
    gt t₀ anchor₁ anchor₂ hx hx₂ hz₁' hy' hz₂'
    hPhiD₁ hPhiD₂ hcompat e₁ e₂ he₁ he₂ u v
  have hC₁ :
      chartRicciCurvatureEndAt (gt t₀) anchor₁ (Phi₁ x) hz₁' =
        chartRicciCurvatureEndAt (gt t₀) anchor₁
          (extChartAt I anchor₁ y) ((extChartAt I anchor₁).map_source hy₁) :=
    chartRicciCurvatureEndAt_congr (gt t₀) anchor₁ hz₁'
      ((extChartAt I anchor₁).map_source hy₁) hPhi₁x
  have hC₂ :
      chartRicciCurvatureEndAt (gt t₀) anchor₂
          (GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ x)) hz₂' =
        chartRicciCurvatureEndAt (gt t₀) anchor₂
          (extChartAt I anchor₂ y) ((extChartAt I anchor₂).map_source hy₂) :=
    chartRicciCurvatureEndAt_congr (gt t₀) anchor₂ hz₂'
      ((extChartAt I anchor₂).map_source hy₂) htargetTransition
  have htrace' :
      LinearMap.trace ℝ E
          (pullbackCurvatureEnd e₂
            (chartRicciCurvatureEndAt (gt t₀) anchor₂
              (extChartAt I anchor₂ y)
              ((extChartAt I anchor₂).map_source hy₂)) (S u) (S v)) =
        LinearMap.trace ℝ E
          (pullbackCurvatureEnd e₁
            (chartRicciCurvatureEndAt (gt t₀) anchor₁
              (extChartAt I anchor₁ y)
              ((extChartAt I anchor₁).map_source hy₁)) u v) := by
    rw [hC₁, hC₂] at htrace
    simpa [S] using htrace
  have hrate₂' : HasDerivAt
      (fun s ↦ inverseGaugePulledChartMetric
        gt anchor₂ phi₂ D₂ s (S u) (S v))
      ((-2 : ℝ) * LinearMap.trace ℝ E
        (pullbackCurvatureEnd e₁
          (chartRicciCurvatureEndAt (gt t₀) anchor₁
            (extChartAt I anchor₁ y)
            ((extChartAt I anchor₁).map_source hy₁)) u v)) t₀ := by
    rw [← htrace']
    exact hrate₂
  have hcompatAt := hcompat.self_of_nhds
  change Phi₂ (GeodesicTransport.chartTransition anchor₁ anchor₂ x) =
    GeodesicTransport.chartTransition anchor₁ anchor₂ (Phi₁ x) at hcompatAt
  have hPhi₂x : Phi₂ (GeodesicTransport.chartTransition anchor₁ anchor₂ x) =
      extChartAt I anchor₂ y := hcompatAt.trans htargetTransition
  have hoverlapSource :
      x ∈ ((extChartAt I anchor₁).symm ≫ extChartAt I anchor₂).source := by
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using
      And.intro hx hx₂
  have hoverlapEndpoint :
      extChartAt I anchor₁ y ∈
        ((extChartAt I anchor₁).symm ≫ extChartAt I anchor₂).source := by
    have htarget₁ := (extChartAt I anchor₁).map_source hy₁
    have hsource₂ :
        (extChartAt I anchor₁).symm (extChartAt I anchor₁ y) ∈
          (extChartAt I anchor₂).source := by
      rw [(extChartAt I anchor₁).left_inv hy₁]
      exact hy₂
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using
      And.intro htarget₁ hsource₂
  have hDconjRaw := chartTransition_flow_fderiv_conjugacy
    anchor₁ anchor₂
    (chartTransition_differentiableAt_of_mem_source
      anchor₁ anchor₂ hoverlapSource)
    hPhiD₁ hPhiD₂
    (chartTransition_differentiableAt_of_mem_source
      anchor₁ anchor₂ (by simpa [hPhi₁x] using hoverlapEndpoint))
    hcompat
  have hDconj :
      (D₂ t₀).comp
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ x) =
        (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
            (extChartAt I anchor₁ y)).comp (D₁ t₀) := by
    simpa [hPhi₁x] using hDconjRaw
  have hPhiTarget : ∀ᶠ a in 𝓝 x,
      Phi₁ a ∈ (extChartAt I anchor₁).target :=
    hPhiC1₁.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target anchor₁).mem_nhds hz₁')
  have hInvPhiCont : ContinuousAt
      ((extChartAt I anchor₁).symm ∘ Phi₁) x :=
    (continuousAt_extChartAt_symm'' hz₁').comp hPhiC1₁.continuousAt
  have hPhiInvSource : ∀ᶠ a in 𝓝 x,
      (extChartAt I anchor₁).symm (Phi₁ a) ∈
        (extChartAt I anchor₂).source := by
    simpa [Function.comp_def] using hInvPhiCont.preimage_mem_nhds
      ((isOpen_extChartAt_source anchor₂).mem_nhds hy')
  have hPhiOverlap : ∀ᶠ a in 𝓝 x,
      Phi₁ a ∈ ((extChartAt I anchor₁).symm ≫ extChartAt I anchor₂).source := by
    filter_upwards [hPhiTarget, hPhiInvSource] with a haTarget haSource
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using
      And.intro haTarget haSource
  have hmanifoldGerm := manifoldMapGerm_eventuallyEq_of_chartTransition
    anchor₁ anchor₂ hcompat hPhiOverlap
  refine ⟨G₁, G₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change U₁ x = phi₁ t₀
    rw [congrFun hU₁coe x, hPhi₁x, ← hphi₁]
  · change U₂ (GeodesicTransport.chartTransition anchor₁ anchor₂ x) = phi₂ t₀
    rw [congrFun hU₂coe
      (GeodesicTransport.chartTransition anchor₁ anchor₂ x), hPhi₂x, ← hphi₂]
  · change (U₂ ∘ GeodesicTransport.chartTransition anchor₁ anchor₂) =ᶠ[𝓝 x]
      (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘ U₁)
    simpa only [hU₁coe, hU₂coe] using hcompat
  · exact hDconj
  · change (fun a ↦ (extChartAt I anchor₁).symm (U₁ a)) =ᶠ[𝓝 x]
      (fun a ↦ (extChartAt I anchor₂).symm
        (U₂ (GeodesicTransport.chartTransition anchor₁ anchor₂ a)))
    simpa only [hU₁coe, hU₂coe] using hmanifoldGerm
  · dsimp [G₁]
    exact ⟨hrate₁, hrate₂'⟩

/-- Concrete local Ricci-flow pullback at a preferred-chart anchor.

The endpoint map `Phi` is promoted by the inverse function theorem to an
actual local coordinate diffeomorphism germ whose derivative is `D t₀`.
The DeTurck Lie terms cancel using the proved moving-chart split, while the
source curvature is the tensor pullback of the intrinsic target curvature
through that same derivative equivalence.  Thus neither Lie cancellation nor
curvature naturality remains as a caller-supplied hypothesis. -/
theorem exists_coordinateLocalDiffeomorphGerm_with_inverseGaugeRicciFlowDerivative_at_anchor
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (phi : ℝ → E) (D : ℝ → E →L[ℝ] E)
    (Phi : E → E) (x : E) {t₀ : ℝ}
    (hphi : phi t₀ = extChartAt I anchor anchor)
    (hreg : DeTurckVectorFieldRegularAt gt bg t₀)
    (hA : HasDerivAt
      (fun s ↦ CovariantDerivative.chartMetric (gt s).inner anchor (phi s))
      (deTurckChartMetricEvolutionBilin gt bg anchor t₀ (phi t₀) -
        deTurckChartMetricAdvectionAtAnchor gt bg anchor t₀) t₀)
    (hD : HasDerivAt D
      (-(deTurckChartFieldDerivativeAtAnchor gt bg anchor t₀).comp (D t₀)) t₀)
    (hDinv : (D t₀).IsInvertible)
    (hPhiC1 : ContDiffAt ℝ 1 Phi x)
    (hPhiD : HasFDerivAt Phi (D t₀) x)
    (u v : E) :
    ∃ e : E ≃L[ℝ] E, e.toContinuousLinearMap = D t₀ ∧
      ∃ U : OpenPartialHomeomorph E E,
        (U : E → E) = Phi ∧
          x ∈ U.source ∧
          Phi x ∈ U.target ∧
          HasFDerivAt U (e : E →L[ℝ] E) x ∧
          HasFDerivAt U.symm (e.symm : E →L[ℝ] E) (Phi x) ∧
          ContDiffAt ℝ 1 U x ∧
          ContDiffAt ℝ 1 U.symm (Phi x) ∧
          (∀ᶠ y in 𝓝 x, U.symm (Phi y) = y) ∧
          (∀ᶠ z in 𝓝 (Phi x), Phi (U.symm z) = z) ∧
          HasDerivAt
            (fun s ↦ inverseGaugePulledChartMetric gt anchor phi D s u v)
            ((-2 : ℝ) * LinearMap.trace ℝ E
              (pullbackCurvatureEnd e
                (ricciCurvatureEndAt (gt t₀) anchor) u v)) t₀ := by
  rcases exists_coordinateLocalDiffeomorphGerm_of_variational_data
      Phi x (D t₀) hPhiC1 hPhiD hDinv with
    ⟨e, he, U, hUcoe, hx, hPhix, hUderiv, hUinvDeriv, hUC1,
      hUinvC1, hleft, hright⟩
  refine ⟨e, he, U, hUcoe, hx, hPhix, hUderiv, hUinvDeriv, hUC1,
    hUinvC1, hleft, hright, ?_⟩
  apply hasDerivAt_inverseGaugePulledChartMetric_eq_neg_two_source_ricciTrace
    gt bg anchor phi D
    (deTurckChartMetricAdvectionAtAnchor gt bg anchor t₀)
    (deTurckChartFieldDerivativeAtAnchor gt bg anchor t₀)
    (pullbackCurvatureEnd e (ricciCurvatureEndAt (gt t₀) anchor))
    (ricciCurvatureEndAt (gt t₀) anchor)
    hA hD hDinv
  · intro p q
    rw [hphi]
    exact deTurckChartLieBilin_apply_anchor_eq_advection_add_DW_slots
      gt bg anchor t₀ hreg p q
  · intro e' he' p q
    rw [hphi]
    exact deTurckChartRicciBilin_apply_anchor_eq_trace_curvatureEnd
      gt anchor t₀ (e' p) (e' q)
  · intro e' he' p q r
    have heq : e' = e := by
      apply ContinuousLinearEquiv.ext
      funext w
      have hmaps : e'.toContinuousLinearMap = e.toContinuousLinearMap :=
        he'.symm.trans he.symm
      exact congrArg (fun L : E →L[ℝ] E ↦ L w) hmaps
    subst e'
    exact curvature_natural_pullbackCurvatureEnd e
      (ricciCurvatureEndAt (gt t₀) anchor) p q r

end ConcreteChartPullbackDerivative

end Poincare
