import Poincare.Global.MetricFamilyCovRicciNormContinuity

/-!
# Coordinate covariant Ricci continuity for metric families

This module gives a concrete producer for the chartwise covariant-Ricci
continuity interface over an arbitrary topological parameter space.  The
inputs stop one derivative earlier: inverse-metric coefficients, Christoffel
values, Ricci entries, and the spatial derivative of each Ricci entry.
-/

noncomputable section

open Bundle Filter Function
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option maxSynthPendingDepth 100

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/-- The cutoff-blended Christoffel field of one smooth closed metric is
globally smooth in its model-chart base point. -/
theorem GeodesicTransport.chartChristoffelField_contDiff_top
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ContDiff ℝ ∞ (GeodesicTransport.chartChristoffelField g x₀) := by
  have hblend :
      ContDiff ℝ ∞
        (CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀) := by
    exact CovariantDerivative.contDiff_blendedChartMetric
      (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀
      (by simp)
      (GeodesicTransport.cutoff_contDiff (n := n) x₀)
      (GeodesicTransport.cutoff_tsupport (n := n) x₀)
      g.contMDiff_inner
  rw [contDiff_iff_contDiffAt]
  intro z
  apply contDiffAt_clm_of_apply
  intro u
  apply contDiffAt_clm_of_apply
  intro v
  simpa [GeodesicTransport.chartChristoffelField] using
    (CovariantDerivative.contDiffAt_christoffelAt
      (G := CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀)
      (k := ∞) (x := z) hblend
      (CovariantDerivative.chartBilin
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀)
      (CovariantDerivative.chartBilin_nondegenerate
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n)) g.inner
        (fun y w hw => g.inner_pos y (v := w) hw) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀))
      (fun y w a => rfl) v u)

section ChartCurvatureSecondJet

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The spatial derivative of chart curvature is the expected six-term
expression in the first two Christoffel jets. -/
theorem fderiv_chartCurvatureOf_apply_component
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (hΓ : ContDiff ℝ 2 Γ)
    (z a u v w : V) :
    fderiv ℝ (fun y ↦ chartCurvatureOf Γ y u v w) z a =
      (fderiv ℝ (fun y ↦ fderiv ℝ Γ y u) z a) v w
        - (fderiv ℝ (fun y ↦ fderiv ℝ Γ y v) z a) u w
        + (fderiv ℝ Γ z a) u (Γ z v w)
        + Γ z u ((fderiv ℝ Γ z a) v w)
        - (fderiv ℝ Γ z a) v (Γ z u w)
        - Γ z v ((fderiv ℝ Γ z a) u w) := by
  have hΓd : Differentiable ℝ Γ := hΓ.differentiable (by norm_num)
  have hDΓd : Differentiable ℝ (fderiv ℝ Γ) :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hDΓu : Differentiable ℝ (fun y ↦ fderiv ℝ Γ y u) :=
    hDΓd.clm_apply (differentiable_const u)
  have hDΓv : Differentiable ℝ (fun y ↦ fderiv ℝ Γ y v) :=
    hDΓd.clm_apply (differentiable_const v)
  have hA : Differentiable ℝ (fun y ↦ (fderiv ℝ Γ y u) v w) :=
    (hDΓu.clm_apply (differentiable_const v)).clm_apply
      (differentiable_const w)
  have hB : Differentiable ℝ (fun y ↦ (fderiv ℝ Γ y v) u w) :=
    (hDΓv.clm_apply (differentiable_const u)).clm_apply
      (differentiable_const w)
  have hΓu : Differentiable ℝ (fun y ↦ Γ y u) :=
    hΓd.clm_apply (differentiable_const u)
  have hΓv : Differentiable ℝ (fun y ↦ Γ y v) :=
    hΓd.clm_apply (differentiable_const v)
  have hΓvw : Differentiable ℝ (fun y ↦ Γ y v w) :=
    hΓv.clm_apply (differentiable_const w)
  have hΓuw : Differentiable ℝ (fun y ↦ Γ y u w) :=
    hΓu.clm_apply (differentiable_const w)
  have hC : Differentiable ℝ (fun y ↦ Γ y u (Γ y v w)) :=
    hΓu.clm_apply hΓvw
  have hD : Differentiable ℝ (fun y ↦ Γ y v (Γ y u w)) :=
    hΓv.clm_apply hΓuw
  unfold chartCurvatureOf
  change (fderiv ℝ
      (((fun y ↦ (fderiv ℝ Γ y u) v w) -
          (fun y ↦ (fderiv ℝ Γ y v) u w)) +
        (fun y ↦ Γ y u (Γ y v w)) -
        (fun y ↦ Γ y v (Γ y u w))) z) a = _
  rw [fderiv_sub (((hA.sub hB).add hC) z) (hD z),
    ContinuousLinearMap.sub_apply,
    fderiv_add ((hA.sub hB) z) (hC z),
    ContinuousLinearMap.add_apply,
    fderiv_sub (hA z) (hB z),
    ContinuousLinearMap.sub_apply]
  rw [fderiv_clm_apply ((hDΓu.clm_apply (differentiable_const v)) z)
      (differentiableAt_const w),
    fderiv_clm_apply (hDΓu z) (differentiableAt_const v),
    fderiv_clm_apply ((hDΓv.clm_apply (differentiable_const u)) z)
      (differentiableAt_const w),
    fderiv_clm_apply (hDΓv z) (differentiableAt_const u),
    fderiv_clm_apply (hΓu z) (hΓvw z),
    fderiv_clm_apply (hΓd z) (differentiableAt_const u),
    fderiv_clm_apply (hΓv z) (differentiableAt_const w),
    fderiv_clm_apply (hΓd z) (differentiableAt_const v),
    fderiv_clm_apply (hΓv z) (hΓuw z),
    fderiv_clm_apply (hΓd z) (differentiableAt_const v),
    fderiv_clm_apply (hΓu z) (differentiableAt_const w),
    fderiv_clm_apply (hΓd z) (differentiableAt_const u)]
  simp [ContinuousLinearMap.add_apply, add_assoc, sub_eq_add_neg]
  abel

/-- Two derivatives of a Christoffel field give one derivative of each
fixed-vector chart-curvature component. -/
theorem chartCurvatureOf_contDiff_one
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (hΓ : ContDiff ℝ 2 Γ)
    (u v w : V) :
    ContDiff ℝ 1 (fun z ↦ chartCurvatureOf Γ z u v w) := by
  have hΓ₁ : ContDiff ℝ 1 Γ := hΓ.of_le (by norm_num)
  have hDΓ : ContDiff ℝ 1 (fderiv ℝ Γ) :=
    hΓ.fderiv_right (m := 1) (by norm_num)
  have hA : ContDiff ℝ 1 (fun z ↦ (fderiv ℝ Γ z u) v w) :=
    (hDΓ.clm_apply contDiff_const |>.clm_apply contDiff_const)
      |>.clm_apply contDiff_const
  have hB : ContDiff ℝ 1 (fun z ↦ (fderiv ℝ Γ z v) u w) :=
    (hDΓ.clm_apply contDiff_const |>.clm_apply contDiff_const)
      |>.clm_apply contDiff_const
  have hΓu : ContDiff ℝ 1 (fun z ↦ Γ z u) :=
    hΓ₁.clm_apply contDiff_const
  have hΓv : ContDiff ℝ 1 (fun z ↦ Γ z v) :=
    hΓ₁.clm_apply contDiff_const
  have hΓvw : ContDiff ℝ 1 (fun z ↦ Γ z v w) :=
    hΓv.clm_apply contDiff_const
  have hΓuw : ContDiff ℝ 1 (fun z ↦ Γ z u w) :=
    hΓu.clm_apply contDiff_const
  unfold chartCurvatureOf
  exact ((hA.sub hB).add (hΓu.clm_apply hΓvw)).sub
    (hΓv.clm_apply hΓuw)

end ChartCurvatureSecondJet

/-- The anchor-chart Christoffel field for a metric family, obtained by
viewing one family member as a constant real-parameter flow. -/
noncomputable def anchorChartChristoffelFieldOperatorFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z : E) : E →L[ℝ] E →L[ℝ] E :=
  anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ g k) x 0 z

/-- The spatial derivative of the operator-valued anchor-chart Christoffel
field for a metric family. -/
noncomputable def anchorChartChristoffelFieldSpatialFDerivFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z : E) : E → (E →L[ℝ] E →L[ℝ] E) := fun u ↦
  fderiv ℝ (anchorChartChristoffelFieldOperatorFamily g x k) z u

/-- A componentwise second spatial derivative of the operator-valued
anchor-chart Christoffel field for a metric family. -/
noncomputable def anchorChartChristoffelFieldSecondSpatialFDerivFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z a u : E) : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ
    (fun z' : E ↦
      anchorChartChristoffelFieldSpatialFDerivFamily g x k z' u) z a

/-- A fixed-vector anchor-chart curvature value for a metric family, obtained
by viewing one family member as a constant real-parameter flow. -/
noncomputable def anchorChartCurvatureFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z u v w : E) : E :=
  anchorChartCurvatureFlow (fun _ : ℝ ↦ g k) x 0 z u v w

/-- The anchor-chart Christoffel field for a metric family, obtained by
viewing one family member as a constant real-parameter flow. -/
noncomputable def anchorChartChristoffelFieldFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z u w : E) : E :=
  anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ g k) x 0 z u w

omit [T2Space M] in
/-- Joint continuity of the operator-valued Christoffel field and its spatial
derivative makes every fixed-vector chart-curvature value jointly continuous. -/
theorem anchorChartCurvatureFamily_continuousAt_of_christoffelJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hDGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (u v w : E) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartCurvatureFamily g x p.1 p.2 u v w)
      (k₀, extChartAt I x x) := by
  have hDGammaU : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2 u)
      (k₀, extChartAt I x x) :=
    (continuous_apply u).continuousAt.comp hDGamma
  have hDGammaV : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2 v)
      (k₀, extChartAt I x x) :=
    (continuous_apply v).continuousAt.comp hDGamma
  have hDu : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2 u v w)
      (k₀, extChartAt I x x) :=
    (hDGammaU.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hDv : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2 v u w)
      (k₀, extChartAt I x x) :=
    (hDGammaV.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hGammaU : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 u)
      (k₀, extChartAt I x x) :=
    hGamma.clm_apply continuousAt_const
  have hGammaV : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 v)
      (k₀, extChartAt I x x) :=
    hGamma.clm_apply continuousAt_const
  have hGammaVW : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 v w)
      (k₀, extChartAt I x x) :=
    hGammaV.clm_apply continuousAt_const
  have hGammaUW : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 u w)
      (k₀, extChartAt I x x) :=
    hGammaU.clm_apply continuousAt_const
  have hFirstProduct : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 u
          (anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 v w))
      (k₀, extChartAt I x x) :=
    hGammaU.clm_apply hGammaVW
  have hSecondProduct : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 v
          (anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 u w))
      (k₀, extChartAt I x x) :=
    hGammaV.clm_apply hGammaUW
  unfold anchorChartCurvatureFamily anchorChartCurvatureFlow chartCurvatureOf
  simpa [anchorChartChristoffelFieldSpatialFDerivFamily,
    anchorChartChristoffelFieldOperatorFamily] using
    ((hDu.sub hDv).add hFirstProduct).sub hSecondProduct

omit [T2Space M] in
/-- Continuity of a family metric and its first spatial chart derivative
constructs continuity of every fixed Christoffel value. -/
theorem anchorChartChristoffelFieldFamily_continuousAt_of_blendedMetric
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (hD : ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
      (k₀, extChartAt I x x))
    (u w : E) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 u w)
      (k₀, extChartAt I x x) := by
  let q : E := extChartAt I x x
  have hInvMap : ContinuousAt ContinuousLinearMap.inverse
      (anchorBlendedMetricFamily g x k₀ q) :=
    ((anchorBlendedMetricFamily_isInvertible g x k₀ q)
      |>.contDiffAt_map_inverse (n := 0)).continuousAt
  have hInv : ContinuousAt
      (fun p : K × E ↦
        (anchorBlendedMetricFamily g x p.1 p.2).inverse)
      (k₀, q) := by
    simpa [Function.comp_def, q] using hInvMap.comp_of_eq hG rfl
  have hDflip : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2).flip)
      (k₀, q) := by
    exact
      (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous
        |>.continuousAt.comp_of_eq hD rfl
  have hDflipW : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2).flip w)
      (k₀, q) :=
    hDflip.clm_apply continuousAt_const
  have hDflipWFlip : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ
          (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip)
      (k₀, q) := by
    exact
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
        |>.continuousAt.comp_of_eq hDflipW rfl
  have hThird : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ
          (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip u)
      (k₀, q) :=
    hDflipWFlip.clm_apply continuousAt_const
  have hDw : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) w)
      (k₀, q) :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) w).continuous
      |>.continuousAt.comp_of_eq hD rfl
  have hFirst : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) w) u)
      (k₀, q) :=
    hDw.clm_apply continuousAt_const
  have hDu : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) u)
      (k₀, q) :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) u).continuous
      |>.continuousAt.comp_of_eq hD rfl
  have hSecond : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) u) w)
      (k₀, q) :=
    hDu.clm_apply continuousAt_const
  have hKoszul : ContinuousAt
      (fun p : K × E ↦
        (1 / 2 : ℝ) •
          (((fderiv ℝ
              (anchorBlendedMetricFamily g x p.1) p.2) w) u
            + ((fderiv ℝ
              (anchorBlendedMetricFamily g x p.1) p.2) u) w
            - ((fderiv ℝ
              (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip u))
      (k₀, q) :=
    (hFirst.add hSecond |>.sub hThird).const_smul (1 / 2 : ℝ)
  have hResult := hInv.clm_apply hKoszul
  have heq :
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 u w) =
      fun p : K × E ↦
        (anchorBlendedMetricFamily g x p.1 p.2).inverse
          ((1 / 2 : ℝ) •
            (((fderiv ℝ
                (anchorBlendedMetricFamily g x p.1) p.2) w) u
              + ((fderiv ℝ
                (anchorBlendedMetricFamily g x p.1) p.2) u) w
              - ((fderiv ℝ
                (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip u)) := by
    funext p
    rw [anchorChartChristoffelFieldFamily,
      anchorChartChristoffelFieldFlow_apply,
      anchorChartChristoffelFlow_apply_eq_inverse_koszul]
    rfl
  rw [heq]
  exact hResult

/-- A coordinate Ricci entry for a metric family, obtained by viewing one
family member as a constant real-parameter flow. -/
noncomputable def anchorChartRicciEntryFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z i j : E) : ℝ :=
  anchorChartRicciEntryFlow (fun _ : ℝ ↦ g k) x 0 z i j

/-- The spatial derivative of a family Ricci entry in one anchor chart. -/
noncomputable def anchorChartRicciEntrySpatialFDerivFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z i j : E) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun z' : E ↦ anchorChartRicciEntryFamily g x k z' i j) z

omit [T2Space M] in
/-- Differentiating the finite-basis curvature trace commutes with that
finite trace. -/
theorem anchorChartRicciEntrySpatialFDerivFamily_apply_eq_basis_sum
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z a v w : E) :
    anchorChartRicciEntrySpatialFDerivFamily g x k z v w a =
      ∑ r, LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ E).coord r)
        (fderiv ℝ
          (fun y : E ↦ anchorChartCurvatureFamily g x k y
            ((Module.finBasis ℝ E) r) v w) z a) := by
  classical
  let b := Module.finBasis ℝ E
  let Γ := GeodesicTransport.chartChristoffelField (g k) x
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hΓ : ContDiff ℝ 2 Γ :=
    (GeodesicTransport.chartChristoffelField_contDiff_top (g k) x).of_le
      htwo_le_top
  have hdiff : ∀ r : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y : E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartCurvatureFamily g x k y (b r) v w)) z := by
    intro r
    have hR : DifferentiableAt ℝ
        (fun y : E ↦ anchorChartCurvatureFamily g x k y (b r) v w) z := by
      have h :=
        (chartCurvatureOf_contDiff_one Γ hΓ (b r) v w).differentiable
          one_ne_zero z
      simpa [anchorChartCurvatureFamily, anchorChartCurvatureFlow,
        anchorChartChristoffelFieldFlow, Γ] using h
    exact (differentiableAt_const
      (LinearMap.toContinuousLinearMap (b.coord r))).clm_apply hR
  unfold anchorChartRicciEntrySpatialFDerivFamily
  change (fderiv ℝ
      (fun y : E ↦ ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
        (anchorChartCurvatureFamily g x k y (b r) v w)) z) a =
      ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
        (fderiv ℝ
          (fun y : E ↦ anchorChartCurvatureFamily g x k y (b r) v w) z a)
  rw [fderiv_fun_sum (fun r _hr ↦ hdiff r),
    ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro r _hr
  have hR : DifferentiableAt ℝ
      (fun y : E ↦ anchorChartCurvatureFamily g x k y (b r) v w) z := by
    have h := (chartCurvatureOf_contDiff_one Γ hΓ (b r) v w).differentiable
      one_ne_zero z
    simpa [anchorChartCurvatureFamily, anchorChartCurvatureFlow,
      anchorChartChristoffelFieldFlow, Γ] using h
  rw [fderiv_clm_apply
    (differentiableAt_const (LinearMap.toContinuousLinearMap (b.coord r))) hR]
  simp

/-- Chart data sufficient to construct continuous coordinate covariant-Ricci
entries for a metric family at one parameter and manifold anchor. -/
structure MetricFamilyRicciJetChartContinuousAt
    {K : Type v} [TopologicalSpace K]
    (g : K → ClosedSmoothRiemannianMetric n M) (k₀ : K) (x : M) : Prop where
  inverseCoeff : ∀ i j : Fin (Module.finrank ℝ E),
    ContinuousAt
      (fun p : K × E ↦
        anchorChartInverseMetricCoeffFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x)
  christoffel : ∀ u w : E,
    ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 u w)
      (k₀, extChartAt I x x)
  ricciEntry : ∀ i j : E,
    ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntryFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x)
  ricciSpatialFDeriv : ∀ i j : E,
    ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x)

private theorem continuousAt_finset_sum_ricci_jet
    {X ι Y : Type*} [TopologicalSpace X] {p : X}
    [TopologicalSpace Y] [AddCommMonoid Y] [ContinuousAdd Y]
    (s : Finset ι) (f : ι → X → Y)
    (hf : ∀ r ∈ s, ContinuousAt (f r) p) :
    ContinuousAt (fun q ↦ ∑ r ∈ s, f r q) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : Y)) p)
  | @insert r s hr ih =>
      have hrCont : ContinuousAt (f r) p :=
        hf r (Finset.mem_insert_self r s)
      have hsCont : ContinuousAt (fun q ↦ ∑ k ∈ s, f k q) p :=
        ih (fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert hr] using hrCont.add hsCont

/-- A path of continuous linear maps with finite-dimensional domain is
continuous when every fixed-input evaluation is continuous. -/
theorem continuousAt_clm_of_apply
    {X A B : Type*}
    [TopologicalSpace X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Φ : X → A →L[ℝ] B} {p : X}
    (h : ∀ a : A, ContinuousAt (fun q ↦ Φ q a) p) :
    ContinuousAt Φ p := by
  let b := Module.finBasis ℝ A
  let coordC : Fin (Module.finrank ℝ A) → A →L[ℝ] ℝ := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  have hrepr : ∀ ρ : A →L[ℝ] B,
      ρ = ∑ i, (coordC i).smulRight (ρ (b i)) := by
    intro ρ
    ext a
    have ha := b.sum_repr a
    conv_lhs => rw [← ha]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show coordC i a = b.coord i a from rfl, Module.Basis.coord_apply]
  have hfun : Φ = fun q ↦
      ∑ i, (coordC i).smulRight (Φ q (b i)) := by
    funext q
    exact hrepr (Φ q)
  rw [hfun]
  apply continuousAt_finset_sum_ricci_jet Finset.univ
  intro i _hi
  exact
    (ContinuousLinearMap.smulRightL ℝ A B (coordC i)).continuous.continuousAt.comp
      (h (b i))

section ChristoffelMetricSecondJet

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Differentiating the closed Christoffel operator in a spatial direction is
the metric variation operator for the corresponding directional metric jet. -/
theorem fderiv_christoffelClosedOp_eq_spatial_christoffelDeriv
    (G : V → V →L[ℝ] V →L[ℝ] ℝ) (hG : ContDiff ℝ 3 G)
    (hinv : ∀ y : V, (G y).IsInvertible) (z a u : V) :
    fderiv ℝ (fun y ↦ RicciFlow.RicciFlow.christoffelClosedOp G y u) z a =
      RicciFlow.RicciFlow.christoffelDerivOp G
        (fun y ↦ fderiv ℝ G y a) z u := by
  let Gt : ℝ → V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun t y ↦ G (y + t • a)
  let H : V → V →L[ℝ] V →L[ℝ] ℝ := fun y ↦ fderiv ℝ G y a
  have hline : HasDerivAt (fun t : ℝ ↦ z + t • a) a 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const a).const_add z
  have hGdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hdG : HasDerivAt (fun t ↦ Gt t z) (H z) 0 := by
    have hGat : HasFDerivAt G (fderiv ℝ G (z + (0 : ℝ) • a))
        (z + (0 : ℝ) • a) := hGdiff.differentiableAt.hasFDerivAt
    have hcomp : HasDerivAt
        (G ∘ fun t : ℝ ↦ z + t • a)
        ((fderiv ℝ G (z + (0 : ℝ) • a)) a) 0 :=
      HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
        (f := fun t : ℝ ↦ z + t • a) (l := G) 0 hGat hline
    simpa [Gt, H, Function.comp_def] using hcomp
  have hev : ∀ᶠ t in nhds (0 : ℝ), (Gt t z).IsInvertible :=
    Filter.Eventually.of_forall fun t ↦ hinv (z + t • a)
  have hshift : ∀ t : ℝ,
      fderiv ℝ (Gt t) z = fderiv ℝ G (z + t • a) := by
    intro t
    simpa [Gt] using
      (fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := z) (t • a))
  have hmix : ∀ p q r : V,
      HasDerivAt (fun t ↦ (fderiv ℝ (Gt t) z p) q r)
        ((fderiv ℝ H z p) q r) 0 := by
    intro p q r
    let φ : V → ℝ := fun y ↦ ((fderiv ℝ G y p) q) r
    have hφ : ContDiff ℝ 1 φ := by
      let hD := hG.fderiv_right (m := 1) (by norm_num)
      have hp := hD.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : V ↦ p))
      have hq := hp.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : V ↦ q))
      have hr := hq.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : V ↦ r))
      simpa [φ] using hr
    have hφpath : HasDerivAt (fun t : ℝ ↦ φ (z + t • a))
        (fderiv ℝ φ z a) 0 := by
      have hφat : HasFDerivAt φ (fderiv ℝ φ (z + (0 : ℝ) • a))
          (z + (0 : ℝ) • a) :=
        (hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hcomp : HasDerivAt (φ ∘ fun t : ℝ ↦ z + t • a)
          ((fderiv ℝ φ (z + (0 : ℝ) • a)) a) 0 :=
        HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
          (f := fun t : ℝ ↦ z + t • a) (l := φ) 0 hφat hline
      simpa [Function.comp_def] using hcomp
    have hHcomp : fderiv ℝ φ z a = ((fderiv ℝ H z p) q) r := by
      have hd2G : DifferentiableAt ℝ (fderiv ℝ G) z :=
        ((hG.contDiffAt).fderiv_right (m := 1) (by norm_num))
          |>.differentiableAt one_ne_zero
      have hp := HasFDerivAt.clm_apply (𝕜 := ℝ)
        (G := V) (H := V →L[ℝ] V →L[ℝ] ℝ)
        hd2G.hasFDerivAt (hasFDerivAt_const p z)
      have hpq := HasFDerivAt.clm_apply (𝕜 := ℝ)
        (G := V) (H := V →L[ℝ] ℝ) hp (hasFDerivAt_const q z)
      have hpqr := HasFDerivAt.clm_apply (𝕜 := ℝ)
        (G := V) (H := ℝ) hpq (hasFDerivAt_const r z)
      have ha := HasFDerivAt.clm_apply (𝕜 := ℝ)
        (G := V) (H := V →L[ℝ] V →L[ℝ] ℝ)
        hd2G.hasFDerivAt (hasFDerivAt_const a z)
      have haq := HasFDerivAt.clm_apply (𝕜 := ℝ)
        (G := V) (H := V →L[ℝ] ℝ) ha (hasFDerivAt_const q z)
      have haqr := HasFDerivAt.clm_apply (𝕜 := ℝ)
        (G := V) (H := ℝ) haq (hasFDerivAt_const r z)
      have hφfd := hpqr.fderiv
      have hHfd := haqr.fderiv
      have hφeval := congrArg (fun L : V →L[ℝ] ℝ ↦ L a) hφfd
      have hHeval := congrArg (fun L : V →L[ℝ] ℝ ↦ L p) hHfd
      simp at hφeval hHeval
      have hsymm := ((hG.contDiffAt (x := z)).isSymmSndFDerivAt
        (by norm_num)).eq a p
      have hsymmEval := congrArg
        (fun L : V →L[ℝ] V →L[ℝ] ℝ ↦ L q r) hsymm
      have hcomm : ((fderiv ℝ H z p) q) r =
          fderiv ℝ (fun y ↦ H y q r) z p := by
        have e1 := RicciFlow.RicciFlow.fderiv_clm_family_apply
          ha.differentiableAt p q
        have e2 := RicciFlow.RicciFlow.fderiv_clm_family_apply
          haq.differentiableAt p r
        calc
          ((fderiv ℝ H z p) q) r =
              (fderiv ℝ (fun y ↦ H y q) z p) r :=
            congrArg (fun L : V →L[ℝ] ℝ ↦ L r) e1
          _ = fderiv ℝ (fun y ↦ H y q r) z p := e2
      simpa [φ, H] using
        (hφeval.trans (hsymmEval.trans hHeval.symm)).trans hcomm.symm
    rw [← hHcomp]
    simpa only [hshift, φ] using hφpath
  have hpath := RicciFlow.RicciFlow.hasDerivAt_christoffelClosedOp
    (Gt := Gt) (H := H) (x := z) (t₀ := 0) u hdG hev hmix
  have hGammaDiff : DifferentiableAt ℝ
      (fun y ↦ RicciFlow.RicciFlow.christoffelClosedOp G y u) z :=
    (RicciFlow.RicciFlow.contDiffAt_christoffelClosedOp G hG hinv u)
      |>.differentiableAt (by norm_num)
  have htarget : HasDerivAt
      (fun t : ℝ ↦ RicciFlow.RicciFlow.christoffelClosedOp G (z + t • a) u)
      (fderiv ℝ (fun y ↦
        RicciFlow.RicciFlow.christoffelClosedOp G y u) z a) 0 := by
    have hGammaAt : HasFDerivAt
        (fun y ↦ RicciFlow.RicciFlow.christoffelClosedOp G y u)
        (fderiv ℝ (fun y ↦
          RicciFlow.RicciFlow.christoffelClosedOp G y u)
          (z + (0 : ℝ) • a)) (z + (0 : ℝ) • a) := by
      simpa using hGammaDiff.hasFDerivAt
    have hcomp : HasDerivAt
        ((fun y ↦ RicciFlow.RicciFlow.christoffelClosedOp G y u) ∘
          fun t : ℝ ↦ z + t • a)
        ((fderiv ℝ (fun y ↦
          RicciFlow.RicciFlow.christoffelClosedOp G y u)
          (z + (0 : ℝ) • a)) a) 0 :=
      HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
        (f := fun t : ℝ ↦ z + t • a)
        (l := fun y ↦ RicciFlow.RicciFlow.christoffelClosedOp G y u)
        0 hGammaAt hline
    simpa [Function.comp_def] using hcomp
  have hpath' : HasDerivAt
      (fun t : ℝ ↦ RicciFlow.RicciFlow.christoffelClosedOp G (z + t • a) u)
      (RicciFlow.RicciFlow.christoffelDerivOp G H z u) 0 := by
    dsimp only [Gt] at hpath
    have hfun :
        (fun t : ℝ ↦ RicciFlow.RicciFlow.christoffelClosedOp
          (fun y ↦ G (y + t • a)) z u) =
        (fun t : ℝ ↦ RicciFlow.RicciFlow.christoffelClosedOp
          G (z + t • a) u) := by
      funext t
      ext v
      simp only [RicciFlow.RicciFlow.christoffelClosedOp_apply]
      have hs : fderiv ℝ (fun y ↦ G (y + t • a)) z =
          fderiv ℝ G (z + t • a) :=
        fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := z) (t • a)
      apply congrArg (G (z + t • a)).inverse
      apply ContinuousLinearMap.ext
      intro w
      change (1 / 2 : ℝ) *
          ((fderiv ℝ (fun y ↦ G (y + t • a)) z u) v w
            + (fderiv ℝ (fun y ↦ G (y + t • a)) z v) u w
            - (fderiv ℝ (fun y ↦ G (y + t • a)) z w) u v) = _
      rw [hs]
      rfl
    rw [hfun] at hpath
    simpa [H, RicciFlow.RicciFlow.christoffelClosedOp,
      CovariantDerivative.christoffelFunctional] using hpath
  exact htarget.unique hpath'

/-- Pointwise-continuous metric values and the first two directional metric
jets make a fixed directional derivative of the closed Christoffel operator
continuous across a parameter family. -/
theorem continuousAt_fderiv_christoffelClosedOp_of_metricJets
    {K : Type*} [TopologicalSpace K]
    (G : K → V → V →L[ℝ] V →L[ℝ] ℝ)
    (hSmooth : ∀ k, ContDiff ℝ 3 (G k))
    (hinv : ∀ k z, (G k z).IsInvertible)
    (k₀ : K) (z₀ a u : V)
    (hG : ContinuousAt (Function.uncurry G) (k₀, z₀))
    (hD : ContinuousAt
      (fun p : K × V ↦ fderiv ℝ (G p.1) p.2) (k₀, z₀))
    (hD2 : ContinuousAt
      (fun p : K × V ↦
        fderiv ℝ (fun y ↦ fderiv ℝ (G p.1) y a) p.2)
      (k₀, z₀)) :
    ContinuousAt
      (fun p : K × V ↦
        fderiv ℝ
          (fun y ↦ RicciFlow.RicciFlow.christoffelClosedOp (G p.1) y u)
          p.2 a)
      (k₀, z₀) := by
  let H : K → V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun k y ↦ fderiv ℝ (G k) y a
  have hInvMap : ContinuousAt ContinuousLinearMap.inverse (G k₀ z₀) :=
    ((hinv k₀ z₀).contDiffAt_map_inverse (n := 0)).continuousAt
  have hInv : ContinuousAt (fun p : K × V ↦ (G p.1 p.2).inverse)
      (k₀, z₀) := by
    simpa [Function.comp_def] using hInvMap.comp_of_eq hG rfl
  have hH : ContinuousAt (Function.uncurry H) (k₀, z₀) := by
    simpa [H] using hD.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : K × V ↦ a) (k₀, z₀))
  have hKG : ∀ v : V, ContinuousAt
      (fun p : K × V ↦ LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional (G p.1) p.2 u v))
      (k₀, z₀) := by
    intro v
    apply continuousAt_clm_of_apply
    intro w
    have hu : ContinuousAt
        (fun p : K × V ↦ fderiv ℝ (G p.1) p.2 u) (k₀, z₀) :=
      hD.clm_apply continuousAt_const
    have hv : ContinuousAt
        (fun p : K × V ↦ fderiv ℝ (G p.1) p.2 v) (k₀, z₀) :=
      hD.clm_apply continuousAt_const
    have hw : ContinuousAt
        (fun p : K × V ↦ fderiv ℝ (G p.1) p.2 w) (k₀, z₀) :=
      hD.clm_apply continuousAt_const
    have huv := (hu.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : K × V ↦ v) (k₀, z₀)))
      |>.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × V ↦ w) (k₀, z₀))
    have hvu := (hv.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : K × V ↦ u) (k₀, z₀)))
      |>.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × V ↦ w) (k₀, z₀))
    have hthird := (hw.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : K × V ↦ u) (k₀, z₀)))
      |>.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × V ↦ v) (k₀, z₀))
    simpa [CovariantDerivative.christoffelFunctional] using
      ((huv.add hvu).sub hthird).const_mul (1 / 2 : ℝ)
  have hKH : ∀ v : V, ContinuousAt
      (fun p : K × V ↦ LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional (H p.1) p.2 u v))
      (k₀, z₀) := by
    intro v
    apply continuousAt_clm_of_apply
    intro w
    have hu : ContinuousAt
        (fun p : K × V ↦ fderiv ℝ (fun y ↦ H p.1 y) p.2 u)
        (k₀, z₀) := hD2.clm_apply continuousAt_const
    have hv : ContinuousAt
        (fun p : K × V ↦ fderiv ℝ (fun y ↦ H p.1 y) p.2 v)
        (k₀, z₀) := hD2.clm_apply continuousAt_const
    have hw : ContinuousAt
        (fun p : K × V ↦ fderiv ℝ (fun y ↦ H p.1 y) p.2 w)
        (k₀, z₀) := hD2.clm_apply continuousAt_const
    have huv := (hu.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : K × V ↦ v) (k₀, z₀)))
      |>.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × V ↦ w) (k₀, z₀))
    have hvu := (hv.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : K × V ↦ u) (k₀, z₀)))
      |>.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × V ↦ w) (k₀, z₀))
    have hthird := (hw.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : K × V ↦ u) (k₀, z₀)))
      |>.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × V ↦ v) (k₀, z₀))
    simpa [H, CovariantDerivative.christoffelFunctional] using
      ((huv.add hvu).sub hthird).const_mul (1 / 2 : ℝ)
  have hCorrection : ContinuousAt
      (fun p : K × V ↦
        -((G p.1 p.2).inverse.comp
          ((H p.1 p.2).comp (G p.1 p.2).inverse)))
      (k₀, z₀) :=
    (hInv.clm_comp (hH.clm_comp hInv)).neg
  have hResult : ContinuousAt
      (fun p : K × V ↦
        RicciFlow.RicciFlow.christoffelDerivOp
          (G p.1) (H p.1) p.2 u)
      (k₀, z₀) := by
    apply continuousAt_clm_of_apply
    intro v
    simpa [RicciFlow.RicciFlow.christoffelDerivOp_apply,
      RicciFlow.christoffelDeriv] using
      (hCorrection.clm_apply (hKG v)).add (hInv.clm_apply (hKH v))
  have heq :
      (fun p : K × V ↦
        fderiv ℝ
          (fun y ↦ RicciFlow.RicciFlow.christoffelClosedOp (G p.1) y u)
          p.2 a) =
      (fun p : K × V ↦
        RicciFlow.RicciFlow.christoffelDerivOp
          (G p.1) (H p.1) p.2 u) := by
    funext p
    simpa [H] using
      fderiv_christoffelClosedOp_eq_spatial_christoffelDeriv
        (G p.1) (hSmooth p.1) (hinv p.1) p.2 a u
  rw [heq]
  exact hResult

end ChristoffelMetricSecondJet

omit [T2Space M] in
/-- The constant-flow anchor Christoffel field is the closed Christoffel
operator for the corresponding blended metric, with its two vector slots
in the field convention. -/
theorem anchorChartChristoffelFieldOperatorFamily_apply_eq_christoffelClosedOp
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z u w : E) :
    anchorChartChristoffelFieldOperatorFamily g x k z u w =
      RicciFlow.RicciFlow.christoffelClosedOp
        (anchorBlendedMetricFamily g x k) z w u := by
  rw [anchorChartChristoffelFieldOperatorFamily,
    anchorChartChristoffelFieldFlow_apply,
    anchorChartChristoffelFlow_apply_eq_inverse_koszul,
    RicciFlow.RicciFlow.christoffelClosedOp_apply]
  rfl

omit [T2Space M] in
/-- Continuity of a blended metric and its first two spatial jets constructs
continuity of the full first spatial Christoffel jet. -/
theorem anchorChartChristoffelFieldSpatialFDerivFamily_continuousAt_of_metricJets
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (hDG : ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
      (k₀, extChartAt I x x))
    (hD2G : ∀ a : E, ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ
          (fun z ↦ fderiv ℝ
            (anchorBlendedMetricFamily g x p.1) z a) p.2)
      (k₀, extChartAt I x x)) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x) := by
  let q : E := extChartAt I x x
  have hSmooth : ∀ k : K,
      ContDiff ℝ 3 (anchorBlendedMetricFamily g x k) := by
    intro k
    have hTop : ContDiff ℝ ∞
        (CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := n) x)
          (GeodesicTransport.backgroundMetric (n := n)) (g k).inner x) := by
      exact CovariantDerivative.contDiff_blendedChartMetric
        (GeodesicTransport.cutoff (n := n) x)
        (GeodesicTransport.backgroundMetric (n := n)) (g k).inner x
        (by simp)
        (GeodesicTransport.cutoff_contDiff (n := n) x)
        (GeodesicTransport.cutoff_tsupport (n := n) x)
        (g k).contMDiff_inner
    have hthree_le_top : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    simpa [anchorBlendedMetricFamily, anchorBlendedMetricFlow] using
      hTop.of_le hthree_le_top
  have hClosed : ∀ a w : E, ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ
          (fun z ↦ RicciFlow.RicciFlow.christoffelClosedOp
            (anchorBlendedMetricFamily g x p.1) z w) p.2 a)
      (k₀, q) := by
    intro a w
    exact continuousAt_fderiv_christoffelClosedOp_of_metricJets
      (anchorBlendedMetricFamily g x) hSmooth
      (anchorBlendedMetricFamily_isInvertible g x)
      k₀ q a w (by simpa [q] using hG) (by simpa [q] using hDG)
      (by simpa [q] using hD2G a)
  unfold anchorChartChristoffelFieldSpatialFDerivFamily
  rw [continuousAt_pi]
  intro a
  apply continuousAt_clm_of_apply
  intro u
  apply continuousAt_clm_of_apply
  intro w
  have hEval : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ
          (fun z ↦ RicciFlow.RicciFlow.christoffelClosedOp
            (anchorBlendedMetricFamily g x p.1) z w) p.2 a) u)
      (k₀, q) :=
    (hClosed a w).clm_apply continuousAt_const
  have hEq :
      (fun p : K × E ↦
        (fderiv ℝ
          (anchorChartChristoffelFieldOperatorFamily g x p.1) p.2 a) u w) =
      (fun p : K × E ↦
        (fderiv ℝ
          (fun z ↦ RicciFlow.RicciFlow.christoffelClosedOp
            (anchorBlendedMetricFamily g x p.1) z w) p.2 a) u) := by
    funext p
    have hOpDiff : DifferentiableAt ℝ
        (anchorChartChristoffelFieldOperatorFamily g x p.1) p.2 := by
      simpa [anchorChartChristoffelFieldOperatorFamily,
        anchorChartChristoffelFieldFlow] using
        (GeodesicTransport.chartChristoffelField_contDiff_top (g p.1) x)
          |>.differentiable (by norm_num) p.2
    have hOpUDiff : DifferentiableAt ℝ
        (fun z ↦ anchorChartChristoffelFieldOperatorFamily
          g x p.1 z u) p.2 :=
      hOpDiff.clm_apply (differentiableAt_const u)
    have hClosedDiff : DifferentiableAt ℝ
        (fun z ↦ RicciFlow.RicciFlow.christoffelClosedOp
          (anchorBlendedMetricFamily g x p.1) z w) p.2 :=
      (RicciFlow.RicciFlow.contDiffAt_christoffelClosedOp
        (anchorBlendedMetricFamily g x p.1) (hSmooth p.1)
        (anchorBlendedMetricFamily_isInvertible g x p.1) w)
        |>.differentiableAt (by norm_num)
    have hFirst := RicciFlow.RicciFlow.fderiv_clm_family_apply
      hOpDiff a u
    have hSecond := RicciFlow.RicciFlow.fderiv_clm_family_apply
      hOpUDiff a w
    have hThird := RicciFlow.RicciFlow.fderiv_clm_family_apply
      hClosedDiff a u
    have hPointwise :
        (fun z ↦ anchorChartChristoffelFieldOperatorFamily
          g x p.1 z u w) =
        (fun z ↦ RicciFlow.RicciFlow.christoffelClosedOp
          (anchorBlendedMetricFamily g x p.1) z w u) := by
      funext z
      exact
        anchorChartChristoffelFieldOperatorFamily_apply_eq_christoffelClosedOp
          g x p.1 z u w
    calc
      (fderiv ℝ
          (anchorChartChristoffelFieldOperatorFamily g x p.1) p.2 a) u w =
          (fderiv ℝ
            (fun z ↦ anchorChartChristoffelFieldOperatorFamily
              g x p.1 z u) p.2 a) w :=
        congrArg (fun L : E →L[ℝ] E ↦ L w) hFirst
      _ = fderiv ℝ
          (fun z ↦ anchorChartChristoffelFieldOperatorFamily
            g x p.1 z u w) p.2 a := hSecond
      _ = fderiv ℝ
          (fun z ↦ RicciFlow.RicciFlow.christoffelClosedOp
            (anchorBlendedMetricFamily g x p.1) z w u) p.2 a := by
        rw [hPointwise]
      _ = (fderiv ℝ
          (fun z ↦ RicciFlow.RicciFlow.christoffelClosedOp
            (anchorBlendedMetricFamily g x p.1) z w) p.2 a) u := hThird.symm
  rw [hEq]
  simpa [q] using hEval

omit [T2Space M] in
/-- The blended metric and its first spatial derivative make the full
operator-valued Christoffel family jointly continuous. -/
theorem anchorChartChristoffelFieldOperatorFamily_continuousAt_of_blendedMetric
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (hDG : ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
      (k₀, extChartAt I x x)) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2)
      (k₀, extChartAt I x x) := by
  apply continuousAt_clm_of_apply
  intro u
  apply continuousAt_clm_of_apply
  intro w
  simpa [anchorChartChristoffelFieldFamily,
    anchorChartChristoffelFieldOperatorFamily] using
    anchorChartChristoffelFieldFamily_continuousAt_of_blendedMetric
      hG hDG u w

omit [T2Space M] in
/-- The operator-valued Christoffel field and its spatial derivative construct
joint continuity of every coordinate Ricci entry by finite-basis trace. -/
theorem anchorChartRicciEntryFamily_continuousAt_of_christoffelJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hDGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (v w : E) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntryFamily g x p.1 p.2 v w)
      (k₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  have hTrace : ContinuousAt
      (fun p : K × E ↦
        ∑ i, LinearMap.toContinuousLinearMap (b.coord i)
          (anchorChartCurvatureFamily g x p.1 p.2 (b i) v w))
      (k₀, extChartAt I x x) := by
    apply continuousAt_finset_sum_ricci_jet Finset.univ
    intro i _hi
    have hR := anchorChartCurvatureFamily_continuousAt_of_christoffelJet
      hGamma hDGamma (b i) v w
    exact continuousAt_const.clm_apply hR
  unfold anchorChartRicciEntryFamily anchorChartRicciEntryFlow
  simpa [anchorChartCurvatureFamily, b] using hTrace

omit [T2Space M] in
/-- Continuity of the first two spatial Christoffel jets makes the
operator-valued spatial derivative of every coordinate Ricci entry jointly
continuous. -/
theorem anchorChartRicciEntrySpatialFDerivFamily_continuousAt_of_christoffelSecondJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hDGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hD2Gamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSecondSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (i j : E) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  let q : E := extChartAt I x x
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  apply continuousAt_clm_of_apply
  intro a
  have hCurvDeriv : ∀ r : Fin (Module.finrank ℝ E),
      ContinuousAt
        (fun p : K × E ↦
          fderiv ℝ
            (fun y : E ↦ anchorChartCurvatureFamily g x p.1 y
              (b r) i j) p.2 a)
        (k₀, q) := by
    intro r
    have hD2A : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSecondSpatialFDerivFamily
            g x p.1 p.2 a)
        (k₀, q) :=
      (continuous_apply a).continuousAt.comp hD2Gamma
    have hD2AU : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSecondSpatialFDerivFamily
            g x p.1 p.2 a (b r))
        (k₀, q) :=
      (continuous_apply (b r)).continuousAt.comp hD2A
    have hD2AI : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSecondSpatialFDerivFamily
            g x p.1 p.2 a i)
        (k₀, q) :=
      (continuous_apply i).continuousAt.comp hD2A
    have hFirst : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSecondSpatialFDerivFamily
            g x p.1 p.2 a (b r) i j)
        (k₀, q) :=
      (hD2AU.clm_apply continuousAt_const).clm_apply continuousAt_const
    have hSecond : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSecondSpatialFDerivFamily
            g x p.1 p.2 a i (b r) j)
        (k₀, q) :=
      (hD2AI.clm_apply continuousAt_const).clm_apply continuousAt_const
    have hDGA : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a)
        (k₀, q) :=
      (continuous_apply a).continuousAt.comp hDGamma
    have hDGAU : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a (b r))
        (k₀, q) :=
      hDGA.clm_apply continuousAt_const
    have hDGAI : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a i)
        (k₀, q) :=
      hDGA.clm_apply continuousAt_const
    have hDGAUI : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a (b r) i)
        (k₀, q) :=
      hDGAU.clm_apply continuousAt_const
    have hDGAUJ : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a (b r) j)
        (k₀, q) :=
      hDGAU.clm_apply continuousAt_const
    have hDGAIJ : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a i j)
        (k₀, q) :=
      hDGAI.clm_apply continuousAt_const
    have hGammaU : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 (b r))
        (k₀, q) :=
      hGamma.clm_apply continuousAt_const
    have hGammaI : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 i)
        (k₀, q) :=
      hGamma.clm_apply continuousAt_const
    have hGammaIJ : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 i j)
        (k₀, q) :=
      hGammaI.clm_apply continuousAt_const
    have hGammaUJ : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 (b r) j)
        (k₀, q) :=
      hGammaU.clm_apply continuousAt_const
    have hThird : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a (b r)
            (anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 i j))
        (k₀, q) :=
      hDGAU.clm_apply hGammaIJ
    have hFourth : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 (b r)
            (anchorChartChristoffelFieldSpatialFDerivFamily
              g x p.1 p.2 a i j))
        (k₀, q) :=
      hGammaU.clm_apply hDGAIJ
    have hFifth : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a i
            (anchorChartChristoffelFieldOperatorFamily
              g x p.1 p.2 (b r) j))
        (k₀, q) :=
      hDGAI.clm_apply hGammaUJ
    have hSixth : ContinuousAt
        (fun p : K × E ↦
          anchorChartChristoffelFieldOperatorFamily g x p.1 p.2 i
            (anchorChartChristoffelFieldSpatialFDerivFamily
              g x p.1 p.2 a (b r) j))
        (k₀, q) :=
      hGammaI.clm_apply hDGAUJ
    have hFormula : ∀ p : K × E,
        fderiv ℝ
            (fun y : E ↦ anchorChartCurvatureFamily g x p.1 y
              (b r) i j) p.2 a =
          anchorChartChristoffelFieldSecondSpatialFDerivFamily
              g x p.1 p.2 a (b r) i j
            - anchorChartChristoffelFieldSecondSpatialFDerivFamily
              g x p.1 p.2 a i (b r) j
            + anchorChartChristoffelFieldSpatialFDerivFamily
              g x p.1 p.2 a (b r)
                (anchorChartChristoffelFieldOperatorFamily
                  g x p.1 p.2 i j)
            + anchorChartChristoffelFieldOperatorFamily
              g x p.1 p.2 (b r)
                (anchorChartChristoffelFieldSpatialFDerivFamily
                  g x p.1 p.2 a i j)
            - anchorChartChristoffelFieldSpatialFDerivFamily
              g x p.1 p.2 a i
                (anchorChartChristoffelFieldOperatorFamily
                  g x p.1 p.2 (b r) j)
            - anchorChartChristoffelFieldOperatorFamily
              g x p.1 p.2 i
                (anchorChartChristoffelFieldSpatialFDerivFamily
                  g x p.1 p.2 a (b r) j) := by
      intro p
      let Γ := GeodesicTransport.chartChristoffelField (g p.1) x
      have hΓ : ContDiff ℝ 2 Γ :=
        (GeodesicTransport.chartChristoffelField_contDiff_top (g p.1) x).of_le
          htwo_le_top
      simpa [anchorChartCurvatureFamily, anchorChartCurvatureFlow,
        anchorChartChristoffelFieldFlow,
        anchorChartChristoffelFieldOperatorFamily,
        anchorChartChristoffelFieldSpatialFDerivFamily,
        anchorChartChristoffelFieldSecondSpatialFDerivFamily, Γ] using
        (fderiv_chartCurvatureOf_apply_component
          Γ hΓ p.2 a (b r) i j)
    rw [show
      (fun p : K × E ↦
        fderiv ℝ
          (fun y : E ↦ anchorChartCurvatureFamily g x p.1 y
            (b r) i j) p.2 a) =
      (fun p : K × E ↦
        anchorChartChristoffelFieldSecondSpatialFDerivFamily
            g x p.1 p.2 a (b r) i j
          - anchorChartChristoffelFieldSecondSpatialFDerivFamily
            g x p.1 p.2 a i (b r) j
          + anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a (b r)
              (anchorChartChristoffelFieldOperatorFamily
                g x p.1 p.2 i j)
          + anchorChartChristoffelFieldOperatorFamily
            g x p.1 p.2 (b r)
              (anchorChartChristoffelFieldSpatialFDerivFamily
                g x p.1 p.2 a i j)
          - anchorChartChristoffelFieldSpatialFDerivFamily
            g x p.1 p.2 a i
              (anchorChartChristoffelFieldOperatorFamily
                g x p.1 p.2 (b r) j)
          - anchorChartChristoffelFieldOperatorFamily
            g x p.1 p.2 i
              (anchorChartChristoffelFieldSpatialFDerivFamily
                g x p.1 p.2 a (b r) j)) by
        funext p
        exact hFormula p]
    exact ((((hFirst.sub hSecond).add hThird).add hFourth).sub hFifth).sub hSixth
  have hTrace : ContinuousAt
      (fun p : K × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
          (fderiv ℝ
            (fun y : E ↦ anchorChartCurvatureFamily g x p.1 y
              (b r) i j) p.2 a))
      (k₀, q) := by
    apply continuousAt_finset_sum_ricci_jet Finset.univ
    intro r _hr
    exact continuousAt_const.clm_apply (hCurvDeriv r)
  have hEq :
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j a) =
      (fun p : K × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
          (fderiv ℝ
            (fun y : E ↦ anchorChartCurvatureFamily g x p.1 y
              (b r) i j) p.2 a)) := by
    funext p
    simpa [b] using
      (anchorChartRicciEntrySpatialFDerivFamily_apply_eq_basis_sum
        g x p.1 p.2 a i j)
  rw [hEq]
  exact hTrace

omit [T2Space M] in
/-- Package a Ricci jet without assuming coordinate Ricci continuity: that
field is derived from the operator-valued Christoffel first jet. -/
theorem metricFamilyRicciJetChartContinuousAt_of_christoffelJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hInverseCoeff : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt
        (fun p : K × E ↦
          anchorChartInverseMetricCoeffFamily g x p.1 p.2 i j)
        (k₀, extChartAt I x x))
    (hGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hDGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hRicciSpatialFDeriv : ∀ i j : E,
      ContinuousAt
        (fun p : K × E ↦
          anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j)
        (k₀, extChartAt I x x)) :
    MetricFamilyRicciJetChartContinuousAt g k₀ x where
  inverseCoeff := hInverseCoeff
  christoffel := by
    intro u w
    simpa [anchorChartChristoffelFieldFamily,
      anchorChartChristoffelFieldOperatorFamily] using
      (hGamma.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × E ↦ u)
          (k₀, extChartAt I x x))).clm_apply
        (continuousAt_const : ContinuousAt (fun _ : K × E ↦ w)
          (k₀, extChartAt I x x))
  ricciEntry :=
    anchorChartRicciEntryFamily_continuousAt_of_christoffelJet hGamma hDGamma
  ricciSpatialFDeriv := hRicciSpatialFDeriv

omit [T2Space M] in
/-- Package the Ricci chart jet from a blended-metric first jet and an
operator-valued Christoffel second jet. No coordinate Ricci regularity is an
independent input. -/
theorem metricFamilyRicciJetChartContinuousAt_of_christoffelSecondJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (hDG : ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
      (k₀, extChartAt I x x))
    (hGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldOperatorFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hDGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hD2Gamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSecondSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x)) :
    MetricFamilyRicciJetChartContinuousAt g k₀ x where
  inverseCoeff :=
    anchorChartInverseMetricCoeffFamily_continuousAt_of_blendedMetric hG
  christoffel :=
    anchorChartChristoffelFieldFamily_continuousAt_of_blendedMetric hG hDG
  ricciEntry :=
    anchorChartRicciEntryFamily_continuousAt_of_christoffelJet hGamma hDGamma
  ricciSpatialFDeriv :=
    anchorChartRicciEntrySpatialFDerivFamily_continuousAt_of_christoffelSecondJet
      hGamma hDGamma hD2Gamma

omit [T2Space M] in
/-- A blended-metric first jet supplies the Christoffel value itself, so only
its first two spatial derivatives remain as separate family inputs. -/
theorem metricFamilyRicciJetChartContinuousAt_of_blendedMetric_and_christoffelSecondJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (hDG : ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
      (k₀, extChartAt I x x))
    (hDGamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x))
    (hD2Gamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSecondSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x)) :
    MetricFamilyRicciJetChartContinuousAt g k₀ x := by
  exact metricFamilyRicciJetChartContinuousAt_of_christoffelSecondJet
    hG hDG
    (anchorChartChristoffelFieldOperatorFamily_continuousAt_of_blendedMetric
      hG hDG)
    hDGamma hD2Gamma

omit [T2Space M] in
/-- The second blended-metric spatial jet supplies the first Christoffel jet,
leaving only the second Christoffel jet as a separate family input. -/
theorem metricFamilyRicciJetChartContinuousAt_of_metricSecondJet_and_christoffelSecondJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (hDG : ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
      (k₀, extChartAt I x x))
    (hD2G : ∀ a : E, ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ
          (fun z ↦ fderiv ℝ
            (anchorBlendedMetricFamily g x p.1) z a) p.2)
      (k₀, extChartAt I x x))
    (hD2Gamma : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldSecondSpatialFDerivFamily g x p.1 p.2)
      (k₀, extChartAt I x x)) :
    MetricFamilyRicciJetChartContinuousAt g k₀ x := by
  exact metricFamilyRicciJetChartContinuousAt_of_blendedMetric_and_christoffelSecondJet
    hG hDG
    (anchorChartChristoffelFieldSpatialFDerivFamily_continuousAt_of_metricJets
      hG hDG hD2G)
    hD2Gamma

omit [T2Space M] in
/-- The lower-order chart data constructs every continuous coordinate
covariant-Ricci entry. -/
theorem anchorChartCovRicciEntryFamily_continuousAt_of_ricciJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyRicciJetChartContinuousAt g k₀ x)
    (a i j : E) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartCovRicciEntryFamily g x p.1 p.2 a i j)
      (k₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  let q : E := extChartAt I x x
  have hDMap : ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j)
      (k₀, q) := by
    simpa [q] using h.ricciSpatialFDeriv i j
  have hD : ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j a)
      (k₀, q) :=
    hDMap.clm_apply continuousAt_const
  have hGammaIA : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 i a)
      (k₀, q) := by
    simpa [q] using h.christoffel i a
  have hGammaJA : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 j a)
      (k₀, q) := by
    simpa [q] using h.christoffel j a
  have hFirstCorrection : ContinuousAt
      (fun p : K × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFamily g x p.1 p.2 i a) *
          anchorChartRicciEntryFamily g x p.1 p.2 (b r) j)
      (k₀, q) := by
    apply continuousAt_finset_sum_ricci_jet Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : K × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFamily g x p.1 p.2 i a))
        (k₀, q) :=
      continuousAt_const.clm_apply hGammaIA
    have hRic : ContinuousAt
        (fun p : K × E ↦
          anchorChartRicciEntryFamily g x p.1 p.2 (b r) j)
        (k₀, q) := by
      simpa [q] using h.ricciEntry (b r) j
    exact hcoord.mul hRic
  have hSecondCorrection : ContinuousAt
      (fun p : K × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFamily g x p.1 p.2 j a) *
          anchorChartRicciEntryFamily g x p.1 p.2 i (b r))
      (k₀, q) := by
    apply continuousAt_finset_sum_ricci_jet Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : K × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFamily g x p.1 p.2 j a))
        (k₀, q) :=
      continuousAt_const.clm_apply hGammaJA
    have hRic : ContinuousAt
        (fun p : K × E ↦
          anchorChartRicciEntryFamily g x p.1 p.2 i (b r))
        (k₀, q) := by
      simpa [q] using h.ricciEntry i (b r)
    exact hcoord.mul hRic
  unfold anchorChartCovRicciEntryFamily anchorChartCovRicciEntryFlow
  dsimp only
  simpa [anchorChartRicciEntrySpatialFDerivFamily,
    anchorChartChristoffelFieldFamily, anchorChartRicciEntryFamily, q, b] using
    (hD.sub hFirstCorrection).sub hSecondCorrection

omit [T2Space M] in
/-- The Ricci-jet chart data supplies the chart interface used by the
coordinate norm contraction. -/
theorem metricFamilyCovRicciChartContinuousAt_of_ricciJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyRicciJetChartContinuousAt g k₀ x) :
    MetricFamilyCovRicciChartContinuousAt g k₀ x where
  inverseCoeff := h.inverseCoeff
  covRicciEntry :=
    anchorChartCovRicciEntryFamily_continuousAt_of_ricciJet h

/-- Ricci-jet chart data at every point gives global joint continuity of the
intrinsic squared covariant Ricci norm. -/
theorem continuous_covRicciNormSqAt_joint_of_ricciJetChartContinuous
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M}
    (h : ∀ k : K, ∀ x : M,
      MetricFamilyRicciJetChartContinuousAt g k x) :
    Continuous (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) :=
  continuous_covRicciNormSqAt_joint_of_chartContinuous
    (fun k x ↦ metricFamilyCovRicciChartContinuousAt_of_ricciJet (h k x))

end Poincare
