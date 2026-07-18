import Poincare.Global.MetricFlowJointScalarTraceBridge
import Poincare.Global.ChartCurvatureBridgeZoneClose

/-!
# Scalar trace in a cutoff-one anchor chart

This module extends the anchor-point scalar trace bridge across the honest
cutoff-one part of the same preferred chart.  The first step identifies the
coordinate curvature with the conjugated intrinsic curvature endomorphism at
the inverse-chart point.  The finite Ricci and inverse-metric contractions can
then be compared with their intrinsic counterparts without changing bases by
fiat.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- On the cutoff-one part of an honest preferred chart, the chart curvature
is the inverse-chart conjugate of the intrinsic curvature endomorphism. -/
theorem anchorChartCurvatureFlow_eq_chartRicciCurvatureEndAt_apply_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in 𝓝 z,
      GeodesicTransport.cutoff (n := n) x z' = 1)
    (u v w : E) :
    anchorChartCurvatureFlow gt x t z u v w =
      chartRicciCurvatureEndAt (gt t) x z hz v w u := by
  let y : M := (extChartAt I x).symm z
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  have hy : y ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hz
  have hzchart : extChartAt I x y = z := by
    simpa [y] using (extChartAt I x).right_inv hz
  have he : (e : E →L[ℝ] E) =
      ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z := by
    exact chartInverseTangentEquiv_toContinuousLinearMap x z hz
  have hzone :=
    ChartCurvatureBridgeZoneClose.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp_zone
      (g := gt t) (x₀ := x) hz hχone u v w
  have htransport :
      CovariantDerivative.chartTransportedLeviCivitaSection x
          (CovariantDerivative.curvatureOp (gt t).leviCivita
            (extend E (x := y) (e u)) (extend E (x := y) (e v))
            (extend E (x := y) (e w))) z =
        e.symm
          (ricciCurvatureEndAt (gt t) y (e v) (e w) (e u)) := by
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        (x₀ := x)
        (σ := CovariantDerivative.curvatureOp (gt t).leviCivita
          (extend E (x := y) (e u)) (extend E (x := y) (e v))
          (extend E (x := y) (e w))) hy
    rw [hzchart] at happly
    rw [happly]
    apply e.injective
    rw [e.apply_symm_apply]
    change (e : E →L[ℝ] E)
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) y)
          (CovariantDerivative.curvatureOp (gt t).leviCivita
            (extend E (x := y) (e u)) (extend E (x := y) (e v))
            (extend E (x := y) (e w)) y)) = _
    rw [he]
    have hround :=
      CovariantDerivative.chartTransportedLeviCivita_direction_roundtrip
        (x₀ := x) hy
        (CovariantDerivative.curvatureOp (gt t).leviCivita
          (extend E (x := y) (e u)) (extend E (x := y) (e v))
          (extend E (x := y) (e w)) y)
    have hround' :
        ChartCurvatureBridgeZone.chartInverseTangent (n := n) x
            (extChartAt I x y)
            ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) y)
              (CovariantDerivative.curvatureOp (gt t).leviCivita
                (extend E (x := y) (e u)) (extend E (x := y) (e v))
                (extend E (x := y) (e w)) y)) =
          CovariantDerivative.curvatureOp (gt t).leviCivita
            (extend E (x := y) (e u)) (extend E (x := y) (e v))
            (extend E (x := y) (e w)) y := by
      simpa [ChartCurvatureBridgeZone.chartInverseTangent] using hround
    have htensor :=
      CovariantDerivative.curvatureTensorAt_apply
        (cov := (gt t).leviCivita)
        (hreg := CovariantDerivative.derivRegularAt_extend
          (x := y) (gt t).leviCivita (e w))
        (mdifferentiableAt_extend (x := y) (σ₀ := e u) ..)
        (mdifferentiableAt_extend (x := y) (σ₀ := e v) ..)
    rw [← hzchart]
    calc
      ChartCurvatureBridgeZone.chartInverseTangent (n := n) x
            (extChartAt I x y)
            ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) y)
              (CovariantDerivative.curvatureOp (gt t).leviCivita
                (extend E (x := y) (e u)) (extend E (x := y) (e v))
                (extend E (x := y) (e w)) y)) =
          CovariantDerivative.curvatureOp (gt t).leviCivita
            (extend E (x := y) (e u)) (extend E (x := y) (e v))
            (extend E (x := y) (e w)) y := hround'
      _ = ricciCurvatureEndAt (gt t) y (e v) (e w) (e u) := by
        simpa [y, ricciCurvatureEndAt,
          CovariantDerivative.curvatureEndAt_apply] using htensor.symm
  rw [show anchorChartCurvatureFlow gt x t z u v w =
      chartCurvatureOf (GeodesicTransport.chartChristoffelField (gt t) x)
        z u v w by rfl]
  rw [hzone]
  rw [show ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z =
      (e : E →L[ℝ] E) by exact he.symm]
  simpa [chartRicciCurvatureEndAt, pullbackCurvatureEnd, e, y] using
    htransport

/-- Tracing the cutoff-one chart curvature in the fixed model basis gives the
honest chart pullback of the intrinsic Ricci tensor. -/
theorem anchorChartRicciEntryFlow_eq_deTurckChartRicciBilin_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in 𝓝 z,
      GeodesicTransport.cutoff (n := n) x z' = 1)
    (v w : E) :
    anchorChartRicciEntryFlow gt x t z v w =
      deTurckChartRicciBilin gt x t z v w := by
  classical
  let b := Module.finBasis ℝ E
  calc
    anchorChartRicciEntryFlow gt x t z v w =
        ∑ i, b.coord i
          (chartRicciCurvatureEndAt (gt t) x z hz v w (b i)) := by
      unfold anchorChartRicciEntryFlow
      dsimp only
      apply Finset.sum_congr rfl
      intro i _hi
      rw [anchorChartCurvatureFlow_eq_chartRicciCurvatureEndAt_apply_zone
        gt x t hz hχone]
      rfl
    _ = LinearMap.trace ℝ E
        (chartRicciCurvatureEndAt (gt t) x z hz v w) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
        Module.Basis.coord_apply]
    _ = deTurckChartRicciBilin gt x t z v w :=
      (deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
        gt x t z hz v w).symm

omit [T2Space M] in
/-- The chart tangent basis is the fixed model basis transported through the
same inverse-chart equivalence used by the curvature pullback. -/
theorem chartTangentBasisAt_eq_finBasis_map_chartInverseTangentEquiv
    (x : M) {z : E} (hz : z ∈ (extChartAt I x).target) :
    chartTangentBasisAt (n := n) (M := M) x hz =
      (Module.finBasis ℝ E).map
        (chartInverseTangentEquiv x z hz).toLinearEquiv := by
  rfl

omit [T2Space M] in
/-- Coordinates in the chart tangent basis are the fixed model coordinates
before applying the inverse-chart tangent equivalence. -/
theorem chartTangentBasisAt_coord_chartInverseTangentEquiv
    (x : M) {z : E} (hz : z ∈ (extChartAt I x).target)
    (i : Fin (Module.finrank ℝ E)) (q : E) :
    (chartTangentBasisAt (n := n) (M := M) x hz).coord i
        (chartInverseTangentEquiv x z hz q) =
      (Module.finBasis ℝ E).coord i q := by
  rw [chartTangentBasisAt_eq_finBasis_map_chartInverseTangentEquiv x hz]
  rw [Module.Basis.coord_apply, Module.Basis.coord_apply]
  let e := chartInverseTangentEquiv x z hz
  change ((Module.finBasis ℝ E).repr (e.symm (e q))) i = _
  rw [e.symm_apply_apply]

/-- At a cutoff-one chart point, raising a fixed model coordinate covector
with the inverse blended metric and then applying the inverse-chart tangent
map gives the intrinsically raised chart-coframe vector. -/
theorem chartInverseTangentEquiv_anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχ : GeodesicTransport.cutoff (n := n) x z = 1)
    (i : Fin (Module.finrank ℝ E)) :
    let e := chartInverseTangentEquiv x z hz
    let B := chartTangentBasisAt (n := n) (M := M) x hz
    e ((anchorBlendedMetricFlow gt x t z).inverse
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))) =
      metricDualVectorAt (gt t) ((extChartAt I x).symm z) (B.coord i) := by
  classical
  let g := gt t
  let y : M := (extChartAt I x).symm z
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  let b := Module.finBasis ℝ E
  let B := chartTangentBasisAt (n := n) (M := M) x hz
  let G := anchorBlendedMetricFlow gt x t z
  let phi : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  let raised : E := G.inverse phi
  let sharp : E := metricDualVectorAt g y (B.coord i)
  have he : (e : E →L[ℝ] E) =
      ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z :=
    chartInverseTangentEquiv_toContinuousLinearMap x z hz
  have hGmetric : ∀ a c : E, G a c = g.inner y (e a) (e c) := by
    intro a c
    have hblend :=
      CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
        (GeodesicTransport.cutoff (n := n) x)
        (GeodesicTransport.backgroundMetric (n := n)) g.inner x hχ
    change anchorBlendedMetricFlow gt x t z a c = _
    rw [show anchorBlendedMetricFlow gt x t z =
        CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := n) x)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x z by rfl]
    rw [hblend]
    change CovariantDerivative.chartMetric g.inner x z a c = _
    rw [CovariantDerivative.chartMetric_apply]
    change g.inner y
        (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z a)
        (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z c) = _
    rw [← he]
    rfl
  have hInv : G.IsInvertible := by
    simpa [G] using anchorBlendedMetricFlow_isInvertible gt x t z
  have hLower : ∀ c : E, G raised c = phi c := by
    intro c
    have hphi : G (G.inverse phi) = phi :=
      (hInv.inverse_apply_eq.mp rfl).symm
    exact congrArg (fun psi : E →L[ℝ] ℝ ↦ psi c) hphi
  have hcoord : ∀ q : E, B.coord i (e q) = b.coord i q := by
    intro q
    simpa [B, b, e] using
      chartTangentBasisAt_coord_chartInverseTangentEquiv x hz i q
  change e raised = sharp
  refine sub_eq_zero.mp
    (LeviCivitaExistence.metric_nondegenerate g y (e raised - sharp) ?_)
  intro c
  calc
    g.inner y (e raised - sharp) c =
        g.inner y (e raised) c - g.inner y sharp c := by
      exact congrArg (fun psi : E →L[ℝ] ℝ ↦ psi c)
        (map_sub (g.inner y) (e raised) sharp)
    _ = G raised (e.symm c) - g.inner y sharp c := by
      rw [hGmetric]
      simp
    _ = phi (e.symm c) - g.inner y sharp c := by rw [hLower]
    _ = B.coord i c - g.inner y sharp c := by
      change b.coord i (e.symm c) - _ = _
      rw [← hcoord (e.symm c), e.apply_symm_apply]
    _ = 0 := by
      rw [show g.inner y sharp c = B.coord i c by
        simpa [sharp] using metricDualVectorAt_inner_apply g y (B.coord i) c]
      simp

/-- Throughout the cutoff-one part of an honest anchor chart, the finite
coordinate scalar trace is exactly intrinsic scalar curvature at the
inverse-chart point. -/
theorem anchorChartScalarTraceFlow_eq_scalarAt_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in 𝓝 z,
      GeodesicTransport.cutoff (n := n) x z' = 1) :
    anchorChartScalarTraceFlow gt x t z =
      (gt t).scalarAt ((extChartAt I x).symm z) := by
  classical
  let g := gt t
  let y : M := (extChartAt I x).symm z
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  let b := Module.finBasis ℝ E
  let B := chartTangentBasisAt (n := n) (M := M) x hz
  let G := anchorBlendedMetricFlow gt x t z
  let phi : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  let raised : Fin (Module.finrank ℝ E) → E := fun i ↦ G.inverse (phi i)
  have hχ : GeodesicTransport.cutoff (n := n) x z = 1 :=
    hχone.self_of_nhds
  have he : (e : E →L[ℝ] E) =
      ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z :=
    chartInverseTangentEquiv_toContinuousLinearMap x z hz
  have hRic : ∀ v w : E,
      anchorChartRicciEntryFlow gt x t z v w =
        g.ricciAt y (e v) (e w) := by
    intro v w
    rw [anchorChartRicciEntryFlow_eq_deTurckChartRicciBilin_zone
      gt x t hz hχone]
    unfold deTurckChartRicciBilin
    rw [CovariantDerivative.chartMetric_apply]
    change ricciContinuousBilinAt g y
        (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z v)
        (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z w) = _
    rw [← he, ricciContinuousBilinAt_apply]
    rfl
  have hBasis : ∀ i, B i = e (b i) := by
    intro i
    rw [show B = b.map e.toLinearEquiv by
      simpa [B, b, e] using
        chartTangentBasisAt_eq_finBasis_map_chartInverseTangentEquiv x hz]
    rfl
  have hRaised : ∀ i,
      e (raised i) = metricDualVectorAt g y (B.coord i) := by
    intro i
    simpa [raised, G, phi, g, y, e, B, b] using
      chartInverseTangentEquiv_anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt_zone
        gt x t hz hχ i
  have hsum : ∀ i,
      (∑ k, b.coord k (raised i) *
          g.ricciAt y (e (b i)) (e (b k))) =
        g.ricciAt y (e (b i)) (e (raised i)) := by
    intro i
    let R : E →L[ℝ] ℝ := ricciContinuousBilinAt g y (e (b i))
    have hrepr : ∑ k, b.coord k (raised i) • b k = raised i :=
      b.sum_repr (raised i)
    have herepr : ∑ k, b.coord k (raised i) • e (b k) = e (raised i) := by
      calc
        (∑ k, b.coord k (raised i) • e (b k)) =
            e (∑ k, b.coord k (raised i) • b k) := by
          symm
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [map_smul]
        _ = e (raised i) := by rw [hrepr]
    calc
      (∑ k, b.coord k (raised i) *
          g.ricciAt y (e (b i)) (e (b k))) =
          ∑ k, R (b.coord k (raised i) • e (b k)) := by
        apply Finset.sum_congr rfl
        intro k _hk
        calc
          b.coord k (raised i) *
              g.ricciAt y (e (b i)) (e (b k)) =
              b.coord k (raised i) * R (e (b k)) := by
            rw [show R (e (b k)) =
                g.ricciAt y (e (b i)) (e (b k)) by
              exact ricciContinuousBilinAt_apply g y (e (b i)) (e (b k))]
          _ = b.coord k (raised i) • R (e (b k)) := rfl
          _ = R (b.coord k (raised i) • e (b k)) := by rw [map_smul]
      _ = R (∑ k, b.coord k (raised i) • e (b k)) := by rw [map_sum]
      _ = R (e (raised i)) := by rw [herepr]
      _ = g.ricciAt y (e (b i)) (e (raised i)) := by
        exact ricciContinuousBilinAt_apply g y (e (b i)) (e (raised i))
  calc
    anchorChartScalarTraceFlow gt x t z =
        ∑ i, ∑ k, b.coord k (raised i) *
          g.ricciAt y (e (b i)) (e (b k)) := by
      unfold anchorChartScalarTraceFlow anchorChartInverseMetricCoeffFlow
      dsimp only
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro k _hk
      rw [hRic]
      rfl
    _ = ∑ i, g.ricciAt y (e (b i)) (e (raised i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hsum i
    _ = ∑ i, g.ricciAt y (B i)
          (metricDualVectorAt g y (B.coord i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hBasis, hRaised]
    _ = metricTraceInBasisAt g y
        (CovariantDerivative.ricciDualAt g.leviCivita y) B := by
      rfl
    _ = traceMetricVariationAt g (ricciVariationField g) y := by
      symm
      exact traceMetricVariationAt_eq_metricTraceInBasisAt
        (g := g) (h := ricciVariationField g) (x := y)
        (B := CovariantDerivative.ricciDualAt g.leviCivita y) (b := B)
        (by intro p q; rfl)
    _ = g.scalarAt y := traceMetricVariationAt_ricci g y
    _ = (gt t).scalarAt ((extChartAt I x).symm z) := rfl

/-- Joint `C³` control of the metric entries gives genuine joint space-time
continuity of intrinsic scalar curvature.  The cutoff-one chart identity is
used only on a neighborhood of the anchor, where the preferred chart is an
honest local inverse. -/
theorem continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) (t₀, x) := by
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ nhds (extChartAt I x x) := by
    apply hopen.mem_nhds
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hchart :
      ContinuousAt (fun p : ℝ × M ↦ extChartAt I x p.2) (t₀, x) := by
    exact ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ p.2)
      (g := fun y : M ↦ extChartAt I x y)
      (x := (t₀, x)) (continuousAt_extChartAt x) continuousAt_snd
  have hchartPair :
      ContinuousAt
        (fun p : ℝ × M ↦ (p.1, extChartAt I x p.2)) (t₀, x) :=
    continuousAt_fst.prodMk hchart
  have htrace :=
    anchorChartScalarTraceFlow_continuousAt_of_metricEntries hJoint
  have hchartScalar :
      ContinuousAt
        (fun p : ℝ × M ↦
          anchorChartScalarTraceFlow gt x p.1 (extChartAt I x p.2))
        (t₀, x) := by
    exact ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
      (g := Function.uncurry (anchorChartScalarTraceFlow gt x))
      (x := (t₀, x)) htrace hchartPair
  have hsource :
      ∀ᶠ p : ℝ × M in nhds (t₀, x),
        p.2 ∈ (extChartAt I x).source :=
    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
  have hone :
      ∀ᶠ p : ℝ × M in nhds (t₀, x),
        extChartAt I x p.2 ∈ oneLocus :=
    hchart.eventually hone_mem
  have hEq :
      (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) =ᶠ[nhds (t₀, x)]
        (fun p : ℝ × M ↦
          anchorChartScalarTraceFlow gt x p.1 (extChartAt I x p.2)) := by
    filter_upwards [hsource, hone] with p hpSource hpOne
    have hz : extChartAt I x p.2 ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hpSource
    have hχone :
        ∀ᶠ z' in nhds (extChartAt I x p.2),
          GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    symm
    calc
      anchorChartScalarTraceFlow gt x p.1 (extChartAt I x p.2) =
          (gt p.1).scalarAt
            ((extChartAt I x).symm (extChartAt I x p.2)) :=
        anchorChartScalarTraceFlow_eq_scalarAt_zone gt x p.1 hz hχone
      _ = (gt p.1).scalarAt p.2 := by
        rw [(extChartAt I x).left_inv hpSource]
  exact hchartScalar.congr_of_eventuallyEq hEq

end Poincare
