import Poincare.Global.CartanCanonicalRootedEndpointAssembly

/-!
# Schedule-free terminal short paths

The rooted endpoint assembly first obtained a short terminal path from the
last datum of a strict-factor schedule.  The actual radial construction does
not depend on that schedule: it only needs a small vector `v`, an endpoint
identity `z = expAt g y v`, and the local constant-speed length formula.

This file exposes that schedule-free core and then uses the fixed-anchor
exponential local homeomorphism to pull it back to an ordinary metric
neighborhood of `y`.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology ENNReal

namespace Poincare
namespace CartanTerminalShortPathScheduleFree

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanCanonicalRootedEndpointAssembly
open CartanAtlasRootedPathSkeleton

omit [T2Space M] in
/--
The radial-path construction only needs an explicit local-exponential
endpoint and the exact anchor-metric length bound.  No rooted realization or
strict-factor schedule occurs in the statement.
-/
theorem exists_terminalShortPathCertificate_of_eq_expAt_of_norm_and_metric_lt
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M) {mesh : ℝ} :
    ∃ δ > (0 : ℝ), ∀ {z : M} {v : E}, ‖v‖ < δ →
      z = GeodesicTransport.expAt g y v →
      Real.sqrt
          (GeodesicTransport.chartGeodesicMetric g y
            (extChartAt I y y) v v) < mesh →
        Nonempty (TerminalShortPathCertificate g y z mesh) := by
  rcases
      GeodesicTransport.expAt_pathELength_eq_chartGeodesicMetric_sqrt
        (g := g) (x₀ := y) with
    ⟨τ, hτ, δ₀, hδ₀, hpath⟩
  let δ : ℝ := τ * δ₀
  have hδ : 0 < δ := mul_pos hτ hδ₀
  refine ⟨δ, hδ, ?_⟩
  intro z v hv hzexp hmetric
  let v₀ : E := τ⁻¹ • v
  have hv₀ : ‖v₀‖ < δ₀ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
    calc
      τ⁻¹ * ‖v‖ < τ⁻¹ * (τ * δ₀) := by
        exact mul_lt_mul_of_pos_left hv (inv_pos.mpr hτ)
      _ = δ₀ := by field_simp [ne_of_gt hτ]
  have hτmem : τ ∈ Set.Icc (0 : ℝ) τ := ⟨hτ.le, le_rfl⟩
  rcases hpath v₀ hv₀ τ hτmem with
    ⟨c, hc0, hcτ, hcSmooth, hcLength⟩
  have harg : τ • v₀ = v := by
    dsimp only [v₀]
    rw [smul_smul]
    have hcoeff : τ * τ⁻¹ = 1 := by field_simp [ne_of_gt hτ]
    rw [hcoeff, one_smul]
  let scale : ℝ → ℝ := fun t ↦ τ * t
  let curve : ℝ → M := c ∘ scale
  have hscaleSmooth :
      ContMDiffOn (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) 1 scale (Set.Icc (0 : ℝ) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_const.mul contDiff_id).contDiffOn
  have hscaleMaps :
      MapsTo scale (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) τ) := by
    intro t ht
    constructor
    · exact mul_nonneg hτ.le ht.1
    · exact mul_le_of_le_one_right hτ.le ht.2
  have hcurveSmooth :
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 curve
        (Set.Icc (0 : ℝ) 1) := by
    exact hcSmooth.comp hscaleSmooth hscaleMaps
  have hcurveZero : curve 0 = y := by
    simpa only [curve, scale, Function.comp_apply, mul_zero] using hc0
  have hcurveOne : curve 1 = z := by
    simpa only [curve, scale, Function.comp_apply, mul_one, harg, hzexp] using hcτ
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    g.toRiemannianBundle
  have hscaleMono : MonotoneOn scale (Set.Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_left hab hτ.le
  have hscaleDiff : DifferentiableOn ℝ scale (Set.Icc (0 : ℝ) 1) := by
    exact ((differentiable_const τ).mul differentiable_id).differentiableOn
  have hcMDiff : MDifferentiableOn (modelWithCornersSelf ℝ ℝ) I c
      (Set.Icc (scale 0) (scale 1)) := by
    simpa only [scale, mul_zero, mul_one] using
      hcSmooth.mdifferentiableOn one_ne_zero
  have hcurveLength :
      Manifold.pathELength I curve 0 1 =
        Manifold.pathELength I c 0 τ := by
    simpa only [curve, scale, mul_zero, mul_one] using
      Manifold.pathELength_comp_of_monotoneOn
        (a := (0 : ℝ)) (b := 1) (f := scale) (γ := c)
        zero_le_one hscaleMono hscaleDiff hcMDiff
  have hmetricSmul :
      GeodesicTransport.chartGeodesicMetric g y (extChartAt I y y) v₀ v₀ =
        τ⁻¹ * τ⁻¹ *
          GeodesicTransport.chartGeodesicMetric g y
            (extChartAt I y y) v v := by
    simp [v₀, mul_assoc]
  have hlengthScale :
      τ * Real.sqrt
          (GeodesicTransport.chartGeodesicMetric g y
            (extChartAt I y y) v₀ v₀) =
        Real.sqrt
          (GeodesicTransport.chartGeodesicMetric g y
            (extChartAt I y y) v v) := by
    rw [hmetricSmul]
    have hτinv_nonneg : 0 ≤ τ⁻¹ := (inv_pos.mpr hτ).le
    rw [Real.sqrt_mul (mul_nonneg hτinv_nonneg hτinv_nonneg),
      Real.sqrt_mul_self hτinv_nonneg]
    field_simp [ne_of_gt hτ]
  have hmesh : 0 < mesh := by
    exact (Real.sqrt_nonneg _).trans_lt hmetric
  refine ⟨?_⟩
  refine
    { curve := curve
      curve_zero := hcurveZero
      curve_one := hcurveOne
      curve_contMDiffOn := hcurveSmooth
      curve_pathELength_lt := ?_ }
  rw [hcurveLength, hcLength, hlengthScale]
  exact (ENNReal.ofReal_lt_ofReal_iff hmesh).2 hmetric

/--
For a positive mesh, one sufficiently small explicit exponential vector
automatically gives the schedule-free terminal certificate.
-/
theorem exists_terminalShortPathCertificate_of_eq_expAt_of_norm_lt
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ δ > (0 : ℝ), ∀ {z : M} {v : E}, ‖v‖ < δ →
      z = GeodesicTransport.expAt g y v →
        Nonempty (TerminalShortPathCertificate g y z mesh) := by
  rcases
      exists_terminalShortPathCertificate_of_eq_expAt_of_norm_and_metric_lt
        g y with
    ⟨δ₀, hδ₀, hradial⟩
  rcases
      CartanCanonicalRootedEndpointAssembly.CanonicalRootedRealizationPackage.exists_anchorChartGeodesicMetric_euclideanUpperBound
        g y with
    ⟨C, hC, hmetric⟩
  let δ : ℝ := min δ₀ (mesh / C)
  have hδ : 0 < δ := lt_min hδ₀ (div_pos hmesh hC)
  refine ⟨δ, hδ, ?_⟩
  intro z v hv hzexp
  apply hradial (hv.trans_le (min_le_left δ₀ (mesh / C))) hzexp
  have hvCutoff : ‖v‖ < mesh / C :=
    hv.trans_le (min_le_right δ₀ (mesh / C))
  have hCnorm : C * ‖v‖ < mesh := by
    calc
      C * ‖v‖ < C * (mesh / C) :=
        mul_lt_mul_of_pos_left hvCutoff hC
      _ = mesh := by field_simp [ne_of_gt hC]
  calc
    Real.sqrt
        (GeodesicTransport.chartGeodesicMetric g y
          (extChartAt I y y) v v)
        ≤ Real.sqrt ((C * ‖v‖) ^ 2) :=
      Real.sqrt_le_sqrt (hmetric v)
    _ = C * ‖v‖ :=
      Real.sqrt_sq (mul_nonneg hC.le (norm_nonneg _))
    _ < mesh := hCnorm

/--
Every positive mesh admits a fixed-anchor metric neighborhood on which a
schedule-free terminal short path exists.  The proof shrinks simultaneously
into the anchor chart source, the target of the exponential local
homeomorphism, the radial-path vector cutoff, and the chart-source cutoff for
the resulting exponential endpoint.
-/
theorem exists_terminalShortPathCertificate_of_dist_lt
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ε > (0 : ℝ), ∀ {z : M}, dist z y < ε →
      Nonempty (TerminalShortPathCertificate g y z mesh) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_terminalShortPathCertificate_of_eq_expAt_of_norm_lt
        g y hmesh with
    ⟨δ₀, hδ₀, hradial⟩
  rcases
      GeodesicTransport.expAt_mem_source_of_norm_lt (g := g) (x₀ := y) with
    ⟨ρ, hρ, hexpSource⟩
  let δ : ℝ := min δ₀ ρ
  have hδ : 0 < δ := lt_min hδ₀ hρ
  let e :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) y
  let normalCoordinate : M → E := fun z ↦
    e.symm ((chartAt E y) z)
  have htarget : (chartAt E y) y ∈ e.target := by
    simpa [e, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) y
  have hchart : ContinuousAt (fun z : M ↦ (chartAt E y) z) y := by
    simpa [extChartAt_coe] using
      continuousAt_extChartAt («I» := I) y
  have hnormal : ContinuousAt normalCoordinate y := by
    exact (e.continuousAt_symm htarget).comp hchart
  have hnormalZero : normalCoordinate y = (0 : E) := by
    simpa [normalCoordinate, e] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g y
  have hnormalNhds :
      normalCoordinate ⁻¹' Metric.ball (0 : E) δ ∈ 𝓝 y := by
    apply hnormal.preimage_mem_nhds
    rw [hnormalZero]
    exact Metric.ball_mem_nhds (0 : E) hδ
  have htargetNhds :
      (fun z : M ↦ (chartAt E y) z) ⁻¹' e.target ∈ 𝓝 y := by
    exact hchart.preimage_mem_nhds (e.open_target.mem_nhds htarget)
  have hcontrolledNhds :
      ((chartAt E y).source ∩
          (fun z : M ↦ (chartAt E y) z) ⁻¹' e.target) ∩
        normalCoordinate ⁻¹' Metric.ball (0 : E) δ ∈ 𝓝 y := by
    exact inter_mem
      (inter_mem (chart_source_mem_nhds E y) htargetNhds) hnormalNhds
  rcases Metric.mem_nhds_iff.mp hcontrolledNhds with
    ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro z hdist
  have hzBall : z ∈ Metric.ball y ε := by
    simpa [Metric.mem_ball] using hdist
  have hzControlled := hball hzBall
  have hzChartSource : z ∈ (chartAt E y).source := hzControlled.1.1
  have hzTarget : (chartAt E y) z ∈ e.target := hzControlled.1.2
  have hvBall : normalCoordinate z ∈ Metric.ball (0 : E) δ :=
    hzControlled.2
  let v : E := normalCoordinate z
  have hv : ‖v‖ < δ := by
    simpa [v, Metric.mem_ball, dist_eq_norm] using hvBall
  have hvρ : ‖v‖ < ρ := hv.trans_le (min_le_right δ₀ ρ)
  have hexpvSource :
      GeodesicTransport.expAt g y v ∈ (extChartAt I y).source :=
    hexpSource v hvρ
  have hcoordinate :
      extChartAt I y z =
        extChartAt I y (GeodesicTransport.expAt g y v) := by
    have hright :
        e (e.symm ((chartAt E y) z)) = (chartAt E y) z :=
      e.right_inv hzTarget
    simpa [e, v, normalCoordinate,
      GeodesicTransport.expAtChartOpenPartialHomeomorph_coe,
      extChartAt_coe] using hright.symm
  have hzSource : z ∈ (extChartAt I y).source := by
    simpa [extChartAt_source] using hzChartSource
  have hzexp : z = GeodesicTransport.expAt g y v :=
    (extChartAt I y).injOn hzSource hexpvSource hcoordinate
  exact hradial (hv.trans_le (min_le_left δ₀ ρ)) hzexp

/-- The chosen schedule-free terminal distance cutoff at one fixed anchor. -/
def scheduleFreeTerminalDistanceRadius
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose
    (exists_terminalShortPathCertificate_of_dist_lt g y hmesh)

/-- The chosen schedule-free terminal distance cutoff is positive. -/
theorem scheduleFreeTerminalDistanceRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    0 < scheduleFreeTerminalDistanceRadius g y hmesh := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_terminalShortPathCertificate_of_dist_lt g y hmesh)).1

/--
Distance below the chosen fixed-anchor cutoff gives a terminal short path
without any rooted realization or strict-factor schedule.
-/
theorem terminalShortPathCertificate_of_dist_lt_scheduleFreeTerminalDistanceRadius
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) {z : M}
    (hdist :
      letI : MetricSpace M := g.toMetricSpace
      dist z y < scheduleFreeTerminalDistanceRadius g y hmesh) :
    Nonempty (TerminalShortPathCertificate g y z mesh) := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_terminalShortPathCertificate_of_dist_lt g y hmesh)).2 hdist

/--
The terminal Cartan source shrunk by the schedule-free fixed-anchor metric
cutoff.  The package is used only to name the reached terminal germ; the
short-path construction itself is independent of every overlap schedule.
-/
def scheduleFreeTerminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) : Set M := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (package.endpoint.terminalState y).germ.source ∩
      Metric.ball y (scheduleFreeTerminalDistanceRadius g y hmesh)

/-- Every schedule-free terminal restricted domain is open. -/
theorem isOpen_scheduleFreeTerminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    IsOpen (scheduleFreeTerminalRestrictedDomain package hmesh y) := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (package.endpoint.terminalState y).germ.open_source.inter
      Metric.isOpen_ball

/-- The terminal anchor belongs to its schedule-free restricted domain. -/
theorem anchor_mem_scheduleFreeTerminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    y ∈ scheduleFreeTerminalRestrictedDomain package hmesh y := by
  letI : MetricSpace M := g.toMetricSpace
  constructor
  · have hmem :
        (package.endpoint.terminalState y).anchor ∈
          (package.endpoint.terminalState y).germ.source := by
      exact
        CartanMap.anchor_mem_source g
          (package.endpoint.terminalState y).anchor
          (package.endpoint.terminalState y).target
          (package.endpoint.terminalState y).alignment
    simpa only [package.endpoint_terminalState_anchor y] using hmem
  · exact Metric.mem_ball_self
      (scheduleFreeTerminalDistanceRadius_pos g y hmesh)

/-- Shrinking stays inside the full reached terminal Cartan source. -/
theorem scheduleFreeTerminalRestrictedDomain_subset_source
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    scheduleFreeTerminalRestrictedDomain package hmesh y ⊆
      (package.endpoint.terminalState y).germ.source :=
  inter_subset_left

/--
Membership in the schedule-free restricted domain produces the proof-bearing
terminal short path with no strict-factor schedule argument.
-/
theorem terminalShortPathCertificate_of_mem_scheduleFreeTerminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) {y z : M}
    (hz : z ∈ scheduleFreeTerminalRestrictedDomain package hmesh y) :
    Nonempty (TerminalShortPathCertificate g y z mesh) := by
  apply
    terminalShortPathCertificate_of_dist_lt_scheduleFreeTerminalDistanceRadius
      g y hmesh
  simpa only [Metric.mem_ball] using hz.2

end CartanTerminalShortPathScheduleFree
end Poincare
