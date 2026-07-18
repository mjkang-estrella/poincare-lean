import Poincare.Global.CartanCanonicalFamilyTransitionAgreementAssembly
import Poincare.Global.CartanCanonicalRootedRealizationTransfer
import Poincare.Global.CartanCanonicalFamilyProvenanceRootedAssembly
import Poincare.Global.CartanAtlasRootedAdaptiveClosenessTransport
import Poincare.Global.CartanRestrictedOverlapCompatibility
import Poincare.Global.DifferentialSuccessorAdaptiveMeshCoordinates
import Poincare.Global.GeodesicDistance
import Poincare.Global.GeodesicLengthFinal

/-!
# Canonical rooted realizations in the generic endpoint pipeline

The transition-agreement assembly constructs rooted chains for the canonical
target exponential.  `CartanCanonicalRootedRealizationTransfer` identifies the
precise extra step data required to forget that family tag and obtain the
generic differential chains consumed by rooted endpoint transport.

This file joins those boundaries.  It packages one canonical realization with
stepwise `GenericSuccessorComparison` witnesses, preserves the prescribed-mesh
certificate, and feeds the transferred endpoint family into the existing
adaptive-closeness transport theorem.  The final consumer proves pairwise
agreement of the actual Cartan germs.  It does not identify the canonical and
generic target charts globally.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology ENNReal

namespace Poincare
namespace CartanCanonicalRootedEndpointAssembly

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanCanonicalRootedRealizationTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanAtlasRootedPathSkeleton
open CartanAtlasRootedReachableEndpointTransport
open CartanAtlasRootedAdaptiveClosenessTransport
open CartanAtlasRootedAdaptiveClosenessTransport.RootedOverlapStrictFactorSchedule
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorStrictFactorInsertionTransport

/-- The mesh facts retained from the canonical transition-agreement
realization theorem. -/
structure PrescribedMeshCertificate
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (realization :
      SuppliedRootedPathChainRealization canonicalFamily skeleton)
    (mesh : ℝ) : Prop where
  terminalIndex_pos : ∀ x : M, 0 < realization.terminalIndex x
  nodeTime_monotone : ∀ x : M, Monotone (realization.nodeTime x)
  nodeTime_eventually_terminal : ∀ x : M,
    ∀ n ≥ realization.terminalIndex x, realization.nodeTime x n = 1
  edge_dist_lt :
    letI : MetricSpace M := g.toMetricSpace
    ∀ (x : M) (n : ℕ),
      dist
        (skeleton.path x (realization.nodeTime x n))
        (skeleton.path x (realization.nodeTime x (n + 1))) < mesh

/--
The exact analytic residue at the terminal overlap edge: one concrete `C¹`
path from `y` to `z` whose Riemannian length is strictly smaller than the
prescribed mesh.  Unlike a direct distance hypothesis, this certificate keeps
the path whose length must be estimated available to downstream geometry.
-/
structure TerminalShortPathCertificate
    (g : ClosedSmoothRiemannianMetric 3 M) (y z : M) (mesh : ℝ) where
  curve : ℝ → M
  curve_zero : curve 0 = y
  curve_one : curve 1 = z
  curve_contMDiffOn :
    ContMDiffOn 𝓘(ℝ) I 1 curve (Set.Icc (0 : ℝ) 1)
  curve_pathELength_lt :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
      g.toRiemannianBundle
    Manifold.pathELength I curve 0 1 < ENNReal.ofReal mesh

namespace TerminalShortPathCertificate

/-- A genuinely short terminal `C¹` path supplies the missing strict metric
edge bound. -/
theorem dist_lt_mesh
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M} {y z : M} {mesh : ℝ}
    (certificate : TerminalShortPathCertificate g y z mesh) :
    letI : MetricSpace M := g.toMetricSpace
    dist y z < mesh := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel 3)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  have hEd :
      edist y z ≤ Manifold.pathELength I certificate.curve 0 1 :=
    GeodesicTransport.induced_edist_le_pathELength (g := g)
      certificate.curve_contMDiffOn certificate.curve_zero
        certificate.curve_one zero_le_one
  exact edist_lt_ofReal.mp (hEd.trans_lt certificate.curve_pathELength_lt)

end TerminalShortPathCertificate

/-- A canonical rooted realization bundled with the exact stepwise comparison
data needed to reconstruct the legacy generic reachable chains. -/
structure CanonicalRootedRealizationPackage
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g) where
  realization :
    SuppliedRootedPathChainRealization canonicalFamily skeleton
  comparison : RootedRealizationComparison realization

namespace CanonicalRootedRealizationPackage

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {skeleton : RootedCartanPathSkeleton g}

/-- The generic rooted realization carried by the package. -/
def genericRealization
    (package : CanonicalRootedRealizationPackage skeleton) :
    RootedPathChainRealization skeleton :=
  package.comparison.toGenericRootedPathChainRealization

/-- The existing rooted endpoint family obtained from the transferred generic
realization. -/
def endpoint
    (package : CanonicalRootedRealizationPackage skeleton) :
    RootedPathContinuedEndpointFamily g :=
  package.comparison.toGenericEndpointFamily

/-- The transferred endpoint uses exactly the sampled nodes of the canonical
rooted realization. -/
@[simp]
theorem endpoint_nodes_eq_realization_path
    (package : CanonicalRootedRealizationPackage skeleton)
    (x : M) (n : ℕ) :
    package.endpoint.nodes x n =
      skeleton.path x (package.realization.nodeTime x n) :=
  rfl

/-- The endpoint consumer sees genuine terminal states anchored at the chosen
source points.  This is inherited from the existing rooted endpoint theorem,
not added as a cast certificate to the canonical package. -/
theorem endpoint_terminalState_anchor
    (package : CanonicalRootedRealizationPackage skeleton) (x : M) :
    (package.endpoint.terminalState x).anchor = x :=
  package.endpoint.terminalState_anchor x

/-- The anchored state reconstructed from the endpoint target and alignment
is the actual reached generic terminal state. -/
theorem endpoint_anchoredFamilyState_eq_terminalState
    (package : CanonicalRootedRealizationPackage skeleton) (x : M) :
    CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x =
      package.endpoint.terminalState x :=
  package.endpoint.anchoredFamilyState_eq_terminalState x

/-- The source normal vector carried by the last differential-induced step
from the rooted endpoint at `y` to the overlap node `z`. -/
def terminalSourceNormal
    (package : CanonicalRootedRealizationPackage skeleton)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z) : E :=
  (schedule.refinedChain.data
    (schedule.factor schedule.length - 1)).v

/--
The final differential-induced successor datum produces the actual short
terminal path once its source normal lies in one honest local exponential
radius and its anchor-metric norm is below the requested mesh.

The selected radius is independent of `mesh`.  The second premise is the
exact Riemannian length of the radial exponential path, not a metric-distance
or arbitrary-path hypothesis.
-/
theorem exists_uniform_terminalShortPathCertificate_of_terminalSourceNormal
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M) {mesh : ℝ} :
    ∃ δ > (0 : ℝ),
      ∀ {skeleton : RootedCartanPathSkeleton g}
        (package : CanonicalRootedRealizationPackage skeleton)
        {x z : M}
        (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z),
          ‖package.terminalSourceNormal schedule‖ < δ →
            Real.sqrt
                (GeodesicTransport.chartGeodesicMetric g y
                  (extChartAt I y y)
                  (package.terminalSourceNormal schedule)
                  (package.terminalSourceNormal schedule)) < mesh →
              Nonempty (TerminalShortPathCertificate g y z mesh) := by
  rcases
      GeodesicTransport.expAt_pathELength_eq_chartGeodesicMetric_sqrt
        (g := g) (x₀ := y) with
    ⟨τ, hτ, δ₀, hδ₀, hpath⟩
  rcases GeodesicTransport.expAt_mem_source_of_norm_lt (g := g) (x₀ := y) with
    ⟨ρ, hρ, hexpSource⟩
  let δ : ℝ := min (τ * δ₀) ρ
  have hδ : 0 < δ := by
    exact lt_min (mul_pos hτ hδ₀) hρ
  refine ⟨δ, hδ, ?_⟩
  intro skeleton package x z schedule
  intro hv hmetric
  let K : ℕ := schedule.factor schedule.length - 1
  let d := schedule.refinedChain.data K
  let v : E := package.terminalSourceNormal schedule
  have hfactor_le :
      schedule.length ≤ schedule.factor schedule.length :=
    strictFactorIndex_le schedule.factor schedule.length
      schedule.factor_zero schedule.factor_strict schedule.length le_rfl
  have hfactor_pos : 0 < schedule.factor schedule.length :=
    schedule.length_pos.trans_le hfactor_le
  have hnext : schedule.refined (K + 1) = z := by
    have hK : K + 1 = schedule.factor schedule.length := by
      dsimp only [K]
      omega
    rw [hK, schedule.factor_value schedule.length le_rfl,
      schedule.left_terminal_node]
  have hstate : schedule.refinedChain.state K =
      package.endpoint.terminalState y := by
    simpa only [K] using schedule.right_predecessor
  have hanchor : (schedule.refinedChain.state K).anchor = y := by
    rw [hstate]
    exact package.endpoint_terminalState_anchor y
  have hzSource : z ∈ (extChartAt I y).source := by
    simpa only [d, K, hanchor, hnext] using d.source_mem_oldChart
  have hvρ : ‖v‖ < ρ := by
    exact hv.trans_le (min_le_right (τ * δ₀) ρ)
  have hexpvSource :
      GeodesicTransport.expAt g y v ∈ (extChartAt I y).source :=
    hexpSource v hvρ
  have hcoordinate :
      extChartAt I y z =
        extChartAt I y (GeodesicTransport.expAt g y v) := by
    simpa only [d, K, v, terminalSourceNormal, hanchor, hnext,
      GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
        d.source_coordinate
  have hzexp : z = GeodesicTransport.expAt g y v :=
    (extChartAt I y).injOn hzSource hexpvSource hcoordinate
  have hvPath : ‖v‖ < τ * δ₀ := by
    exact hv.trans_le (min_le_left (τ * δ₀) ρ)
  let v₀ : E := τ⁻¹ • v
  have hv₀ : ‖v₀‖ < δ₀ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
    calc
      τ⁻¹ * ‖v‖ < τ⁻¹ * (τ * δ₀) := by
        exact mul_lt_mul_of_pos_left hvPath (inv_pos.mpr hτ)
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
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) 1 scale (Set.Icc (0 : ℝ) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_const.mul contDiff_id).contDiffOn
  have hscaleMaps :
      MapsTo scale (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) τ) := by
    intro t ht
    constructor
    · exact mul_nonneg hτ.le ht.1
    · exact mul_le_of_le_one_right hτ.le ht.2
  have hcurveSmooth :
      ContMDiffOn 𝓘(ℝ) I 1 curve (Set.Icc (0 : ℝ) 1) := by
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
  have hcMDiff : MDifferentiableOn 𝓘(ℝ) I c
      (Set.Icc (scale 0) (scale 1)) := by
    simpa only [scale, mul_zero, mul_one] using
      hcSmooth.mdifferentiableOn one_ne_zero
  have hcurveLength :
      Manifold.pathELength I curve 0 1 =
        Manifold.pathELength I c 0 τ := by
    simpa only [curve, scale, mul_zero, mul_one] using
      Manifold.pathELength_comp_of_monotoneOn
        (a := (0 : ℝ)) (b := 1) (f := scale) (γ := c)
        zero_le_one hscaleMono hscaleDiff
          hcMDiff
  have hmetricSmul :
      GeodesicTransport.chartGeodesicMetric g y (extChartAt I y y) v₀ v₀ =
        τ⁻¹ * τ⁻¹ *
          GeodesicTransport.chartGeodesicMetric g y (extChartAt I y y) v v := by
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
  exact (ENNReal.ofReal_lt_ofReal_iff hmesh).2 (by simpa only [v] using hmetric)

/-- Schedule-specific form of the uniform terminal radial-path radius. -/
theorem exists_terminalShortPathCertificate_of_terminalSourceNormal
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z) :
    ∃ δ > (0 : ℝ),
      ‖package.terminalSourceNormal schedule‖ < δ →
        Real.sqrt
            (GeodesicTransport.chartGeodesicMetric g y
              (extChartAt I y y)
              (package.terminalSourceNormal schedule)
              (package.terminalSourceNormal schedule)) < mesh →
          Nonempty (TerminalShortPathCertificate g y z mesh) := by
  rcases exists_uniform_terminalShortPathCertificate_of_terminalSourceNormal
      g y with ⟨δ, hδ, hterminal⟩
  exact ⟨δ, hδ, hterminal package schedule⟩

/-- The fixed-anchor chart metric has an automatic global Euclidean
quadratic upper bound.  No regularity in the anchor is needed: this is just
the operator-norm estimate for one continuous bilinear form. -/
theorem exists_anchorChartGeodesicMetric_euclideanUpperBound
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M) :
    ∃ C > (0 : ℝ), ∀ v : E,
      GeodesicTransport.chartGeodesicMetric g y (extChartAt I y y) v v ≤
        (C * ‖v‖) ^ 2 := by
  let B : E →L[ℝ] E →L[ℝ] ℝ :=
    GeodesicTransport.chartGeodesicMetric g y (extChartAt I y y)
  let C : ℝ := ‖B‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hBnorm : ‖B‖ ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith [norm_nonneg B]
  refine ⟨C, hC, ?_⟩
  intro v
  calc
    GeodesicTransport.chartGeodesicMetric g y (extChartAt I y y) v v =
        B v v := rfl
    _ ≤ ‖B v v‖ := Real.le_norm_self _
    _ ≤ ‖B v‖ * ‖v‖ := (B v).le_opNorm v
    _ ≤ (‖B‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg v)
    _ ≤ (C ^ 2 * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBnorm (norm_nonneg v))
        (norm_nonneg v)
    _ = (C * ‖v‖) ^ 2 := by ring

/--
For every positive mesh, one positive Euclidean normal radius alone is enough
to produce the proof-bearing terminal short path.  The radius is the minimum
of the local radial-exponential radius and the operator-norm metric cutoff
`mesh / C`.
-/
theorem exists_uniform_terminalShortPathCertificate_of_terminalSourceNormal_norm_lt
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ δ > (0 : ℝ),
      ∀ {skeleton : RootedCartanPathSkeleton g}
        (package : CanonicalRootedRealizationPackage skeleton)
        {x z : M}
        (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z),
          ‖package.terminalSourceNormal schedule‖ < δ →
            Nonempty (TerminalShortPathCertificate g y z mesh) := by
  rcases exists_uniform_terminalShortPathCertificate_of_terminalSourceNormal
      g y with ⟨δ₀, hδ₀, hradial⟩
  rcases exists_anchorChartGeodesicMetric_euclideanUpperBound g y with
    ⟨C, hC, hmetric⟩
  let δ : ℝ := min δ₀ (mesh / C)
  have hδ : 0 < δ := by
    exact lt_min hδ₀ (div_pos hmesh hC)
  refine ⟨δ, hδ, ?_⟩
  intro skeleton package x z schedule
  intro hv
  apply hradial package schedule
    (hv.trans_le (min_le_left δ₀ (mesh / C)))
  have hvCutoff : ‖package.terminalSourceNormal schedule‖ < mesh / C :=
    hv.trans_le (min_le_right δ₀ (mesh / C))
  have hCnorm :
      C * ‖package.terminalSourceNormal schedule‖ < mesh := by
    calc
      C * ‖package.terminalSourceNormal schedule‖ < C * (mesh / C) :=
        mul_lt_mul_of_pos_left hvCutoff hC
      _ = mesh := by field_simp [ne_of_gt hC]
  calc
    Real.sqrt
        (GeodesicTransport.chartGeodesicMetric g y (extChartAt I y y)
          (package.terminalSourceNormal schedule)
          (package.terminalSourceNormal schedule))
        ≤ Real.sqrt ((C * ‖package.terminalSourceNormal schedule‖) ^ 2) :=
      Real.sqrt_le_sqrt (hmetric (package.terminalSourceNormal schedule))
    _ = C * ‖package.terminalSourceNormal schedule‖ :=
      Real.sqrt_sq (mul_nonneg hC.le (norm_nonneg _))
    _ < mesh := hCnorm

/-- Schedule-specific form of the uniform Euclidean terminal-normal radius. -/
theorem exists_terminalShortPathCertificate_of_terminalSourceNormal_norm_lt
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z) :
    ∃ δ > (0 : ℝ),
      ‖package.terminalSourceNormal schedule‖ < δ →
        Nonempty (TerminalShortPathCertificate g y z mesh) := by
  rcases
      exists_uniform_terminalShortPathCertificate_of_terminalSourceNormal_norm_lt
        g y hmesh with
    ⟨δ, hδ, hterminal⟩
  exact ⟨δ, hδ, hterminal package schedule⟩

/--
The Euclidean terminal-normal cutoff can be pulled back to an ordinary metric
ball about the terminal anchor, uniformly over every rooted realization and
every final differential datum anchored there.
-/
theorem exists_uniform_terminalShortPathCertificate_of_dist_lt
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ε > (0 : ℝ),
      ∀ {skeleton : RootedCartanPathSkeleton g}
        (package : CanonicalRootedRealizationPackage skeleton)
        {x z : M}
        (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z),
          dist z y < ε →
            Nonempty (TerminalShortPathCertificate g y z mesh) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_uniform_terminalShortPathCertificate_of_terminalSourceNormal_norm_lt
        g y hmesh with
    ⟨δ, hδ, hterminal⟩
  rcases
      DifferentialSuccessorAdaptiveMeshCoordinates.exists_distance_radius_for_all_states_at_anchor
        g y hδ with
    ⟨ε, hε, hcoordinate⟩
  refine ⟨ε, hε, ?_⟩
  intro skeleton package x z schedule hdist
  let K : ℕ := schedule.factor schedule.length - 1
  let s : CartanChain.ChainState g := schedule.refinedChain.state K
  let d := schedule.refinedChain.data K
  have hfactor_le :
      schedule.length ≤ schedule.factor schedule.length :=
    strictFactorIndex_le schedule.factor schedule.length
      schedule.factor_zero schedule.factor_strict schedule.length le_rfl
  have hfactor_pos : 0 < schedule.factor schedule.length :=
    schedule.length_pos.trans_le hfactor_le
  have hnext : schedule.refined (K + 1) = z := by
    have hK : K + 1 = schedule.factor schedule.length := by
      dsimp only [K]
      omega
    rw [hK, schedule.factor_value schedule.length le_rfl,
      schedule.left_terminal_node]
  have hs : s = package.endpoint.terminalState y := by
    simpa only [s, K] using schedule.right_predecessor
  have hsanchor : s.anchor = y := by
    rw [hs]
    exact package.endpoint_terminalState_anchor y
  apply hterminal package schedule
  have hv := hcoordinate s hsanchor d (by simpa only [hnext] using hdist)
  simpa only [d, K, terminalSourceNormal] using hv

/-- The chosen schedule-uniform metric cutoff at one terminal anchor. -/
def terminalDistanceRadius
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose
    (exists_uniform_terminalShortPathCertificate_of_dist_lt g y hmesh)

/-- Every chosen terminal metric cutoff is positive. -/
theorem terminalDistanceRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (y : M)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    0 < terminalDistanceRadius g y hmesh := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_uniform_terminalShortPathCertificate_of_dist_lt g y hmesh)).1

/-- Distance below the chosen anchor cutoff produces the terminal short path
for every rooted realization and every compatible final schedule. -/
theorem terminalShortPathCertificate_of_dist_lt_terminalDistanceRadius
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hdist :
      letI : MetricSpace M := g.toMetricSpace
      dist z y < terminalDistanceRadius g y hmesh) :
    Nonempty (TerminalShortPathCertificate g y z mesh) := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_uniform_terminalShortPathCertificate_of_dist_lt g y hmesh)).2
        package schedule hdist

/-- The terminal Cartan source shrunk by the schedule-uniform metric cutoff.
This is the domain on which the final normal-vector estimate is automatic. -/
def terminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) : Set M := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (package.endpoint.terminalState y).germ.source ∩
      Metric.ball y (terminalDistanceRadius g y hmesh)

/-- Every terminal restricted domain is open. -/
theorem isOpen_terminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    IsOpen (package.terminalRestrictedDomain hmesh y) := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (package.endpoint.terminalState y).germ.open_source.inter
      Metric.isOpen_ball

/-- The anchor belongs to its restricted terminal domain. -/
theorem anchor_mem_terminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    y ∈ package.terminalRestrictedDomain hmesh y := by
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
      (terminalDistanceRadius_pos g y hmesh)

/-- Shrinking never leaves the full terminal Cartan source. -/
theorem terminalRestrictedDomain_subset_source
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    package.terminalRestrictedDomain hmesh y ⊆
      (package.endpoint.terminalState y).germ.source :=
  inter_subset_left

/-- Membership in the restricted domain of the right endpoint automatically
constructs the final proof-bearing short path. -/
theorem terminalShortPathCertificate_of_mem_terminalRestrictedDomain
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hz : z ∈ package.terminalRestrictedDomain hmesh y) :
    Nonempty (TerminalShortPathCertificate g y z mesh) := by
  apply package.terminalShortPathCertificate_of_dist_lt_terminalDistanceRadius
    hmesh schedule
  simpa only [Metric.mem_ball] using hz.2

/-- Every first-stage adaptive defect is an adjacent certified endpoint-path
edge.  At predecessor index zero the state anchor is the common root; at every
positive predecessor index it is the corresponding refined node. -/
theorem adaptiveFirstDefect_lt_mesh
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n : Fin schedule.length,
      ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
        dist
            (insertNodeListSchedule
              (factorRefinementStage schedule.seed schedule.refined
                schedule.factor n) (schedule.factor n)
              (factorGapNodes schedule.refined schedule.factor n) (i + 1)
                (schedule.factor n + i + 1))
            ((schedule.insertionChain n (i + 1)).state
              (schedule.factor n + i)).anchor < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  intro n i
  have hgap :
      schedule.factor n + i + 1 < schedule.factor (n + 1) := by
    have hi := i.isLt
    simp only [factorGapNodes_length] at hi
    omega
  have hnext_le :
      schedule.factor (n + 1) ≤ schedule.factor schedule.length :=
    CartanAtlasRootedAdaptiveClosenessTransport.RootedOverlapStrictFactorSchedule.factor_le_factor_of_le
      schedule (by omega) le_rfl
  have hnewPrefix :
      schedule.refined (schedule.factor n + i + 1) =
        package.endpoint.nodes y (schedule.factor n + i + 1) :=
    schedule.right_prefix (schedule.factor n + i) (by omega)
  have hedge (q : ℕ) :
      dist (package.endpoint.nodes y q)
          (package.endpoint.nodes y (q + 1)) < mesh := by
    simpa only [endpoint_nodes_eq_realization_path] using
      certificate.edge_dist_lt y q
  by_cases hzero : schedule.factor n + i = 0
  · have hstateRoot :
        ((schedule.insertionChain n (i + 1)).state 0).anchor =
          package.endpoint.root.anchor :=
      congrArg CartanChain.ChainState.anchor
        (schedule.insertionChain n (i + 1)).initial_eq
    have hrootNode :
        package.endpoint.root.anchor = package.endpoint.nodes y 0 := by
      simp [RootedPathContinuedEndpointFamily.nodes,
        package.endpoint.nodeTime_zero y]
    have hnewPrefixZero :
        schedule.refined 1 = package.endpoint.nodes y 1 := by
      simpa [hzero] using hnewPrefix
    calc
      dist
          (insertNodeListSchedule
            (factorRefinementStage schedule.seed schedule.refined
              schedule.factor n) (schedule.factor n)
            (factorGapNodes schedule.refined schedule.factor n) (i + 1)
              (schedule.factor n + i + 1))
          ((schedule.insertionChain n (i + 1)).state
            (schedule.factor n + i)).anchor =
          dist (package.endpoint.nodes y 1)
            (package.endpoint.nodes y 0) := by
        rw [CartanAtlasRootedAdaptiveClosenessTransport.RootedOverlapStrictFactorSchedule.insertedNode_eq_refined
          schedule n i, hzero, hstateRoot,
          hrootNode, hnewPrefixZero]
      _ < mesh := by simpa only [dist_comm] using hedge 0
  · have hpos : 0 < schedule.factor n + i := Nat.pos_of_ne_zero hzero
    have hanchor :=
      CartanAtlasRootedAdaptiveClosenessTransport.RootedOverlapStrictFactorSchedule.insertionPredecessorAnchor_eq_refined_of_pos
        schedule n i hpos
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hpreviousPrefix :
        schedule.refined (schedule.factor n + i) =
          package.endpoint.nodes y (schedule.factor n + i) := by
      have h := schedule.right_prefix q (by omega)
      simpa [hq] using h
    calc
      dist
          (insertNodeListSchedule
            (factorRefinementStage schedule.seed schedule.refined
              schedule.factor n) (schedule.factor n)
            (factorGapNodes schedule.refined schedule.factor n) (i + 1)
              (schedule.factor n + i + 1))
          ((schedule.insertionChain n (i + 1)).state
            (schedule.factor n + i)).anchor =
          dist (package.endpoint.nodes y (schedule.factor n + i + 1))
            (package.endpoint.nodes y (schedule.factor n + i)) := by
        rw [CartanAtlasRootedAdaptiveClosenessTransport.RootedOverlapStrictFactorSchedule.insertedNode_eq_refined
          schedule n i, hanchor,
          hnewPrefix, hpreviousPrefix]
      _ < mesh := by
        simpa only [dist_comm] using hedge (schedule.factor n + i)

/-- The prescribed mesh proves the first adaptive closeness field as soon as
that mesh lies below every curvature-selected first radius.  No second-stage
assumption is repackaged here. -/
theorem adaptiveFirstCloseness_of_mesh_le_adaptiveFirstRadius
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hmesh :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n : Fin schedule.length,
        ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
          mesh ≤
            RootedOverlapStrictFactorSchedule.adaptiveFirstRadius
              schedule hcurv n i) :
    RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
      schedule hcurv := by
  letI : MetricSpace M := g.toMetricSpace
  intro n i
  exact (package.adaptiveFirstDefect_lt_mesh certificate schedule n i).trans_le
    (hmesh n i)

/-- Every positive nonfinal refined edge is inherited automatically from the
certified endpoint path.  The exclusions are exact: index zero need not equal
the root node, and the final refined edge ends at the overlap point `z`, not
on the already-terminal endpoint path. -/
theorem refinedEdge_dist_lt_mesh_of_pos_of_nonfinal
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    {j : ℕ} (hjpos : 0 < j)
    (hjnonfinal : j < schedule.factor schedule.length - 1) :
    letI : MetricSpace M := g.toMetricSpace
    dist (schedule.refined j) (schedule.refined (j + 1)) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨q, hq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hleft :
      schedule.refined j = package.endpoint.nodes y j := by
    have h := schedule.right_prefix q (by omega)
    simpa [hq] using h
  have hright :
      schedule.refined (j + 1) = package.endpoint.nodes y (j + 1) :=
    schedule.right_prefix j hjnonfinal
  rw [hleft, hright]
  simpa only [endpoint_nodes_eq_realization_path] using
    certificate.edge_dist_lt y j

/-- A finite string of strict adjacent mesh bounds controls the chord by the
number of traversed edges times the mesh. -/
theorem refinedChord_lt_accumulated_mesh
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    {mesh : ℝ} (a k : ℕ)
    (hedge : ∀ j ≤ k,
      letI : MetricSpace M := g.toMetricSpace
      dist (schedule.refined (a + j))
        (schedule.refined (a + j + 1)) < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    dist (schedule.refined (a + (k + 1))) (schedule.refined a) <
      (((k + 1 : ℕ) : ℝ) * mesh) := by
  letI : MetricSpace M := g.toMetricSpace
  induction k with
  | zero =>
      simpa only [Nat.zero_add, Nat.add_zero, Nat.cast_one, one_mul,
        dist_comm] using hedge 0 le_rfl
  | succ k ih =>
      have hprevious := ih (fun j hj ↦ hedge j (hj.trans (Nat.le_succ k)))
      have hlast := hedge (k + 1) (by omega)
      have hlast' :
          dist (schedule.refined (a + (Nat.succ k + 1)))
              (schedule.refined (a + (k + 1))) < mesh := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, dist_comm] using hlast
      calc
        dist (schedule.refined (a + (Nat.succ k + 1)))
            (schedule.refined a) ≤
            dist (schedule.refined (a + (Nat.succ k + 1)))
                (schedule.refined (a + (k + 1))) +
              dist (schedule.refined (a + (k + 1)))
                (schedule.refined a) := dist_triangle _ _ _
        _ < mesh + (((k + 1 : ℕ) : ℝ) * mesh) :=
          add_lt_add hlast' hprevious
        _ = (((Nat.succ k + 1 : ℕ) : ℝ) * mesh) := by
          simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
          ring

/-- The canonical mesh certificate discharges every edge in the second-stage
chord except the final endpoint-to-overlap edge.  Once `dist y z < mesh` and
the accumulated scalar mesh bound lies below the chosen dependent radius,
the complete second closeness field follows. -/
theorem adaptiveSecondCloseness_of_finalEdge_lt_mesh_of_accumulatedMesh
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv)
    (hfinal :
      letI : MetricSpace M := g.toMetricSpace
      dist y z < mesh)
    (hscalar :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n : Fin schedule.length,
        ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
          (((schedule.factor (n + 1) -
              (schedule.factor n + i + 1) : ℕ) : ℝ) * mesh) <
            RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
              schedule hcurv hfirst n i) :
    RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
      schedule hcurv hfirst := by
  letI : MetricSpace M := g.toMetricSpace
  intro n i
  let a : ℕ := schedule.factor n + i + 1
  let b : ℕ := schedule.factor (n + 1)
  have hab : a < b := by
    have hi := i.isLt
    simp only [factorGapNodes_length] at hi
    dsimp [a, b]
    omega
  have hbterminal : b ≤ schedule.factor schedule.length := by
    dsimp [b]
    exact
      CartanAtlasRootedAdaptiveClosenessTransport.RootedOverlapStrictFactorSchedule.factor_le_factor_of_le
        schedule (by omega) le_rfl
  have hedge : ∀ j < b - a,
      dist (schedule.refined (a + j))
        (schedule.refined (a + j + 1)) < mesh := by
    intro j hj
    have haj_lt : a + j < b := by omega
    have haj_pos : 0 < a + j := by
      dsimp [a]
      omega
    by_cases hnonfinal :
        a + j < schedule.factor schedule.length - 1
    · exact package.refinedEdge_dist_lt_mesh_of_pos_of_nonfinal
        certificate schedule haj_pos hnonfinal
    · have hlastIndex :
          a + j = schedule.factor schedule.length - 1 := by
        omega
      have hlastSucc :
          a + j + 1 = schedule.factor schedule.length := by
        omega
      obtain ⟨q, hq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt haj_pos)
      have hrefinedEndpointNode :
          schedule.refined (a + j) =
            package.endpoint.nodes y (a + j) := by
        have h := schedule.right_prefix q (by omega)
        simpa [hq] using h
      have hendpointNode :
          package.endpoint.nodes y (package.endpoint.terminalIndex y) = y := by
        simp [RootedPathContinuedEndpointFamily.nodes,
          package.endpoint.nodeTime_terminal y]
      have hrefinedEndpoint : schedule.refined (a + j) = y := by
        rw [hrefinedEndpointNode, hlastIndex, schedule.right_index,
          hendpointNode]
      have hrefinedOverlap : schedule.refined (a + j + 1) = z := by
        rw [hlastSucc, schedule.factor_value schedule.length le_rfl,
          schedule.left_terminal_node]
      simpa only [hrefinedEndpoint, hrefinedOverlap] using hfinal
  have hchord := package.refinedChord_lt_accumulated_mesh schedule a
    (b - a - 1) (by
      intro j hj
      apply hedge j
      omega)
  have hindex : a + (b - a - 1 + 1) = b := by omega
  have hcount : b - a - 1 + 1 = b - a := by omega
  rw [hindex, hcount] at hchord
  rw [CartanAtlasRootedAdaptiveClosenessTransport.RootedOverlapStrictFactorSchedule.secondDefect_eq_refinedChord
    schedule n i]
  exact hchord.trans (by simpa [a, b] using hscalar n i)

/--
The terminal second-stage closeness theorem with its genuine analytic input
exposed: a proof-bearing short `C¹` path from the rooted endpoint `y` to the
overlap point `z`.  Its path length, rather than a repackaged metric-distance
bound, is the sole additional terminal-edge estimate.
-/
theorem adaptiveSecondCloseness_of_terminalPathELength_lt_mesh_of_accumulatedMesh
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv)
    (terminalPath : TerminalShortPathCertificate g y z mesh)
    (hscalar :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n : Fin schedule.length,
        ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
          (((schedule.factor (n + 1) -
              (schedule.factor n + i + 1) : ℕ) : ℝ) * mesh) <
            RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
              schedule hcurv hfirst n i) :
    RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
      schedule hcurv hfirst := by
  apply package.adaptiveSecondCloseness_of_finalEdge_lt_mesh_of_accumulatedMesh
    certificate schedule hcurv hfirst
  · exact terminalPath.dist_lt_mesh
  · exact hscalar

/--
For a positive prescribed mesh, sufficiently small Euclidean norm of the
terminal source-normal vector discharges the only terminal-edge input in the
accumulated-mesh second-closeness theorem.  The first-stage closeness and the
finite family of accumulated scalar radius bounds remain explicit.
-/
theorem exists_terminalSourceNormalRadius_for_adaptiveSecondCloseness_of_accumulatedMesh
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (hmesh : 0 < mesh)
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv) :
    ∃ δ > (0 : ℝ),
      ‖package.terminalSourceNormal schedule‖ < δ →
        (letI : MetricSpace M := g.toMetricSpace
         ∀ n : Fin schedule.length,
           ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
             (((schedule.factor (n + 1) -
                 (schedule.factor n + i + 1) : ℕ) : ℝ) * mesh) <
               RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
                 schedule hcurv hfirst n i) →
          RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
            schedule hcurv hfirst := by
  rcases
      package.exists_terminalShortPathCertificate_of_terminalSourceNormal_norm_lt
        hmesh schedule with
    ⟨δ, hδ, hterminal⟩
  refine ⟨δ, hδ, ?_⟩
  intro hv hscalar
  rcases hterminal hv with ⟨terminalPath⟩
  exact
    package.adaptiveSecondCloseness_of_terminalPathELength_lt_mesh_of_accumulatedMesh
      certificate schedule hcurv hfirst terminalPath hscalar

/--
Ordinary metric proximity to the terminal anchor now replaces the terminal
normal-vector hypothesis in the accumulated-mesh second-closeness theorem.
The radius comes from the anchor-uniform inverse normal-coordinate estimate.
-/
theorem exists_terminalDistanceRadius_for_adaptiveSecondCloseness_of_accumulatedMesh
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (hmesh : 0 < mesh)
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv) :
    ∃ ε > (0 : ℝ),
      (letI : MetricSpace M := g.toMetricSpace
       dist z y < ε) →
        (letI : MetricSpace M := g.toMetricSpace
         ∀ n : Fin schedule.length,
           ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
             (((schedule.factor (n + 1) -
                 (schedule.factor n + i + 1) : ℕ) : ℝ) * mesh) <
               RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
                 schedule hcurv hfirst n i) →
          RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
            schedule hcurv hfirst := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_terminalShortPathCertificate_of_dist_lt
      g y hmesh with ⟨ε, hε, hterminal⟩
  refine ⟨ε, hε, ?_⟩
  intro hdist hscalar
  rcases hterminal package schedule hdist with ⟨terminalPath⟩
  exact
    package.adaptiveSecondCloseness_of_terminalPathELength_lt_mesh_of_accumulatedMesh
      certificate schedule hcurv hfirst terminalPath hscalar

/--
Adaptive strict-factor closeness for the transferred endpoint family reaches
the existing realized-endpoint theorem and proves pairwise agreement of the
actual generic Cartan germs.

The schedule and its two closeness stages are the exact remaining overlap
boundary: arbitrary independently chosen rooted paths do not supply them.
-/
theorem endpoint_pairwise_eqOn_of_adaptiveCloseness
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (schedule : ∀ x y z : M,
      z ∈ (package.endpoint.terminalState x).germ.source ∩
          (package.endpoint.terminalState y).germ.source →
        RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (firstClose : ∀ x y z : M,
      ∀ hz : z ∈ (package.endpoint.terminalState x).germ.source ∩
          (package.endpoint.terminalState y).germ.source,
        RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
          (schedule x y z hz) hcurv)
    (secondClose : ∀ x y z : M,
      ∀ hz : z ∈ (package.endpoint.terminalState x).germ.source ∩
          (package.endpoint.terminalState y).germ.source,
        RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
          (schedule x y z hz) hcurv (firstClose x y z hz)) :
    ∀ x y : M,
      EqOn
        (CartanMap.openPartialHomeomorph
          g x (package.endpoint.target x) (package.endpoint.alignment x))
        (CartanMap.openPartialHomeomorph
          g y (package.endpoint.target y) (package.endpoint.alignment y))
        ((CartanMap.openPartialHomeomorph
            g x (package.endpoint.target x)
              (package.endpoint.alignment x)).source ∩
          (CartanMap.openPartialHomeomorph
            g y (package.endpoint.target y)
              (package.endpoint.alignment y)).source) := by
  let data : RootedPathAdaptiveClosenessAtlasData g hcurv :=
    { endpoint := package.endpoint
      schedule := schedule
      firstClose := firstClose
      secondClose := secondClose }
  exact data.toRealized.pairwise_eqOn

/--
The exact coherence still missing after canonical provenance has constructed
the rooted realization and its generic-successor comparison.

No target point, tangent alignment, local Cartan isometry, terminal-state
equality, or canonical-to-generic comparison is assumed here.  Those are
already carried by `package`.  The remaining data are only a common rooted
strict-factor schedule on each actual terminal-germ overlap and the two finite
families of metric inequalities which make that schedule transport.
-/
def AdaptiveOverlapCoherence
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1) : Prop :=
  ∃ schedule :
      (∀ x y z : M,
        z ∈ (package.endpoint.terminalState x).germ.source ∩
            (package.endpoint.terminalState y).germ.source →
          RootedOverlapStrictFactorSchedule package.endpoint x y z),
    ∃ firstClose :
        (∀ x y z : M,
          ∀ hz : z ∈ (package.endpoint.terminalState x).germ.source ∩
              (package.endpoint.terminalState y).germ.source,
            RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
              (schedule x y z hz) hcurv),
      ∀ x y z : M,
        ∀ hz : z ∈ (package.endpoint.terminalState x).germ.source ∩
            (package.endpoint.terminalState y).germ.source,
          RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
            (schedule x y z hz) hcurv (firstClose x y z hz)

end CanonicalRootedRealizationPackage

/--
Canonical rooted adaptive overlap coherence is sufficient for the complete
unit-curvature recognition payload.

This is the noncircular endgame composition: the existential package supplies
the actual continued target field and alignments produced by canonical
provenance, while `AdaptiveOverlapCoherence` supplies only the residual finite
overlap refinement.  Pairwise agreement then glues the existing Cartan local
homeomorphisms, and compact covering-space recognition gives the round sphere.
-/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedAdaptiveOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            package.AdaptiveOverlapCoherence hcurv) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
  intro g hcurv
  rcases completion g hcurv with
    ⟨skeleton, package, hcoherence⟩
  rcases hcoherence with ⟨schedule, firstClose, secondClose⟩
  exact
    ⟨package.endpoint.target, package.endpoint.alignment,
      package.endpoint_pairwise_eqOn_of_adaptiveCloseness
        hcurv schedule firstClose secondClose⟩

section TransitionAgreementAssembly

variable [CompactSpace M] [ConnectedSpace M]

/--
The canonical transition-agreement construction yields a prescribed-mesh
rooted package whose stepwise generic-successor comparisons are retained
automatically from the generic data used by the local transfer.  No comparison
for arbitrary canonical data or counterfactual chains is assumed.
-/
theorem exists_canonicalRootedRealizationPackage_with_prescribed_mesh
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤
        canonicalTransferredAnchorTargetRadius hcurv x p)
    (htransition : ∀ x₀ : M,
      ∃ C : CartanSourceExponentialLocalFamilyTransport.FixedChartAnchorEndpointPackage
          g x₀,
        Nonempty C.TransitionAgreementPackage)
    (skeleton : RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ package : CanonicalRootedRealizationPackage skeleton,
      PrescribedMeshCertificate package.realization mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_comparedCanonicalRootedRealization_with_prescribed_mesh_of_joint_minorant_of_transitionAgreementPackages
        hcurv pairRadius hpositive hlower hminorant htransition skeleton mesh
          hmesh with
    ⟨realization, comparison, hterminal, hmonotone, heventually, hedge⟩
  let certificate : PrescribedMeshCertificate realization mesh :=
    { terminalIndex_pos := hterminal
      nodeTime_monotone := hmonotone
      nodeTime_eventually_terminal := heventually
      edge_dist_lt := hedge }
  exact ⟨⟨realization, comparison⟩, certificate⟩

/--
If the fixed-pair provenance radius selected from the concrete successor
theorem is jointly lower semicontinuous, use it directly as the radius
minorant.  Pointwise positivity is already supplied by
`canonicalTransferredAnchorTargetRadius_pos`, and the minorant comparison is
reflexivity.

This removes the auxiliary choice of a separate `pairRadius` from the rooted
endpoint interface.  The lower-semicontinuity of the classically selected
radius and the varying-anchor transition packages remain explicit: neither is
inferred from pointwise existence.
-/
theorem exists_canonicalRootedRealizationPackage_with_prescribed_mesh_of_selectedRadius_lowerSemicontinuous
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalTransferredAnchorTargetRadius hcurv xp.1 xp.2))
    (htransition : ∀ x₀ : M,
      ∃ C : CartanSourceExponentialLocalFamilyTransport.FixedChartAnchorEndpointPackage
          g x₀,
        Nonempty C.TransitionAgreementPackage)
    (skeleton : RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ package : CanonicalRootedRealizationPackage skeleton,
      PrescribedMeshCertificate package.realization mesh := by
  apply exists_canonicalRootedRealizationPackage_with_prescribed_mesh
    hcurv
    (fun x p ↦ canonicalTransferredAnchorTargetRadius hcurv x p)
    (canonicalTransferredAnchorTargetRadius_pos hcurv)
    hlower
    (fun _x _p ↦ le_rfl)
    htransition skeleton mesh hmesh

/--
The canonical capped supremum of locally uniform admissible provenance radii
is positive, lower semicontinuous, and itself admissible.  It therefore
removes both the arbitrary `Classical.choose` radius and the separate
lower-semicontinuity premise from the rooted endpoint interface.

The remaining radius boundary is the exact geometric stability statement
that some positive admissible radius persists on a neighborhood of every
source-target pair.  Pointwise curvature existence does not prove that
statement for the independently chosen generic source exponential charts.
-/
theorem exists_canonicalRootedRealizationPackage_with_prescribed_mesh_of_transferredRadiusLocalStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : TransferredNormalRadiusLocalStability g)
    (htransition : ∀ x₀ : M,
      ∃ C : CartanSourceExponentialLocalFamilyTransport.FixedChartAnchorEndpointPackage
          g x₀,
        Nonempty C.TransitionAgreementPackage)
    (skeleton : RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ package : CanonicalRootedRealizationPackage skeleton,
      PrescribedMeshCertificate package.realization mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_comparedCanonicalRootedRealization_with_prescribed_mesh_of_localStability_of_transitionAgreementPackages
        hstable htransition skeleton mesh hmesh with
    ⟨realization, comparison, hterminal, hmonotone, heventually, hedge⟩
  let certificate : PrescribedMeshCertificate realization mesh :=
    { terminalIndex_pos := hterminal
      nodeTime_monotone := hmonotone
      nodeTime_eventually_terminal := heventually
      edge_dist_lt := hedge }
  exact ⟨⟨realization, comparison⟩, certificate⟩

end TransitionAgreementAssembly

end CartanCanonicalRootedEndpointAssembly
end Poincare
