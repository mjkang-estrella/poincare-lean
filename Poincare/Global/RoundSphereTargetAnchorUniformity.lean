import Poincare.Global.RoundSphereCurvature
import Poincare.Global.TangentAlignmentFiberCompactness

/-!
# Target-anchor-uniform round-sphere metric bounds

Mathlib's stereographic chart at a point of the unit sphere sends that point
to the origin.  At the origin the round metric's conformal factor is one, so
the target anchor chart metric is the same Euclidean inner product for every
target anchor.  Consequently, for a fixed source metric and source anchor,
the Euclidean operator norms of all Cartan tangent alignments have one bound
which is independent of both the alignment and the round-sphere target anchor.

Together with the canonical whole-target cutoff clause, this removes both the
target-anchor dependence of the alignment operator bound and the separately
chosen target-cutoff radius from the round-sphere side of the adaptive Cartan
continuation boundary.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare
namespace RoundSphereTargetAnchorUniformity

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/-- The anchor point has zero stereographic coordinate in its own sphere
chart. -/
theorem extChartAt_roundSphere_self_eq_zero (p : RoundSphere3) :
    extChartAt I p p = (0 : E) := by
  change (chartAt E p) p = (0 : E)
  change stereographic' 3 (-p) p = (0 : E)
  change
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
        (ne_zero_of_mem_unit_sphere (-p))).repr
      (stereographic (norm_eq_of_mem_sphere (-p)) p) = 0
  rw [stereographic_neg_apply p]
  exact map_zero _

/-- Every stereographic chart of the round sphere has the whole Euclidean
model space as its target. -/
theorem extChartAt_roundSphere_target_eq_univ (p : RoundSphere3) :
    (extChartAt I p).target = Set.univ := by
  have hchart : (chartAt E p).target = Set.univ := by
    change (stereographic' 3 (-p)).target = Set.univ
    exact stereographic'_target (-p)
  rw [extChartAt_target]
  simp [closedSmoothModelWithCorners, hchart]

/-- The canonicality clause in `exists_blending_cutoff` forces the global
geodesic-transport cutoff of every round-sphere chart to be identically one. -/
theorem cutoff_roundSphere_eq_one (p : RoundSphere3) :
    GeodesicTransport.cutoff (n := 3) p = fun _ : E ↦ (1 : ℝ) :=
  GeodesicTransport.cutoff_eq_one_of_target_eq_univ (n := 3) p
    (extChartAt_roundSphere_target_eq_univ p)

/-- The chart geodesic coefficient of the round sphere is literally
independent of the target anchor.  Canonical blending makes both cutoffs
identically one, so both fields reduce to the same stereographic Christoffel
formula. -/
theorem chartChristoffelField_roundSphere_anchor_independent
    (p q : RoundSphere3) :
    GeodesicTransport.chartChristoffelField roundSphereMetric3 p =
      GeodesicTransport.chartChristoffelField roundSphereMetric3 q := by
  funext z
  apply ContinuousLinearMap.ext
  intro s
  apply ContinuousLinearMap.ext
  intro v
  calc
    GeodesicTransport.chartChristoffelField roundSphereMetric3 p z s v =
        sphereChristoffel z s v :=
      roundSphereMetric3_chartChristoffelField_eq_sphereChristoffel_of_eventuallyEq_one
        p (Filter.Eventually.of_forall fun y : E ↦
          congrFun (cutoff_roundSphere_eq_one p) y) s v
    _ = GeodesicTransport.chartChristoffelField
          roundSphereMetric3 q z s v :=
      (roundSphereMetric3_chartChristoffelField_eq_sphereChristoffel_of_eventuallyEq_one
        q (Filter.Eventually.of_forall fun y : E ↦
          congrFun (cutoff_roundSphere_eq_one q) y) s v).symm

/-- The round-sphere metric in the chart based at its evaluation point is
exactly the Euclidean inner product, independently of the point. -/
theorem targetAnchorChartMetric_eq_innerSL (p : RoundSphere3) :
    CartanMap.targetAnchorChartMetric p = innerSL ℝ := by
  ext u v
  rw [CartanMap.targetAnchorChartMetric,
    roundSphereMetric3_chartMetric_eq,
    extChartAt_roundSphere_self_eq_zero]
  norm_num [stereoInvFunAuxConformalFactor]
  exact (innerSL_apply_apply (𝕜 := ℝ) u v).symm

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- For a fixed source anchor, all tangent alignments into every round-sphere
target anchor have one common positive Euclidean operator-norm bound. -/
theorem exists_pos_uniform_tangentAlignment_operatorNorm_bound_all_targets
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ C > (0 : ℝ), ∀ (p₀ : RoundSphere3)
      (L : CartanMap.TangentAlignment g x₀ p₀),
        ‖L.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ C := by
  let Jalg := CartanMap.sourceEuclideanAlignment g x₀
  let J : E ≃L[ℝ] E := CartanMap.sourceEuclideanContinuousLinearEquiv g x₀
  let C : ℝ := ‖J.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro p₀ L
  let A : E →L[ℝ] E :=
    L.toContinuousLinearEquiv.toContinuousLinearMap
  apply ContinuousLinearMap.opNorm_le_bound A hC.le
  intro v
  have hsq : ‖A v‖ ^ 2 = ‖J v‖ ^ 2 := by
    calc
      ‖A v‖ ^ 2 = inner ℝ (A v) (A v) :=
        (real_inner_self_eq_norm_sq (A v)).symm
      _ = CartanMap.targetAnchorChartMetric p₀ (L v) (L v) := by
        rw [targetAnchorChartMetric_eq_innerSL]
        rfl
      _ = CartanMap.sourceAnchorChartMetric g x₀ v v :=
        L.map_app v v
      _ = CartanMap.euclideanBilinForm (Jalg v) (Jalg v) := by
        simpa [Jalg] using (Jalg.map_app' v v).symm
      _ = inner ℝ (J v) (J v) := by
        rfl
      _ = ‖J v‖ ^ 2 := real_inner_self_eq_norm_sq (J v)
  have hnorm : ‖A v‖ = ‖J v‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  calc
    ‖A v‖ = ‖J v‖ := hnorm
    _ ≤ ‖J.toContinuousLinearMap‖ * ‖v‖ :=
      J.toContinuousLinearMap.le_opNorm v
    _ ≤ C * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      dsimp [C]
      linarith

end RoundSphereTargetAnchorUniformity
end Poincare
