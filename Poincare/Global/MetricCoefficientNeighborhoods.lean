import Poincare.Global.BufferedFrozenParabolicSolver

/-!
# Metric-selected coordinate neighborhoods

The actual inverse metric entries determine an oscillation ball at each
manifold anchor. Intersecting that ball with the genuine chart target and
the open neighborhood where the fixed anchor cutoff is locally one gives
coordinate neighborhoods suitable for a later buffered atlas construction.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace Poincare.MetricCoefficientNeighborhoods

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The chart Gram field is nonsingular on its genuine target, since the
inverse-chart derivative transports a genuine tangent basis. -/
theorem gramField_det_ne_zero
    (g0 : ClosedSmoothRiemannianMetric 3 M) (p : M)
    {z : ClosedSmoothModel 3}
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target) :
    (inverseChartPullbackGramMatrixField g0 p z).det ≠ 0 := by
  let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p hz
  have hmatrix : inverseChartPullbackGramMatrixField g0 p z =
      g0.metricMatrixInBasisAt ((extChartAt (closedSmoothModelWithCorners 3) p).symm z) b := by
    ext i j
    change CovariantDerivative.chartMetric g0.inner p z
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      g0.inner ((extChartAt (closedSmoothModelWithCorners 3) p).symm z) (b i) (b j)
    dsimp only [b]
    rw [ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply,
      ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
    rfl
  rw [hmatrix]
  exact g0.metricMatrixInBasisAt_det_ne_zero _ b

/-- Actual inverse metric entries are continuous at genuine chart coordinates.
The local proof uses no connectedness or measure-space assumptions. -/
theorem inverse_metric_entry_continuousAt
    (g0 : ClosedSmoothRiemannianMetric 3 M) (p : M)
    {z : ClosedSmoothModel 3}
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target)
    (i j : Fin 3) :
    ContinuousAt (fun y ↦ (inverseChartPullbackGramMatrixField g0 p y)⁻¹ i j) z := by
  have hentry (a b : Fin 3) :
      ContDiffOn ℝ ∞ (fun y ↦ inverseChartPullbackGramMatrixField g0 p y a b)
        (extChartAt (closedSmoothModelWithCorners 3) p).target :=
    (CovariantDerivative.contMDiffOn_chartMetric_pairing
      g0.inner p (m := ∞) (by simp) g0.contMDiff_inner
      (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b)).contDiffOn
  have hfield : ContinuousAt (inverseChartPullbackGramMatrixField g0 p) z :=
    continuousAt_pi.mpr fun a ↦ continuousAt_pi.mpr fun b ↦
      ((hentry a b) z hz).contDiffAt
        ((isOpen_extChartAt_target p).mem_nhds hz) |>.continuousAt
  have hinverse : ContinuousAt Inv.inv (inverseChartPullbackGramMatrixField g0 p z) :=
    continuousAt_matrix_inv _ (by
      simpa only [Ring.inverse_eq_inv'] using
        continuousAt_inv₀ (gramField_det_ne_zero g0 p hz))
  exact (continuous_apply_apply i j).continuousAt.comp (hinverse.comp hfield)

/-- Every positive pointwise tolerance selects a genuine coordinate neighborhood
on which the anchor cutoff is locally one and all actual inverse metric
entries satisfy the requested bound on any contained function support. -/
theorem exists_coefficient_neighborhoods
    (g0 : ClosedSmoothRiemannianMetric 3 M) (ε : M → ℝ)
    (hε : ∀ p, 0 < ε p) :
    ∃ V : M → Set (ClosedSmoothModel 3),
      (∀ p, IsOpen (V p) ∧
        extChartAt (closedSmoothModelWithCorners 3) p p ∈ V p ∧
        V p ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).target ∧
        ∀ z ∈ V p, ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) p y = 1) ∧
      ∀ p (ξ : ClosedSmoothModel 3 → ℝ), tsupport ξ ⊆ V p →
        ∀ z ∈ tsupport ξ, ∀ a b : Fin 3,
          |(inverseChartPullbackGramMatrixField g0 p z)⁻¹ a b -
            (inverseChartPullbackGramMatrixField g0 p
              (extChartAt (closedSmoothModelWithCorners 3) p p))⁻¹ a b| ≤ ε p := by
  classical
  have hradius (p : M) :=
    BufferedFrozenParabolicSolver.exists_oscillation_radius
      (fun z a b ↦ (inverseChartPullbackGramMatrixField g0 p z)⁻¹ a b)
      (extChartAt (closedSmoothModelWithCorners 3) p p)
      (fun a b ↦ inverse_metric_entry_continuousAt g0 p (mem_extChartAt_target p) a b)
      (hε p)
  choose ρ hρpos hρbound using hradius
  let V (p : M) : Set (ClosedSmoothModel 3) :=
    (extChartAt (closedSmoothModelWithCorners 3) p).target ∩
      {z | ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) p y = 1} ∩
      Metric.ball (extChartAt (closedSmoothModelWithCorners 3) p p) (ρ p)
  refine ⟨V, ?_, ?_⟩
  · intro p
    refine ⟨((isOpen_extChartAt_target p).inter
      isOpen_setOf_eventually_nhds).inter Metric.isOpen_ball, ?_, ?_, ?_⟩
    · exact ⟨⟨mem_extChartAt_target p,
        GeodesicTransport.cutoff_eventuallyEq_one (n := 3) p⟩,
        Metric.mem_ball_self (hρpos p)⟩
    · intro z hz
      exact hz.1.1
    · intro z hz
      exact hz.1.2
  · intro p ξ hξ z hz a b
    exact hρbound p ξ (fun z hz ↦ (hξ hz).2) z hz a b

end Poincare.MetricCoefficientNeighborhoods
