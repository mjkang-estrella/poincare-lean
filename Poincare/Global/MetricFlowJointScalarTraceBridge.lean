import Poincare.Global.MetricFlowJointCurvatureRegularity
import Poincare.Global.DeTurckChartIndependentPullback
import Poincare.Global.ScalarVariation

/-!
# Anchor-chart scalar trace bridge

The joint-curvature module constructs a finite-basis inverse-metric trace from
the actual anchor-chart Christoffel field.  This file identifies that
coordinate expression with the intrinsic Ricci and scalar curvatures at the
preferred-chart anchor.  Consequently joint `C³` metric entries imply honest
time continuity of intrinsic scalar curvature at every fixed spatial point.

The stronger equality at arbitrary points of the cutoff-one chart germ, which
is needed for full joint space-time continuity on the manifold, remains a
separate zone bridge.
-/

noncomputable section

open Bundle FiberBundle Filter
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

/-- At the preferred-chart anchor, the chart curvature vector is the
intrinsic curvature endomorphism used in the Ricci trace. -/
theorem anchorChartCurvatureFlow_eq_ricciCurvatureEndAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) (u v w : E) :
    anchorChartCurvatureFlow gt x t (extChartAt I x x) u v w =
      ricciCurvatureEndAt (gt t) x v w u := by
  let R : ∀ y : M, TM y :=
    CovariantDerivative.curvatureOp (gt t).leviCivita
      (extend E (x := x) u) (extend E (x := x) v) (extend E (x := x) w)
  have hbridge :=
    ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp
      (g := gt t) (x₀ := x) u v w
  have htransport :
      CovariantDerivative.chartTransportedLeviCivitaSection x R
          (extChartAt I x x) = R x := by
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x) (σ := R) (y := x)
        (mem_extChartAt_source x)
    rw [mfderiv_extChartAt_self] at happly
    simpa [R] using happly
  have htensor :
      CovariantDerivative.curvatureTensorAt (gt t).leviCivita
          (CovariantDerivative.derivRegularAt_extend (gt t).leviCivita w)
          u v = R x := by
    simpa [R] using
      (CovariantDerivative.curvatureTensorAt_apply
        (cov := (gt t).leviCivita)
        (hreg := CovariantDerivative.derivRegularAt_extend
          (gt t).leviCivita w)
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..))
  rw [show anchorChartCurvatureFlow gt x t (extChartAt I x x) u v w =
      CovariantDerivative.chartTransportedLeviCivitaSection x R
        (extChartAt I x x) by
    simpa [anchorChartCurvatureFlow,
      anchorChartChristoffelFieldFlow, R] using hbridge]
  rw [htransport]
  simpa [ricciCurvatureEndAt,
    CovariantDerivative.curvatureEndAt_apply] using htensor.symm

/-- The fixed-basis chart Ricci trace equals the intrinsic Ricci tensor at the
preferred-chart anchor. -/
theorem anchorChartRicciEntryFlow_eq_ricciAt_anchor
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) (v w : E) :
    anchorChartRicciEntryFlow gt x t (extChartAt I x x) v w =
      (gt t).ricciAt x v w := by
  classical
  let b := Module.finBasis ℝ E
  calc
    anchorChartRicciEntryFlow gt x t (extChartAt I x x) v w =
        ∑ i, b.coord i (ricciCurvatureEndAt (gt t) x v w (b i)) := by
          unfold anchorChartRicciEntryFlow
          dsimp only
          apply Finset.sum_congr rfl
          intro i _hi
          rw [anchorChartCurvatureFlow_eq_ricciCurvatureEndAt_apply]
          rfl
    _ = LinearMap.trace ℝ E (ricciCurvatureEndAt (gt t) x v w) := by
          rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
            Module.Basis.coord_apply]
          rfl
    _ = (gt t).ricciAt x v w := rfl

/-- At the preferred-chart anchor, applying the inverse blended metric to a
basis coordinate covector gives the intrinsic metric-raised dual vector. -/
theorem anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) (i : Fin (Module.finrank ℝ E)) :
    let b := Module.finBasis ℝ E
    (anchorBlendedMetricFlow gt x t (extChartAt I x x)).inverse
        (LinearMap.toContinuousLinearMap (b.coord i)) =
      metricDualVectorAt (gt t) x (b.coord i) := by
  let b := Module.finBasis ℝ E
  let G := anchorBlendedMetricFlow gt x t (extChartAt I x x)
  let phi : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  let raised : E := G.inverse phi
  let sharp : E := metricDualVectorAt (gt t) x (b.coord i)
  have hGmetric : ∀ a c : E, G a c = (gt t).inner x a c := by
    intro a c
    have hblend :=
      (anchorBlendedMetricFlow_eventuallyEq_anchorChartMetricFlow
        gt t x).self_of_nhds
    change anchorBlendedMetricFlow gt x t (extChartAt I x x) =
      anchorChartMetricFlow gt x t (extChartAt I x x) at hblend
    have hchart := CovariantDerivative.chartMetric_apply_chart
      (gt t).inner x (mem_extChartAt_source x) a c
    rw [mfderiv_extChartAt_self] at hchart
    change anchorBlendedMetricFlow gt x t (extChartAt I x x) a c = _
    rw [hblend]
    simpa [anchorChartMetricFlow] using hchart
  have hInv : G.IsInvertible := by
    simpa [G] using
      anchorBlendedMetricFlow_isInvertible gt x t (extChartAt I x x)
  have hLower : ∀ c : E, (gt t).inner x raised c = phi c := by
    intro c
    have hphi : G (G.inverse phi) = phi :=
      (hInv.inverse_apply_eq.mp rfl).symm
    calc
      (gt t).inner x raised c = G raised c := (hGmetric raised c).symm
      _ = phi c := congrArg (fun psi : E →L[ℝ] ℝ ↦ psi c) hphi
  change raised = sharp
  refine sub_eq_zero.mp
    (LeviCivitaExistence.metric_nondegenerate (gt t) x (raised - sharp) ?_)
  intro c
  calc
    (gt t).inner x (raised - sharp) c =
        (gt t).inner x raised c - (gt t).inner x sharp c := by
          exact congrArg (fun psi : E →L[ℝ] ℝ ↦ psi c)
            (map_sub ((gt t).inner x) raised sharp)
    _ = phi c - (gt t).inner x sharp c := by rw [hLower]
    _ = 0 := by
      rw [show (gt t).inner x sharp c = b.coord i c by
        simpa [sharp] using
          (metricDualVectorAt_inner_apply (gt t) x (b.coord i) c)]
      simp [phi]

/-- The finite-coordinate scalar trace is exactly intrinsic scalar curvature
at the preferred-chart anchor. -/
theorem anchorChartScalarTraceFlow_eq_scalarAt_anchor
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) :
    anchorChartScalarTraceFlow gt x t (extChartAt I x x) =
      (gt t).scalarAt x := by
  classical
  let g := gt t
  let b := Module.finBasis ℝ E
  let G := anchorBlendedMetricFlow gt x t (extChartAt I x x)
  let phi : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  let raised : Fin (Module.finrank ℝ E) → E := fun i ↦ G.inverse (phi i)
  have hRic : ∀ v w : E,
      anchorChartRicciEntryFlow gt x t (extChartAt I x x) v w =
        g.ricciAt x v w := by
    intro v w
    simpa [g] using anchorChartRicciEntryFlow_eq_ricciAt_anchor gt x t v w
  have hsum : ∀ i,
      (∑ k, b.coord k (raised i) * g.ricciAt x (b i) (b k)) =
        g.ricciAt x (b i) (raised i) := by
    intro i
    let R : E →L[ℝ] ℝ := ricciContinuousBilinAt g x (b i)
    have hrepr : ∑ k, b.coord k (raised i) • b k = raised i :=
      b.sum_repr (raised i)
    calc
      (∑ k, b.coord k (raised i) * g.ricciAt x (b i) (b k)) =
          ∑ k, R (b.coord k (raised i) • b k) := by
            apply Finset.sum_congr rfl
            intro k _hk
            calc
              b.coord k (raised i) * g.ricciAt x (b i) (b k) =
                  b.coord k (raised i) * R (b k) := by
                    have hRbk : R (b k) =
                        g.ricciAt x (b i) (b k) := by
                      change ricciContinuousBilinAt g x (b i) (b k) = _
                      exact ricciContinuousBilinAt_apply g x (b i) (b k)
                    rw [hRbk]
              _ = R (b.coord k (raised i) • b k) := by
                    simp [smul_eq_mul]
      _ = R (∑ k, b.coord k (raised i) • b k) := by
            rw [map_sum]
      _ = R (raised i) := by rw [hrepr]
      _ = g.ricciAt x (b i) (raised i) := by
            change ricciContinuousBilinAt g x (b i) (raised i) = _
            exact ricciContinuousBilinAt_apply g x (b i) (raised i)
  calc
    anchorChartScalarTraceFlow gt x t (extChartAt I x x) =
        ∑ i, ∑ k,
          b.coord k (raised i) * g.ricciAt x (b i) (b k) := by
            unfold anchorChartScalarTraceFlow
              anchorChartInverseMetricCoeffFlow
            dsimp only
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro k _hk
            rw [hRic]
            rfl
    _ = ∑ i, g.ricciAt x (b i) (raised i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hsum i
    _ = ∑ i, g.ricciAt x (b i)
          (metricDualVectorAt g x (b.coord i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [show raised i = metricDualVectorAt g x (b.coord i) by
            simpa [raised, G, phi, g, b] using
              anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt
                gt x t i]
    _ = traceMetricVariationAt g (ricciVariationField g) x := by
          rfl
    _ = g.scalarAt x := traceMetricVariationAt_ricci g x
    _ = (gt t).scalarAt x := rfl

/-- Joint `C³` metric entries imply time continuity of intrinsic scalar
curvature at the fixed spatial anchor. -/
theorem continuousAt_scalarAt_time_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt (fun t ↦ (gt t).scalarAt x) t₀ := by
  have htrace :=
    anchorChartScalarTraceFlow_continuousAt_of_metricEntries hJoint
  have hpath :
      (fun t ↦ (gt t).scalarAt x) =
        fun t ↦ anchorChartScalarTraceFlow gt x t (extChartAt I x x) := by
    funext t
    exact (anchorChartScalarTraceFlow_eq_scalarAt_anchor gt x t).symm
  rw [hpath]
  have hline :
      ContinuousAt (fun t : ℝ ↦ (t, extChartAt I x x)) t₀ :=
    continuousAt_id.prodMk continuousAt_const
  exact ContinuousAt.comp'
    (f := fun t : ℝ ↦ (t, extChartAt I x x))
    (g := Function.uncurry (anchorChartScalarTraceFlow gt x))
    (x := t₀) htrace hline

end Poincare
