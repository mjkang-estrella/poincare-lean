import Poincare.Global.MetricFlowJointRegularity
import Poincare.Global.MetricRaiseTimeDerivative

/-!
# Joint metric regularity differentiates connection values

This module closes the first connection-regularity boundary left by joint
time-space regularity of metric entries.  The proof is intrinsic and
finite-dimensional: the Koszul formula defines a continuous covector from
three first spatial derivatives of the metric, and the inverse metric raises
that covector to the actual Levi-Civita connection value.

Consequently, joint `C²` regularity of the metric entries differentiates the
Levi-Civita connection on canonical extensions at the anchor point.  No
independent differentiability hypothesis for Christoffel symbols is used.
-/

noncomputable section

open Bundle FiberBundle Filter Set Function
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "Iₘ" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace Iₘ : M → Type _)

/-- The scalar half-Koszul expression on three fixed tangent vectors. -/
noncomputable def connectionKoszulScalarAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v w z : TM x) : ℝ :=
  (1 / 2 : ℝ) *
    (spatialMetricDerivAt g x v w z
      + spatialMetricDerivAt g x w v z
      - spatialMetricDerivAt g x z v w)

/-- Package the scalar Koszul values as a continuous covector by expanding in
the canonical finite basis of the fixed tangent fiber. -/
noncomputable def connectionKoszulCovectorAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v w : TM x) : TM x →L[ℝ] ℝ :=
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  ∑ i, connectionKoszulScalarAt g x v w (b i) •
    LinearMap.toContinuousLinearMap (b.coord i)

/-- Joint `C²` metric entries differentiate every scalar coefficient in the
Koszul expression. -/
theorem connectionKoszulScalarAt_differentiableAt_of_jointContDiffAt_two
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 2)
    (v w z : TM x) :
    DifferentiableAt ℝ
      (fun t ↦ connectionKoszulScalarAt (gt t) x v w z) t₀ := by
  have h₁ : DifferentiableAt ℝ
      (fun t ↦ spatialMetricDerivAt (gt t) x v w z) t₀ := by
    simpa [spatialMetricDerivAt] using
      (metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
        hJoint v w z).differentiableAt
  have h₂ : DifferentiableAt ℝ
      (fun t ↦ spatialMetricDerivAt (gt t) x w v z) t₀ := by
    simpa [spatialMetricDerivAt] using
      (metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
        hJoint w v z).differentiableAt
  have h₃ : DifferentiableAt ℝ
      (fun t ↦ spatialMetricDerivAt (gt t) x z v w) t₀ := by
    simpa [spatialMetricDerivAt] using
      (metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
        hJoint z v w).differentiableAt
  simpa [connectionKoszulScalarAt] using
    ((h₁.add h₂).sub h₃).const_mul (1 / 2 : ℝ)

/-- Joint `C²` metric entries differentiate the continuous Koszul covector
on the fixed tangent fiber. -/
theorem connectionKoszulCovectorAt_differentiableAt_of_jointContDiffAt_two
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 2)
    (v w : TM x) :
    DifferentiableAt ℝ
      (fun t ↦ connectionKoszulCovectorAt (gt t) x v w) t₀ := by
  classical
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold connectionKoszulCovectorAt
  refine DifferentiableAt.fun_sum ?_
  intro i _
  exact
    (connectionKoszulScalarAt_differentiableAt_of_jointContDiffAt_two
      hJoint v w ((Module.finBasis ℝ (TM x)) i)).smul_const
        (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ (TM x)).coord i))

/-- The finite-basis Koszul covector has the prescribed value on every basis
vector. -/
@[simp] theorem connectionKoszulCovectorAt_apply_finBasis
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (v w : TM x) (i : Fin (Module.finrank ℝ (TM x))) :
    connectionKoszulCovectorAt g x v w
        ((Module.finBasis ℝ (TM x)) i) =
      connectionKoszulScalarAt g x v w
        ((Module.finBasis ℝ (TM x)) i) := by
  classical
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  simp [connectionKoszulCovectorAt, Module.Basis.coord_apply,
    Finsupp.single_apply]

/-- For canonical extensions, the Koszul formula reduces to the scalar
half-Koszul expression because all three Lie brackets vanish at their common
anchor. -/
theorem leviCivita_extend_inner_eq_connectionKoszulScalarAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v w z : TM x) :
    g.inner x (g.leviCivita (extend E w) x v) z =
      connectionKoszulScalarAt g x v w z := by
  let X := extend E v
  let Y := extend E w
  let Z := extend E z
  have hK := CovariantDerivative.koszul_formula
    (g := g.inner) (cov := g.leviCivita) (x := x)
    (g.inner_symm x)
    (g.leviCivita_metricCompatibleAt x)
    (g.leviCivita_torsionFreeAt x)
    (X := X) (Y := Y) (Z := Z)
    (by simpa [X] using (mdifferentiableAt_extend Iₘ E v))
    (by simpa [Y] using (mdifferentiableAt_extend Iₘ E w))
    (by simpa [Z] using (mdifferentiableAt_extend Iₘ E z))
  have hXY : VectorField.mlieBracket Iₘ X Y x = 0 := by
    simpa [X, Y] using
      (mlieBracket_extend_extend_apply_self
        (n := n) (M := M) (x := x) v w)
  have hXZ : VectorField.mlieBracket Iₘ X Z x = 0 := by
    simpa [X, Z] using
      (mlieBracket_extend_extend_apply_self
        (n := n) (M := M) (x := x) v z)
  have hYZ : VectorField.mlieBracket Iₘ Y Z x = 0 := by
    simpa [Y, Z] using
      (mlieBracket_extend_extend_apply_self
        (n := n) (M := M) (x := x) w z)
  have hK' :
      2 * g.inner x (g.leviCivita (extend E w) x v) z =
        spatialMetricDerivAt g x v w z
          + spatialMetricDerivAt g x w v z
          - spatialMetricDerivAt g x z v w := by
    simpa [spatialMetricDerivAt, X, Y, Z, hXY, hXZ, hYZ] using hK
  unfold connectionKoszulScalarAt
  linarith

/-- Raising the finite-basis Koszul covector gives the actual Levi-Civita
connection value. -/
theorem leviCivita_extend_eq_metricRaise_connectionKoszulCovectorAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v w : TM x) :
    g.leviCivita (extend E w) x v =
      g.metricRaiseContinuousAt x (connectionKoszulCovectorAt g x v w) := by
  classical
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  apply (LinearMap.BilinForm.toDual (g.metricBilinAt x)
    (g.metricBilinAt_nondegenerate x)).injective
  apply b.ext
  intro i
  change g.inner x (g.leviCivita (extend E w) x v) (b i) =
    g.inner x
      (g.metricRaiseContinuousAt x (connectionKoszulCovectorAt g x v w))
      (b i)
  rw [ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  rw [connectionKoszulCovectorAt_apply_finBasis]
  exact leviCivita_extend_inner_eq_connectionKoszulScalarAt g x v w (b i)

/-- Joint `C²` metric-entry regularity differentiates the genuine
Levi-Civita connection value on canonical extensions at the anchor point. -/
theorem connectionValueTimeDifferentiableAt_of_metricEntriesJointContDiffAt_two
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 2) :
    ConnectionValueTimeDifferentiableAt gt t₀ x := by
  intro v w
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have hgt : TimeDifferentiableAt gt t₀ x :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      (hJoint.of_le (by norm_num))
  have hRaise : DifferentiableAt ℝ
      (fun t ↦ (gt t).metricRaiseContinuousAt x) t₀ :=
    metricRaiseContinuousAt_differentiableAt_of_timeDifferentiableAt hgt
  have hKoszul : DifferentiableAt ℝ
      (fun t ↦ connectionKoszulCovectorAt (gt t) x v w) t₀ :=
    connectionKoszulCovectorAt_differentiableAt_of_jointContDiffAt_two
      hJoint v w
  have heq :
      (fun t ↦ (gt t).leviCivita (extend E w) x v) =
        fun t ↦ (gt t).metricRaiseContinuousAt x
          (connectionKoszulCovectorAt (gt t) x v w) := by
    funext t
    exact leviCivita_extend_eq_metricRaise_connectionKoszulCovectorAt
      (gt t) x v w
  rw [heq]
  exact hRaise.clm_apply hKoszul

/-- A global joint `C²` hypothesis supplies the connection field required by
the first component of `MetricFlowRegularAt` at every point. -/
theorem connectionValueTimeDifferentiableAt_all_of_jointContDiffAt_two
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hJoint : ∀ x : M, MetricEntriesJointContDiffAt gt t₀ x 2) :
    ∀ x : M, ConnectionValueTimeDifferentiableAt gt t₀ x :=
  fun x ↦
    connectionValueTimeDifferentiableAt_of_metricEntriesJointContDiffAt_two
      (hJoint x)

end Poincare
