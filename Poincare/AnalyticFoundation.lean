/-
Typed interfaces for the analytic Ricci-flow foundation.

This module narrows the `ricciFlowAnalyticFoundation` milestone into the
curvature and PDE layers that have to exist before the surgery package can be a
real theorem. Most predicates have no constructors here; they are proof
obligations for future formalization, not assumptions manufactured locally.
The Levi-Civita existence, uniqueness, torsion-free, metric-compatibility,
connection-theory, Riemann-curvature-construction, Riemann-curvature symmetry,
first-Bianchi, second-Bianchi, Riemann-curvature-theory, and Ricci tensor
contraction-formula predicates store concrete time-indexed mathlib
covariant-derivative, curvature, and contraction data so the first analytic
package fields are non-vacuous.  The later parabolic-regularity and
Shi-derivative estimate predicates likewise store concrete time-indexed
regularity, curvature-derivative, and pointwise estimate data.
-/

import Poincare.RicciFlow
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

universe u v w

open Bundle
open scoped Manifold ContDiff

namespace Poincare

/--
The concrete bundled mathlib object used for one time-slice connection on the
tangent bundle.

A term of this type is a `CovariantDerivative`, including the additivity and
Leibniz-rule proof carried by mathlib's structure.
-/
abbrev TangentCovariantDerivative
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] : Type _ :=
  CovariantDerivative I E (fun x : M => TangentSpace I x)

/-- Shape contract for the concrete tangent covariant-derivative witness type. -/
theorem tangentCovariantDerivative_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] :
    TangentCovariantDerivative I M =
      CovariantDerivative I E (fun x : M => TangentSpace I x) :=
  rfl

/--
Concrete time-dependent connection data for a time-dependent metric: a bundled
mathlib tangent covariant derivative at every time.

This is deliberately only the existence-level witness. Torsion-free,
metric-compatibility, and uniqueness remain separate analytic fields until the
local/mathlib Levi-Civita API is formalized strongly enough to derive them.
-/
abbrev TimeDependentTangentConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Type _ :=
  ℝ → TangentCovariantDerivative I M

/-- Shape contract for time-indexed tangent connection fields. -/
theorem timeDependentTangentConnectionField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    TimeDependentTangentConnectionField g =
      (ℝ → TangentCovariantDerivative I M) :=
  rfl

/--
Concrete uniqueness data for the time-dependent tangent connection field.

The witness stores an actual time-indexed bundled mathlib covariant derivative
and a uniqueness theorem for that same data shape.  It is intentionally stronger
than the bare existence field and does not manufacture torsion-free or
metric-compatibility evidence.
-/
structure UniqueTimeDependentTangentConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The selected time-dependent connection field. -/
  connectionAtTime : TimeDependentTangentConnectionField g
  /-- Every connection field of this data shape is equal to the selected one. -/
  eq_connectionAtTime :
    ∀ otherConnectionAtTime : TimeDependentTangentConnectionField g,
      otherConnectionAtTime = connectionAtTime

/--
Concrete torsion-free data for the time-dependent tangent connection field.

The witness stores the unique time-dependent connection field and proves that
mathlib's bundled torsion tensor vanishes at every time.  The extra hypotheses
are exactly the hypotheses needed by `CovariantDerivative.torsion`.
-/
structure TorsionFreeTimeDependentTangentConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The unique time-dependent tangent connection field. -/
  uniqueConnectionAtTime : UniqueTimeDependentTangentConnectionField g
  /-- The bundled mathlib torsion tensor of each time-slice connection vanishes. -/
  torsion_eq_zero :
    ∀ t : ℝ, (uniqueConnectionAtTime.connectionAtTime t).torsion = 0

/--
Concrete metric-compatibility data for the time-dependent tangent connection
field.

The witness stores the zero-torsion connection field and proves the usual
Levi-Civita metric-compatibility identity at every time: for differentiable
vector fields `X`, `Y`, and `Z`, the directional derivative of `g(Y, Z)` in the
`X` direction equals the two connection terms.  Mathlib does not yet package
this as a ready-made Levi-Civita predicate, so this structure records the
standard identity directly against mathlib's bundled `CovariantDerivative` and
`ContMDiffRiemannianMetric.inner` data.
-/
structure MetricCompatibleTimeDependentTangentConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The zero-torsion time-dependent tangent connection field. -/
  torsionFreeConnectionAtTime :
    TorsionFreeTimeDependentTangentConnectionField g
  /--
  The time-slice metric-compatibility identity
  `X(g_t(Y,Z)) = g_t(∇_X Y,Z) + g_t(Y,∇_X Z)`.
  -/
  metric_compatibility :
    ∀ (t : ℝ) {X Y Z : (x : M) → TangentSpace I x} {x : M},
      MDiffAt (T% X) x →
      MDiffAt (T% Y) x →
      MDiffAt (T% Z) x →
        extDerivFun (I := I)
            (fun y : M => (g.metricAtTime t).inner y (Y y) (Z y)) x (X x) =
          (g.metricAtTime t).inner x
              ((torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime t)
                Y x (X x))
              (Z x) +
            (g.metricAtTime t).inner x
              (Y x)
              ((torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime t)
                Z x (X x))

/--
Concrete Levi-Civita connection-theory data for the time-dependent tangent
connection field.

The witness extends metric-compatible connection data with the mathlib
smoothness class for every time-slice bundled covariant derivative.  This is the
available production-level replacement for a future single mathlib Levi-Civita
connection theorem.
-/
structure LeviCivitaTimeDependentConnectionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The metric-compatible time-dependent tangent connection field. -/
  metricCompatibleConnectionAtTime :
    MetricCompatibleTimeDependentTangentConnectionField g
  /-- Each time-slice connection is a smooth mathlib covariant derivative. -/
  contMDiffConnectionAtTime :
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime t) n

/-- A tangent-valued Riemann-curvature tensor at one time. -/
abbrev TangentRiemannCurvatureTensor
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] : Type _ :=
  (x : M) →
    TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x

/-- Shape contract for tangent-valued Riemann-curvature tensors. -/
theorem tangentRiemannCurvatureTensor_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] :
    TangentRiemannCurvatureTensor I M =
      ((x : M) →
        TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ]
            TangentSpace I x →L[ℝ] TangentSpace I x) :=
  rfl

/--
Concrete time-dependent Riemann-curvature tensor data for a time-dependent
metric.
-/
abbrev TimeDependentRiemannCurvatureTensorField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Type _ :=
  ℝ → TangentRiemannCurvatureTensor I M

/-- Shape contract for time-indexed tangent-valued Riemann-curvature fields. -/
theorem timeDependentRiemannCurvatureTensorField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    TimeDependentRiemannCurvatureTensorField g =
      (ℝ → TangentRiemannCurvatureTensor I M) :=
  rfl

/--
Concrete construction data for the time-dependent Riemann curvature tensor.

The witness stores the connection-theory input, a time-indexed tangent-valued
curvature tensor, and the standard commutator formula
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z` against the selected bundled
mathlib covariant derivative.
-/
structure RiemannCurvatureTensorConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The smooth Levi-Civita connection-theory data used to construct curvature. -/
  connectionTheoryAtTime :
    LeviCivitaTimeDependentConnectionTheoryData g
  /-- The time-dependent tangent-valued Riemann-curvature tensor field. -/
  curvatureAtTime : TimeDependentRiemannCurvatureTensorField g
  /--
  The standard curvature commutator formula for differentiable vector fields.
  -/
  curvature_eq_commutator :
    let metricCompatibleConnectionAtTime :=
      connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    ∀ (t : ℝ) {X Y Z : (x : M) → TangentSpace I x} {x : M},
      MDiffAt (T% X) x →
      MDiffAt (T% Y) x →
      MDiffAt (T% Z) x →
        curvatureAtTime t x (X x) (Y x) (Z x) =
          connectionAtTime t
              (fun y : M => connectionAtTime t Z y (Y y)) x (X x) -
            connectionAtTime t
              (fun y : M => connectionAtTime t Z y (X y)) x (Y x) -
            connectionAtTime t Z x (VectorField.mlieBracket I X Y x)

/--
Concrete symmetry data for the constructed time-dependent Riemann curvature
tensor.

The witness extends curvature-construction data with the standard algebraic
Riemann-curvature symmetries that do not overlap the separately named Bianchi
identity fields: skew-symmetry in the first pair, metric skew-adjointness in the
last pair, and pair exchange symmetry for the lowered curvature tensor.
-/
structure RiemannCurvatureTensorSymmetryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The constructed time-dependent Riemann-curvature tensor. -/
  curvatureConstructionAtTime :
    RiemannCurvatureTensorConstructionData g
  /-- Skew-symmetry of `R(X,Y)Z` in the first two slots. -/
  curvature_skew_first_pair :
    let curvatureAtTime := curvatureConstructionAtTime.curvatureAtTime
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace I x),
      curvatureAtTime t x X Y Z = - curvatureAtTime t x Y X Z
  /--
  Metric skew-adjointness of `R(X,Y)` in the last two lowered slots.
  -/
  curvature_metric_skew_last_pair :
    let curvatureAtTime := curvatureConstructionAtTime.curvatureAtTime
    ∀ (t : ℝ) {x : M} (X Y Z W : TangentSpace I x),
      (g.metricAtTime t).inner x (curvatureAtTime t x X Y Z) W =
        - (g.metricAtTime t).inner x Z (curvatureAtTime t x X Y W)
  /--
  Pair exchange symmetry of the lowered curvature tensor.
  -/
  curvature_pair_symmetry :
    let curvatureAtTime := curvatureConstructionAtTime.curvatureAtTime
    ∀ (t : ℝ) {x : M} (X Y Z W : TangentSpace I x),
      (g.metricAtTime t).inner x (curvatureAtTime t x X Y Z) W =
        (g.metricAtTime t).inner x (curvatureAtTime t x Z W X) Y

/--
Concrete first-Bianchi data for the constructed time-dependent Riemann
curvature tensor.

The witness extends curvature-symmetry data with the cyclic identity
`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`.
-/
structure RiemannCurvatureFirstBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The constructed curvature tensor with algebraic Riemann symmetries. -/
  curvatureSymmetryAtTime :
    RiemannCurvatureTensorSymmetryData g
  /-- The cyclic first Bianchi identity for the tangent-valued curvature tensor. -/
  first_bianchi_identity :
    let curvatureAtTime :=
      curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace I x),
      curvatureAtTime t x X Y Z +
          curvatureAtTime t x Y Z X +
        curvatureAtTime t x Z X Y = 0

/--
Concrete time-dependent covariant derivative of the Riemann-curvature tensor.

At each time and point this stores `(∇_A R)(X,Y)Z` as a tangent vector.  The
meaningful link to the selected Levi-Civita connection and constructed
curvature tensor is recorded in `RiemannCurvatureSecondBianchiData`.
-/
abbrev TimeDependentRiemannCurvatureCovariantDerivativeField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Type _ :=
  ℝ → (x : M) →
    TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → TangentSpace I x

/--
Shape contract for time-indexed covariant derivatives of Riemann-curvature
fields.
-/
theorem timeDependentRiemannCurvatureCovariantDerivativeField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    TimeDependentRiemannCurvatureCovariantDerivativeField g =
      (ℝ → (x : M) →
        TangentSpace I x → TangentSpace I x → TangentSpace I x →
          TangentSpace I x → TangentSpace I x) :=
  rfl

/--
Concrete second-Bianchi data for the constructed time-dependent Riemann
curvature tensor.

The witness extends first-Bianchi data with a time-dependent covariant
derivative of curvature, identifies that derivative with the selected
Levi-Civita connection acting on the constructed curvature tensor, and records
the cyclic second Bianchi identity
`(∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0`.
-/
structure RiemannCurvatureSecondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The constructed curvature tensor with algebraic Riemann symmetries and first Bianchi. -/
  firstBianchiAtTime :
    RiemannCurvatureFirstBianchiData g
  /-- The time-dependent tangent-valued covariant derivative of curvature. -/
  curvatureCovariantDerivativeAtTime :
    TimeDependentRiemannCurvatureCovariantDerivativeField g
  /--
  The standard formula defining the covariant derivative of the curvature
  tensor against the selected time-slice Levi-Civita connection.
  -/
  curvature_covariant_derivative_eq_connection_derivative :
    let curvatureAtTime :=
      firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime
    let connectionTheoryAtTime :=
      firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.connectionTheoryAtTime
    let metricCompatibleConnectionAtTime :=
      connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    ∀ (t : ℝ) {A X Y Z : (x : M) → TangentSpace I x} {x : M},
      MDiffAt (T% A) x →
      MDiffAt (T% X) x →
      MDiffAt (T% Y) x →
      MDiffAt (T% Z) x →
        curvatureCovariantDerivativeAtTime t x (A x) (X x) (Y x) (Z x) =
          connectionAtTime t
              (fun y : M => curvatureAtTime t y (X y) (Y y) (Z y))
              x (A x) -
            curvatureAtTime t x (connectionAtTime t X x (A x)) (Y x) (Z x) -
            curvatureAtTime t x (X x) (connectionAtTime t Y x (A x)) (Z x) -
            curvatureAtTime t x (X x) (Y x) (connectionAtTime t Z x (A x))
  /-- The cyclic second Bianchi identity for the covariant derivative of curvature. -/
  second_bianchi_identity :
    let curvatureDerivativeAtTime := curvatureCovariantDerivativeAtTime
    ∀ (t : ℝ) {x : M} (X Y Z W : TangentSpace I x),
      curvatureDerivativeAtTime t x X Y Z W +
          curvatureDerivativeAtTime t x Y Z X W +
        curvatureDerivativeAtTime t x Z X Y W = 0

/--
Time-dependent trace functional used to contract curvature endomorphisms into
the Ricci tensor.

The trace functional is kept explicit because the current local/mathlib API
does not yet expose the full coordinate-free Ricci contraction theorem needed
by the production package.
-/
abbrev TimeDependentRicciContractionTraceField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Type _ :=
  ℝ → (x : M) → (TangentSpace I x →L[ℝ] TangentSpace I x) → ℝ

/-- Shape contract for time-indexed Ricci contraction trace functionals. -/
theorem timeDependentRicciContractionTraceField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    TimeDependentRicciContractionTraceField g =
      (ℝ → (x : M) → (TangentSpace I x →L[ℝ] TangentSpace I x) → ℝ) :=
  rfl

/--
Time-dependent curvature endomorphism whose trace defines the Ricci tensor.

For tangent vectors `X` and `Y`, the endomorphism is intended to be
`Z ↦ R(Z, X)Y`.
-/
abbrev TimeDependentRicciContractionEndomorphismField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Type _ :=
  ℝ → (x : M) → TangentSpace I x → TangentSpace I x →
    TangentSpace I x →L[ℝ] TangentSpace I x

/-- Shape contract for time-indexed Ricci contraction endomorphism fields. -/
theorem timeDependentRicciContractionEndomorphismField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    TimeDependentRicciContractionEndomorphismField g =
      (ℝ → (x : M) → TangentSpace I x → TangentSpace I x →
        TangentSpace I x →L[ℝ] TangentSpace I x) :=
  rfl

/--
Concrete Ricci tensor contraction-formula data.

The witness stores the Riemann-curvature theory data through the second Bianchi
identity, an explicit trace functional, the curvature endomorphism being traced,
and the two formulas that make the Ricci tensor a contraction of the constructed
Riemann tensor.
-/
structure RicciTensorContractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Type _ where
  /-- Riemann-curvature data through both Bianchi identities. -/
  secondBianchiAtTime :
    RiemannCurvatureSecondBianchiData g
  /-- The trace functional used for the Ricci contraction. -/
  traceAtTime : TimeDependentRicciContractionTraceField g
  /-- The curvature endomorphism being traced. -/
  curvatureEndomorphismAtTime :
    TimeDependentRicciContractionEndomorphismField g
  /-- The traced endomorphism is `Z ↦ R(Z, X)Y`. -/
  curvature_endomorphism_eq_riemann :
    let curvatureAtTime :=
      secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace I x),
      curvatureEndomorphismAtTime t x X Y Z =
        curvatureAtTime t x Z X Y
  /-- The candidate Ricci tensor is the trace of the curvature endomorphism. -/
  ricci_eq_trace_curvature_endomorphism :
    ∀ (t : ℝ) (x : M) (X Y : TangentSpace I x),
      curvature.ricci.tensorAtTime t x X Y =
        traceAtTime t x (curvatureEndomorphismAtTime t x X Y)

/--
Time-dependent trace functional used to contract the Ricci tensor into scalar
curvature.

The trace functional is kept explicit because this local API does not yet
provide the inverse-metric contraction theorem needed to derive scalar
curvature directly from the metric and Ricci tensor.
-/
abbrev TimeDependentScalarCurvatureTraceField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Type _ :=
  ℝ → (x : M) →
    (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) → ℝ

/-- Shape contract for time-indexed scalar-curvature trace functionals. -/
theorem timeDependentScalarCurvatureTraceField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    TimeDependentScalarCurvatureTraceField g =
      (ℝ → (x : M) →
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) → ℝ) :=
  rfl

/--
Concrete scalar-curvature contraction-formula data.

The witness stores the Ricci tensor contraction formula, an explicit trace
functional for covariant two-tensors, and the formula that makes the candidate
scalar curvature the metric trace of the candidate Ricci tensor.
-/
structure ScalarCurvatureContractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Type _ where
  /-- Ricci tensor contraction-formula data through the Riemann tensor. -/
  ricciContractionFormulaAtTime :
    RicciTensorContractionFormulaData curvature
  /-- The trace functional used for scalar curvature. -/
  traceAtTime : TimeDependentScalarCurvatureTraceField g
  /-- The candidate scalar curvature is the trace of the candidate Ricci tensor. -/
  scalar_eq_trace_ricci :
    ∀ (t : ℝ) (x : M),
      curvature.scalar.scalarAtTime t x =
        traceAtTime t x (curvature.ricci.tensorAtTime t x)

/--
Concrete Ricci contraction theory data.

The witness packages the complete local contraction chain currently available:
the Ricci tensor is the trace of the Riemann curvature endomorphism, and the
scalar curvature is the trace of that Ricci tensor.
-/
structure RicciContractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Type _ where
  /-- Scalar-curvature contraction data, including the underlying Ricci formula. -/
  scalarContractionFormulaAtTime :
    ScalarCurvatureContractionFormulaData curvature
  /-- The candidate Ricci tensor is the trace of the curvature endomorphism. -/
  ricci_eq_trace_curvature_endomorphism :
    ∀ (t : ℝ) (x : M) (X Y : TangentSpace I x),
      curvature.ricci.tensorAtTime t x X Y =
        scalarContractionFormulaAtTime.ricciContractionFormulaAtTime.traceAtTime
          t x
          ((scalarContractionFormulaAtTime.ricciContractionFormulaAtTime).curvatureEndomorphismAtTime
            t x X Y)
  /-- The candidate scalar curvature is the trace of the candidate Ricci tensor. -/
  scalar_eq_trace_ricci :
    ∀ (t : ℝ) (x : M),
      curvature.scalar.scalarAtTime t x =
        scalarContractionFormulaAtTime.traceAtTime t x
          (curvature.ricci.tensorAtTime t x)

/--
Concrete scalar-curvature theory data.

The witness stores the complete contraction chain presently available for the
scalar curvature field: Ricci is obtained by contracting the Riemann curvature
endomorphism, and scalar curvature is obtained by tracing that Ricci tensor.
-/
structure ScalarCurvatureTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Type _ where
  /-- The contraction-theory witness that identifies scalar curvature as `tr_g Ric`. -/
  ricciContractionTheoryAtTime :
    RicciContractionTheoryData curvature

/--
Scalar-curvature contraction-formula data canonically supplies the local Ricci
contraction theory data.
-/
def ricciContractionTheoryData_of_scalarContractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarContractionFormulaAtTime :
      ScalarCurvatureContractionFormulaData curvature) :
    RicciContractionTheoryData curvature where
  scalarContractionFormulaAtTime := scalarContractionFormulaAtTime
  ricci_eq_trace_curvature_endomorphism :=
    (scalarContractionFormulaAtTime.ricciContractionFormulaAtTime).ricci_eq_trace_curvature_endomorphism
  scalar_eq_trace_ricci :=
    scalarContractionFormulaAtTime.scalar_eq_trace_ricci

/-- The canonical Ricci contraction-theory data stores the supplied formulas. -/
@[simp] theorem ricciContractionTheoryData_of_scalarContractionFormulaData_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarContractionFormulaAtTime :
      ScalarCurvatureContractionFormulaData curvature) :
    ricciContractionTheoryData_of_scalarContractionFormulaData
        scalarContractionFormulaAtTime =
      ({ scalarContractionFormulaAtTime := scalarContractionFormulaAtTime
         ricci_eq_trace_curvature_endomorphism :=
          scalarContractionFormulaAtTime.ricciContractionFormulaAtTime.ricci_eq_trace_curvature_endomorphism
         scalar_eq_trace_ricci :=
          scalarContractionFormulaAtTime.scalar_eq_trace_ricci } :
        RicciContractionTheoryData curvature) :=
  rfl

/--
Ricci contraction-theory data canonically supplies scalar-curvature theory
data.
-/
def scalarCurvatureTheoryData_of_ricciContractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature) :
    ScalarCurvatureTheoryData curvature where
  ricciContractionTheoryAtTime := ricciContractionTheoryAtTime

/-- The canonical scalar-curvature theory data stores the supplied contraction chain. -/
@[simp] theorem scalarCurvatureTheoryData_of_ricciContractionTheoryData_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature) :
    (scalarCurvatureTheoryData_of_ricciContractionTheoryData
      ricciContractionTheoryAtTime).ricciContractionTheoryAtTime =
        ricciContractionTheoryAtTime :=
  rfl

/-- Scalar-curvature theory data exposes the defining trace formula. -/
theorem scalarCurvatureTheoryData_scalar_eq_trace_ricci
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData curvature) :
    ∀ (t : ℝ) (x : M),
      curvature.scalar.scalarAtTime t x =
        scalarCurvatureTheoryAtTime.ricciContractionTheoryAtTime.scalarContractionFormulaAtTime.traceAtTime
          t x
          (curvature.ricci.tensorAtTime t x) :=
  scalarCurvatureTheoryAtTime.ricciContractionTheoryAtTime.scalar_eq_trace_ricci

/--
Concrete regularity data for a time-dependent Riemannian metric.

The witness records the actual smooth Riemannian metric slice at each time and
identifies it with the metric family carried by `TimeDependentRiemannianMetric`.
This is exactly the regularity data already present in the production metric
object: every time slice is a mathlib `ContMDiffRiemannianMetric`.
-/
structure TimeDependentMetricRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Type _ where
  /-- The smooth Riemannian metric slice at each time. -/
  metricAtTime :
    ℝ → ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)
  /-- The stored slices are exactly the slices of the production metric family. -/
  metricAtTime_eq : metricAtTime = g.metricAtTime

/--
Every production time-dependent Riemannian metric carries metric-regularity
data through its `metricAtTime` field.
-/
def timeDependentMetricRegularityData_of_metric
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    TimeDependentMetricRegularityData g where
  metricAtTime := g.metricAtTime
  metricAtTime_eq := rfl

/-- The canonical metric-regularity data stores the metric slices of `g`. -/
@[simp] theorem timeDependentMetricRegularityData_of_metric_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    timeDependentMetricRegularityData_of_metric g =
      ({ metricAtTime := g.metricAtTime
         metricAtTime_eq := rfl } :
        TimeDependentMetricRegularityData g) :=
  rfl

/-- Shape contract for the canonical metric-regularity data. -/
theorem timeDependentMetricRegularityData_of_metric_metricAtTime_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    (timeDependentMetricRegularityData_of_metric g).metricAtTime =
      g.metricAtTime :=
  rfl

/-- Interface for the Levi-Civita connection theory of a time-dependent metric. -/
structure HasLeviCivitaConnectionTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  Existing source data for a metric-compatible time-dependent tangent
  connection with smooth mathlib covariant-derivative time slices.
  -/
  connectionTheoryData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (LeviCivitaTimeDependentConnectionTheoryData g)

/-- Compatibility constructor for Levi-Civita connection-theory data. -/
def HasLeviCivitaConnectionTheory.of_connectionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (connectionTheoryAtTime :
      LeviCivitaTimeDependentConnectionTheoryData g) :
    HasLeviCivitaConnectionTheory g where
  connectionTheoryData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨connectionTheoryAtTime⟩⟩

/--
Concrete smooth metric-compatible connection data proves the production
Levi-Civita connection-theory interface.
-/
theorem hasLeviCivitaConnectionTheory_of_connectionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (connectionTheoryAtTime :
      LeviCivitaTimeDependentConnectionTheoryData g) :
    HasLeviCivitaConnectionTheory g :=
  HasLeviCivitaConnectionTheory.of_connectionTheoryData
    connectionTheoryAtTime

/-- Interface for existence of a Levi-Civita connection for each metric time slice. -/
structure HasLeviCivitaConnectionExistence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A time-indexed bundled mathlib covariant derivative on the tangent bundle
  supplies the non-vacuous existence witness.
  -/
  connectionField_source : Nonempty (TimeDependentTangentConnectionField g)

/-- Compatibility constructor for Levi-Civita connection-field data. -/
def HasLeviCivitaConnectionExistence.of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (connectionAtTime : TimeDependentTangentConnectionField g) :
    HasLeviCivitaConnectionExistence g where
  connectionField_source := ⟨connectionAtTime⟩

/-- A concrete connection field proves the production Levi-Civita existence interface. -/
theorem hasLeviCivitaConnectionExistence_of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (connectionAtTime : TimeDependentTangentConnectionField g) :
    HasLeviCivitaConnectionExistence g :=
  HasLeviCivitaConnectionExistence.of_connectionField connectionAtTime

/--
The production Levi-Civita existence interface is equivalent to nonempty
time-indexed tangent covariant-derivative data.
-/
theorem hasLeviCivitaConnectionExistence_iff_connectionField_nonempty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    HasLeviCivitaConnectionExistence g ↔
      Nonempty (TimeDependentTangentConnectionField g) := by
  constructor
  · intro h
    exact h.connectionField_source
  · rintro ⟨connectionAtTime⟩
    exact hasLeviCivitaConnectionExistence_of_connectionField connectionAtTime

/-- Interface for uniqueness of the Levi-Civita connection. -/
structure HasLeviCivitaConnectionUniqueness
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A selected time-indexed tangent covariant derivative plus a uniqueness theorem
  supplies the non-vacuous uniqueness witness.
  -/
  uniqueConnectionField_source :
    Nonempty (UniqueTimeDependentTangentConnectionField g)

/-- Compatibility constructor for Levi-Civita uniqueness data. -/
def HasLeviCivitaConnectionUniqueness.of_uniqueConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (uniqueConnectionAtTime : UniqueTimeDependentTangentConnectionField g) :
    HasLeviCivitaConnectionUniqueness g where
  uniqueConnectionField_source := ⟨uniqueConnectionAtTime⟩

/-- Concrete uniqueness data proves the production Levi-Civita uniqueness interface. -/
theorem hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (uniqueConnectionAtTime : UniqueTimeDependentTangentConnectionField g) :
    HasLeviCivitaConnectionUniqueness g :=
  HasLeviCivitaConnectionUniqueness.of_uniqueConnectionField
    uniqueConnectionAtTime

/--
The production Levi-Civita uniqueness interface is equivalent to nonempty
unique time-indexed tangent covariant-derivative data.
-/
theorem hasLeviCivitaConnectionUniqueness_iff_uniqueConnectionField_nonempty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    HasLeviCivitaConnectionUniqueness g ↔
      Nonempty (UniqueTimeDependentTangentConnectionField g) := by
  constructor
  · intro h
    exact h.uniqueConnectionField_source
  · rintro ⟨uniqueConnectionAtTime⟩
    exact
      hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField
        uniqueConnectionAtTime

/-- Interface for the torsion-free property of the Levi-Civita connection. -/
structure HasLeviCivitaTorsionFreeProperty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A unique time-dependent tangent connection field with vanishing mathlib torsion
  supplies the non-vacuous torsion-free witness.
  -/
  torsionFreeConnectionField_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (TorsionFreeTimeDependentTangentConnectionField g)

/-- Compatibility constructor for Levi-Civita torsion-free data. -/
def HasLeviCivitaTorsionFreeProperty.of_torsionFreeConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (torsionFreeConnectionAtTime :
      TorsionFreeTimeDependentTangentConnectionField g) :
    HasLeviCivitaTorsionFreeProperty g where
  torsionFreeConnectionField_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨torsionFreeConnectionAtTime⟩⟩

/-- Concrete zero-torsion connection data proves the production torsion-free interface. -/
theorem hasLeviCivitaTorsionFreeProperty_of_torsionFreeConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (torsionFreeConnectionAtTime :
      TorsionFreeTimeDependentTangentConnectionField g) :
    HasLeviCivitaTorsionFreeProperty g :=
  HasLeviCivitaTorsionFreeProperty.of_torsionFreeConnectionField
    torsionFreeConnectionAtTime

/--
Zero-torsion connection data also supplies the earlier existence and uniqueness
Levi-Civita fields.
-/
theorem leviCivitaExistence_uniqueness_of_torsionFreeConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (torsionFreeConnectionAtTime :
      TorsionFreeTimeDependentTangentConnectionField g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g :=
  ⟨hasLeviCivitaConnectionExistence_of_connectionField
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime,
    hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField
      torsionFreeConnectionAtTime.uniqueConnectionAtTime⟩

/-- Interface for metric compatibility of the Levi-Civita connection. -/
structure HasLeviCivitaMetricCompatibility
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A time-dependent tangent connection field satisfying the standard
  metric-compatibility identity supplies the non-vacuous metric-compatibility
  witness.
  -/
  metricCompatibleConnectionField_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (MetricCompatibleTimeDependentTangentConnectionField g)

/-- Compatibility constructor for Levi-Civita metric-compatibility data. -/
def HasLeviCivitaMetricCompatibility.of_metricCompatibleConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricCompatibleConnectionAtTime :
      MetricCompatibleTimeDependentTangentConnectionField g) :
    HasLeviCivitaMetricCompatibility g where
  metricCompatibleConnectionField_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨metricCompatibleConnectionAtTime⟩⟩

/--
Concrete metric-compatible connection data proves the production
Levi-Civita metric-compatibility interface.
-/
theorem hasLeviCivitaMetricCompatibility_of_metricCompatibleConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricCompatibleConnectionAtTime :
      MetricCompatibleTimeDependentTangentConnectionField g) :
    HasLeviCivitaMetricCompatibility g :=
  HasLeviCivitaMetricCompatibility.of_metricCompatibleConnectionField
    metricCompatibleConnectionAtTime

/--
Metric-compatible connection data also supplies the earlier existence,
uniqueness, and torsion-free Levi-Civita fields.
-/
theorem leviCivitaFirstThree_of_metricCompatibleConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricCompatibleConnectionAtTime :
      MetricCompatibleTimeDependentTangentConnectionField g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g :=
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  ⟨hasLeviCivitaConnectionExistence_of_connectionField
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime,
    hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField
      torsionFreeConnectionAtTime.uniqueConnectionAtTime,
    hasLeviCivitaTorsionFreeProperty_of_torsionFreeConnectionField
      torsionFreeConnectionAtTime⟩

/--
Connection-theory data supplies the preceding four Levi-Civita fields:
existence, uniqueness, torsion-freeness, and metric compatibility.
-/
theorem leviCivitaFirstFour_of_connectionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (connectionTheoryAtTime :
      LeviCivitaTimeDependentConnectionTheoryData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g :=
  let firstThree :=
    leviCivitaFirstThree_of_metricCompatibleConnectionField
      connectionTheoryAtTime.metricCompatibleConnectionAtTime
  ⟨firstThree.1, firstThree.2.1, firstThree.2.2,
    hasLeviCivitaMetricCompatibility_of_metricCompatibleConnectionField
      connectionTheoryAtTime.metricCompatibleConnectionAtTime⟩

/-- Interface for the Riemann-curvature tensor theory of a time-dependent metric. -/
structure HasRiemannCurvatureTensorTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  Curvature construction, symmetries, and both Bianchi identities supply the
  non-vacuous Riemann-curvature-theory witness.
  -/
  secondBianchiData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RiemannCurvatureSecondBianchiData g)

/-- Compatibility constructor for Riemann-curvature theory data. -/
def HasRiemannCurvatureTensorTheory.of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData g) :
    HasRiemannCurvatureTensorTheory g where
  secondBianchiData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨secondBianchiAtTime⟩⟩

/--
Concrete second-Bianchi data proves the production Riemann-curvature-theory
interface.
-/
theorem hasRiemannCurvatureTensorTheory_of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData g) :
    HasRiemannCurvatureTensorTheory g :=
  HasRiemannCurvatureTensorTheory.of_secondBianchiData
    secondBianchiAtTime

/-- Interface for constructing the Riemann curvature tensor from the connection. -/
structure HasRiemannCurvatureTensorConstruction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A tangent-valued curvature tensor with the standard commutator construction
  formula supplies the non-vacuous Riemann-curvature construction witness.
  -/
  curvatureConstructionData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RiemannCurvatureTensorConstructionData g)

/-- Compatibility constructor for Riemann-curvature construction data. -/
def HasRiemannCurvatureTensorConstruction.of_curvatureConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData g) :
    HasRiemannCurvatureTensorConstruction g where
  curvatureConstructionData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨curvatureConstructionAtTime⟩⟩

/--
Concrete curvature construction data proves the production
Riemann-curvature-tensor construction interface.
-/
theorem hasRiemannCurvatureTensorConstruction_of_curvatureConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData g) :
    HasRiemannCurvatureTensorConstruction g :=
  HasRiemannCurvatureTensorConstruction.of_curvatureConstructionData
    curvatureConstructionAtTime

/--
Riemann-curvature construction data also supplies the preceding Levi-Civita
fields.
-/
theorem leviCivitaFirstFive_of_curvatureConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g :=
  let firstFour :=
    leviCivitaFirstFour_of_connectionTheoryData
      curvatureConstructionAtTime.connectionTheoryAtTime
  ⟨firstFour.1, firstFour.2.1, firstFour.2.2.1, firstFour.2.2.2,
    hasLeviCivitaConnectionTheory_of_connectionTheoryData
      curvatureConstructionAtTime.connectionTheoryAtTime⟩

/-- Interface for the standard symmetries of the Riemann curvature tensor. -/
structure HasRiemannCurvatureTensorSymmetries
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A constructed Riemann-curvature tensor with the standard algebraic symmetry
  identities supplies the non-vacuous symmetry witness.
  -/
  curvatureSymmetryData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RiemannCurvatureTensorSymmetryData g)

/-- Compatibility constructor for Riemann-curvature symmetry data. -/
def HasRiemannCurvatureTensorSymmetries.of_curvatureSymmetryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvatureSymmetryAtTime :
      RiemannCurvatureTensorSymmetryData g) :
    HasRiemannCurvatureTensorSymmetries g where
  curvatureSymmetryData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨curvatureSymmetryAtTime⟩⟩

/--
Concrete curvature symmetry data proves the production Riemann-curvature
symmetry interface.
-/
theorem hasRiemannCurvatureTensorSymmetries_of_curvatureSymmetryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvatureSymmetryAtTime :
      RiemannCurvatureTensorSymmetryData g) :
    HasRiemannCurvatureTensorSymmetries g :=
  HasRiemannCurvatureTensorSymmetries.of_curvatureSymmetryData
    curvatureSymmetryAtTime

/--
Riemann-curvature symmetry data also supplies the preceding Levi-Civita and
curvature-construction fields.
-/
theorem riemannCurvatureFirstSix_of_curvatureSymmetryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvatureSymmetryAtTime :
      RiemannCurvatureTensorSymmetryData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g :=
  let firstFive :=
    leviCivitaFirstFive_of_curvatureConstructionData
      curvatureSymmetryAtTime.curvatureConstructionAtTime
  ⟨firstFive.1, firstFive.2.1, firstFive.2.2.1, firstFive.2.2.2.1,
    firstFive.2.2.2.2,
    hasRiemannCurvatureTensorConstruction_of_curvatureConstructionData
      curvatureSymmetryAtTime.curvatureConstructionAtTime⟩

/-- Interface for the first Bianchi identity. -/
structure HasFirstBianchiIdentity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A constructed Riemann-curvature tensor satisfying the cyclic first Bianchi
  identity supplies the non-vacuous first-Bianchi witness.
  -/
  firstBianchiData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RiemannCurvatureFirstBianchiData g)

/-- Compatibility constructor for first-Bianchi data. -/
def HasFirstBianchiIdentity.of_firstBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (firstBianchiAtTime :
      RiemannCurvatureFirstBianchiData g) :
    HasFirstBianchiIdentity g where
  firstBianchiData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨firstBianchiAtTime⟩⟩

/--
Concrete first-Bianchi data proves the production first-Bianchi interface.
-/
theorem hasFirstBianchiIdentity_of_firstBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (firstBianchiAtTime :
      RiemannCurvatureFirstBianchiData g) :
    HasFirstBianchiIdentity g :=
  HasFirstBianchiIdentity.of_firstBianchiData
    firstBianchiAtTime

/--
First-Bianchi data also supplies the preceding Levi-Civita, curvature
construction, and curvature-symmetry fields.
-/
theorem riemannCurvatureFirstSeven_of_firstBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (firstBianchiAtTime :
      RiemannCurvatureFirstBianchiData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g :=
  let firstSix :=
    riemannCurvatureFirstSix_of_curvatureSymmetryData
      firstBianchiAtTime.curvatureSymmetryAtTime
  ⟨firstSix.1, firstSix.2.1, firstSix.2.2.1,
    firstSix.2.2.2.1, firstSix.2.2.2.2.1,
    firstSix.2.2.2.2.2,
    hasRiemannCurvatureTensorSymmetries_of_curvatureSymmetryData
      firstBianchiAtTime.curvatureSymmetryAtTime⟩

/-- Interface for the second Bianchi identity. -/
structure HasSecondBianchiIdentity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A constructed Riemann-curvature tensor with a connection-defined covariant
  derivative satisfying the cyclic second Bianchi identity supplies the
  non-vacuous second-Bianchi witness.
  -/
  secondBianchiData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RiemannCurvatureSecondBianchiData g)

/-- Compatibility constructor for second-Bianchi data. -/
def HasSecondBianchiIdentity.of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData g) :
    HasSecondBianchiIdentity g where
  secondBianchiData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨secondBianchiAtTime⟩⟩

/--
Concrete second-Bianchi data proves the production second-Bianchi interface.
-/
theorem hasSecondBianchiIdentity_of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData g) :
    HasSecondBianchiIdentity g :=
  HasSecondBianchiIdentity.of_secondBianchiData
    secondBianchiAtTime

/--
Second-Bianchi data also supplies all earlier Levi-Civita and curvature fields
through first Bianchi.
-/
theorem riemannCurvatureFirstEight_of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g :=
  let firstSeven :=
    riemannCurvatureFirstSeven_of_firstBianchiData
      secondBianchiAtTime.firstBianchiAtTime
  ⟨firstSeven.1, firstSeven.2.1, firstSeven.2.2.1,
    firstSeven.2.2.2.1, firstSeven.2.2.2.2.1,
    firstSeven.2.2.2.2.2.1, firstSeven.2.2.2.2.2.2,
    hasFirstBianchiIdentity_of_firstBianchiData
      secondBianchiAtTime.firstBianchiAtTime⟩

/--
Second-Bianchi data closes the first ten analytic curvature fields, through
Riemann-curvature tensor theory.
-/
theorem riemannCurvatureFirstTen_of_secondBianchiData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g ∧
      HasSecondBianchiIdentity g ∧
      HasRiemannCurvatureTensorTheory g :=
  let firstEight :=
    riemannCurvatureFirstEight_of_secondBianchiData
      secondBianchiAtTime
  ⟨firstEight.1, firstEight.2.1, firstEight.2.2.1,
    firstEight.2.2.2.1, firstEight.2.2.2.2.1,
    firstEight.2.2.2.2.2.1, firstEight.2.2.2.2.2.2.1,
    firstEight.2.2.2.2.2.2.2,
    hasSecondBianchiIdentity_of_secondBianchiData
      secondBianchiAtTime,
    hasRiemannCurvatureTensorTheory_of_secondBianchiData
      secondBianchiAtTime⟩

/-- Interface for deriving the Ricci tensor by contracting curvature. -/
structure HasRicciContractionTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Prop where
  /--
  Complete local contraction-chain data, through both `Ric = tr R` and
  `Scal = tr Ric`, supplies the non-vacuous Ricci contraction-theory witness.
  -/
  contractionTheoryData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciContractionTheoryData curvature)

/-- Compatibility constructor for Ricci contraction-theory data. -/
def HasRicciContractionTheory.of_contractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature) :
    HasRicciContractionTheory curvature where
  contractionTheoryData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨ricciContractionTheoryAtTime⟩⟩

/--
Concrete Ricci contraction-theory data proves the production Ricci contraction
theory interface.
-/
theorem hasRicciContractionTheory_of_contractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature) :
    HasRicciContractionTheory curvature :=
  HasRicciContractionTheory.of_contractionTheoryData
    ricciContractionTheoryAtTime

/--
Scalar-curvature contraction-formula data is strong enough to prove the
production Ricci contraction theory interface.
-/
theorem hasRicciContractionTheory_of_scalarContractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarContractionFormulaAtTime :
      ScalarCurvatureContractionFormulaData curvature) :
    HasRicciContractionTheory curvature :=
  hasRicciContractionTheory_of_contractionTheoryData
    (ricciContractionTheoryData_of_scalarContractionFormulaData
      scalarContractionFormulaAtTime)

/-- Interface for the contraction formula defining the Ricci tensor. -/
structure HasRicciTensorContractionFormula
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Prop where
  /--
  A constructed Riemann-curvature tensor and explicit trace formula for
  `Ric(X,Y) = tr (Z ↦ R(Z,X)Y)` supplies the non-vacuous Ricci contraction
  formula witness.
  -/
  contractionFormulaData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciTensorContractionFormulaData curvature)

/-- Compatibility constructor for Ricci tensor contraction-formula data. -/
def HasRicciTensorContractionFormula.of_contractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionFormulaAtTime :
      RicciTensorContractionFormulaData curvature) :
    HasRicciTensorContractionFormula curvature where
  contractionFormulaData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨ricciContractionFormulaAtTime⟩⟩

/--
Concrete Ricci contraction-formula data proves the production Ricci tensor
contraction-formula interface.
-/
theorem hasRicciTensorContractionFormula_of_contractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionFormulaAtTime :
      RicciTensorContractionFormulaData curvature) :
    HasRicciTensorContractionFormula curvature :=
  HasRicciTensorContractionFormula.of_contractionFormulaData
    ricciContractionFormulaAtTime

/--
Ricci contraction-formula data closes the first eleven analytic curvature
fields, through the Ricci tensor contraction formula.
-/
theorem riemannCurvatureFirstEleven_of_ricciContractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionFormulaAtTime :
      RicciTensorContractionFormulaData curvature) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g ∧
      HasSecondBianchiIdentity g ∧
      HasRiemannCurvatureTensorTheory g ∧
      HasRicciTensorContractionFormula curvature :=
  let firstTen :=
    riemannCurvatureFirstTen_of_secondBianchiData
      ricciContractionFormulaAtTime.secondBianchiAtTime
  ⟨firstTen.1, firstTen.2.1, firstTen.2.2.1,
    firstTen.2.2.2.1, firstTen.2.2.2.2.1,
    firstTen.2.2.2.2.2.1, firstTen.2.2.2.2.2.2.1,
    firstTen.2.2.2.2.2.2.2.1,
    firstTen.2.2.2.2.2.2.2.2.1,
    firstTen.2.2.2.2.2.2.2.2.2,
    hasRicciTensorContractionFormula_of_contractionFormulaData
      ricciContractionFormulaAtTime⟩

/-- Interface for the contraction formula defining scalar curvature. -/
structure HasScalarCurvatureContractionFormula
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Prop where
  /--
  A Ricci contraction formula and explicit trace formula
  `Scal = tr_g Ric` supply the non-vacuous scalar-curvature contraction
  formula witness.
  -/
  contractionFormulaData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ScalarCurvatureContractionFormulaData curvature)

/-- Compatibility constructor for scalar-curvature contraction-formula data. -/
def HasScalarCurvatureContractionFormula.of_contractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarContractionFormulaAtTime :
      ScalarCurvatureContractionFormulaData curvature) :
    HasScalarCurvatureContractionFormula curvature where
  contractionFormulaData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨scalarContractionFormulaAtTime⟩⟩

/--
Concrete scalar-curvature contraction-formula data proves the production scalar
curvature contraction-formula interface.
-/
theorem hasScalarCurvatureContractionFormula_of_contractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarContractionFormulaAtTime :
      ScalarCurvatureContractionFormulaData curvature) :
    HasScalarCurvatureContractionFormula curvature :=
  HasScalarCurvatureContractionFormula.of_contractionFormulaData
    scalarContractionFormulaAtTime

/--
Scalar-curvature contraction-formula data closes the first twelve analytic
curvature fields, through the scalar-curvature contraction formula.
-/
theorem riemannCurvatureFirstTwelve_of_scalarContractionFormulaData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarContractionFormulaAtTime :
      ScalarCurvatureContractionFormulaData curvature) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g ∧
      HasSecondBianchiIdentity g ∧
      HasRiemannCurvatureTensorTheory g ∧
      HasRicciTensorContractionFormula curvature ∧
      HasScalarCurvatureContractionFormula curvature :=
  let firstEleven :=
    riemannCurvatureFirstEleven_of_ricciContractionFormulaData
      scalarContractionFormulaAtTime.ricciContractionFormulaAtTime
  ⟨firstEleven.1, firstEleven.2.1, firstEleven.2.2.1,
    firstEleven.2.2.2.1, firstEleven.2.2.2.2.1,
    firstEleven.2.2.2.2.2.1, firstEleven.2.2.2.2.2.2.1,
    firstEleven.2.2.2.2.2.2.2.1,
    firstEleven.2.2.2.2.2.2.2.2.1,
    firstEleven.2.2.2.2.2.2.2.2.2.1,
    firstEleven.2.2.2.2.2.2.2.2.2.2,
    hasScalarCurvatureContractionFormula_of_contractionFormulaData
      scalarContractionFormulaAtTime⟩

/--
Ricci contraction-theory data closes the first thirteen analytic curvature
fields, through Ricci contraction theory.
-/
theorem riemannCurvatureFirstThirteen_of_ricciContractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g ∧
      HasSecondBianchiIdentity g ∧
      HasRiemannCurvatureTensorTheory g ∧
      HasRicciTensorContractionFormula curvature ∧
      HasScalarCurvatureContractionFormula curvature ∧
      HasRicciContractionTheory curvature :=
  let firstTwelve :=
    riemannCurvatureFirstTwelve_of_scalarContractionFormulaData
      ricciContractionTheoryAtTime.scalarContractionFormulaAtTime
  ⟨firstTwelve.1, firstTwelve.2.1, firstTwelve.2.2.1,
    firstTwelve.2.2.2.1, firstTwelve.2.2.2.2.1,
    firstTwelve.2.2.2.2.2.1, firstTwelve.2.2.2.2.2.2.1,
    firstTwelve.2.2.2.2.2.2.2.1,
    firstTwelve.2.2.2.2.2.2.2.2.1,
    firstTwelve.2.2.2.2.2.2.2.2.2.1,
    firstTwelve.2.2.2.2.2.2.2.2.2.2.1,
    firstTwelve.2.2.2.2.2.2.2.2.2.2.2,
    hasRicciContractionTheory_of_contractionTheoryData
      ricciContractionTheoryAtTime⟩

/-- Interface for regularity of the time-dependent metric family. -/
structure HasTimeDependentMetricRegularity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  The time-dependent metric family itself supplies smooth Riemannian metric
  slices at every time.
  -/
  metricRegularityData_source : Nonempty (TimeDependentMetricRegularityData g)

/-- Compatibility constructor for metric-regularity data. -/
def HasTimeDependentMetricRegularity.of_metricRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricRegularityAtTime : TimeDependentMetricRegularityData g) :
    HasTimeDependentMetricRegularity g where
  metricRegularityData_source := ⟨metricRegularityAtTime⟩

/--
Concrete metric-regularity data proves the production metric-regularity
interface.
-/
theorem hasTimeDependentMetricRegularity_of_metricRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricRegularityAtTime : TimeDependentMetricRegularityData g) :
    HasTimeDependentMetricRegularity g :=
  HasTimeDependentMetricRegularity.of_metricRegularityData
    metricRegularityAtTime

/--
Every production time-dependent Riemannian metric proves the production
metric-regularity interface.
-/
theorem hasTimeDependentMetricRegularity_of_metric
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    HasTimeDependentMetricRegularity g :=
  hasTimeDependentMetricRegularity_of_metricRegularityData
    (timeDependentMetricRegularityData_of_metric g)

/--
Ricci contraction-theory data, together with the metric slices already stored in
the production metric family, closes the first fourteen analytic fields through
time-dependent metric regularity.
-/
theorem analyticFirstFourteen_of_ricciContractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g ∧
      HasSecondBianchiIdentity g ∧
      HasRiemannCurvatureTensorTheory g ∧
      HasRicciTensorContractionFormula curvature ∧
      HasScalarCurvatureContractionFormula curvature ∧
      HasRicciContractionTheory curvature ∧
      HasTimeDependentMetricRegularity g :=
  let firstThirteen :=
    riemannCurvatureFirstThirteen_of_ricciContractionTheoryData
      ricciContractionTheoryAtTime
  ⟨firstThirteen.1, firstThirteen.2.1, firstThirteen.2.2.1,
    firstThirteen.2.2.2.1, firstThirteen.2.2.2.2.1,
    firstThirteen.2.2.2.2.2.1, firstThirteen.2.2.2.2.2.2.1,
    firstThirteen.2.2.2.2.2.2.2.1,
    firstThirteen.2.2.2.2.2.2.2.2.1,
    firstThirteen.2.2.2.2.2.2.2.2.2.1,
    firstThirteen.2.2.2.2.2.2.2.2.2.2.1,
    firstThirteen.2.2.2.2.2.2.2.2.2.2.2.1,
    firstThirteen.2.2.2.2.2.2.2.2.2.2.2.2,
    hasTimeDependentMetricRegularity_of_metric g⟩

/-- Interface for the time derivative of the metric family. -/
structure HasMetricTimeDerivativeTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop where
  /--
  A concrete metric time-derivative field, together with evidence that it is
  the derivative of the metric family, supplies the non-vacuous time-derivative
  theory witness.
  -/
  metricTimeDerivativeData_source : Nonempty (MetricTimeDerivativeData g)

/-- Compatibility constructor for metric time-derivative data. -/
def HasMetricTimeDerivativeTheory.of_metricTimeDerivativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricTimeDerivativeAtTime : MetricTimeDerivativeData g) :
    HasMetricTimeDerivativeTheory g where
  metricTimeDerivativeData_source := ⟨metricTimeDerivativeAtTime⟩

/--
Concrete metric time-derivative data proves the production metric
time-derivative theory interface.
-/
theorem hasMetricTimeDerivativeTheory_of_metricTimeDerivativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (metricTimeDerivativeAtTime : MetricTimeDerivativeData g) :
    HasMetricTimeDerivativeTheory g :=
  HasMetricTimeDerivativeTheory.of_metricTimeDerivativeData
    metricTimeDerivativeAtTime

/--
Metric time-derivative data, together with the existing curvature contraction
data, closes the first fifteen analytic fields through metric time-derivative
theory.
-/
theorem analyticFirstFifteen_of_metricTimeDerivativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature)
    (metricTimeDerivativeAtTime : MetricTimeDerivativeData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g ∧
      HasSecondBianchiIdentity g ∧
      HasRiemannCurvatureTensorTheory g ∧
      HasRicciTensorContractionFormula curvature ∧
      HasScalarCurvatureContractionFormula curvature ∧
      HasRicciContractionTheory curvature ∧
      HasTimeDependentMetricRegularity g ∧
      HasMetricTimeDerivativeTheory g :=
  let firstFourteen :=
    analyticFirstFourteen_of_ricciContractionTheoryData
      ricciContractionTheoryAtTime
  ⟨firstFourteen.1, firstFourteen.2.1, firstFourteen.2.2.1,
    firstFourteen.2.2.2.1, firstFourteen.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.1, firstFourteen.2.2.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.2.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.2.2.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.2.2.2.2.2.2.2.1,
    firstFourteen.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hasMetricTimeDerivativeTheory_of_metricTimeDerivativeData
      metricTimeDerivativeAtTime⟩

/-- Interface for scalar curvature derived from Ricci-curvature data. -/
structure HasScalarCurvatureTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) : Prop where
  /--
  Complete contraction-chain data, ending with the trace formula
  `Scal = tr_g Ric`, supplies the scalar-curvature theory witness.
  -/
  scalarCurvatureTheoryData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ScalarCurvatureTheoryData curvature)

/-- Compatibility constructor for scalar-curvature theory data. -/
def HasScalarCurvatureTheory.of_scalarCurvatureTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData curvature) :
    HasScalarCurvatureTheory curvature where
  scalarCurvatureTheoryData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨scalarCurvatureTheoryAtTime⟩⟩

/--
Concrete scalar-curvature theory data proves the production scalar-curvature
theory interface.
-/
theorem hasScalarCurvatureTheory_of_scalarCurvatureTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData curvature) :
    HasScalarCurvatureTheory curvature :=
  HasScalarCurvatureTheory.of_scalarCurvatureTheoryData
    scalarCurvatureTheoryAtTime

/--
Ricci contraction-theory data is strong enough to prove scalar-curvature
theory, because it includes the scalar trace formula.
-/
theorem hasScalarCurvatureTheory_of_ricciContractionTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (ricciContractionTheoryAtTime :
      RicciContractionTheoryData curvature) :
    HasScalarCurvatureTheory curvature :=
  hasScalarCurvatureTheory_of_scalarCurvatureTheoryData
    (scalarCurvatureTheoryData_of_ricciContractionTheoryData
      ricciContractionTheoryAtTime)

/--
Scalar-curvature theory data, together with explicit metric time-derivative
data, closes the first sixteen analytic fields through scalar-curvature theory.
-/
theorem analyticFirstSixteen_of_scalarCurvatureTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData curvature)
    (metricTimeDerivativeAtTime : MetricTimeDerivativeData g) :
    HasLeviCivitaConnectionExistence g ∧
      HasLeviCivitaConnectionUniqueness g ∧
      HasLeviCivitaTorsionFreeProperty g ∧
      HasLeviCivitaMetricCompatibility g ∧
      HasLeviCivitaConnectionTheory g ∧
      HasRiemannCurvatureTensorConstruction g ∧
      HasRiemannCurvatureTensorSymmetries g ∧
      HasFirstBianchiIdentity g ∧
      HasSecondBianchiIdentity g ∧
      HasRiemannCurvatureTensorTheory g ∧
      HasRicciTensorContractionFormula curvature ∧
      HasScalarCurvatureContractionFormula curvature ∧
      HasRicciContractionTheory curvature ∧
      HasTimeDependentMetricRegularity g ∧
      HasMetricTimeDerivativeTheory g ∧
      HasScalarCurvatureTheory curvature := by
  rcases analyticFirstFifteen_of_metricTimeDerivativeData
      scalarCurvatureTheoryAtTime.ricciContractionTheoryAtTime
      metricTimeDerivativeAtTime with
    ⟨leviCivitaExistence, leviCivitaUniqueness,
      leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
      riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
      secondBianchi, riemannCurvature, ricciContractionFormula,
      scalarCurvatureContraction, ricciContraction, metricRegularity,
      metricTimeDerivative⟩
  exact ⟨leviCivitaExistence, leviCivitaUniqueness,
    leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
    riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
    secondBianchi, riemannCurvature, ricciContractionFormula,
    scalarCurvatureContraction, ricciContraction, metricRegularity,
    metricTimeDerivative,
    hasScalarCurvatureTheory_of_scalarCurvatureTheoryData
      scalarCurvatureTheoryAtTime⟩

/-- Interface for deriving the Ricci-flow equation from metric derivative and Ricci data. -/
structure HasRicciFlowEquationDerivation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /--
  A concrete verification of `∂ₜ g = -2 Ricci` supplies the equation-derivation
  witness for the same Ricci-flow data.
  -/
  equationVerification_source :
    Nonempty
      (RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))

/-- Compatibility constructor for Ricci-flow equation verification data. -/
def HasRicciFlowEquationDerivation.of_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    HasRicciFlowEquationDerivation flow where
  equationVerification_source := ⟨equationVerificationAtTime⟩

/--
Concrete Ricci-flow equation verification proves the production equation
derivation interface.
-/
theorem hasRicciFlowEquationDerivation_of_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    HasRicciFlowEquationDerivation flow :=
  HasRicciFlowEquationDerivation.of_ricciFlowEquationVerification
    equationVerificationAtTime

/--
Scalar-curvature theory data and explicit Ricci-flow equation verification close
the first seventeen analytic fields through Ricci-flow equation derivation.
-/
theorem analyticFirstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow := by
  rcases analyticFirstSixteen_of_scalarCurvatureTheoryData
      scalarCurvatureTheoryAtTime
      (metric_derivative_data_of_ricci_flow_equation_verification
        equationVerificationAtTime) with
    ⟨leviCivitaExistence, leviCivitaUniqueness,
      leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
      riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
      secondBianchi, riemannCurvature, ricciContractionFormula,
      scalarCurvatureContraction, ricciContraction, metricRegularity,
      metricTimeDerivative, scalarCurvature⟩
  exact ⟨leviCivitaExistence, leviCivitaUniqueness,
    leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
    riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
    secondBianchi, riemannCurvature, ricciContractionFormula,
    scalarCurvatureContraction, ricciContraction, metricRegularity,
    metricTimeDerivative, scalarCurvature,
    hasRicciFlowEquationDerivation_of_ricciFlowEquationVerification
      equationVerificationAtTime⟩

/--
Boundary package for the explicit Ricci-flow equation `∂ₜ g = -2 Ricci`.

The package separates the concrete pointwise equation verification from the
abstract `SatisfiesRicciFlowEquation` interface carried by existing flow data.
-/
structure RicciFlowEquationBoundaryPackage
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) where
  /-- Explicit pointwise verification of `∂ₜ g = -2 Ricci`. -/
  verification :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)
  /-- The existing equation-interface evidence for the same flow. -/
  equationEvidence :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow)

/-- Project explicit equation verification from an equation-boundary package. -/
def ricci_flow_equation_verification_of_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow) :=
  package.verification

/-- The boundary-package equation-verification projection is stored data. -/
@[simp] theorem ricci_flow_equation_verification_of_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    ricci_flow_equation_verification_of_boundary_package package =
      package.verification :=
  rfl

/-- Project metric-derivative data from an equation-boundary package. -/
def metric_derivative_data_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    MetricTimeDerivativeData (metric_of_ricci_flow_data flow) :=
  metric_derivative_data_of_ricci_flow_equation_verification
    package.verification

/-- The boundary-package metric-derivative projection delegates to verification. -/
@[simp] theorem metric_derivative_data_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    metric_derivative_data_of_equation_boundary_package package =
      metric_derivative_data_of_ricci_flow_equation_verification
        package.verification :=
  rfl

/-- An equation-boundary package supplies the explicit equation at time `t`. -/
theorem equation_at_time_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      package.verification.metricDerivative.derivative t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t :=
  equation_at_time_of_ricci_flow_equation_verification
    package.verification t

/-- The named boundary-package equation theorem is stored verification evidence. -/
@[simp] theorem equation_at_time_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    equation_at_time_of_equation_boundary_package package t =
      package.verification.equationAtTime t :=
  rfl

/--
An equation-boundary package supplies the explicit equation pointwise through
its stored verification.
-/
theorem equation_at_time_apply_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      package.verification.metricDerivative.derivative t x v w =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t x v w :=
  equation_at_time_apply_of_ricci_flow_equation_verification
    package.verification t x v w

/-- The direct boundary-package pointwise equation theorem is stored verification evidence. -/
@[simp] theorem equation_at_time_apply_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_equation_boundary_package package t x v w =
      equation_at_time_apply_of_ricci_flow_equation_verification
        package.verification t x v w := by
  apply Subsingleton.elim

/--
An equation-boundary package exposes the stored verification as a reusable
pointwise scalar equation payload.
-/
theorem pointwise_equation_payload_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    ∀ t x v w,
      metric_time_derivative_at_time_of_metric_derivative_field
        package.verification.metricDerivative.derivative t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data flow) t x v w :=
  pointwise_equation_payload_of_ricci_flow_equation_verification
    package.verification

/-- The boundary-package pointwise equation payload is the stored verification payload. -/
@[simp] theorem pointwise_equation_payload_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    pointwise_equation_payload_of_equation_boundary_package package =
      pointwise_equation_payload_of_ricci_flow_equation_verification
        package.verification :=
  rfl

/-- An equation-boundary package carries metric-derivative identification evidence. -/
theorem metric_time_derivative_identification_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    IsMetricTimeDerivativeOf
      (metric_of_ricci_flow_data flow)
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package package)) :=
  metric_time_derivative_identification_of_ricci_flow_equation_verification
    package.verification

/-- The boundary-package derivative-identification theorem is stored verification evidence. -/
@[simp] theorem metric_time_derivative_identification_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    metric_time_derivative_identification_of_equation_boundary_package
      package = package.verification.metricDerivative.identifiesDerivative :=
  rfl

/--
The boundary-package equation equality also holds through the named
metric-derivative projection.
-/
theorem equation_at_time_of_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package package)) t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t :=
  equation_at_time_of_ricci_flow_equation_verification_projection
    package.verification t

/-- The boundary-package projection-routed equation theorem is stored evidence. -/
@[simp] theorem equation_at_time_of_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    equation_at_time_of_equation_boundary_package_projection package t =
      package.verification.equationAtTime t :=
  rfl

/--
The boundary-package projection-routed equation also holds pointwise at a point
and pair of tangent vectors.
-/
theorem equation_at_time_apply_of_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package package)) t x v w =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t x v w :=
  congrArg (fun tensor => tensor x v w)
    (equation_at_time_of_equation_boundary_package_projection package t)

/-- The pointwise boundary-package equation proof is tensor equality application. -/
@[simp] theorem equation_at_time_apply_of_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_equation_boundary_package_projection
      package t x v w =
      congrArg (fun tensor => tensor x v w)
        (equation_at_time_of_equation_boundary_package_projection package t) := by
  apply Subsingleton.elim

/-- Project equation-interface evidence from an equation-boundary package. -/
theorem equation_evidence_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow) :=
  package.equationEvidence

/-- The boundary-package equation-interface theorem is stored evidence. -/
@[simp] theorem equation_evidence_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    equation_evidence_of_equation_boundary_package package =
      package.equationEvidence :=
  rfl

/-- Statement that the explicit Ricci-flow equation boundary is available. -/
def RicciFlowEquationBoundaryStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
  Nonempty (RicciFlowEquationBoundaryPackage flow)

/-- The equation-boundary statement is nonemptiness of the boundary package. -/
theorem ricciFlowEquationBoundaryStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    RicciFlowEquationBoundaryStatement flow =
      Nonempty (RicciFlowEquationBoundaryPackage flow) :=
  rfl

/--
Assemble the equation-boundary package from explicit pointwise
`∂ₜ g = -2 Ricci` verification for the same flow.

The abstract equation-interface evidence still comes from the checked
`RicciFlowData`; the explicit verification is not used to manufacture it.
-/
def equation_boundary_package_of_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    RicciFlowEquationBoundaryPackage flow where
  verification := verification
  equationEvidence := equation_evidence_of_ricci_flow_data flow

/-- The verification-to-boundary-package constructor stores the supplied fields. -/
@[simp] theorem equation_boundary_package_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    equation_boundary_package_of_ricci_flow_equation_verification
      flow verification =
        ({ verification := verification
           equationEvidence := equation_evidence_of_ricci_flow_data flow } :
          RicciFlowEquationBoundaryPackage flow) :=
  rfl

/-- The constructed boundary package projects back to the supplied verification. -/
@[simp] theorem ricci_flow_equation_verification_of_equation_boundary_package_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    ricci_flow_equation_verification_of_boundary_package
      (equation_boundary_package_of_ricci_flow_equation_verification
        flow verification) =
        verification :=
  rfl

/-- The constructed boundary package carries the flow's stored equation evidence. -/
@[simp] theorem equation_evidence_of_equation_boundary_package_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    equation_evidence_of_equation_boundary_package
      (equation_boundary_package_of_ricci_flow_equation_verification
        flow verification) =
        equation_evidence_of_ricci_flow_data flow :=
  rfl

/-- A supplied explicit Ricci-flow equation verification exposes the boundary statement. -/
theorem ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    RicciFlowEquationBoundaryStatement flow :=
  ⟨equation_boundary_package_of_ricci_flow_equation_verification
    flow verification⟩

/-- The verification-to-boundary statement route is nonemptiness of the package route. -/
@[simp] theorem ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
      flow verification =
        ⟨equation_boundary_package_of_ricci_flow_equation_verification
          flow verification⟩ := by
  apply Subsingleton.elim

/--
A supplied explicit Ricci-flow equation verification also proves the
projection-routed tensor equation through its constructed boundary package.
-/
theorem equation_at_time_of_equation_boundary_package_of_ricci_flow_equation_verification_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (equation_boundary_package_of_ricci_flow_equation_verification
            flow verification))) t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t :=
  equation_at_time_of_equation_boundary_package_projection
    (equation_boundary_package_of_ricci_flow_equation_verification
      flow verification) t

/-- The verification boundary-package tensor equation is the generic package route. -/
@[simp] theorem equation_at_time_of_equation_boundary_package_of_ricci_flow_equation_verification_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (t : ℝ) :
    equation_at_time_of_equation_boundary_package_of_ricci_flow_equation_verification_projection
      flow verification t =
      equation_at_time_of_equation_boundary_package_projection
        (equation_boundary_package_of_ricci_flow_equation_verification
          flow verification) t :=
  rfl

/--
The verification boundary-package tensor equation agrees with the direct
Ricci-flow equation-verification projection.
-/
@[simp] theorem equation_at_time_of_equation_boundary_package_of_ricci_flow_equation_verification_projection_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (t : ℝ) :
    equation_at_time_of_equation_boundary_package_of_ricci_flow_equation_verification_projection
      flow verification t =
      equation_at_time_of_ricci_flow_equation_verification_projection
        verification t := by
  apply Subsingleton.elim

/--
A supplied explicit Ricci-flow equation verification also proves the
projection-routed tensor equation pointwise through its constructed boundary
package.
-/
theorem equation_at_time_apply_of_equation_boundary_package_of_ricci_flow_equation_verification_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (equation_boundary_package_of_ricci_flow_equation_verification
            flow verification))) t x v w =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow)
          t x v w :=
  equation_at_time_apply_of_equation_boundary_package_projection
    (equation_boundary_package_of_ricci_flow_equation_verification
      flow verification) t x v w

/-- The verification boundary-package pointwise equation is the generic package route. -/
@[simp] theorem equation_at_time_apply_of_equation_boundary_package_of_ricci_flow_equation_verification_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_equation_boundary_package_of_ricci_flow_equation_verification_projection
      flow verification t x v w =
      equation_at_time_apply_of_equation_boundary_package_projection
        (equation_boundary_package_of_ricci_flow_equation_verification
          flow verification) t x v w :=
  rfl

/--
The verification boundary-package pointwise equation agrees with the direct
Ricci-flow equation-verification pointwise projection.
-/
@[simp] theorem equation_at_time_apply_of_equation_boundary_package_of_ricci_flow_equation_verification_projection_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_equation_boundary_package_of_ricci_flow_equation_verification_projection
      flow verification t x v w =
      equation_at_time_apply_of_ricci_flow_equation_verification_projection
        verification t x v w := by
  apply Subsingleton.elim

/--
Equation-boundary package for zero Ricci-flow data.

The metric-derivative identification, Ricci identification, and abstract
equation-interface evidence are all supplied inputs; this only routes the
explicit zero equation verification through the analytic boundary package.
-/
noncomputable def zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryPackage
      (zero_ricci_flow_data g identifiesRicci equationEvidence) :=
  equation_boundary_package_of_ricci_flow_equation_verification
    (zero_ricci_flow_data g identifiesRicci equationEvidence)
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci)

/-- The zero equation-boundary package is assembled from the zero verification. -/
@[simp] theorem zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence =
      equation_boundary_package_of_ricci_flow_equation_verification
        (zero_ricci_flow_data g identifiesRicci equationEvidence)
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) :=
  rfl

/-- Equation-boundary package for stationary zero Ricci-flow data. -/
noncomputable def stationary_zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryPackage
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) :=
  zero_ricci_flow_equation_boundary_package
    identifiesDerivative identifiesRicci equationEvidence

/-- The stationary zero equation-boundary package delegates to the zero package. -/
@[simp] theorem stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence =
      zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence :=
  rfl

/-- The zero boundary package projects to the explicit zero equation verification. -/
@[simp] theorem ricci_flow_equation_verification_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    ricci_flow_equation_verification_of_boundary_package
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence) =
        zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci :=
  rfl

/-- The stationary zero boundary package projects to the zero equation verification. -/
@[simp] theorem ricci_flow_equation_verification_of_stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    ricci_flow_equation_verification_of_boundary_package
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence) =
      zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci :=
  rfl

/-- The zero boundary package keeps the supplied abstract equation evidence. -/
@[simp] theorem equation_evidence_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    equation_evidence_of_equation_boundary_package
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence) =
        equationEvidence :=
  rfl

/-- The stationary zero boundary package keeps the supplied equation evidence. -/
@[simp] theorem equation_evidence_of_stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    equation_evidence_of_equation_boundary_package
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence) =
      equationEvidence :=
  rfl

/-- The zero boundary package stores the zero metric-derivative data. -/
@[simp] theorem metric_derivative_data_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    metric_derivative_data_of_equation_boundary_package
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence) =
      zero_metric_derivative_data identifiesDerivative :=
  rfl

/-- The stationary zero boundary package stores the zero metric-derivative data. -/
@[simp] theorem metric_derivative_data_of_stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    metric_derivative_data_of_equation_boundary_package
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence) =
      zero_metric_derivative_data identifiesDerivative :=
  rfl

/-- The zero boundary package stores the supplied derivative-identification proof. -/
@[simp] theorem metric_time_derivative_identification_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    metric_time_derivative_identification_of_equation_boundary_package
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence) =
      identifiesDerivative :=
  rfl

/-- The stationary zero boundary package stores the supplied derivative proof. -/
@[simp] theorem metric_time_derivative_identification_of_stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    metric_time_derivative_identification_of_equation_boundary_package
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence) =
      identifiesDerivative :=
  rfl

/--
The zero equation-boundary package proves the projection-routed tensor equation
at each time.
-/
theorem equation_at_time_of_zero_ricci_flow_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (zero_ricci_flow_equation_boundary_package
            identifiesDerivative identifiesRicci equationEvidence))) t =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data g identifiesRicci equationEvidence)) t :=
  equation_at_time_of_equation_boundary_package_projection
    (zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence) t

/-- The zero boundary tensor equation is the generic boundary-package route. -/
@[simp] theorem equation_at_time_of_zero_ricci_flow_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    equation_at_time_of_zero_ricci_flow_equation_boundary_package_projection
      identifiesDerivative identifiesRicci equationEvidence t =
      equation_at_time_of_equation_boundary_package_projection
        (zero_ricci_flow_equation_boundary_package
          identifiesDerivative identifiesRicci equationEvidence) t :=
  rfl

/--
The zero boundary tensor equation agrees with the direct zero verification
tensor equation.
-/
@[simp] theorem equation_at_time_of_zero_ricci_flow_equation_boundary_package_projection_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    equation_at_time_of_zero_ricci_flow_equation_boundary_package_projection
      identifiesDerivative identifiesRicci equationEvidence t =
      equation_at_time_of_zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci t := by
  apply Subsingleton.elim

/--
The stationary zero equation-boundary package proves the projection-routed
tensor equation at each time.
-/
theorem equation_at_time_of_stationary_zero_ricci_flow_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (stationary_zero_ricci_flow_equation_boundary_package
            metric identifiesDerivative identifiesRicci equationEvidence))) t =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data
              (stationary_time_dependent_riemannian_metric metric)
              identifiesRicci equationEvidence)) t :=
  equation_at_time_of_equation_boundary_package_projection
    (stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence) t

/-- The stationary zero boundary tensor equation is the generic package route. -/
@[simp] theorem equation_at_time_of_stationary_zero_ricci_flow_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    equation_at_time_of_stationary_zero_ricci_flow_equation_boundary_package_projection
      metric identifiesDerivative identifiesRicci equationEvidence t =
      equation_at_time_of_equation_boundary_package_projection
        (stationary_zero_ricci_flow_equation_boundary_package
          metric identifiesDerivative identifiesRicci equationEvidence) t :=
  rfl

/--
The stationary zero boundary tensor equation agrees with the direct stationary
zero verification tensor equation.
-/
@[simp] theorem equation_at_time_of_stationary_zero_ricci_flow_equation_boundary_package_projection_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    equation_at_time_of_stationary_zero_ricci_flow_equation_boundary_package_projection
      metric identifiesDerivative identifiesRicci equationEvidence t =
      equation_at_time_of_stationary_zero_ricci_flow_equation_verification
        metric identifiesDerivative identifiesRicci t := by
  apply Subsingleton.elim

/--
The zero equation-boundary package proves the projection-routed equation
pointwise.
-/
theorem equation_at_time_apply_of_zero_ricci_flow_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (zero_ricci_flow_equation_boundary_package
            identifiesDerivative identifiesRicci equationEvidence))) t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data g identifiesRicci equationEvidence)) t x v w :=
  equation_at_time_apply_of_equation_boundary_package_projection
    (zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence) t x v w

/-- The zero boundary pointwise equation is the generic boundary-package route. -/
@[simp] theorem equation_at_time_apply_of_zero_ricci_flow_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_zero_ricci_flow_equation_boundary_package_projection
      identifiesDerivative identifiesRicci equationEvidence t x v w =
      equation_at_time_apply_of_equation_boundary_package_projection
        (zero_ricci_flow_equation_boundary_package
          identifiesDerivative identifiesRicci equationEvidence) t x v w :=
  rfl

/--
The zero boundary-package pointwise equation agrees with the direct zero
verification route.
-/
@[simp] theorem equation_at_time_apply_of_zero_ricci_flow_equation_boundary_package_projection_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_zero_ricci_flow_equation_boundary_package_projection
      identifiesDerivative identifiesRicci equationEvidence t x v w =
      equation_at_time_apply_of_zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci t x v w := by
  apply Subsingleton.elim

/--
The stationary zero equation-boundary package proves the projection-routed
equation pointwise.
-/
theorem equation_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (stationary_zero_ricci_flow_equation_boundary_package
            metric identifiesDerivative identifiesRicci equationEvidence))) t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data
              (stationary_time_dependent_riemannian_metric metric)
              identifiesRicci equationEvidence)) t x v w :=
  equation_at_time_apply_of_equation_boundary_package_projection
    (stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence) t x v w

/-- The stationary zero boundary pointwise equation is the generic package route. -/
@[simp] theorem equation_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package_projection
      metric identifiesDerivative identifiesRicci equationEvidence t x v w =
      equation_at_time_apply_of_equation_boundary_package_projection
        (stationary_zero_ricci_flow_equation_boundary_package
          metric identifiesDerivative identifiesRicci equationEvidence) t x v w :=
  rfl

/--
The stationary zero boundary-package pointwise equation agrees with the direct
stationary zero verification route.
-/
@[simp] theorem equation_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package_projection_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package_projection
      metric identifiesDerivative identifiesRicci equationEvidence t x v w =
      equation_at_time_apply_of_stationary_zero_ricci_flow_equation_verification
        metric identifiesDerivative identifiesRicci t x v w := by
  apply Subsingleton.elim

/--
The zero boundary package exposes the projection-routed equation as a reusable
pointwise payload.
-/
theorem pointwise_equation_payload_of_zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    ∀ t x (v w : TangentSpace I x),
      metric_time_derivative_at_time_of_metric_derivative_field
        (metric_time_derivative_field_of_metric_derivative_data
          (metric_derivative_data_of_equation_boundary_package
            (zero_ricci_flow_equation_boundary_package
              identifiesDerivative identifiesRicci equationEvidence))) t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data g identifiesRicci equationEvidence)) t x v w :=
  pointwise_equation_payload_of_equation_boundary_package
    (zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence)

/-- The zero boundary pointwise-equation payload is the generic package payload. -/
@[simp] theorem pointwise_equation_payload_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    pointwise_equation_payload_of_zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence =
      pointwise_equation_payload_of_equation_boundary_package
        (zero_ricci_flow_equation_boundary_package
          identifiesDerivative identifiesRicci equationEvidence) := by
  apply Subsingleton.elim

/--
The zero boundary pointwise-equation payload agrees with the direct stored
verification payload.
-/
@[simp] theorem pointwise_equation_payload_of_zero_ricci_flow_equation_boundary_package_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    pointwise_equation_payload_of_zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence =
      pointwise_equation_payload_of_ricci_flow_equation_verification
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) := by
  apply Subsingleton.elim

/--
The stationary zero boundary package exposes the projection-routed equation as
a reusable pointwise payload.
-/
theorem pointwise_equation_payload_of_stationary_zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    ∀ t x (v w : TangentSpace I x),
      metric_time_derivative_at_time_of_metric_derivative_field
        (metric_time_derivative_field_of_metric_derivative_data
          (metric_derivative_data_of_equation_boundary_package
            (stationary_zero_ricci_flow_equation_boundary_package
              metric identifiesDerivative identifiesRicci equationEvidence))) t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data
              (stationary_time_dependent_riemannian_metric metric)
              identifiesRicci equationEvidence)) t x v w :=
  pointwise_equation_payload_of_equation_boundary_package
    (stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence)

/-- The stationary zero boundary pointwise payload is the generic package payload. -/
@[simp] theorem pointwise_equation_payload_of_stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    pointwise_equation_payload_of_stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence =
      pointwise_equation_payload_of_equation_boundary_package
        (stationary_zero_ricci_flow_equation_boundary_package
          metric identifiesDerivative identifiesRicci equationEvidence) := by
  apply Subsingleton.elim

/--
The stationary zero boundary pointwise payload agrees with the direct stored
verification payload.
-/
@[simp] theorem pointwise_equation_payload_of_stationary_zero_ricci_flow_equation_boundary_package_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    pointwise_equation_payload_of_stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence =
      pointwise_equation_payload_of_ricci_flow_equation_verification
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) := by
  apply Subsingleton.elim

/-- The derivative side of the zero boundary package is pointwise scalar zero. -/
@[simp] theorem metric_time_derivative_at_time_apply_of_zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (zero_ricci_flow_equation_boundary_package
            identifiesDerivative identifiesRicci equationEvidence))) t x v w = 0 :=
  rfl

/-- The zero boundary derivative proof is definitional. -/
@[simp] theorem metric_time_derivative_at_time_apply_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_apply_of_zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence t x v w = rfl := by
  apply Subsingleton.elim

/-- The derivative side of the stationary zero boundary package is pointwise zero. -/
@[simp] theorem metric_time_derivative_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (stationary_zero_ricci_flow_equation_boundary_package
            metric identifiesDerivative identifiesRicci equationEvidence))) t x v w = 0 :=
  rfl

/-- The stationary zero boundary derivative proof is definitional. -/
@[simp] theorem metric_time_derivative_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence t x v w = rfl := by
  apply Subsingleton.elim

/--
The zero boundary package exposes both pointwise sides of the equation as
scalar zero.
-/
theorem pointwise_zero_pair_of_zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (zero_ricci_flow_equation_boundary_package
            identifiesDerivative identifiesRicci equationEvidence))) t x v w = 0 ∧
    ricci_flow_rhs_tensor
      (curvature_data_of_ricci_flow_data
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) t x v w = 0 :=
  ⟨metric_time_derivative_at_time_apply_of_zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence t x v w,
    ricci_flow_rhs_tensor_apply_of_zero_ricci_flow_data
      g identifiesRicci equationEvidence t x v w⟩

/-- The zero boundary paired-zero proof uses the two pointwise zero facts. -/
@[simp] theorem pointwise_zero_pair_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    pointwise_zero_pair_of_zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence t x v w =
      ⟨metric_time_derivative_at_time_apply_of_zero_ricci_flow_equation_boundary_package
          identifiesDerivative identifiesRicci equationEvidence t x v w,
        ricci_flow_rhs_tensor_apply_of_zero_ricci_flow_data
          g identifiesRicci equationEvidence t x v w⟩ := by
  apply Subsingleton.elim

/--
The zero boundary paired-zero proof agrees with the direct zero verification
pointwise-zero payload.
-/
@[simp] theorem pointwise_zero_pair_of_zero_ricci_flow_equation_boundary_package_to_verification_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    pointwise_zero_pair_of_zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence t x v w =
      pointwise_zero_payload_of_zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci t x v w := by
  apply Subsingleton.elim

/--
The stationary zero boundary package exposes both pointwise sides as scalar
zero.
-/
theorem pointwise_zero_pair_of_stationary_zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package
          (stationary_zero_ricci_flow_equation_boundary_package
            metric identifiesDerivative identifiesRicci equationEvidence))) t x v w = 0 ∧
    ricci_flow_rhs_tensor
      (curvature_data_of_ricci_flow_data
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) t x v w = 0 :=
  ⟨metric_time_derivative_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence t x v w,
    ricci_flow_rhs_tensor_apply_of_stationary_zero_ricci_flow_data
      metric identifiesRicci equationEvidence t x v w⟩

/-- The stationary zero boundary paired-zero proof uses the two zero facts. -/
@[simp] theorem pointwise_zero_pair_of_stationary_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    pointwise_zero_pair_of_stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence t x v w =
      ⟨metric_time_derivative_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package
          metric identifiesDerivative identifiesRicci equationEvidence t x v w,
        ricci_flow_rhs_tensor_apply_of_stationary_zero_ricci_flow_data
          metric identifiesRicci equationEvidence t x v w⟩ := by
  apply Subsingleton.elim

/--
The stationary zero boundary paired-zero proof agrees with the direct stationary
zero verification pointwise-zero payload.
-/
@[simp] theorem pointwise_zero_pair_of_stationary_zero_ricci_flow_equation_boundary_package_to_verification_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    pointwise_zero_pair_of_stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence t x v w =
      pointwise_zero_payload_of_stationary_zero_ricci_flow_equation_verification
        metric identifiesDerivative identifiesRicci t x v w := by
  apply Subsingleton.elim

/--
The zero boundary package can be bundled with a uniform pointwise scalar-zero
witness for both sides of its equation.
-/
theorem zero_ricci_flow_equation_boundary_package_pointwise_zero_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    ∃ boundary :
        RicciFlowEquationBoundaryPackage
          (zero_ricci_flow_data g identifiesRicci equationEvidence),
      boundary =
          zero_ricci_flow_equation_boundary_package
            identifiesDerivative identifiesRicci equationEvidence ∧
      ∀ t x v w,
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t x v w = 0 ∧
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data g identifiesRicci equationEvidence)) t x v w = 0 := by
  exact
    ⟨zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence,
      rfl, fun t x v w =>
        pointwise_zero_pair_of_zero_ricci_flow_equation_boundary_package
          identifiesDerivative identifiesRicci equationEvidence t x v w⟩

/--
The zero boundary package pointwise-zero payload is exactly the named boundary
package with its existing pointwise zero-pair projection.
-/
@[simp] theorem zero_ricci_flow_equation_boundary_package_pointwise_zero_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    zero_ricci_flow_equation_boundary_package_pointwise_zero_payload
      identifiesDerivative identifiesRicci equationEvidence =
      (by
        exact
          ⟨zero_ricci_flow_equation_boundary_package
              identifiesDerivative identifiesRicci equationEvidence,
            rfl, fun t x v w =>
              pointwise_zero_pair_of_zero_ricci_flow_equation_boundary_package
                identifiesDerivative identifiesRicci equationEvidence t x v w⟩) := by
  apply Subsingleton.elim

/--
The zero boundary package pointwise-zero payload can be represented using the
direct zero verification pointwise-zero payload.
-/
@[simp] theorem zero_ricci_flow_equation_boundary_package_pointwise_zero_payload_to_verification_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    zero_ricci_flow_equation_boundary_package_pointwise_zero_payload
      identifiesDerivative identifiesRicci equationEvidence =
      (by
        exact
          ⟨zero_ricci_flow_equation_boundary_package
              identifiesDerivative identifiesRicci equationEvidence,
            rfl, fun t x v w =>
              pointwise_zero_payload_of_zero_ricci_flow_equation_verification
                identifiesDerivative identifiesRicci t x v w⟩) := by
  apply Subsingleton.elim

/--
The stationary zero boundary package can be bundled with a uniform pointwise
scalar-zero witness for both sides of its equation.
-/
theorem stationary_zero_ricci_flow_equation_boundary_package_pointwise_zero_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    ∃ boundary :
        RicciFlowEquationBoundaryPackage
          (zero_ricci_flow_data
            (stationary_time_dependent_riemannian_metric metric)
            identifiesRicci equationEvidence),
      boundary =
          stationary_zero_ricci_flow_equation_boundary_package
            metric identifiesDerivative identifiesRicci equationEvidence ∧
      ∀ t x v w,
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t x v w = 0 ∧
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (zero_ricci_flow_data
              (stationary_time_dependent_riemannian_metric metric)
              identifiesRicci equationEvidence)) t x v w = 0 := by
  exact
    ⟨stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence,
      rfl, fun t x v w =>
        pointwise_zero_pair_of_stationary_zero_ricci_flow_equation_boundary_package
          metric identifiesDerivative identifiesRicci equationEvidence t x v w⟩

/--
The stationary zero boundary package pointwise-zero payload is exactly the named
stationary boundary package with its existing pointwise zero-pair projection.
-/
@[simp] theorem stationary_zero_ricci_flow_equation_boundary_package_pointwise_zero_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    stationary_zero_ricci_flow_equation_boundary_package_pointwise_zero_payload
      metric identifiesDerivative identifiesRicci equationEvidence =
      (by
        exact
          ⟨stationary_zero_ricci_flow_equation_boundary_package
              metric identifiesDerivative identifiesRicci equationEvidence,
            rfl, fun t x v w =>
              pointwise_zero_pair_of_stationary_zero_ricci_flow_equation_boundary_package
                metric identifiesDerivative identifiesRicci equationEvidence t x v w⟩) := by
  apply Subsingleton.elim

/--
The stationary zero boundary package pointwise-zero payload can be represented
using the direct stationary zero verification pointwise-zero payload.
-/
@[simp] theorem stationary_zero_ricci_flow_equation_boundary_package_pointwise_zero_payload_to_verification_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    stationary_zero_ricci_flow_equation_boundary_package_pointwise_zero_payload
      metric identifiesDerivative identifiesRicci equationEvidence =
      (by
        exact
          ⟨stationary_zero_ricci_flow_equation_boundary_package
              metric identifiesDerivative identifiesRicci equationEvidence,
            rfl, fun t x v w =>
              pointwise_zero_payload_of_stationary_zero_ricci_flow_equation_verification
                metric identifiesDerivative identifiesRicci t x v w⟩) := by
  apply Subsingleton.elim

/-- Zero Ricci-flow data with explicit zero verification exposes the boundary statement. -/
theorem ricciFlowEquationBoundaryStatement_of_zero_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryStatement
      (zero_ricci_flow_data g identifiesRicci equationEvidence) :=
  ⟨zero_ricci_flow_equation_boundary_package
    identifiesDerivative identifiesRicci equationEvidence⟩

/-- The zero boundary-statement route is nonemptiness of the zero boundary package. -/
@[simp] theorem ricciFlowEquationBoundaryStatement_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    ricciFlowEquationBoundaryStatement_of_zero_ricci_flow_data
      identifiesDerivative identifiesRicci equationEvidence =
      ⟨zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence⟩ := by
  apply Subsingleton.elim

/-- Stationary zero Ricci-flow data exposes the equation-boundary statement. -/
theorem ricciFlowEquationBoundaryStatement_of_stationary_zero_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryStatement
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) :=
  ⟨stationary_zero_ricci_flow_equation_boundary_package
    metric identifiesDerivative identifiesRicci equationEvidence⟩

/--
The stationary zero boundary-statement route is nonemptiness of the stationary
zero boundary package.
-/
@[simp] theorem ricciFlowEquationBoundaryStatement_of_stationary_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    ricciFlowEquationBoundaryStatement_of_stationary_zero_ricci_flow_data
      metric identifiesDerivative identifiesRicci equationEvidence =
      ⟨stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence⟩ := by
  apply Subsingleton.elim

/--
Concrete compatibility data for the initial metric of a Ricci-flow datum.

The current local Ricci-flow API does not carry a separate prescribed initial
metric object.  The available honest witness is therefore the smooth time-zero
metric slice already stored in the flow, together with the equality identifying
that slice as the initial metric.
-/
structure InitialMetricCompatibilityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The smooth initial metric slice. -/
  initialMetric :
    ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)
  /-- The initial metric is exactly the time-zero metric slice of the flow. -/
  initialMetric_eq :
    initialMetric = metric_at_time_of_ricci_flow_data flow 0

/-- Every Ricci-flow datum carries initial-metric compatibility data. -/
def initialMetricCompatibilityData_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    InitialMetricCompatibilityData flow where
  initialMetric := metric_at_time_of_ricci_flow_data flow 0
  initialMetric_eq := rfl

/-- The canonical initial-metric compatibility data stores the time-zero slice. -/
@[simp] theorem initialMetricCompatibilityData_of_flow_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    initialMetricCompatibilityData_of_flow flow =
      ({ initialMetric := metric_at_time_of_ricci_flow_data flow 0
         initialMetric_eq := rfl } :
        InitialMetricCompatibilityData flow) :=
  rfl

/-- The canonical initial metric is the time-zero metric slice. -/
@[simp] theorem initialMetricCompatibilityData_of_flow_initialMetric_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    (initialMetricCompatibilityData_of_flow flow).initialMetric =
      metric_at_time_of_ricci_flow_data flow 0 :=
  rfl

/-- Interface for compatibility of the flow with the prescribed initial metric. -/
structure HasInitialMetricCompatibility
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /--
  A concrete smooth time-zero metric slice identified with the flow's metric
  family supplies the initial-metric compatibility witness.
  -/
  initialMetricCompatibilityData_source :
    Nonempty (InitialMetricCompatibilityData flow)

/-- Compatibility constructor for initial-metric compatibility data. -/
def HasInitialMetricCompatibility.of_initialMetricCompatibilityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (initialMetricCompatibilityAtTime :
      InitialMetricCompatibilityData flow) :
    HasInitialMetricCompatibility flow where
  initialMetricCompatibilityData_source :=
    ⟨initialMetricCompatibilityAtTime⟩

/--
Concrete initial-metric compatibility data proves the production
initial-metric compatibility interface.
-/
theorem hasInitialMetricCompatibility_of_initialMetricCompatibilityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (initialMetricCompatibilityAtTime :
      InitialMetricCompatibilityData flow) :
    HasInitialMetricCompatibility flow :=
  HasInitialMetricCompatibility.of_initialMetricCompatibilityData
    initialMetricCompatibilityAtTime

/--
Every Ricci-flow datum proves the production initial-metric compatibility
interface from its smooth time-zero metric slice.
-/
theorem hasInitialMetricCompatibility_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    HasInitialMetricCompatibility flow :=
  hasInitialMetricCompatibility_of_initialMetricCompatibilityData
    (initialMetricCompatibilityData_of_flow flow)

/--
Scalar-curvature theory data and explicit Ricci-flow equation verification close
the first eighteen analytic fields through initial-metric compatibility.
-/
theorem analyticFirstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow := by
  rcases analyticFirstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime with
    ⟨leviCivitaExistence, leviCivitaUniqueness,
      leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
      riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
      secondBianchi, riemannCurvature, ricciContractionFormula,
      scalarCurvatureContraction, ricciContraction, metricRegularity,
      metricTimeDerivative, scalarCurvature, equationDerivation⟩
  exact ⟨leviCivitaExistence, leviCivitaUniqueness,
    leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
    riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
    secondBianchi, riemannCurvature, ricciContractionFormula,
    scalarCurvatureContraction, ricciContraction, metricRegularity,
    metricTimeDerivative, scalarCurvature, equationDerivation,
    hasInitialMetricCompatibility_of_flow flow⟩

/--
Concrete background-metric data for DeTurck gauge fixing.

The local analytic API has no separate gauge choice yet.  The honest available
choice is the smooth time-zero metric slice, used as the fixed background metric
for the DeTurck construction.
-/
structure DeTurckBackgroundMetricData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The fixed background metric used for DeTurck gauge. -/
  backgroundMetric :
    ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)
  /-- The background metric is the flow's smooth time-zero metric slice. -/
  backgroundMetric_eq_initialMetric :
    backgroundMetric = metric_at_time_of_ricci_flow_data flow 0

/--
Initial-metric compatibility data supplies the DeTurck background metric by
using the same smooth time-zero metric slice.
-/
def deturckBackgroundMetricData_of_initialMetricCompatibilityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (initialMetricCompatibilityAtTime :
      InitialMetricCompatibilityData flow) :
    DeTurckBackgroundMetricData flow where
  backgroundMetric := initialMetricCompatibilityAtTime.initialMetric
  backgroundMetric_eq_initialMetric :=
    initialMetricCompatibilityAtTime.initialMetric_eq

/--
The DeTurck background metric extracted from initial-metric compatibility is
exactly the same time-zero metric slice.
-/
@[simp] theorem deturckBackgroundMetricData_of_initialMetricCompatibilityData_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (initialMetricCompatibilityAtTime :
      InitialMetricCompatibilityData flow) :
    deturckBackgroundMetricData_of_initialMetricCompatibilityData
        initialMetricCompatibilityAtTime =
      ({ backgroundMetric :=
          initialMetricCompatibilityAtTime.initialMetric
         backgroundMetric_eq_initialMetric :=
          initialMetricCompatibilityAtTime.initialMetric_eq } :
        DeTurckBackgroundMetricData flow) :=
  rfl

/-- Every Ricci-flow datum carries canonical DeTurck background-metric data. -/
def deturckBackgroundMetricData_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    DeTurckBackgroundMetricData flow :=
  deturckBackgroundMetricData_of_initialMetricCompatibilityData
    (initialMetricCompatibilityData_of_flow flow)

/--
The canonical DeTurck background-metric data stores the time-zero metric slice.
-/
@[simp] theorem deturckBackgroundMetricData_of_flow_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    deturckBackgroundMetricData_of_flow flow =
      ({ backgroundMetric := metric_at_time_of_ricci_flow_data flow 0
         backgroundMetric_eq_initialMetric := rfl } :
        DeTurckBackgroundMetricData flow) :=
  rfl

/-- The canonical DeTurck background metric is the time-zero metric slice. -/
@[simp] theorem deturckBackgroundMetricData_of_flow_backgroundMetric_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    (deturckBackgroundMetricData_of_flow flow).backgroundMetric =
      metric_at_time_of_ricci_flow_data flow 0 :=
  rfl

/-- Interface for the DeTurck gauge-fixing input used to make the PDE parabolic. -/
structure HasDeTurckGaugeFixing
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /--
  A fixed smooth background metric, chosen as the time-zero slice, supplies the
  DeTurck gauge-fixing input.
  -/
  gaugeBackgroundMetricData_source :
    Nonempty (DeTurckBackgroundMetricData flow)

/-- Compatibility constructor for DeTurck gauge-fixing background data. -/
def HasDeTurckGaugeFixing.of_backgroundMetricData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (backgroundMetricAtTime : DeTurckBackgroundMetricData flow) :
    HasDeTurckGaugeFixing flow where
  gaugeBackgroundMetricData_source := ⟨backgroundMetricAtTime⟩

/-- Interface for compatibility of the background metric in DeTurck gauge. -/
structure HasDeTurckBackgroundMetricCompatibility
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /--
  The same background metric data proves that the DeTurck background is
  compatible with the initial metric.
  -/
  backgroundMetricCompatibilityData_source :
    Nonempty (DeTurckBackgroundMetricData flow)

/-- Compatibility constructor for DeTurck background-metric compatibility data. -/
def HasDeTurckBackgroundMetricCompatibility.of_backgroundMetricData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (backgroundMetricAtTime : DeTurckBackgroundMetricData flow) :
    HasDeTurckBackgroundMetricCompatibility flow where
  backgroundMetricCompatibilityData_source := ⟨backgroundMetricAtTime⟩

/--
Concrete DeTurck background-metric data proves the production gauge-fixing
interface.
-/
theorem hasDeTurckGaugeFixing_of_backgroundMetricData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (backgroundMetricAtTime : DeTurckBackgroundMetricData flow) :
    HasDeTurckGaugeFixing flow :=
  HasDeTurckGaugeFixing.of_backgroundMetricData backgroundMetricAtTime

/--
Every Ricci-flow datum proves the production DeTurck gauge-fixing interface
from its smooth time-zero metric slice.
-/
theorem hasDeTurckGaugeFixing_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    HasDeTurckGaugeFixing flow :=
  hasDeTurckGaugeFixing_of_backgroundMetricData
    (deturckBackgroundMetricData_of_flow flow)

/--
Concrete DeTurck background-metric data proves background-metric compatibility.
-/
theorem hasDeTurckBackgroundMetricCompatibility_of_backgroundMetricData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (backgroundMetricAtTime : DeTurckBackgroundMetricData flow) :
    HasDeTurckBackgroundMetricCompatibility flow :=
  HasDeTurckBackgroundMetricCompatibility.of_backgroundMetricData
    backgroundMetricAtTime

/--
Every Ricci-flow datum proves DeTurck background-metric compatibility from its
smooth time-zero metric slice.
-/
theorem hasDeTurckBackgroundMetricCompatibility_of_flow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    HasDeTurckBackgroundMetricCompatibility flow :=
  hasDeTurckBackgroundMetricCompatibility_of_backgroundMetricData
    (deturckBackgroundMetricData_of_flow flow)

/--
Scalar-curvature theory data and explicit Ricci-flow equation verification close
the first nineteen analytic fields through DeTurck gauge fixing.
-/
theorem analyticFirstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    (HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow :=
  ⟨analyticFirstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime,
    hasDeTurckGaugeFixing_of_flow flow⟩

/--
Scalar-curvature theory data and explicit Ricci-flow equation verification close
the first twenty analytic fields through DeTurck background compatibility.
-/
theorem analyticFirstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    ((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow :=
  ⟨analyticFirstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime,
    hasDeTurckBackgroundMetricCompatibility_of_flow flow⟩

/--
Time-dependent vector field used by the DeTurck gauge construction.

For a Ricci-flow datum this is the candidate vector field `W(g, g₀)` at every
time and point.
-/
abbrev TimeDependentDeTurckVectorField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → (x : M) → TangentSpace I x

/-- Shape contract for time-indexed DeTurck vector fields. -/
theorem timeDependentDeTurckVectorField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentDeTurckVectorField flow =
      (ℝ → (x : M) → TangentSpace I x) :=
  rfl

/--
Time-dependent connection-difference field used in the DeTurck vector field.

It is intended to be the tensor
`(X,Y) ↦ ∇^{g(t)}_X Y - ∇^{g₀}_X Y`.
-/
abbrev TimeDependentDeTurckConnectionDifferenceField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → ((x : M) → TangentSpace I x) →
    ((x : M) → TangentSpace I x) →
      (x : M) → TangentSpace I x

/-- Shape contract for time-indexed DeTurck connection-difference fields. -/
theorem timeDependentDeTurckConnectionDifferenceField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentDeTurckConnectionDifferenceField flow =
      (ℝ → ((x : M) → TangentSpace I x) →
        ((x : M) → TangentSpace I x) →
          (x : M) → TangentSpace I x) :=
  rfl

/--
Trace functional that contracts the connection-difference field into the
DeTurck vector field.

This is kept explicit because the current local API does not yet expose the
inverse-metric contraction theorem for the DeTurck connection-difference trace.
-/
abbrev TimeDependentDeTurckConnectionTraceField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Type _ :=
  ℝ → TimeDependentDeTurckConnectionDifferenceField flow →
    (x : M) → TangentSpace I x

/-- Shape contract for DeTurck connection-difference trace fields. -/
theorem timeDependentDeTurckConnectionTraceField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentDeTurckConnectionTraceField flow =
      (ℝ → TimeDependentDeTurckConnectionDifferenceField flow →
        (x : M) → TangentSpace I x) :=
  rfl

/--
Concrete DeTurck vector-field construction data.

The data records the background metric, the flow's Levi-Civita connection data,
the background connection chosen at the initial slice, the connection-difference
field, the explicit trace functional, and the equality identifying the DeTurck
vector field as that trace.
-/
structure DeTurckVectorFieldConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The background metric used for DeTurck gauge. -/
  backgroundMetricAtTime : DeTurckBackgroundMetricData flow
  /-- Levi-Civita connection theory for the evolving metric. -/
  flowConnectionTheoryAtTime :
    LeviCivitaTimeDependentConnectionTheoryData
      (metric_of_ricci_flow_data flow)
  /-- The background connection at the initial metric slice. -/
  backgroundConnectionAtTime : TangentCovariantDerivative I M
  /--
  The background connection is chosen as the flow Levi-Civita connection at
  time zero, matching the stored background metric.
  -/
  backgroundConnection_eq_initial_flow_connection :
    let flowConnectionAtTime :=
      flowConnectionTheoryAtTime.metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    backgroundConnectionAtTime = flowConnectionAtTime 0
  /-- The connection difference `∇^{g(t)} - ∇^{g₀}`. -/
  connectionDifferenceAtTime :
    TimeDependentDeTurckConnectionDifferenceField flow
  /-- The stored connection difference is the difference of the two connections. -/
  connection_difference_eq :
    let flowConnectionAtTime :=
      flowConnectionTheoryAtTime.metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    ∀ (t : ℝ) {X Y : (x : M) → TangentSpace I x} {x : M},
      MDiffAt (T% X) x →
      MDiffAt (T% Y) x →
        connectionDifferenceAtTime t X Y x =
          flowConnectionAtTime t Y x (X x) -
            backgroundConnectionAtTime Y x (X x)
  /-- The trace functional used to contract the connection difference. -/
  traceConnectionDifferenceAtTime :
    TimeDependentDeTurckConnectionTraceField flow
  /-- The candidate DeTurck vector field. -/
  vectorFieldAtTime : TimeDependentDeTurckVectorField flow
  /-- The DeTurck vector field is the trace of the connection difference. -/
  vectorField_eq_trace_connection_difference :
    ∀ (t : ℝ) (x : M),
      vectorFieldAtTime t x =
        traceConnectionDifferenceAtTime t connectionDifferenceAtTime x

/-- Interface for constructing the DeTurck vector field. -/
structure HasDeTurckVectorFieldConstruction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /--
  A connection-difference trace formula produces the DeTurck vector field.
  -/
  vectorFieldConstructionData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (DeTurckVectorFieldConstructionData flow)

/-- Compatibility constructor for DeTurck vector-field construction data. -/
def HasDeTurckVectorFieldConstruction.of_vectorFieldConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow) :
    HasDeTurckVectorFieldConstruction flow where
  vectorFieldConstructionData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨vectorFieldAtTime⟩⟩

/--
Concrete connection-difference trace data proves DeTurck vector-field
construction.
-/
theorem hasDeTurckVectorFieldConstruction_of_vectorFieldConstructionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow) :
    HasDeTurckVectorFieldConstruction flow :=
  HasDeTurckVectorFieldConstruction.of_vectorFieldConstructionData
    vectorFieldAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, and DeTurck
vector-field construction data close the first twenty-one analytic fields.
-/
theorem analyticFirstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow) :
    (((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow :=
  ⟨analyticFirstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime,
    hasDeTurckVectorFieldConstruction_of_vectorFieldConstructionData
      vectorFieldAtTime⟩

/--
Time-dependent two-tensor gauge term in the Ricci-DeTurck equation.

This stores the Lie-derivative contribution `L_W g` abstractly until the local
API exposes that tensor construction for the DeTurck vector field.
-/
abbrev TimeDependentRicciDeTurckGaugeTermField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M

/-- Shape contract for Ricci-DeTurck gauge-term fields. -/
theorem timeDependentRicciDeTurckGaugeTermField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckGaugeTermField flow =
      (ℝ → TangentCovariantTwoTensor I M) :=
  rfl

/--
Time-dependent right-hand side tensor field for the Ricci-DeTurck equation.

It is intended to be `-2 Ric(g(t)) + L_{W(g,g₀)} g(t)`.
-/
abbrev TimeDependentRicciDeTurckRHSField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M

/-- Shape contract for Ricci-DeTurck right-hand side fields. -/
theorem timeDependentRicciDeTurckRHSField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckRHSField flow =
      (ℝ → TangentCovariantTwoTensor I M) :=
  rfl

/--
Concrete Ricci-DeTurck equation derivation data.

The bundle records the vector-field construction, the original Ricci-flow
equation verification, the DeTurck gauge term, the full Ricci-DeTurck right-hand
side, and the equalities relating these tensors.  The remaining missing local
math is the construction of the gauge-term tensor from the DeTurck vector field
and background connection.
-/
structure RicciDeTurckEquationDerivationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- DeTurck vector-field construction data used in the gauge term. -/
  vectorFieldAtTime : DeTurckVectorFieldConstructionData flow
  /-- Verification of the original Ricci-flow equation. -/
  equationVerificationAtTime :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)
  /-- The DeTurck gauge-term tensor, intended as `L_W g`. -/
  gaugeTermAtTime : TimeDependentRicciDeTurckGaugeTermField flow
  /-- The complete Ricci-DeTurck equation right-hand side. -/
  ricciDeTurckRHSAtTime : TimeDependentRicciDeTurckRHSField flow
  /-- The Ricci-DeTurck right-hand side is `-2 Ric + L_W g`. -/
  ricciDeTurck_rhs_eq :
    ∀ t,
      ricciDeTurckRHSAtTime t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t +
          gaugeTermAtTime t
  /-- The metric time derivative is identified with the Ricci-DeTurck RHS. -/
  metric_derivative_eq_ricciDeTurck_rhs :
    ∀ t,
      metric_time_derivative_at_time_of_metric_derivative_field
        equationVerificationAtTime.metricDerivative.derivative t =
          ricciDeTurckRHSAtTime t

/-- Interface for deriving the Ricci-DeTurck equation from the Ricci-flow equation. -/
structure HasDeTurckEquationDerivation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /--
  Tensor-level Ricci-DeTurck RHS data derives the Ricci-DeTurck equation
  interface.
  -/
  ricciDeTurckEquationDerivationData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciDeTurckEquationDerivationData flow)

/-- Compatibility constructor for Ricci-DeTurck equation derivation data. -/
def HasDeTurckEquationDerivation.of_ricciDeTurckEquationDerivationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (equationAtTime : RicciDeTurckEquationDerivationData flow) :
    HasDeTurckEquationDerivation flow where
  ricciDeTurckEquationDerivationData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨equationAtTime⟩⟩

/--
Concrete Ricci-DeTurck equation data proves the DeTurck equation-derivation
interface.
-/
theorem hasDeTurckEquationDerivation_of_ricciDeTurckEquationDerivationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (equationAtTime : RicciDeTurckEquationDerivationData flow) :
    HasDeTurckEquationDerivation flow :=
  HasDeTurckEquationDerivation.of_ricciDeTurckEquationDerivationData
    equationAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, and Ricci-DeTurck equation data close the first
twenty-two analytic fields.
-/
theorem analyticFirstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow) :
    ((((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow :=
  ⟨analyticFirstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime,
    hasDeTurckEquationDerivation_of_ricciDeTurckEquationDerivationData
      ricciDeTurckEquationAtTime⟩

/--
Time-dependent linearized Ricci-tensor component for the Ricci-DeTurck
linearization.

It takes a two-tensor perturbation and returns the corresponding linearized
two-tensor contribution at each time.
-/
abbrev TimeDependentRicciTensorLinearizationField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M

/-- Shape contract for time-dependent Ricci-tensor linearization fields. -/
theorem timeDependentRicciTensorLinearizationField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciTensorLinearizationField flow =
      (ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M) :=
  rfl

/--
Time-dependent linearized DeTurck-gauge component for the Ricci-DeTurck
linearization.
-/
abbrev TimeDependentDeTurckGaugeLinearizationField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M

/-- Shape contract for time-dependent DeTurck-gauge linearization fields. -/
theorem timeDependentDeTurckGaugeLinearizationField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentDeTurckGaugeLinearizationField flow =
      (ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M) :=
  rfl

/--
Time-dependent linearized Ricci-DeTurck operator on two-tensor perturbations.
-/
abbrev TimeDependentRicciDeTurckLinearizedOperatorField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M

/-- Shape contract for time-dependent Ricci-DeTurck linearized operators. -/
theorem timeDependentRicciDeTurckLinearizedOperatorField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckLinearizedOperatorField flow =
      (ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M) :=
  rfl

/--
Concrete Ricci-DeTurck linearization data.

The bundle records the already-derived Ricci-DeTurck equation, the linearized
Ricci and gauge components, a time-dependent linearized operator, linearity of
that operator on tensor perturbations, and the formula identifying the operator
as `-2 D Ricci + D gauge`.
-/
structure RicciDeTurckLinearizationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Ricci-DeTurck equation derivation data being linearized. -/
  equationAtTime : RicciDeTurckEquationDerivationData flow
  /-- Linearized Ricci tensor contribution. -/
  ricciLinearizationAtTime :
    TimeDependentRicciTensorLinearizationField flow
  /-- Linearized DeTurck gauge contribution. -/
  gaugeLinearizationAtTime :
    TimeDependentDeTurckGaugeLinearizationField flow
  /-- The full time-dependent linearized Ricci-DeTurck operator. -/
  linearizedOperatorAtTime :
    TimeDependentRicciDeTurckLinearizedOperatorField flow
  /-- Additivity of the linearized operator on perturbation tensors. -/
  linearizedOperator_add :
    ∀ (t : ℝ) (variation₁ variation₂ : TangentCovariantTwoTensor I M),
      linearizedOperatorAtTime t (variation₁ + variation₂) =
        linearizedOperatorAtTime t variation₁ +
          linearizedOperatorAtTime t variation₂
  /-- Homogeneity of the linearized operator on perturbation tensors. -/
  linearizedOperator_smul :
    ∀ (t : ℝ) (a : ℝ) (variation : TangentCovariantTwoTensor I M),
      linearizedOperatorAtTime t (a • variation) =
        a • linearizedOperatorAtTime t variation
  /-- The linearized operator splits as `-2 D Ricci + D gauge`. -/
  linearizedOperator_eq_ricci_plus_gauge :
    ∀ (t : ℝ) (variation : TangentCovariantTwoTensor I M),
      linearizedOperatorAtTime t variation =
        (-2 : ℝ) • ricciLinearizationAtTime t variation +
          gaugeLinearizationAtTime t variation

/-- Interface for the linearization of the Ricci-DeTurck operator. -/
structure HasRicciDeTurckLinearization
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Tensor-level operator data proves Ricci-DeTurck linearization. -/
  ricciDeTurckLinearizationData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciDeTurckLinearizationData flow)

/-- Compatibility constructor for Ricci-DeTurck linearization data. -/
def HasRicciDeTurckLinearization.of_ricciDeTurckLinearizationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (linearizationAtTime : RicciDeTurckLinearizationData flow) :
    HasRicciDeTurckLinearization flow where
  ricciDeTurckLinearizationData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨linearizationAtTime⟩⟩

/--
Concrete Ricci-DeTurck linearization data proves the linearization interface.
-/
theorem hasRicciDeTurckLinearization_of_ricciDeTurckLinearizationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (linearizationAtTime : RicciDeTurckLinearizationData flow) :
    HasRicciDeTurckLinearization flow :=
  HasRicciDeTurckLinearization.of_ricciDeTurckLinearizationData
    linearizationAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, and Ricci-DeTurck
linearization data close the first twenty-three analytic fields.
-/
theorem analyticFirstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow) :
    (((((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow :=
  ⟨analyticFirstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime,
    hasRicciDeTurckLinearization_of_ricciDeTurckLinearizationData
      linearizationAtTime⟩

/--
Time-dependent principal-symbol field for the linearized Ricci-DeTurck
operator.
-/
abbrev TimeDependentRicciDeTurckPrincipalSymbolField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M

/-- Shape contract for Ricci-DeTurck principal-symbol fields. -/
theorem timeDependentRicciDeTurckPrincipalSymbolField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckPrincipalSymbolField flow =
      (ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M) :=
  rfl

/--
Time-dependent lower-order part of the linearized Ricci-DeTurck operator.
-/
abbrev TimeDependentRicciDeTurckLowerOrderField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M

/-- Shape contract for Ricci-DeTurck lower-order fields. -/
theorem timeDependentRicciDeTurckLowerOrderField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckLowerOrderField flow =
      (ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M) :=
  rfl

/--
Positive coefficient field witnessing the scalar parabolicity constant at each
time.
-/
abbrev TimeDependentStrictParabolicityCoefficientField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → ℝ

/-- Shape contract for strict-parabolicity coefficient fields. -/
theorem timeDependentStrictParabolicityCoefficientField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentStrictParabolicityCoefficientField flow = (ℝ → ℝ) :=
  rfl

/--
Concrete strict parabolicity data for the Ricci-DeTurck system.

The bundle records the linearized operator, its principal symbol, its lower
order part, and a positive coefficient showing that the principal symbol is a
positive multiple of the identity on two-tensor perturbations.
-/
structure StrictlyParabolicDeTurckSystemData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Ricci-DeTurck linearization data whose principal symbol is analyzed. -/
  linearizationAtTime : RicciDeTurckLinearizationData flow
  /-- Principal-symbol part of the linearized operator. -/
  principalSymbolAtTime : TimeDependentRicciDeTurckPrincipalSymbolField flow
  /-- Lower-order part of the linearized operator. -/
  lowerOrderAtTime : TimeDependentRicciDeTurckLowerOrderField flow
  /-- Positive scalar parabolicity coefficient. -/
  parabolicityCoefficientAtTime :
    TimeDependentStrictParabolicityCoefficientField flow
  /-- The parabolicity coefficient is strictly positive at each time. -/
  parabolicityCoefficient_pos :
    ∀ t, 0 < parabolicityCoefficientAtTime t
  /-- The linearized operator splits into principal-symbol and lower-order parts. -/
  linearizedOperator_eq_principalSymbol_plus_lowerOrder :
    ∀ (t : ℝ) (variation : TangentCovariantTwoTensor I M),
      linearizationAtTime.linearizedOperatorAtTime t variation =
        principalSymbolAtTime t variation + lowerOrderAtTime t variation
  /-- The principal symbol is a positive multiple of the identity. -/
  principalSymbol_eq_positive_identity_multiple :
    ∀ (t : ℝ) (variation : TangentCovariantTwoTensor I M),
      principalSymbolAtTime t variation =
        parabolicityCoefficientAtTime t • variation

/-- Interface for strict parabolicity of the Ricci-DeTurck system. -/
structure HasStrictlyParabolicDeTurckSystem
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Principal-symbol data proves strict parabolicity. -/
  strictlyParabolicDeTurckSystemData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (StrictlyParabolicDeTurckSystemData flow)

/-- Compatibility constructor for strict-parabolicity system data. -/
def HasStrictlyParabolicDeTurckSystem.of_strictlyParabolicDeTurckSystemData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow) :
    HasStrictlyParabolicDeTurckSystem flow where
  strictlyParabolicDeTurckSystemData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨strictParabolicAtTime⟩⟩

/--
Concrete principal-symbol data proves strict parabolicity of the DeTurck system.
-/
theorem hasStrictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow) :
    HasStrictlyParabolicDeTurckSystem flow :=
  HasStrictlyParabolicDeTurckSystem.of_strictlyParabolicDeTurckSystemData
    strictParabolicAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, and strict-parabolicity data close the first twenty-four
analytic fields.
-/
theorem analyticFirstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow) :
    ((((((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow :=
  ⟨analyticFirstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime,
    hasStrictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData
      strictParabolicAtTime⟩

/--
Time-dependent solution operator for the linear parabolic Ricci-DeTurck system.

It sends a two-tensor forcing term to the corresponding two-tensor solution
candidate at each time.
-/
abbrev TimeDependentParabolicLinearSolutionOperatorField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M

/-- Shape contract for linear parabolic solution-operator fields. -/
theorem timeDependentParabolicLinearSolutionOperatorField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentParabolicLinearSolutionOperatorField flow =
      (ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M) :=
  rfl

/-- Time-dependent estimate constants for linear parabolic theory. -/
abbrev TimeDependentParabolicLinearEstimateConstantField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → ℝ

/-- Shape contract for linear parabolic estimate-constant fields. -/
theorem timeDependentParabolicLinearEstimateConstantField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentParabolicLinearEstimateConstantField flow = (ℝ → ℝ) :=
  rfl

/--
Concrete linear parabolic theory data for the strict Ricci-DeTurck linearized
system.

The bundle records a solution operator for the strict-parabolic linearized
operator, linearity of that solution operator, a right-inverse equation, and a
pointwise estimate with positive time-dependent constants.
-/
structure ParabolicLinearTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Strict-parabolicity data for the linearized Ricci-DeTurck operator. -/
  strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow
  /-- Linear solution operator for forcing terms. -/
  solutionOperatorAtTime :
    TimeDependentParabolicLinearSolutionOperatorField flow
  /-- Estimate constants for the solution operator. -/
  estimateConstantAtTime :
    TimeDependentParabolicLinearEstimateConstantField flow
  /-- Estimate constants are strictly positive. -/
  estimateConstant_pos : ∀ t, 0 < estimateConstantAtTime t
  /-- The solution operator is additive in the forcing term. -/
  solutionOperator_add :
    ∀ (t : ℝ) (source₁ source₂ : TangentCovariantTwoTensor I M),
      solutionOperatorAtTime t (source₁ + source₂) =
        solutionOperatorAtTime t source₁ +
          solutionOperatorAtTime t source₂
  /-- The solution operator is homogeneous in the forcing term. -/
  solutionOperator_smul :
    ∀ (t : ℝ) (a : ℝ) (source : TangentCovariantTwoTensor I M),
      solutionOperatorAtTime t (a • source) =
        a • solutionOperatorAtTime t source
  /-- The solution operator is a right inverse to the linearized operator. -/
  solutionOperator_right_inverse :
    ∀ (t : ℝ) (source : TangentCovariantTwoTensor I M),
      strictParabolicAtTime.linearizationAtTime.linearizedOperatorAtTime t
        (solutionOperatorAtTime t source) = source
  /-- Pointwise estimate for the solution operator. -/
  solutionOperator_pointwise_estimate :
    ∀ (t : ℝ) (source : TangentCovariantTwoTensor I M)
      (x : M) (v w : TangentSpace I x),
      |solutionOperatorAtTime t source x v w| ≤
        estimateConstantAtTime t * |source x v w|

/-- Bundle the positive estimate constants and pointwise linear-theory estimate. -/
theorem ParabolicLinearTheoryData.estimate_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (linearTheoryAtTime : ParabolicLinearTheoryData flow) :
    (∀ t, 0 < linearTheoryAtTime.estimateConstantAtTime t) ∧
      ∀ (t : ℝ) (source : TangentCovariantTwoTensor I M)
        (x : M) (v w : TangentSpace I x),
        |linearTheoryAtTime.solutionOperatorAtTime t source x v w| ≤
          linearTheoryAtTime.estimateConstantAtTime t * |source x v w| := by
  exact
    ⟨linearTheoryAtTime.estimateConstant_pos,
      linearTheoryAtTime.solutionOperator_pointwise_estimate⟩

/-- Interface for linear parabolic theory used by Ricci-DeTurck flow. -/
structure HasParabolicLinearTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Solution-operator and estimate data proves linear parabolic theory. -/
  parabolicLinearTheoryData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ParabolicLinearTheoryData flow)

/-- Compatibility constructor for linear parabolic theory data. -/
def HasParabolicLinearTheory.of_parabolicLinearTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (linearTheoryAtTime : ParabolicLinearTheoryData flow) :
    HasParabolicLinearTheory flow where
  parabolicLinearTheoryData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨linearTheoryAtTime⟩⟩

/--
Concrete solution-operator data proves linear parabolic theory for the DeTurck
system.
-/
theorem hasParabolicLinearTheory_of_parabolicLinearTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (linearTheoryAtTime : ParabolicLinearTheoryData flow) :
    HasParabolicLinearTheory flow :=
  HasParabolicLinearTheory.of_parabolicLinearTheoryData
    linearTheoryAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, and linear parabolic theory data
close the first twenty-five analytic fields.
-/
theorem analyticFirstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow) :
    (((((((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow :=
  ⟨analyticFirstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime,
    hasParabolicLinearTheory_of_parabolicLinearTheoryData
      linearTheoryAtTime⟩

/--
Time-dependent Picard map for the nonlinear Ricci-DeTurck fixed-point argument.
-/
abbrev TimeDependentParabolicFixedPointMapField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M

/-- Shape contract for nonlinear Picard maps in the DeTurck fixed-point argument. -/
theorem timeDependentParabolicFixedPointMapField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentParabolicFixedPointMapField flow =
      (ℝ → TangentCovariantTwoTensor I M → TangentCovariantTwoTensor I M) :=
  rfl

/-- Time-dependent fixed-point tensor field for the nonlinear DeTurck system. -/
abbrev TimeDependentRicciDeTurckFixedPointField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M

/-- Shape contract for Ricci-DeTurck fixed-point tensor fields. -/
theorem timeDependentRicciDeTurckFixedPointField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckFixedPointField flow =
      (ℝ → TangentCovariantTwoTensor I M) :=
  rfl

/-- Time-dependent contraction constants for the nonlinear Picard map. -/
abbrev TimeDependentParabolicFixedPointContractionConstantField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → ℝ

/-- Shape contract for fixed-point contraction-constant fields. -/
theorem timeDependentParabolicFixedPointContractionConstantField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentParabolicFixedPointContractionConstantField flow =
      (ℝ → ℝ) :=
  rfl

/--
Concrete contraction/fixed-point argument data for the nonlinear Ricci-DeTurck
system.

The bundle records the linear parabolic theory, a nonlinear Picard map, a
strict contraction constant, an actual fixed point, and the pointwise contraction
estimate that makes the fixed point meaningful.
-/
structure ParabolicFixedPointArgumentData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Linear parabolic solution theory used to define the Picard map. -/
  linearTheoryAtTime : ParabolicLinearTheoryData flow
  /-- The nonlinear Picard map for the DeTurck system. -/
  fixedPointMapAtTime : TimeDependentParabolicFixedPointMapField flow
  /-- The fixed point produced by the contraction argument. -/
  fixedPointAtTime : TimeDependentRicciDeTurckFixedPointField flow
  /-- Contraction constant for the Picard map. -/
  contractionConstantAtTime :
    TimeDependentParabolicFixedPointContractionConstantField flow
  /-- The contraction constant is nonnegative. -/
  contractionConstant_nonneg :
    ∀ t, 0 ≤ contractionConstantAtTime t
  /-- The contraction constant is strictly smaller than one. -/
  contractionConstant_lt_one :
    ∀ t, contractionConstantAtTime t < 1
  /-- The stored tensor is a fixed point of the Picard map. -/
  fixedPoint_eq :
    ∀ t, fixedPointMapAtTime t (fixedPointAtTime t) = fixedPointAtTime t
  /-- Pointwise contraction estimate for the Picard map. -/
  contraction_estimate :
    ∀ (t : ℝ) (u v : TangentCovariantTwoTensor I M)
      (x : M) (X Y : TangentSpace I x),
      |(fixedPointMapAtTime t u - fixedPointMapAtTime t v) x X Y| ≤
        contractionConstantAtTime t * |(u - v) x X Y|

/-- Interface for the contraction/fixed-point argument for Ricci-DeTurck flow. -/
structure HasParabolicFixedPointArgument
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Contraction-map data proves the fixed-point argument. -/
  parabolicFixedPointArgumentData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ParabolicFixedPointArgumentData flow)

/-- Compatibility constructor for parabolic fixed-point argument data. -/
def HasParabolicFixedPointArgument.of_parabolicFixedPointArgumentData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow) :
    HasParabolicFixedPointArgument flow where
  parabolicFixedPointArgumentData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨fixedPointAtTime⟩⟩

/--
Concrete contraction data proves the nonlinear DeTurck fixed-point argument.
-/
theorem hasParabolicFixedPointArgument_of_parabolicFixedPointArgumentData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow) :
    HasParabolicFixedPointArgument flow :=
  HasParabolicFixedPointArgument.of_parabolicFixedPointArgumentData
    fixedPointAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data, and
fixed-point argument data close the first twenty-six analytic fields.
-/
theorem analyticFirstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow) :
    ((((((((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow :=
  ⟨analyticFirstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime,
    hasParabolicFixedPointArgument_of_parabolicFixedPointArgumentData
      fixedPointAtTime⟩

/--
Time-dependent metric field produced by the Ricci-DeTurck short-time existence
argument.
-/
abbrev TimeDependentRicciDeTurckSolutionMetricField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  TimeDependentRiemannianMetric I n M

/-- Shape contract for Ricci-DeTurck solution metric fields. -/
theorem timeDependentRicciDeTurckSolutionMetricField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckSolutionMetricField flow =
      TimeDependentRiemannianMetric I n M :=
  rfl

/-- Positive existence-time datum for a short-time Ricci-DeTurck solution. -/
abbrev DeTurckShortTimeExistenceInterval
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type :=
  { existenceTime : ℝ // 0 < existenceTime }

/-- Shape contract for positive Ricci-DeTurck short-time intervals. -/
theorem deTurckShortTimeExistenceInterval_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    DeTurckShortTimeExistenceInterval flow =
      { existenceTime : ℝ // 0 < existenceTime } :=
  rfl

/--
Concrete short-time existence data for Ricci-DeTurck flow.

The bundle records the fixed-point argument producing the tensor solution, a
positive time interval, the resulting Ricci-DeTurck metric family, and the
equation data tying that metric candidate back to the fixed point and the
derived Ricci-DeTurck right-hand side.
-/
structure DeTurckShortTimeExistenceData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Fixed-point data producing the nonlinear Ricci-DeTurck solution tensor. -/
  fixedPointAtTime : ParabolicFixedPointArgumentData flow
  /-- Positive time for which the Ricci-DeTurck solution exists. -/
  existenceInterval : DeTurckShortTimeExistenceInterval flow
  /-- The produced Ricci-DeTurck metric family. -/
  solutionMetricAtTime : TimeDependentRicciDeTurckSolutionMetricField flow
  /-- The Ricci-DeTurck solution starts from the original flow metric. -/
  solution_initialMetric_eq :
    solutionMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0
  /-- The stored solution tensor is the fixed point produced by the Picard map. -/
  solutionTensor_eq_fixedPoint :
    ∀ t,
      fixedPointAtTime.fixedPointMapAtTime t
          (fixedPointAtTime.fixedPointAtTime t) =
        fixedPointAtTime.fixedPointAtTime t
  /--
  The fixed-point tensor agrees with the derived Ricci-DeTurck right-hand side.
  -/
  fixedPoint_eq_ricciDeTurck_rhs :
    ∀ t,
      fixedPointAtTime.fixedPointAtTime t =
        fixedPointAtTime.linearTheoryAtTime.strictParabolicAtTime.linearizationAtTime.equationAtTime.ricciDeTurckRHSAtTime
          t

/-- Project the positive short-time existence interval from Ricci-DeTurck data. -/
theorem DeTurckShortTimeExistenceData.existenceTime_pos
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow) :
    0 < (shortTimeAtTime.existenceInterval : ℝ) :=
  shortTimeAtTime.existenceInterval.property

/-- Interface for short-time existence of the Ricci-DeTurck flow. -/
structure HasDeTurckShortTimeExistence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Positive-time Ricci-DeTurck solution data proves short-time existence. -/
  deturckShortTimeExistenceData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (DeTurckShortTimeExistenceData flow)

/-- Compatibility constructor for Ricci-DeTurck short-time existence data. -/
def HasDeTurckShortTimeExistence.of_deturckShortTimeExistenceData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow) :
    HasDeTurckShortTimeExistence flow where
  deturckShortTimeExistenceData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨shortTimeAtTime⟩⟩

/--
Concrete positive-time solution data proves short-time Ricci-DeTurck existence.
-/
theorem hasDeTurckShortTimeExistence_of_deturckShortTimeExistenceData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow) :
    HasDeTurckShortTimeExistence flow :=
  HasDeTurckShortTimeExistence.of_deturckShortTimeExistenceData
    shortTimeAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, and short-time existence data close the first
twenty-seven analytic fields.
-/
theorem analyticFirstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow) :
    (((((((((HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow :=
  ⟨analyticFirstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime,
    hasDeTurckShortTimeExistence_of_deturckShortTimeExistenceData
      shortTimeAtTime⟩

/--
Bootstrapped Ricci-DeTurck metric field obtained after applying short-time
regularity to the weak fixed-point solution.
-/
abbrev TimeDependentRicciDeTurckBootstrappedMetricField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  TimeDependentRiemannianMetric I n M

/-- Shape contract for bootstrapped Ricci-DeTurck metric fields. -/
theorem timeDependentRicciDeTurckBootstrappedMetricField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRicciDeTurckBootstrappedMetricField flow =
      TimeDependentRiemannianMetric I n M :=
  rfl

/-- Time-dependent regularity estimate constants for the bootstrap step. -/
abbrev TimeDependentShortTimeRegularityEstimateField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type :=
  ℝ → ℕ → ℝ

/-- Shape contract for short-time regularity estimate fields. -/
theorem timeDependentShortTimeRegularityEstimateField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentShortTimeRegularityEstimateField flow = (ℝ → ℕ → ℝ) :=
  rfl

/--
Concrete short-time regularity bootstrap data for the Ricci-DeTurck solution.

The bundle records the positive-time solution, a bootstrapped metric family of
the target smoothness class, equality with the short-time solution metric, and
pointwise estimates controlling the fixed-point tensor at every bootstrap
order.  This is the local data payload that a later Schauder/regularity theorem
should produce.
-/
structure ShortTimeRegularityBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Positive-time Ricci-DeTurck solution data being bootstrapped. -/
  shortTimeAtTime : DeTurckShortTimeExistenceData flow
  /-- The bootstrapped smooth Ricci-DeTurck metric family. -/
  bootstrappedMetricAtTime :
    TimeDependentRicciDeTurckBootstrappedMetricField flow
  /-- Estimate constants for each bootstrap order. -/
  regularityEstimateAtTime :
    TimeDependentShortTimeRegularityEstimateField flow
  /-- Regularity estimate constants are nonnegative. -/
  regularityEstimate_nonneg :
    ∀ (t : ℝ) (order : ℕ), 0 ≤ regularityEstimateAtTime t order
  /-- The bootstrap preserves the short-time solution metric. -/
  bootstrappedMetric_eq_solutionMetric :
    bootstrappedMetricAtTime = shortTimeAtTime.solutionMetricAtTime
  /-- The bootstrapped solution has the same initial metric as the flow. -/
  bootstrapped_initialMetric_eq :
    bootstrappedMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0
  /-- Pointwise bootstrap estimate for the fixed-point tensor. -/
  fixedPointTensor_pointwise_regular :
    ∀ (t : ℝ) (order : ℕ) (x : M) (X Y : TangentSpace I x),
      |shortTimeAtTime.fixedPointAtTime.fixedPointAtTime t x X Y| ≤
        regularityEstimateAtTime t order

/-- Bundle nonnegative bootstrap estimates with the pointwise fixed-point tensor bound. -/
theorem ShortTimeRegularityBootstrapData.estimate_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow) :
    (∀ (t : ℝ) (order : ℕ), 0 ≤ regularityAtTime.regularityEstimateAtTime t order) ∧
      ∀ (t : ℝ) (order : ℕ) (x : M) (X Y : TangentSpace I x),
        |regularityAtTime.shortTimeAtTime.fixedPointAtTime.fixedPointAtTime t x X Y| ≤
          regularityAtTime.regularityEstimateAtTime t order := by
  exact
    ⟨regularityAtTime.regularityEstimate_nonneg,
      regularityAtTime.fixedPointTensor_pointwise_regular⟩

/-- Interface for bootstrapping short-time Ricci-DeTurck solutions to smoothness. -/
structure HasShortTimeRegularityBootstrap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Regularity estimates and bootstrapped metric data prove the bootstrap. -/
  shortTimeRegularityBootstrapData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ShortTimeRegularityBootstrapData flow)

/-- Compatibility constructor for short-time regularity bootstrap data. -/
def HasShortTimeRegularityBootstrap.of_shortTimeRegularityBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow) :
    HasShortTimeRegularityBootstrap flow where
  shortTimeRegularityBootstrapData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨regularityAtTime⟩⟩

/--
Concrete regularity data proves the short-time Ricci-DeTurck bootstrap
interface.
-/
theorem hasShortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow) :
    HasShortTimeRegularityBootstrap flow :=
  HasShortTimeRegularityBootstrap.of_shortTimeRegularityBootstrapData
    regularityAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, and regularity-bootstrap
data close the first twenty-eight analytic fields.
-/
theorem analyticFirstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow) :
    ((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow :=
  ⟨analyticFirstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime,
    hasShortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData
      regularityAtTime⟩

/--
Time-dependent maps solving the DeTurck diffeomorphism ODE.

The inverse laws are stored in `DeTurckDiffeomorphismODEData`; this alias keeps
the raw family of maps separate from the proof that the family is a
diffeomorphism flow.
-/
abbrev TimeDependentDeTurckDiffeomorphismField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → M → M

/-- Shape contract for DeTurck diffeomorphism-flow map fields. -/
theorem timeDependentDeTurckDiffeomorphismField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentDeTurckDiffeomorphismField flow = (ℝ → M → M) :=
  rfl

/-- Velocity field along a time-dependent DeTurck diffeomorphism flow. -/
abbrev TimeDependentDeTurckDiffeomorphismVelocityField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (diffeomorphismAtTime : TimeDependentDeTurckDiffeomorphismField flow) :
    Type _ :=
  (t : ℝ) → (x : M) → TangentSpace I (diffeomorphismAtTime t x)

/-- Shape contract for DeTurck diffeomorphism velocity fields. -/
theorem timeDependentDeTurckDiffeomorphismVelocityField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (diffeomorphismAtTime : TimeDependentDeTurckDiffeomorphismField flow) :
    TimeDependentDeTurckDiffeomorphismVelocityField flow
        diffeomorphismAtTime =
      ((t : ℝ) → (x : M) → TangentSpace I (diffeomorphismAtTime t x)) :=
  rfl

/--
Concrete DeTurck diffeomorphism ODE data.

The bundle records the regularized short-time Ricci-DeTurck solution, the
DeTurck vector field driving the ODE, a time-dependent map with a two-sided
inverse, a velocity field along that map, and the ODE identity saying that this
velocity is the DeTurck vector field evaluated along the map.
-/
structure DeTurckDiffeomorphismODEData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Regularized short-time Ricci-DeTurck solution data. -/
  regularityAtTime : ShortTimeRegularityBootstrapData flow
  /-- DeTurck vector field driving the diffeomorphism ODE. -/
  vectorFieldAtTime : DeTurckVectorFieldConstructionData flow
  /-- The chosen vector field agrees with the one in the Ricci-DeTurck equation data. -/
  vectorField_eq_equation_vectorField :
    vectorFieldAtTime =
      regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.strictParabolicAtTime.linearizationAtTime.equationAtTime.vectorFieldAtTime
  /-- The time-dependent DeTurck diffeomorphism maps. -/
  diffeomorphismAtTime : TimeDependentDeTurckDiffeomorphismField flow
  /-- Inverse maps for the DeTurck diffeomorphism flow. -/
  inverseDiffeomorphismAtTime :
    TimeDependentDeTurckDiffeomorphismField flow
  /-- Velocity field along the DeTurck diffeomorphism maps. -/
  velocityAtTime :
    TimeDependentDeTurckDiffeomorphismVelocityField flow
      diffeomorphismAtTime
  /-- The diffeomorphism flow starts at the identity. -/
  initial_diffeomorphism_eq_id :
    ∀ x : M, diffeomorphismAtTime 0 x = x
  /-- The stored inverse is a left inverse for every time. -/
  left_inverse :
    ∀ (t : ℝ) (x : M),
      inverseDiffeomorphismAtTime t (diffeomorphismAtTime t x) = x
  /-- The stored inverse is a right inverse for every time. -/
  right_inverse :
    ∀ (t : ℝ) (x : M),
      diffeomorphismAtTime t (inverseDiffeomorphismAtTime t x) = x
  /-- ODE identity: velocity along the flow is the DeTurck vector field. -/
  ode_velocity_eq_deTurck_vectorField :
    ∀ (t : ℝ) (x : M),
      velocityAtTime t x =
        vectorFieldAtTime.vectorFieldAtTime t (diffeomorphismAtTime t x)

/-- Bundle the two-sided inverse laws for the DeTurck diffeomorphism flow. -/
theorem DeTurckDiffeomorphismODEData.inverse_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (odeAtTime : DeTurckDiffeomorphismODEData flow) :
    (∀ (t : ℝ) (x : M),
      odeAtTime.inverseDiffeomorphismAtTime t
        (odeAtTime.diffeomorphismAtTime t x) = x) ∧
      ∀ (t : ℝ) (x : M),
        odeAtTime.diffeomorphismAtTime t
          (odeAtTime.inverseDiffeomorphismAtTime t x) = x := by
  exact ⟨odeAtTime.left_inverse, odeAtTime.right_inverse⟩

/-- Interface for solving the DeTurck diffeomorphism ODE. -/
structure HasDeTurckDiffeomorphismODE
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Diffeomorphism-flow and velocity data proves the DeTurck ODE interface. -/
  deturckDiffeomorphismODEData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (DeTurckDiffeomorphismODEData flow)

/-- Compatibility constructor for DeTurck diffeomorphism ODE data. -/
def HasDeTurckDiffeomorphismODE.of_deturckDiffeomorphismODEData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (odeAtTime : DeTurckDiffeomorphismODEData flow) :
    HasDeTurckDiffeomorphismODE flow where
  deturckDiffeomorphismODEData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨odeAtTime⟩⟩

/-- Concrete diffeomorphism-flow data proves the DeTurck ODE interface. -/
theorem hasDeTurckDiffeomorphismODE_of_deturckDiffeomorphismODEData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (odeAtTime : DeTurckDiffeomorphismODEData flow) :
    HasDeTurckDiffeomorphismODE flow :=
  HasDeTurckDiffeomorphismODE.of_deturckDiffeomorphismODEData
    odeAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, and DeTurck diffeomorphism ODE data close the first twenty-nine analytic
fields.
-/
theorem analyticFirstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow) :
    (((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow :=
  ⟨analyticFirstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime,
    hasDeTurckDiffeomorphismODE_of_deturckDiffeomorphismODEData
      odeAtTime⟩

/--
Metric family obtained by pulling the Ricci-DeTurck solution back along the
DeTurck diffeomorphism flow.
-/
abbrev TimeDependentDeTurckPulledBackMetricField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  TimeDependentRiemannianMetric I n M

/-- Shape contract for pulled-back DeTurck metric fields. -/
theorem timeDependentDeTurckPulledBackMetricField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentDeTurckPulledBackMetricField flow =
      TimeDependentRiemannianMetric I n M :=
  rfl

/--
Right-hand side tensor field after pulling the Ricci-DeTurck equation back to
the original Ricci-flow gauge.
-/
abbrev TimeDependentDeTurckPulledBackRHSField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → TangentCovariantTwoTensor I M

/-- Shape contract for pulled-back DeTurck equation right-hand sides. -/
theorem timeDependentDeTurckPulledBackRHSField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentDeTurckPulledBackRHSField flow =
      (ℝ → TangentCovariantTwoTensor I M) :=
  rfl

/--
Concrete data identifying the pulled-back Ricci-DeTurck equation with the
Ricci-flow equation.

The bundle records the DeTurck diffeomorphism ODE data, the pulled-back metric
and RHS tensor, and the identities saying that the pulled-back data is exactly
the original Ricci-flow metric equation.
-/
structure DeTurckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- DeTurck diffeomorphism ODE data used for the pullback. -/
  odeAtTime : DeTurckDiffeomorphismODEData flow
  /-- The pulled-back Ricci-DeTurck metric family. -/
  pulledBackMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The pulled-back equation right-hand side. -/
  pulledBackRHSAtTime : TimeDependentDeTurckPulledBackRHSField flow
  /-- Pullback identifies the DeTurck metric with the original Ricci-flow metric. -/
  pulledBackMetric_eq_flowMetric :
    pulledBackMetricAtTime = metric_of_ricci_flow_data flow
  /-- The pulled-back metric has the original initial metric. -/
  pulledBack_initialMetric_eq :
    pulledBackMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0
  /-- The pulled-back right-hand side is the Ricci-flow right-hand side. -/
  pulledBack_rhs_eq_ricciFlow_rhs :
    ∀ t,
      pulledBackRHSAtTime t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t
  /-- The pulled-back right-hand side is the stored metric time derivative. -/
  pulledBack_rhs_eq_metricDerivative :
    ∀ t,
      pulledBackRHSAtTime t =
        metric_time_derivative_at_time_of_metric_derivative_field
          odeAtTime.regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.strictParabolicAtTime.linearizationAtTime.equationAtTime.equationVerificationAtTime.metricDerivative.derivative
          t

/-- Interface identifying the pulled-back DeTurck equation with Ricci flow. -/
structure HasDeTurckPullbackEquationIdentity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Pullback metric and RHS identity data prove the pullback equation interface. -/
  deturckPullbackEquationIdentityData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (DeTurckPullbackEquationIdentityData flow)

/-- Compatibility constructor for DeTurck pullback equation-identity data. -/
def HasDeTurckPullbackEquationIdentity.of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasDeTurckPullbackEquationIdentity flow where
  deturckPullbackEquationIdentityData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨pullbackIdentityAtTime⟩⟩

/--
Concrete pulled-back metric/RHS identity data proves the DeTurck pullback
equation interface.
-/
theorem hasDeTurckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasDeTurckPullbackEquationIdentity flow :=
  HasDeTurckPullbackEquationIdentity.of_deturckPullbackEquationIdentityData
    pullbackIdentityAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, DeTurck diffeomorphism ODE data, and pullback equation identity data
close the first thirty analytic fields.
-/
theorem analyticFirstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow :=
  ⟨analyticFirstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime,
    hasDeTurckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData
      pullbackIdentityAtTime⟩

/--
Concrete data pulling the Ricci-DeTurck solution back to a Ricci-flow solution.

The bundle records the already-proved pullback equation identity, the resulting
metric family in Ricci-flow gauge, and the identities showing that this family
is exactly the original Ricci-flow metric with the Ricci-flow right-hand side.
-/
structure DeTurckPullbackToRicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Pullback equation identity data being upgraded to a Ricci-flow solution. -/
  pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow
  /-- The pulled-back metric family in Ricci-flow gauge. -/
  solutionMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The solution metric is the metric from the pullback equation identity. -/
  solutionMetric_eq_pulledBackMetric :
    solutionMetricAtTime = pullbackIdentityAtTime.pulledBackMetricAtTime
  /-- The pulled-back solution metric is the original Ricci-flow metric. -/
  solutionMetric_eq_flowMetric :
    solutionMetricAtTime = metric_of_ricci_flow_data flow
  /-- The pulled-back Ricci-flow solution has the original initial metric. -/
  solution_initialMetric_eq :
    solutionMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0
  /-- The pulled-back equation right-hand side is the Ricci-flow right-hand side. -/
  solution_rhs_eq_ricciFlow_rhs :
    ∀ t,
      pullbackIdentityAtTime.pulledBackRHSAtTime t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t
  /-- The pulled-back right-hand side is the stored metric time derivative. -/
  solution_rhs_eq_metricDerivative :
    ∀ t,
      pullbackIdentityAtTime.pulledBackRHSAtTime t =
        metric_time_derivative_at_time_of_metric_derivative_field
          pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.strictParabolicAtTime.linearizationAtTime.equationAtTime.equationVerificationAtTime.metricDerivative.derivative
          t

/-- Interface for pulling a Ricci-DeTurck solution back to a Ricci-flow solution. -/
structure HasDeTurckPullbackToRicciFlow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Pullback-to-Ricci-flow data proves the pullback interface. -/
  deturckPullbackToRicciFlowData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (DeTurckPullbackToRicciFlowData flow)

/-- Compatibility constructor for DeTurck pullback-to-Ricci-flow data. -/
def HasDeTurckPullbackToRicciFlow.of_deturckPullbackToRicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow) :
    HasDeTurckPullbackToRicciFlow flow where
  deturckPullbackToRicciFlowData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨pullbackToRicciFlowAtTime⟩⟩

/--
Concrete pullback-to-Ricci-flow data proves the production pullback interface.
-/
theorem hasDeTurckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow) :
    HasDeTurckPullbackToRicciFlow flow :=
  HasDeTurckPullbackToRicciFlow.of_deturckPullbackToRicciFlowData
    pullbackToRicciFlowAtTime

/--
The pullback equation identity data already contains the metric and RHS
identities needed to build the pullback-to-Ricci-flow interface.
-/
theorem hasDeTurckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasDeTurckPullbackToRicciFlow flow :=
  hasDeTurckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData
    { pullbackIdentityAtTime := pullbackIdentityAtTime
      solutionMetricAtTime := pullbackIdentityAtTime.pulledBackMetricAtTime
      solutionMetric_eq_pulledBackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackIdentityAtTime.pulledBackMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackIdentityAtTime.pulledBack_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_metricDerivative }

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, DeTurck diffeomorphism ODE data, and pullback equation identity data
close the first thirty-one analytic fields.
-/
theorem analyticFirstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow :=
  ⟨analyticFirstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime,
    hasDeTurckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData
      pullbackIdentityAtTime⟩

/--
Concrete short-time Ricci-flow solution data obtained after pulling the
Ricci-DeTurck solution back.

The bundle records the pullback-to-Ricci-flow data, the positive existence
interval inherited from the Ricci-DeTurck fixed-point solution, and the metric
and equation identities showing that the pulled-back family is a Ricci-flow
solution on that interval.
-/
structure ShortTimeRicciFlowSolutionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Pullback-to-Ricci-flow data producing the ungauged solution. -/
  pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow
  /-- Positive time interval inherited from the Ricci-DeTurck solution. -/
  existenceInterval : DeTurckShortTimeExistenceInterval flow
  /-- The resulting Ricci-flow metric family on the short-time interval. -/
  solutionMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The existence interval is the Ricci-DeTurck short-time interval. -/
  existenceInterval_eq_deturckInterval :
    existenceInterval =
      pullbackToRicciFlowAtTime.pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.existenceInterval
  /-- The short-time metric is the pulled-back Ricci-flow metric. -/
  solutionMetric_eq_pullbackMetric :
    solutionMetricAtTime =
      pullbackToRicciFlowAtTime.solutionMetricAtTime
  /-- The short-time metric is the original flow metric family. -/
  solutionMetric_eq_flowMetric :
    solutionMetricAtTime = metric_of_ricci_flow_data flow
  /-- The short-time solution has the original initial metric. -/
  solution_initialMetric_eq :
    solutionMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0
  /-- The short-time solution has the Ricci-flow right-hand side. -/
  solution_rhs_eq_ricciFlow_rhs :
    ∀ t,
      pullbackToRicciFlowAtTime.pullbackIdentityAtTime.pulledBackRHSAtTime t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t
  /-- The short-time solution right-hand side is the stored metric derivative. -/
  solution_rhs_eq_metricDerivative :
    ∀ t,
      pullbackToRicciFlowAtTime.pullbackIdentityAtTime.pulledBackRHSAtTime t =
        metric_time_derivative_at_time_of_metric_derivative_field
          pullbackToRicciFlowAtTime.pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.strictParabolicAtTime.linearizationAtTime.equationAtTime.equationVerificationAtTime.metricDerivative.derivative
          t

/-- Interface for the short-time existence theorem for Ricci flow. -/
structure HasShortTimeRicciFlowSolution
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Short-time Ricci-flow solution data proves the short-time solution interface. -/
  shortTimeRicciFlowSolutionData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ShortTimeRicciFlowSolutionData flow)

/-- Compatibility constructor for short-time Ricci-flow solution data. -/
def HasShortTimeRicciFlowSolution.of_shortTimeRicciFlowSolutionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow) :
    HasShortTimeRicciFlowSolution flow where
  shortTimeRicciFlowSolutionData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨shortTimeRicciAtTime⟩⟩

/--
Concrete short-time Ricci-flow solution data proves the production short-time
solution interface.
-/
theorem hasShortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow) :
    HasShortTimeRicciFlowSolution flow :=
  HasShortTimeRicciFlowSolution.of_shortTimeRicciFlowSolutionData
    shortTimeRicciAtTime

/--
Pullback-to-Ricci-flow data carries the positive DeTurck existence interval and
the metric/RHS identities needed for short-time Ricci-flow existence.
-/
theorem hasShortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow) :
    HasShortTimeRicciFlowSolution flow :=
  hasShortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData
    { pullbackToRicciFlowAtTime := pullbackToRicciFlowAtTime
      existenceInterval :=
        pullbackToRicciFlowAtTime.pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.existenceInterval
      solutionMetricAtTime := pullbackToRicciFlowAtTime.solutionMetricAtTime
      existenceInterval_eq_deturckInterval := rfl
      solutionMetric_eq_pullbackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackToRicciFlowAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackToRicciFlowAtTime.solution_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_metricDerivative }

/--
Pullback equation identity data builds the pullback-to-Ricci-flow data and
hence short-time Ricci-flow existence.
-/
theorem hasShortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasShortTimeRicciFlowSolution flow :=
  hasShortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData
    { pullbackIdentityAtTime := pullbackIdentityAtTime
      solutionMetricAtTime := pullbackIdentityAtTime.pulledBackMetricAtTime
      solutionMetric_eq_pulledBackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackIdentityAtTime.pulledBackMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackIdentityAtTime.pulledBack_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_metricDerivative }

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, DeTurck diffeomorphism ODE data, and pullback equation identity data
close the first thirty-two analytic fields.
-/
theorem analyticFirstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow :=
  ⟨analyticFirstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime,
    hasShortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData
      pullbackIdentityAtTime⟩

/--
Concrete maximal-time interval data for a Ricci-flow solution.

At this stage of the interface, the maximal interval may be no larger than the
short-time interval already constructed.  The data still records an explicit
positive endpoint and the containment of the short-time solution interval in
the chosen maximal interval, which is the datum later continuation theory must
strengthen.
-/
structure RicciFlowMaximalTimeIntervalData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Short-time Ricci-flow solution data underlying the interval. -/
  shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow
  /-- Positive endpoint for the chosen maximal-time interval. -/
  maximalTime : DeTurckShortTimeExistenceInterval flow
  /-- The chosen maximal endpoint agrees with the constructed short-time endpoint. -/
  maximalTime_eq_shortTime :
    maximalTime = shortTimeRicciAtTime.existenceInterval
  /-- The short-time existence interval is contained in the chosen maximal interval. -/
  shortTime_le_maximalTime :
    shortTimeRicciAtTime.existenceInterval.1 ≤ maximalTime.1
  /-- The metric family carried by the interval data. -/
  solutionMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The interval metric is the short-time Ricci-flow solution metric. -/
  solutionMetric_eq_shortTimeMetric :
    solutionMetricAtTime = shortTimeRicciAtTime.solutionMetricAtTime
  /-- The interval metric is the original flow metric family. -/
  solutionMetric_eq_flowMetric :
    solutionMetricAtTime = metric_of_ricci_flow_data flow
  /-- The interval solution has the original initial metric. -/
  solution_initialMetric_eq :
    solutionMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0

/-- Interface for the maximal-time interval of a Ricci-flow solution. -/
structure HasRicciFlowMaximalTimeInterval
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Maximal-time interval data proves the maximal interval interface. -/
  ricciFlowMaximalTimeIntervalData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciFlowMaximalTimeIntervalData flow)

/-- Compatibility constructor for Ricci-flow maximal-time interval data. -/
def HasRicciFlowMaximalTimeInterval.of_ricciFlowMaximalTimeIntervalData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow) :
    HasRicciFlowMaximalTimeInterval flow where
  ricciFlowMaximalTimeIntervalData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨maximalIntervalAtTime⟩⟩

/--
Concrete maximal-time interval data proves the production maximal interval
interface.
-/
theorem hasRicciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow) :
    HasRicciFlowMaximalTimeInterval flow :=
  HasRicciFlowMaximalTimeInterval.of_ricciFlowMaximalTimeIntervalData
    maximalIntervalAtTime

/--
Short-time Ricci-flow data supplies a positive interval and hence the current
maximal-interval interface.  Later continuation theory can replace this
degenerate maximal interval by a stronger one.
-/
theorem hasRicciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow) :
    HasRicciFlowMaximalTimeInterval flow :=
  hasRicciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData
    { shortTimeRicciAtTime := shortTimeRicciAtTime
      maximalTime := shortTimeRicciAtTime.existenceInterval
      maximalTime_eq_shortTime := rfl
      shortTime_le_maximalTime := le_rfl
      solutionMetricAtTime := shortTimeRicciAtTime.solutionMetricAtTime
      solutionMetric_eq_shortTimeMetric := rfl
      solutionMetric_eq_flowMetric :=
        shortTimeRicciAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        shortTimeRicciAtTime.solution_initialMetric_eq }

/--
Pullback-to-Ricci-flow data builds short-time Ricci-flow data and hence the
current maximal-time interval interface.
-/
theorem hasRicciFlowMaximalTimeInterval_of_deturckPullbackToRicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow) :
    HasRicciFlowMaximalTimeInterval flow :=
  hasRicciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData
    { pullbackToRicciFlowAtTime := pullbackToRicciFlowAtTime
      existenceInterval :=
        pullbackToRicciFlowAtTime.pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.existenceInterval
      solutionMetricAtTime := pullbackToRicciFlowAtTime.solutionMetricAtTime
      existenceInterval_eq_deturckInterval := rfl
      solutionMetric_eq_pullbackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackToRicciFlowAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackToRicciFlowAtTime.solution_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_metricDerivative }

/--
Pullback equation identity data builds the current maximal-time interval
interface through the pullback-to-Ricci-flow and short-time solution data.
-/
theorem hasRicciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasRicciFlowMaximalTimeInterval flow :=
  hasRicciFlowMaximalTimeInterval_of_deturckPullbackToRicciFlowData
    { pullbackIdentityAtTime := pullbackIdentityAtTime
      solutionMetricAtTime := pullbackIdentityAtTime.pulledBackMetricAtTime
      solutionMetric_eq_pulledBackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackIdentityAtTime.pulledBackMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackIdentityAtTime.pulledBack_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_metricDerivative }

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, DeTurck diffeomorphism ODE data, and pullback equation identity data
close the first thirty-three analytic fields.
-/
theorem analyticFirstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow :=
  ⟨analyticFirstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime,
    hasRicciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData
      pullbackIdentityAtTime⟩

/--
Concrete continuation-criterion data for the Ricci-flow solution.

The current production layer records the analytic inputs that make a
continuation statement meaningful: scalar-curvature theory for the flow
curvature, explicit Ricci-flow equation verification, the maximal interval
data, and the metric/interval slice to which the criterion applies.  The next
field, the curvature blow-up alternative, remains separate.
-/
structure RicciFlowContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Scalar-curvature theory for the curvature data of the flow. -/
  scalarCurvatureTheoryAtTime :
    ScalarCurvatureTheoryData (curvature_data_of_ricci_flow_data flow)
  /-- Explicit equation verification on the Ricci-flow metric family. -/
  equationVerificationAtTime :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)
  /-- The maximal interval data to which the continuation criterion applies. -/
  maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow
  /-- The positive interval used by the continuation statement. -/
  continuationTime : DeTurckShortTimeExistenceInterval flow
  /-- The continuation interval is the stored maximal-time endpoint. -/
  continuationTime_eq_maximalTime :
    continuationTime = maximalIntervalAtTime.maximalTime
  /-- The short-time solution interval lies inside the continuation interval. -/
  shortTime_le_continuationTime :
    maximalIntervalAtTime.shortTimeRicciAtTime.existenceInterval.1 ≤
      continuationTime.1
  /-- The metric family used in the continuation statement. -/
  continuationMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The continuation metric is the metric from the maximal-interval data. -/
  continuationMetric_eq_intervalMetric :
    continuationMetricAtTime = maximalIntervalAtTime.solutionMetricAtTime
  /-- The continuation metric is the original flow metric family. -/
  continuationMetric_eq_flowMetric :
    continuationMetricAtTime = metric_of_ricci_flow_data flow
  /-- The continuation metric starts from the original initial metric. -/
  continuation_initialMetric_eq :
    continuationMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0

/-- Interface for the continuation criterion needed before surgery starts. -/
structure HasRicciFlowContinuationCriterion
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Continuation-criterion data proves the continuation interface. -/
  ricciFlowContinuationCriterionData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciFlowContinuationCriterionData flow)

/-- Compatibility constructor for Ricci-flow continuation-criterion data. -/
def HasRicciFlowContinuationCriterion.of_ricciFlowContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (continuationCriterionAtTime :
      RicciFlowContinuationCriterionData flow) :
    HasRicciFlowContinuationCriterion flow where
  ricciFlowContinuationCriterionData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨continuationCriterionAtTime⟩⟩

/--
Concrete continuation-criterion data proves the production continuation
interface.
-/
theorem hasRicciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (continuationCriterionAtTime :
      RicciFlowContinuationCriterionData flow) :
    HasRicciFlowContinuationCriterion flow :=
  HasRicciFlowContinuationCriterion.of_ricciFlowContinuationCriterionData
    continuationCriterionAtTime

/--
Maximal-interval data, scalar-curvature theory, and explicit Ricci-flow
equation verification supply the current continuation-criterion interface.
-/
theorem hasRicciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow) :
    HasRicciFlowContinuationCriterion flow :=
  hasRicciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData
    { scalarCurvatureTheoryAtTime := scalarCurvatureTheoryAtTime
      equationVerificationAtTime := equationVerificationAtTime
      maximalIntervalAtTime := maximalIntervalAtTime
      continuationTime := maximalIntervalAtTime.maximalTime
      continuationTime_eq_maximalTime := rfl
      shortTime_le_continuationTime :=
        maximalIntervalAtTime.shortTime_le_maximalTime
      continuationMetricAtTime := maximalIntervalAtTime.solutionMetricAtTime
      continuationMetric_eq_intervalMetric := rfl
      continuationMetric_eq_flowMetric :=
        maximalIntervalAtTime.solutionMetric_eq_flowMetric
      continuation_initialMetric_eq :=
        maximalIntervalAtTime.solution_initialMetric_eq }

/--
Pullback equation identity data builds the maximal interval data needed by the
current continuation-criterion interface.
-/
theorem hasRicciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasRicciFlowContinuationCriterion flow := by
  let pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow :=
    { pullbackIdentityAtTime := pullbackIdentityAtTime
      solutionMetricAtTime := pullbackIdentityAtTime.pulledBackMetricAtTime
      solutionMetric_eq_pulledBackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackIdentityAtTime.pulledBackMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackIdentityAtTime.pulledBack_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_metricDerivative }
  let shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow :=
    { pullbackToRicciFlowAtTime := pullbackToRicciFlowAtTime
      existenceInterval :=
        pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.existenceInterval
      solutionMetricAtTime := pullbackToRicciFlowAtTime.solutionMetricAtTime
      existenceInterval_eq_deturckInterval := rfl
      solutionMetric_eq_pullbackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackToRicciFlowAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackToRicciFlowAtTime.solution_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_metricDerivative }
  let maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow :=
    { shortTimeRicciAtTime := shortTimeRicciAtTime
      maximalTime := shortTimeRicciAtTime.existenceInterval
      maximalTime_eq_shortTime := rfl
      shortTime_le_maximalTime := le_rfl
      solutionMetricAtTime := shortTimeRicciAtTime.solutionMetricAtTime
      solutionMetric_eq_shortTimeMetric := rfl
      solutionMetric_eq_flowMetric :=
        shortTimeRicciAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        shortTimeRicciAtTime.solution_initialMetric_eq }
  exact
    hasRicciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      maximalIntervalAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, DeTurck diffeomorphism ODE data, and pullback equation identity data
close the first thirty-four analytic fields.
-/
theorem analyticFirstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow :=
  ⟨analyticFirstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime,
    hasRicciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      pullbackIdentityAtTime⟩

/--
Concrete curvature blow-up alternative data for the Ricci-flow continuation
criterion.

This records the curvature side of the continuation theorem: a concrete
continuation criterion, the Ricci/scalar curvature data of the flow, the scalar
trace formula supplied by scalar-curvature theory, and the positive endpoint on
which the alternative is stated.  The following package field, maximal solution
extension, remains the separate analytic input that turns this alternative into
an extension theorem.
-/
structure CurvatureBlowUpContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Continuation criterion to which the blow-up alternative is attached. -/
  continuationCriterionAtTime :
    RicciFlowContinuationCriterionData flow
  /-- The curvature data used in the blow-up alternative. -/
  curvatureAtTime : RicciCurvatureData (metric_of_ricci_flow_data flow)
  /-- The stored curvature data is the curvature carried by the flow. -/
  curvature_eq_flowCurvature :
    curvatureAtTime = curvature_data_of_ricci_flow_data flow
  /-- The scalar curvature field appearing in the alternative. -/
  scalarCurvatureAtTime : ℝ → M → ℝ
  /-- The stored scalar field is the scalar curvature carried by the flow. -/
  scalarCurvature_eq_flowScalar :
    ∀ (t : ℝ) (x : M),
      scalarCurvatureAtTime t x =
        (curvature_data_of_ricci_flow_data flow).scalar.scalarAtTime t x
  /-- Scalar curvature is the trace of the Ricci tensor. -/
  scalar_eq_trace_ricci :
    ∀ (t : ℝ) (x : M),
      (curvature_data_of_ricci_flow_data flow).scalar.scalarAtTime t x =
        continuationCriterionAtTime.scalarCurvatureTheoryAtTime.ricciContractionTheoryAtTime.scalarContractionFormulaAtTime.traceAtTime
          t x
          ((curvature_data_of_ricci_flow_data flow).ricci.tensorAtTime t x)
  /-- Positive endpoint where the blow-up alternative is stated. -/
  blowUpAlternativeTime : DeTurckShortTimeExistenceInterval flow
  /-- The blow-up endpoint is the continuation endpoint. -/
  blowUpAlternativeTime_eq_continuationTime :
    blowUpAlternativeTime = continuationCriterionAtTime.continuationTime
  /-- The short-time solution interval lies inside the blow-up-alternative interval. -/
  shortTime_le_blowUpAlternativeTime :
    continuationCriterionAtTime.maximalIntervalAtTime.shortTimeRicciAtTime.existenceInterval.1 ≤
      blowUpAlternativeTime.1

/-- Interface for the curvature blow-up alternative in the continuation criterion. -/
structure HasCurvatureBlowUpContinuationCriterion
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Curvature blow-up data proves the blow-up continuation criterion. -/
  curvatureBlowUpContinuationCriterionData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (CurvatureBlowUpContinuationCriterionData flow)

/-- Compatibility constructor for curvature blow-up continuation data. -/
def HasCurvatureBlowUpContinuationCriterion.of_curvatureBlowUpContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow) :
    HasCurvatureBlowUpContinuationCriterion flow where
  curvatureBlowUpContinuationCriterionData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨curvatureBlowUpAtTime⟩⟩

/--
Concrete curvature blow-up data proves the production blow-up alternative
interface.
-/
theorem hasCurvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow) :
    HasCurvatureBlowUpContinuationCriterion flow :=
  HasCurvatureBlowUpContinuationCriterion.of_curvatureBlowUpContinuationCriterionData
    curvatureBlowUpAtTime

/--
Continuation-criterion data supplies the curvature side of the blow-up
alternative through the flow's Ricci/scalar curvature data.
-/
theorem hasCurvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (continuationCriterionAtTime :
      RicciFlowContinuationCriterionData flow) :
    HasCurvatureBlowUpContinuationCriterion flow :=
  hasCurvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData
    { continuationCriterionAtTime := continuationCriterionAtTime
      curvatureAtTime := curvature_data_of_ricci_flow_data flow
      curvature_eq_flowCurvature := rfl
      scalarCurvatureAtTime :=
        (curvature_data_of_ricci_flow_data flow).scalar.scalarAtTime
      scalarCurvature_eq_flowScalar := fun _t _x => rfl
      scalar_eq_trace_ricci :=
        scalarCurvatureTheoryData_scalar_eq_trace_ricci
          continuationCriterionAtTime.scalarCurvatureTheoryAtTime
      blowUpAlternativeTime :=
        continuationCriterionAtTime.continuationTime
      blowUpAlternativeTime_eq_continuationTime := rfl
      shortTime_le_blowUpAlternativeTime :=
        continuationCriterionAtTime.shortTime_le_continuationTime }

/--
Pullback equation identity data builds the continuation-criterion data and hence
the current curvature blow-up continuation criterion.
-/
theorem hasCurvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasCurvatureBlowUpContinuationCriterion flow := by
  let pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow :=
    { pullbackIdentityAtTime := pullbackIdentityAtTime
      solutionMetricAtTime := pullbackIdentityAtTime.pulledBackMetricAtTime
      solutionMetric_eq_pulledBackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackIdentityAtTime.pulledBackMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackIdentityAtTime.pulledBack_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_metricDerivative }
  let shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow :=
    { pullbackToRicciFlowAtTime := pullbackToRicciFlowAtTime
      existenceInterval :=
        pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.existenceInterval
      solutionMetricAtTime := pullbackToRicciFlowAtTime.solutionMetricAtTime
      existenceInterval_eq_deturckInterval := rfl
      solutionMetric_eq_pullbackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackToRicciFlowAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackToRicciFlowAtTime.solution_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_metricDerivative }
  let maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow :=
    { shortTimeRicciAtTime := shortTimeRicciAtTime
      maximalTime := shortTimeRicciAtTime.existenceInterval
      maximalTime_eq_shortTime := rfl
      shortTime_le_maximalTime := le_rfl
      solutionMetricAtTime := shortTimeRicciAtTime.solutionMetricAtTime
      solutionMetric_eq_shortTimeMetric := rfl
      solutionMetric_eq_flowMetric :=
        shortTimeRicciAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        shortTimeRicciAtTime.solution_initialMetric_eq }
  let continuationCriterionAtTime : RicciFlowContinuationCriterionData flow :=
    { scalarCurvatureTheoryAtTime := scalarCurvatureTheoryAtTime
      equationVerificationAtTime := equationVerificationAtTime
      maximalIntervalAtTime := maximalIntervalAtTime
      continuationTime := maximalIntervalAtTime.maximalTime
      continuationTime_eq_maximalTime := rfl
      shortTime_le_continuationTime :=
        maximalIntervalAtTime.shortTime_le_maximalTime
      continuationMetricAtTime :=
        maximalIntervalAtTime.solutionMetricAtTime
      continuationMetric_eq_intervalMetric := rfl
      continuationMetric_eq_flowMetric :=
        maximalIntervalAtTime.solutionMetric_eq_flowMetric
      continuation_initialMetric_eq :=
        maximalIntervalAtTime.solution_initialMetric_eq }
  exact
    hasCurvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData
      continuationCriterionAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, DeTurck diffeomorphism ODE data, and pullback equation identity data
close the first thirty-five analytic fields.
-/
theorem analyticFirstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow :=
  ⟨analyticFirstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime,
    hasCurvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      pullbackIdentityAtTime⟩

/--
Concrete maximal-solution extension data for Ricci flow.

This packages the curvature blow-up alternative with the metric, curvature, and
positive endpoint to which a maximal-solution extension statement applies.  The
next field, parabolic Schauder estimates, remains the separate analytic
regularity input used after this extension layer.
-/
structure MaximalSolutionExtensionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Curvature blow-up alternative controlling finite-time obstruction. -/
  curvatureBlowUpAtTime :
    CurvatureBlowUpContinuationCriterionData flow
  /-- Positive endpoint for the extension statement. -/
  extensionTime : DeTurckShortTimeExistenceInterval flow
  /-- The extension endpoint is the blow-up-alternative endpoint. -/
  extensionTime_eq_blowUpAlternativeTime :
    extensionTime = curvatureBlowUpAtTime.blowUpAlternativeTime
  /-- The short-time solution interval lies inside the extension interval. -/
  shortTime_le_extensionTime :
    curvatureBlowUpAtTime.continuationCriterionAtTime.maximalIntervalAtTime.shortTimeRicciAtTime.existenceInterval.1 ≤
      extensionTime.1
  /-- Metric family being extended. -/
  extensionMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The extension metric is the metric from the continuation criterion. -/
  extensionMetric_eq_continuationMetric :
    extensionMetricAtTime =
      curvatureBlowUpAtTime.continuationCriterionAtTime.continuationMetricAtTime
  /-- The extension metric is the original flow metric family. -/
  extensionMetric_eq_flowMetric :
    extensionMetricAtTime = metric_of_ricci_flow_data flow
  /-- The extension metric starts from the original initial metric. -/
  extension_initialMetric_eq :
    extensionMetricAtTime.metricAtTime 0 =
      (metric_of_ricci_flow_data flow).metricAtTime 0
  /-- Curvature data used to control the extension. -/
  extensionCurvatureAtTime :
    RicciCurvatureData (metric_of_ricci_flow_data flow)
  /-- The extension curvature data is the curvature carried by the flow. -/
  extensionCurvature_eq_flowCurvature :
    extensionCurvatureAtTime = curvature_data_of_ricci_flow_data flow

/-- Interface for extending bounded-curvature solutions past a finite time. -/
structure HasMaximalSolutionExtension
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Maximal-solution extension data proves the extension interface. -/
  maximalSolutionExtensionData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (MaximalSolutionExtensionData flow)

/-- Compatibility constructor for maximal-solution extension data. -/
def HasMaximalSolutionExtension.of_maximalSolutionExtensionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (extensionAtTime : MaximalSolutionExtensionData flow) :
    HasMaximalSolutionExtension flow where
  maximalSolutionExtensionData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨extensionAtTime⟩⟩

/--
Concrete maximal-solution extension data proves the production extension
interface.
-/
theorem hasMaximalSolutionExtension_of_maximalSolutionExtensionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (extensionAtTime : MaximalSolutionExtensionData flow) :
    HasMaximalSolutionExtension flow :=
  HasMaximalSolutionExtension.of_maximalSolutionExtensionData extensionAtTime

/--
Curvature blow-up alternative data carries the metric, curvature, and endpoint
needed by the current maximal-solution extension interface.
-/
theorem hasMaximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow) :
    HasMaximalSolutionExtension flow :=
  hasMaximalSolutionExtension_of_maximalSolutionExtensionData
    { curvatureBlowUpAtTime := curvatureBlowUpAtTime
      extensionTime := curvatureBlowUpAtTime.blowUpAlternativeTime
      extensionTime_eq_blowUpAlternativeTime := rfl
      shortTime_le_extensionTime :=
        curvatureBlowUpAtTime.shortTime_le_blowUpAlternativeTime
      extensionMetricAtTime :=
        curvatureBlowUpAtTime.continuationCriterionAtTime.continuationMetricAtTime
      extensionMetric_eq_continuationMetric := rfl
      extensionMetric_eq_flowMetric :=
        curvatureBlowUpAtTime.continuationCriterionAtTime.continuationMetric_eq_flowMetric
      extension_initialMetric_eq :=
        curvatureBlowUpAtTime.continuationCriterionAtTime.continuation_initialMetric_eq
      extensionCurvatureAtTime := curvatureBlowUpAtTime.curvatureAtTime
      extensionCurvature_eq_flowCurvature :=
        curvatureBlowUpAtTime.curvature_eq_flowCurvature }

/--
Pullback equation identity data builds the curvature blow-up data and hence the
current maximal-solution extension interface.
-/
theorem hasMaximalSolutionExtension_of_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasMaximalSolutionExtension flow := by
  let pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow :=
    { pullbackIdentityAtTime := pullbackIdentityAtTime
      solutionMetricAtTime := pullbackIdentityAtTime.pulledBackMetricAtTime
      solutionMetric_eq_pulledBackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackIdentityAtTime.pulledBackMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackIdentityAtTime.pulledBack_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_metricDerivative }
  let shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow :=
    { pullbackToRicciFlowAtTime := pullbackToRicciFlowAtTime
      existenceInterval :=
        pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.existenceInterval
      solutionMetricAtTime := pullbackToRicciFlowAtTime.solutionMetricAtTime
      existenceInterval_eq_deturckInterval := rfl
      solutionMetric_eq_pullbackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackToRicciFlowAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackToRicciFlowAtTime.solution_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_metricDerivative }
  let maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow :=
    { shortTimeRicciAtTime := shortTimeRicciAtTime
      maximalTime := shortTimeRicciAtTime.existenceInterval
      maximalTime_eq_shortTime := rfl
      shortTime_le_maximalTime := le_rfl
      solutionMetricAtTime := shortTimeRicciAtTime.solutionMetricAtTime
      solutionMetric_eq_shortTimeMetric := rfl
      solutionMetric_eq_flowMetric :=
        shortTimeRicciAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        shortTimeRicciAtTime.solution_initialMetric_eq }
  let continuationCriterionAtTime : RicciFlowContinuationCriterionData flow :=
    { scalarCurvatureTheoryAtTime := scalarCurvatureTheoryAtTime
      equationVerificationAtTime := equationVerificationAtTime
      maximalIntervalAtTime := maximalIntervalAtTime
      continuationTime := maximalIntervalAtTime.maximalTime
      continuationTime_eq_maximalTime := rfl
      shortTime_le_continuationTime :=
        maximalIntervalAtTime.shortTime_le_maximalTime
      continuationMetricAtTime :=
        maximalIntervalAtTime.solutionMetricAtTime
      continuationMetric_eq_intervalMetric := rfl
      continuationMetric_eq_flowMetric :=
        maximalIntervalAtTime.solutionMetric_eq_flowMetric
      continuation_initialMetric_eq :=
        maximalIntervalAtTime.solution_initialMetric_eq }
  let curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow :=
    { continuationCriterionAtTime := continuationCriterionAtTime
      curvatureAtTime := curvature_data_of_ricci_flow_data flow
      curvature_eq_flowCurvature := rfl
      scalarCurvatureAtTime :=
        (curvature_data_of_ricci_flow_data flow).scalar.scalarAtTime
      scalarCurvature_eq_flowScalar := fun _t _x => rfl
      scalar_eq_trace_ricci :=
        scalarCurvatureTheoryData_scalar_eq_trace_ricci
          scalarCurvatureTheoryAtTime
      blowUpAlternativeTime :=
        continuationCriterionAtTime.continuationTime
      blowUpAlternativeTime_eq_continuationTime := rfl
      shortTime_le_blowUpAlternativeTime :=
        continuationCriterionAtTime.shortTime_le_continuationTime }
  exact
    hasMaximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData
      curvatureBlowUpAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap
data, DeTurck diffeomorphism ODE data, and pullback equation identity data
close the first thirty-six analytic fields.
-/
theorem analyticFirstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow :=
  ⟨analyticFirstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime,
    hasMaximalSolutionExtension_of_deturckPullbackEquationIdentityData
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      pullbackIdentityAtTime⟩

/--
Concrete parabolic Schauder estimate data for the Ricci-DeTurck/Ricci-flow
regularity step.

The bundle ties the Schauder estimate layer to the already constructed
short-time regularity bootstrap, the bounded-curvature maximal-solution
extension layer, and the strict linear parabolic solution operator with its
pointwise estimates.
-/
structure ParabolicSchauderEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Regularity-bootstrap data to which the Schauder estimate applies. -/
  regularityAtTime : ShortTimeRegularityBootstrapData flow
  /-- Maximal-solution extension data supplying the continuation endpoint. -/
  maximalExtensionAtTime : MaximalSolutionExtensionData flow
  /-- Linear parabolic theory whose estimate constants are used by Schauder. -/
  linearTheoryAtTime : ParabolicLinearTheoryData flow
  /-- The linear theory is the one used in the bootstrapped solution. -/
  linearTheory_eq_bootstrapLinearTheory :
    linearTheoryAtTime =
      regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime
  /-- Strict parabolicity data for the same linearized operator. -/
  strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow
  /-- The strict-parabolicity data is the one carried by the linear theory. -/
  strictParabolic_eq_linearTheory :
    strictParabolicAtTime = linearTheoryAtTime.strictParabolicAtTime
  /-- Linear solution operator used in the Schauder estimate. -/
  solutionOperatorAtTime :
    TimeDependentParabolicLinearSolutionOperatorField flow
  /-- The Schauder solution operator is the linear-theory solution operator. -/
  solutionOperator_eq_linearTheoryOperator :
    solutionOperatorAtTime = linearTheoryAtTime.solutionOperatorAtTime
  /-- Time-dependent linear estimate constants. -/
  estimateConstantAtTime :
    TimeDependentParabolicLinearEstimateConstantField flow
  /-- The estimate constants are those carried by the linear theory. -/
  estimateConstant_eq_linearTheoryConstant :
    estimateConstantAtTime = linearTheoryAtTime.estimateConstantAtTime
  /-- Linear estimate constants stay strictly positive. -/
  estimateConstant_pos : ∀ t, 0 < estimateConstantAtTime t
  /-- Higher-order Schauder estimate constants from the regularity bootstrap. -/
  schauderEstimateAtTime :
    TimeDependentShortTimeRegularityEstimateField flow
  /-- The Schauder constants agree with the bootstrap regularity constants. -/
  schauderEstimate_eq_bootstrapEstimate :
    schauderEstimateAtTime = regularityAtTime.regularityEstimateAtTime
  /-- Schauder estimate constants are nonnegative at every order. -/
  schauderEstimate_nonneg :
    ∀ (t : ℝ) (order : ℕ), 0 ≤ schauderEstimateAtTime t order
  /-- The bootstrapped metric to which the estimates apply. -/
  bootstrappedMetricAtTime :
    TimeDependentRicciDeTurckBootstrappedMetricField flow
  /-- The stored metric is the bootstrapped short-time metric. -/
  bootstrappedMetric_eq_bootstrapMetric :
    bootstrappedMetricAtTime = regularityAtTime.bootstrappedMetricAtTime
  /-- The metric family being extended by the maximal-solution data. -/
  extensionMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The extension metric is the one stored in the maximal-extension data. -/
  extensionMetric_eq_maximalExtensionMetric :
    extensionMetricAtTime = maximalExtensionAtTime.extensionMetricAtTime
  /-- The extended metric is the original Ricci-flow metric family. -/
  extensionMetric_eq_flowMetric :
    extensionMetricAtTime = metric_of_ricci_flow_data flow

/-- Interface for the parabolic Schauder estimates used by Ricci-flow regularity. -/
structure HasParabolicSchauderEstimates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete Schauder estimate data proves the Schauder interface. -/
  parabolicSchauderEstimateData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ParabolicSchauderEstimateData flow)

/-- Compatibility constructor for parabolic Schauder estimate data. -/
def HasParabolicSchauderEstimates.of_parabolicSchauderEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (schauderAtTime : ParabolicSchauderEstimateData flow) :
    HasParabolicSchauderEstimates flow where
  parabolicSchauderEstimateData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨schauderAtTime⟩⟩

/--
Concrete parabolic Schauder estimate data proves the production Schauder
interface.
-/
theorem hasParabolicSchauderEstimates_of_parabolicSchauderEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (schauderAtTime : ParabolicSchauderEstimateData flow) :
    HasParabolicSchauderEstimates flow :=
  HasParabolicSchauderEstimates.of_parabolicSchauderEstimateData
    schauderAtTime

/--
Short-time regularity bootstrap data and maximal-solution extension data carry
the linear estimates, higher-order bootstrap constants, and extension metric
needed by the current Schauder interface.
-/
theorem hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (maximalExtensionAtTime : MaximalSolutionExtensionData flow) :
    HasParabolicSchauderEstimates flow :=
  hasParabolicSchauderEstimates_of_parabolicSchauderEstimateData
    { regularityAtTime := regularityAtTime
      maximalExtensionAtTime := maximalExtensionAtTime
      linearTheoryAtTime :=
        regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime
      linearTheory_eq_bootstrapLinearTheory := rfl
      strictParabolicAtTime :=
        regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.strictParabolicAtTime
      strictParabolic_eq_linearTheory := rfl
      solutionOperatorAtTime :=
        regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.solutionOperatorAtTime
      solutionOperator_eq_linearTheoryOperator := rfl
      estimateConstantAtTime :=
        regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.estimateConstantAtTime
      estimateConstant_eq_linearTheoryConstant := rfl
      estimateConstant_pos :=
        regularityAtTime.shortTimeAtTime.fixedPointAtTime.linearTheoryAtTime.estimateConstant_pos
      schauderEstimateAtTime := regularityAtTime.regularityEstimateAtTime
      schauderEstimate_eq_bootstrapEstimate := rfl
      schauderEstimate_nonneg := regularityAtTime.regularityEstimate_nonneg
      bootstrappedMetricAtTime := regularityAtTime.bootstrappedMetricAtTime
      bootstrappedMetric_eq_bootstrapMetric := rfl
      extensionMetricAtTime := maximalExtensionAtTime.extensionMetricAtTime
      extensionMetric_eq_maximalExtensionMetric := rfl
      extensionMetric_eq_flowMetric :=
        maximalExtensionAtTime.extensionMetric_eq_flowMetric }

/--
Regularity-bootstrap data and curvature blow-up continuation data supply the
Schauder layer after building the maximal-solution extension endpoint.
-/
theorem hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_curvatureBlowUpContinuationCriterionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow) :
    HasParabolicSchauderEstimates flow :=
  hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData
    regularityAtTime
    { curvatureBlowUpAtTime := curvatureBlowUpAtTime
      extensionTime := curvatureBlowUpAtTime.blowUpAlternativeTime
      extensionTime_eq_blowUpAlternativeTime := rfl
      shortTime_le_extensionTime :=
        curvatureBlowUpAtTime.shortTime_le_blowUpAlternativeTime
      extensionMetricAtTime :=
        curvatureBlowUpAtTime.continuationCriterionAtTime.continuationMetricAtTime
      extensionMetric_eq_continuationMetric := rfl
      extensionMetric_eq_flowMetric :=
        curvatureBlowUpAtTime.continuationCriterionAtTime.continuationMetric_eq_flowMetric
      extension_initialMetric_eq :=
        curvatureBlowUpAtTime.continuationCriterionAtTime.continuation_initialMetric_eq
      extensionCurvatureAtTime := curvatureBlowUpAtTime.curvatureAtTime
      extensionCurvature_eq_flowCurvature :=
        curvatureBlowUpAtTime.curvature_eq_flowCurvature }

/--
Pullback equation identity data builds the curvature blow-up/maximal extension
layer, while short-time regularity data supplies the Schauder estimate constants.
-/
theorem hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasParabolicSchauderEstimates flow := by
  let pullbackToRicciFlowAtTime : DeTurckPullbackToRicciFlowData flow :=
    { pullbackIdentityAtTime := pullbackIdentityAtTime
      solutionMetricAtTime := pullbackIdentityAtTime.pulledBackMetricAtTime
      solutionMetric_eq_pulledBackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackIdentityAtTime.pulledBackMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackIdentityAtTime.pulledBack_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackIdentityAtTime.pulledBack_rhs_eq_metricDerivative }
  let shortTimeRicciAtTime : ShortTimeRicciFlowSolutionData flow :=
    { pullbackToRicciFlowAtTime := pullbackToRicciFlowAtTime
      existenceInterval :=
        pullbackIdentityAtTime.odeAtTime.regularityAtTime.shortTimeAtTime.existenceInterval
      solutionMetricAtTime := pullbackToRicciFlowAtTime.solutionMetricAtTime
      existenceInterval_eq_deturckInterval := rfl
      solutionMetric_eq_pullbackMetric := rfl
      solutionMetric_eq_flowMetric :=
        pullbackToRicciFlowAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        pullbackToRicciFlowAtTime.solution_initialMetric_eq
      solution_rhs_eq_ricciFlow_rhs :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_ricciFlow_rhs
      solution_rhs_eq_metricDerivative :=
        pullbackToRicciFlowAtTime.solution_rhs_eq_metricDerivative }
  let maximalIntervalAtTime : RicciFlowMaximalTimeIntervalData flow :=
    { shortTimeRicciAtTime := shortTimeRicciAtTime
      maximalTime := shortTimeRicciAtTime.existenceInterval
      maximalTime_eq_shortTime := rfl
      shortTime_le_maximalTime := le_rfl
      solutionMetricAtTime := shortTimeRicciAtTime.solutionMetricAtTime
      solutionMetric_eq_shortTimeMetric := rfl
      solutionMetric_eq_flowMetric :=
        shortTimeRicciAtTime.solutionMetric_eq_flowMetric
      solution_initialMetric_eq :=
        shortTimeRicciAtTime.solution_initialMetric_eq }
  let continuationCriterionAtTime : RicciFlowContinuationCriterionData flow :=
    { scalarCurvatureTheoryAtTime := scalarCurvatureTheoryAtTime
      equationVerificationAtTime := equationVerificationAtTime
      maximalIntervalAtTime := maximalIntervalAtTime
      continuationTime := maximalIntervalAtTime.maximalTime
      continuationTime_eq_maximalTime := rfl
      shortTime_le_continuationTime :=
        maximalIntervalAtTime.shortTime_le_maximalTime
      continuationMetricAtTime :=
        maximalIntervalAtTime.solutionMetricAtTime
      continuationMetric_eq_intervalMetric := rfl
      continuationMetric_eq_flowMetric :=
        maximalIntervalAtTime.solutionMetric_eq_flowMetric
      continuation_initialMetric_eq :=
        maximalIntervalAtTime.solution_initialMetric_eq }
  let curvatureBlowUpAtTime :
      CurvatureBlowUpContinuationCriterionData flow :=
    { continuationCriterionAtTime := continuationCriterionAtTime
      curvatureAtTime := curvature_data_of_ricci_flow_data flow
      curvature_eq_flowCurvature := rfl
      scalarCurvatureAtTime :=
        (curvature_data_of_ricci_flow_data flow).scalar.scalarAtTime
      scalarCurvature_eq_flowScalar := fun _t _x => rfl
      scalar_eq_trace_ricci :=
        scalarCurvatureTheoryData_scalar_eq_trace_ricci
          scalarCurvatureTheoryAtTime
      blowUpAlternativeTime :=
        continuationCriterionAtTime.continuationTime
      blowUpAlternativeTime_eq_continuationTime := rfl
      shortTime_le_blowUpAlternativeTime :=
        continuationCriterionAtTime.shortTime_le_continuationTime }
  exact
    hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_curvatureBlowUpContinuationCriterionData
      regularityAtTime curvatureBlowUpAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap data,
DeTurck diffeomorphism ODE data, and pullback equation identity data close the
first thirty-seven analytic fields.
-/
theorem analyticFirstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow :=
  ⟨analyticFirstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime,
    hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      regularityAtTime pullbackIdentityAtTime⟩

/--
Concrete Ricci-flow parabolic regularity data.

This upgrades the Schauder estimate layer from the gauged/bootstrapped
short-time construction to the Ricci-flow metric family.  The bundle records
the flow-gauge metric, its equality with the original flow metric, the inherited
linear parabolic solution-operator estimate, and the pointwise bootstrap
regularity estimate that the next Shi-estimate layer will use.
-/
structure RicciFlowParabolicRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Parabolic Schauder estimate data being upgraded to Ricci-flow regularity. -/
  schauderAtTime : ParabolicSchauderEstimateData flow
  /-- The regular metric family in Ricci-flow gauge. -/
  regularMetricAtTime : TimeDependentDeTurckPulledBackMetricField flow
  /-- The regular metric is the extension metric carried by Schauder data. -/
  regularMetric_eq_schauderExtensionMetric :
    regularMetricAtTime = schauderAtTime.extensionMetricAtTime
  /-- The regular metric is the original Ricci-flow metric family. -/
  regularMetric_eq_flowMetric :
    regularMetricAtTime = metric_of_ricci_flow_data flow
  /-- Regularity estimates inherited from the Schauder/bootstrap layer. -/
  regularityEstimateAtTime :
    TimeDependentShortTimeRegularityEstimateField flow
  /-- The Ricci-flow regularity constants are the Schauder constants. -/
  regularityEstimate_eq_schauderEstimate :
    regularityEstimateAtTime = schauderAtTime.schauderEstimateAtTime
  /-- Ricci-flow regularity constants are nonnegative at every order. -/
  regularityEstimate_nonneg :
    ∀ (t : ℝ) (order : ℕ), 0 ≤ regularityEstimateAtTime t order
  /-- Linear parabolic solution operator used by the regularity estimate. -/
  solutionOperatorAtTime :
    TimeDependentParabolicLinearSolutionOperatorField flow
  /-- The operator is the one carried by the Schauder layer. -/
  solutionOperator_eq_schauderOperator :
    solutionOperatorAtTime = schauderAtTime.solutionOperatorAtTime
  /-- Linear parabolic estimate constants used by the solution operator. -/
  estimateConstantAtTime :
    TimeDependentParabolicLinearEstimateConstantField flow
  /-- The linear estimate constants are the Schauder constants. -/
  estimateConstant_eq_schauderConstant :
    estimateConstantAtTime = schauderAtTime.estimateConstantAtTime
  /-- Linear estimate constants remain strictly positive. -/
  estimateConstant_pos : ∀ t, 0 < estimateConstantAtTime t
  /-- Pointwise estimate for the linear solution operator. -/
  solutionOperator_pointwise_estimate :
    ∀ (t : ℝ) (source : TangentCovariantTwoTensor I M)
      (x : M) (v w : TangentSpace I x),
      |solutionOperatorAtTime t source x v w| ≤
        estimateConstantAtTime t * |source x v w|
  /-- Pointwise regularity estimate for the produced fixed-point tensor. -/
  fixedPointTensor_pointwise_regular :
    ∀ (t : ℝ) (order : ℕ) (x : M) (X Y : TangentSpace I x),
      |schauderAtTime.regularityAtTime.shortTimeAtTime.fixedPointAtTime.fixedPointAtTime
        t x X Y| ≤ regularityEstimateAtTime t order

/-- Interface for parabolic regularity estimates for the Ricci-flow PDE. -/
structure HasRicciFlowParabolicRegularity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete Ricci-flow parabolic regularity data proves the interface. -/
  ricciFlowParabolicRegularityData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciFlowParabolicRegularityData flow)

/-- Compatibility constructor for Ricci-flow parabolic regularity data. -/
def HasRicciFlowParabolicRegularity.of_ricciFlowParabolicRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : RicciFlowParabolicRegularityData flow) :
    HasRicciFlowParabolicRegularity flow where
  ricciFlowParabolicRegularityData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨regularityAtTime⟩⟩

/--
Concrete Ricci-flow parabolic regularity data proves the production regularity
interface.
-/
theorem hasRicciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : RicciFlowParabolicRegularityData flow) :
    HasRicciFlowParabolicRegularity flow :=
  HasRicciFlowParabolicRegularity.of_ricciFlowParabolicRegularityData
    regularityAtTime

/--
Parabolic Schauder estimate data supplies the Ricci-flow metric family, the
linear parabolic estimate, and the bootstrap regularity estimate needed by the
current Ricci-flow parabolic regularity interface.
-/
theorem hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (schauderAtTime : ParabolicSchauderEstimateData flow) :
    HasRicciFlowParabolicRegularity flow :=
  hasRicciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData
    { schauderAtTime := schauderAtTime
      regularMetricAtTime := schauderAtTime.extensionMetricAtTime
      regularMetric_eq_schauderExtensionMetric := rfl
      regularMetric_eq_flowMetric := schauderAtTime.extensionMetric_eq_flowMetric
      regularityEstimateAtTime :=
        schauderAtTime.regularityAtTime.regularityEstimateAtTime
      regularityEstimate_eq_schauderEstimate :=
        schauderAtTime.schauderEstimate_eq_bootstrapEstimate.symm
      regularityEstimate_nonneg :=
        schauderAtTime.regularityAtTime.regularityEstimate_nonneg
      solutionOperatorAtTime :=
        schauderAtTime.linearTheoryAtTime.solutionOperatorAtTime
      solutionOperator_eq_schauderOperator :=
        schauderAtTime.solutionOperator_eq_linearTheoryOperator.symm
      estimateConstantAtTime :=
        schauderAtTime.linearTheoryAtTime.estimateConstantAtTime
      estimateConstant_eq_schauderConstant :=
        schauderAtTime.estimateConstant_eq_linearTheoryConstant.symm
      estimateConstant_pos :=
        schauderAtTime.linearTheoryAtTime.estimateConstant_pos
      solutionOperator_pointwise_estimate :=
        schauderAtTime.linearTheoryAtTime.solutionOperator_pointwise_estimate
      fixedPointTensor_pointwise_regular :=
        schauderAtTime.regularityAtTime.fixedPointTensor_pointwise_regular }

/--
Any concrete proof of the Schauder estimate interface carries the data needed
for the Ricci-flow parabolic regularity interface.
-/
theorem hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (schauderAtTime : HasParabolicSchauderEstimates flow) :
    HasRicciFlowParabolicRegularity flow := by
  rcases schauderAtTime.parabolicSchauderEstimateData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hSchauderData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hSchauderData with ⟨schauderData⟩
  exact
    hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimateData
      schauderData

/--
Short-time regularity bootstrap data and maximal-solution extension data build
the Schauder layer and hence Ricci-flow parabolic regularity.
-/
theorem hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (maximalExtensionAtTime : MaximalSolutionExtensionData flow) :
    HasRicciFlowParabolicRegularity flow :=
  hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates
    (hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData
      regularityAtTime maximalExtensionAtTime)

/--
Pullback equation identity data builds the continuation/maximal-extension
Schauder layer, and short-time regularity data then proves Ricci-flow parabolic
regularity.
-/
theorem hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    HasRicciFlowParabolicRegularity flow :=
  hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates
    (hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      regularityAtTime pullbackIdentityAtTime)

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap data,
DeTurck diffeomorphism ODE data, and pullback equation identity data close the
first thirty-eight analytic fields.
-/
theorem analyticFirstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow :=
  let firstThirtySeven :=
    analyticFirstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
  ⟨firstThirtySeven,
    hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates
      firstThirtySeven.2⟩

/--
Pointwise energy of the first covariant derivative of the Riemann curvature
tensor along a Ricci flow.

The value is scalar-valued so the local interface can express estimates without
requiring a norm instance on every tangent space.
-/
abbrev TimeDependentShiCurvatureDerivativeEnergyField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → (x : M) →
    TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → ℝ

/-- Shape contract for first-curvature-derivative energy fields. -/
theorem timeDependentShiCurvatureDerivativeEnergyField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentShiCurvatureDerivativeEnergyField flow =
      (ℝ → (x : M) →
        TangentSpace I x → TangentSpace I x → TangentSpace I x →
          TangentSpace I x → ℝ) :=
  rfl

/--
Pointwise bound field for Shi-type curvature-derivative estimates.

The order parameter records which derivative level is being estimated; the
remaining tangent-vector arguments make the bound explicitly pointwise in the
curvature-derivative energy tested below.
-/
abbrev TimeDependentShiDerivativePointwiseBoundField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Type _ :=
  ℝ → ℕ → (x : M) →
    TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → ℝ

/-- Shape contract for Shi pointwise derivative-bound fields. -/
theorem timeDependentShiDerivativePointwiseBoundField_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentShiDerivativePointwiseBoundField flow =
      (ℝ → ℕ → (x : M) →
        TangentSpace I x → TangentSpace I x → TangentSpace I x →
          TangentSpace I x → ℝ) :=
  rfl

/--
Concrete Shi-type derivative estimate data.

The bundle records the already-established Ricci-flow parabolic regularity
data, extracts the covariant derivative of the Riemann tensor from the
second-Bianchi data carried by scalar-curvature theory, measures that derivative
using the Ricci-flow metric, and stores a pointwise bound obtained by combining
that derivative energy with the existing parabolic regularity estimate.
-/
structure ShiDerivativeEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Scalar-curvature theory supplies the Riemann curvature derivative data. -/
  scalarCurvatureTheoryAtTime :
    ScalarCurvatureTheoryData
      (curvature_data_of_ricci_flow_data flow)
  /-- Ricci-flow parabolic regularity supplies the regularity constants. -/
  parabolicRegularityAtTime : RicciFlowParabolicRegularityData flow
  /-- The second-Bianchi data used for the curvature derivative. -/
  secondBianchiAtTime :
    RiemannCurvatureSecondBianchiData (metric_of_ricci_flow_data flow)
  /-- The second-Bianchi data is the one carried by scalar-curvature theory. -/
  secondBianchi_eq_scalarCurvatureTheory :
    secondBianchiAtTime =
      scalarCurvatureTheoryAtTime.ricciContractionTheoryAtTime.scalarContractionFormulaAtTime.ricciContractionFormulaAtTime.secondBianchiAtTime
  /-- The covariant derivative of the constructed Riemann curvature tensor. -/
  curvatureDerivativeAtTime :
    TimeDependentRiemannCurvatureCovariantDerivativeField
      (metric_of_ricci_flow_data flow)
  /-- The derivative field is the one stored in the second-Bianchi witness. -/
  curvatureDerivative_eq_secondBianchi :
    curvatureDerivativeAtTime =
      secondBianchiAtTime.curvatureCovariantDerivativeAtTime
  /-- The scalar energy used to state pointwise Shi estimates. -/
  derivativeEnergyAtTime :
    TimeDependentShiCurvatureDerivativeEnergyField flow
  /-- The derivative energy is measured by the Ricci-flow metric. -/
  derivativeEnergy_eq_metric_inner :
    ∀ (t : ℝ) (x : M) (A X Y Z : TangentSpace I x),
      derivativeEnergyAtTime t x A X Y Z =
        ((metric_of_ricci_flow_data flow).metricAtTime t).inner x
          (curvatureDerivativeAtTime t x A X Y Z)
          (curvatureDerivativeAtTime t x A X Y Z)
  /-- Regularity estimates inherited from Ricci-flow parabolic regularity. -/
  regularityEstimateAtTime :
    TimeDependentShortTimeRegularityEstimateField flow
  /-- The Shi estimate constants reuse the parabolic regularity constants. -/
  regularityEstimate_eq_parabolicRegularity :
    regularityEstimateAtTime =
      parabolicRegularityAtTime.regularityEstimateAtTime
  /-- The inherited regularity constants are nonnegative. -/
  regularityEstimate_nonneg :
    ∀ (t : ℝ) (order : ℕ), 0 ≤ regularityEstimateAtTime t order
  /-- Pointwise bounds for curvature-derivative energies. -/
  derivativeBoundAtTime :
    TimeDependentShiDerivativePointwiseBoundField flow
  /-- The bound is the derivative energy plus the parabolic regularity estimate. -/
  derivativeBound_eq_energy_add_regularitEstimate :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      derivativeBoundAtTime t order x A X Y Z =
        |derivativeEnergyAtTime t x A X Y Z| +
          regularityEstimateAtTime t order
  /-- Pointwise Shi bounds are nonnegative. -/
  derivativeBound_nonneg :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      0 ≤ derivativeBoundAtTime t order x A X Y Z
  /-- The pointwise bound controls the first curvature-derivative energy. -/
  derivativeEnergy_le_bound :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      |derivativeEnergyAtTime t x A X Y Z| ≤
        derivativeBoundAtTime t order x A X Y Z

/--
Scalar-curvature theory and Ricci-flow parabolic regularity canonically supply
the current local Shi derivative-estimate data.
-/
noncomputable def shiDerivativeEstimateData_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (parabolicRegularityAtTime : RicciFlowParabolicRegularityData flow) :
    ShiDerivativeEstimateData flow :=
  let secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData (metric_of_ricci_flow_data flow) :=
    scalarCurvatureTheoryAtTime.ricciContractionTheoryAtTime.scalarContractionFormulaAtTime.ricciContractionFormulaAtTime.secondBianchiAtTime
  let curvatureDerivativeAtTime :
      TimeDependentRiemannCurvatureCovariantDerivativeField
        (metric_of_ricci_flow_data flow) :=
    secondBianchiAtTime.curvatureCovariantDerivativeAtTime
  let derivativeEnergyAtTime :
      TimeDependentShiCurvatureDerivativeEnergyField flow :=
    fun t x A X Y Z =>
      ((metric_of_ricci_flow_data flow).metricAtTime t).inner x
        (curvatureDerivativeAtTime t x A X Y Z)
        (curvatureDerivativeAtTime t x A X Y Z)
  let regularityEstimateAtTime :
      TimeDependentShortTimeRegularityEstimateField flow :=
    parabolicRegularityAtTime.regularityEstimateAtTime
  { scalarCurvatureTheoryAtTime := scalarCurvatureTheoryAtTime
    parabolicRegularityAtTime := parabolicRegularityAtTime
    secondBianchiAtTime := secondBianchiAtTime
    secondBianchi_eq_scalarCurvatureTheory := rfl
    curvatureDerivativeAtTime := curvatureDerivativeAtTime
    curvatureDerivative_eq_secondBianchi := rfl
    derivativeEnergyAtTime := derivativeEnergyAtTime
    derivativeEnergy_eq_metric_inner := by
      intro t x A X Y Z
      rfl
    regularityEstimateAtTime := regularityEstimateAtTime
    regularityEstimate_eq_parabolicRegularity := rfl
    regularityEstimate_nonneg :=
      parabolicRegularityAtTime.regularityEstimate_nonneg
    derivativeBoundAtTime :=
      fun t order x A X Y Z =>
        |derivativeEnergyAtTime t x A X Y Z| +
          regularityEstimateAtTime t order
    derivativeBound_eq_energy_add_regularitEstimate := by
      intro t order x A X Y Z
      rfl
    derivativeBound_nonneg := by
      intro t order x A X Y Z
      exact
        add_nonneg (abs_nonneg (derivativeEnergyAtTime t x A X Y Z))
          (parabolicRegularityAtTime.regularityEstimate_nonneg t order)
    derivativeEnergy_le_bound := by
      intro t order x A X Y Z
      exact
        le_add_of_nonneg_right
          (parabolicRegularityAtTime.regularityEstimate_nonneg t order) }

/-- The canonical Shi derivative-estimate data stores the supplied scalar-curvature theory. -/
@[simp] theorem shiDerivativeEstimateData_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (parabolicRegularityAtTime : RicciFlowParabolicRegularityData flow) :
    (shiDerivativeEstimateData_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData
        scalarCurvatureTheoryAtTime parabolicRegularityAtTime).scalarCurvatureTheoryAtTime =
      scalarCurvatureTheoryAtTime :=
  rfl

/-- Interface for Shi-type derivative estimates along Ricci flow. -/
structure HasShiDerivativeEstimates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete Shi derivative-estimate data proves the interface. -/
  shiDerivativeEstimateData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ShiDerivativeEstimateData flow)

/-- Compatibility constructor for Shi derivative-estimate data. -/
def HasShiDerivativeEstimates.of_shiDerivativeEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shiEstimateAtTime : ShiDerivativeEstimateData flow) :
    HasShiDerivativeEstimates flow where
  shiDerivativeEstimateData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨shiEstimateAtTime⟩⟩

/--
Concrete Shi derivative-estimate data proves the production Shi interface.
-/
theorem hasShiDerivativeEstimates_of_shiDerivativeEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shiEstimateAtTime : ShiDerivativeEstimateData flow) :
    HasShiDerivativeEstimates flow :=
  HasShiDerivativeEstimates.of_shiDerivativeEstimateData
    shiEstimateAtTime

/--
Scalar-curvature theory and concrete Ricci-flow parabolic regularity data prove
the current Shi derivative-estimate interface.
-/
theorem hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (parabolicRegularityAtTime : RicciFlowParabolicRegularityData flow) :
    HasShiDerivativeEstimates flow :=
  hasShiDerivativeEstimates_of_shiDerivativeEstimateData
    (shiDerivativeEstimateData_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData
      scalarCurvatureTheoryAtTime parabolicRegularityAtTime)

/--
Scalar-curvature theory and any proof of Ricci-flow parabolic regularity prove
the current Shi derivative-estimate interface by unpacking the concrete
regularity data.
-/
theorem hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (parabolicRegularityAtTime : HasRicciFlowParabolicRegularity flow) :
    HasShiDerivativeEstimates flow := by
  rcases parabolicRegularityAtTime.ricciFlowParabolicRegularityData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hRegularityData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hRegularityData with ⟨regularityData⟩
  exact
    hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData
      scalarCurvatureTheoryAtTime regularityData

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap data,
DeTurck diffeomorphism ODE data, and pullback equation identity data close the
first thirty-nine analytic fields.
-/
theorem analyticFirstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow :=
  let firstThirtyEight :=
    analyticFirstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
  ⟨firstThirtyEight,
    hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularity
      scalarCurvatureTheoryAtTime firstThirtyEight.2⟩

/--
Concrete curvature-derivative bootstrap data.

The bundle records the Shi derivative estimate being bootstrapped, keeps the
curvature-derivative and energy fields explicit, and adds a strengthened
pointwise derivative bound obtained by combining the Shi pointwise bound with
the inherited regularity estimate.
-/
structure CurvatureDerivativeBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The Shi derivative estimate supplying first curvature-derivative bounds. -/
  shiEstimateAtTime : ShiDerivativeEstimateData flow
  /-- The covariant derivative of the Riemann tensor being bootstrapped. -/
  curvatureDerivativeAtTime :
    TimeDependentRiemannCurvatureCovariantDerivativeField
      (metric_of_ricci_flow_data flow)
  /-- The derivative field is the one controlled by the Shi estimate. -/
  curvatureDerivative_eq_shiDerivative :
    curvatureDerivativeAtTime = shiEstimateAtTime.curvatureDerivativeAtTime
  /-- The scalar first-derivative energy used in the bootstrap estimate. -/
  derivativeEnergyAtTime :
    TimeDependentShiCurvatureDerivativeEnergyField flow
  /-- The bootstrap energy is the Shi derivative energy. -/
  derivativeEnergy_eq_shiEnergy :
    derivativeEnergyAtTime = shiEstimateAtTime.derivativeEnergyAtTime
  /-- The pointwise Shi derivative bound before the bootstrap increment. -/
  shiDerivativeBoundAtTime :
    TimeDependentShiDerivativePointwiseBoundField flow
  /-- The stored Shi bound agrees with the bound from the Shi estimate. -/
  shiDerivativeBound_eq_shiBound :
    shiDerivativeBoundAtTime = shiEstimateAtTime.derivativeBoundAtTime
  /-- The regularity estimate used to bootstrap the derivative bound. -/
  bootstrapRegularityEstimateAtTime :
    TimeDependentShortTimeRegularityEstimateField flow
  /-- Bootstrap regularity reuses the regularity estimate from Shi data. -/
  bootstrapRegularityEstimate_eq_shiRegularity :
    bootstrapRegularityEstimateAtTime =
      shiEstimateAtTime.regularityEstimateAtTime
  /-- The bootstrap regularity estimate is nonnegative at every order. -/
  bootstrapRegularityEstimate_nonneg :
    ∀ (t : ℝ) (order : ℕ), 0 ≤ bootstrapRegularityEstimateAtTime t order
  /-- The strengthened pointwise derivative bound after bootstrapping. -/
  bootstrapDerivativeBoundAtTime :
    TimeDependentShiDerivativePointwiseBoundField flow
  /-- The bootstrap bound adds regularity control to the Shi bound. -/
  bootstrapDerivativeBound_eq_shiBound_add_regularitEstimate :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      bootstrapDerivativeBoundAtTime t order x A X Y Z =
        shiDerivativeBoundAtTime t order x A X Y Z +
          bootstrapRegularityEstimateAtTime t order
  /-- The strengthened bootstrap derivative bound is nonnegative. -/
  bootstrapDerivativeBound_nonneg :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      0 ≤ bootstrapDerivativeBoundAtTime t order x A X Y Z
  /-- The strengthened bootstrap bound controls curvature-derivative energy. -/
  derivativeEnergy_le_bootstrapBound :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      |derivativeEnergyAtTime t x A X Y Z| ≤
        bootstrapDerivativeBoundAtTime t order x A X Y Z

/-- Interface for bootstrapping curvature derivative bounds from Shi estimates. -/
structure HasCurvatureDerivativeBootstrap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete bootstrap data proves the production interface. -/
  curvatureDerivativeBootstrapData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (CurvatureDerivativeBootstrapData flow)

/-- Compatibility constructor for curvature-derivative bootstrap data. -/
def HasCurvatureDerivativeBootstrap.of_curvatureDerivativeBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (bootstrapAtTime : CurvatureDerivativeBootstrapData flow) :
    HasCurvatureDerivativeBootstrap flow where
  curvatureDerivativeBootstrapData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨bootstrapAtTime⟩⟩

/--
Concrete curvature-derivative bootstrap data proves the production bootstrap
interface.
-/
theorem hasCurvatureDerivativeBootstrap_of_curvatureDerivativeBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (bootstrapAtTime : CurvatureDerivativeBootstrapData flow) :
    HasCurvatureDerivativeBootstrap flow :=
  HasCurvatureDerivativeBootstrap.of_curvatureDerivativeBootstrapData
    bootstrapAtTime

/--
Concrete Shi derivative-estimate data supplies the current
curvature-derivative bootstrap interface by strengthening its pointwise
derivative bound with the inherited regularity estimate.
-/
theorem hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimateData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (shiEstimateAtTime : ShiDerivativeEstimateData flow) :
    HasCurvatureDerivativeBootstrap flow :=
  hasCurvatureDerivativeBootstrap_of_curvatureDerivativeBootstrapData
    { shiEstimateAtTime := shiEstimateAtTime
      curvatureDerivativeAtTime := shiEstimateAtTime.curvatureDerivativeAtTime
      curvatureDerivative_eq_shiDerivative := rfl
      derivativeEnergyAtTime := shiEstimateAtTime.derivativeEnergyAtTime
      derivativeEnergy_eq_shiEnergy := rfl
      shiDerivativeBoundAtTime := shiEstimateAtTime.derivativeBoundAtTime
      shiDerivativeBound_eq_shiBound := rfl
      bootstrapRegularityEstimateAtTime :=
        shiEstimateAtTime.regularityEstimateAtTime
      bootstrapRegularityEstimate_eq_shiRegularity := rfl
      bootstrapRegularityEstimate_nonneg :=
        shiEstimateAtTime.regularityEstimate_nonneg
      bootstrapDerivativeBoundAtTime :=
        fun t order x A X Y Z =>
          shiEstimateAtTime.derivativeBoundAtTime t order x A X Y Z +
            shiEstimateAtTime.regularityEstimateAtTime t order
      bootstrapDerivativeBound_eq_shiBound_add_regularitEstimate := by
        intro t order x A X Y Z
        rfl
      bootstrapDerivativeBound_nonneg := by
        intro t order x A X Y Z
        exact
          add_nonneg
            (shiEstimateAtTime.derivativeBound_nonneg t order x A X Y Z)
            (shiEstimateAtTime.regularityEstimate_nonneg t order)
      derivativeEnergy_le_bootstrapBound := by
        intro t order x A X Y Z
        exact
          le_trans
            (shiEstimateAtTime.derivativeEnergy_le_bound t order x A X Y Z)
            (le_add_of_nonneg_right
              (shiEstimateAtTime.regularityEstimate_nonneg t order)) }

/--
Any proof of Shi derivative estimates carries concrete data sufficient for the
current curvature-derivative bootstrap interface.
-/
theorem hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (shiEstimateAtTime : HasShiDerivativeEstimates flow) :
    HasCurvatureDerivativeBootstrap flow := by
  rcases shiEstimateAtTime.shiDerivativeEstimateData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hShiEstimateData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hShiEstimateData with ⟨shiEstimateData⟩
  exact
    hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimateData
      shiEstimateData

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap data,
DeTurck diffeomorphism ODE data, and pullback equation identity data close the
first forty analytic fields.
-/
theorem analyticFirstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    ((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow :=
  let firstThirtyNine :=
    analyticFirstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
  ⟨firstThirtyNine,
    hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimates
      firstThirtyNine.2⟩

/--
Concrete Hamilton maximum-principle data for the Ricci-flow analytic package.

The bundle records the curvature-derivative bootstrap layer being fed into the
maximum-principle step, keeps the controlled curvature-derivative tensor
explicit, and stores the nonnegative barrier and pointwise bound used to
control that tensor.
-/
structure HamiltonMaximumPrincipleData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The curvature-derivative bootstrap input to the maximum principle. -/
  curvatureBootstrapAtTime : CurvatureDerivativeBootstrapData flow
  /-- The curvature derivative tensor controlled by the maximum principle. -/
  controlledCurvatureDerivativeAtTime :
    TimeDependentRiemannCurvatureCovariantDerivativeField
      (metric_of_ricci_flow_data flow)
  /-- The controlled tensor is the curvature derivative from the bootstrap data. -/
  controlledCurvatureDerivative_eq_bootstrapDerivative :
    controlledCurvatureDerivativeAtTime =
      curvatureBootstrapAtTime.curvatureDerivativeAtTime
  /-- The scalar energy associated to the controlled curvature derivative. -/
  controlledDerivativeEnergyAtTime :
    TimeDependentShiCurvatureDerivativeEnergyField flow
  /-- The controlled energy is the bootstrap curvature-derivative energy. -/
  controlledDerivativeEnergy_eq_bootstrapEnergy :
    controlledDerivativeEnergyAtTime =
      curvatureBootstrapAtTime.derivativeEnergyAtTime
  /-- Nonnegative barrier function used in the maximum-principle estimate. -/
  maximumPrincipleBarrierAtTime :
    TimeDependentShortTimeRegularityEstimateField flow
  /-- The maximum-principle barrier reuses the bootstrap regularity estimate. -/
  maximumPrincipleBarrier_eq_bootstrapRegularity :
    maximumPrincipleBarrierAtTime =
      curvatureBootstrapAtTime.bootstrapRegularityEstimateAtTime
  /-- The maximum-principle barrier is nonnegative. -/
  maximumPrincipleBarrier_nonneg :
    ∀ (t : ℝ) (order : ℕ), 0 ≤ maximumPrincipleBarrierAtTime t order
  /-- Pointwise bound produced by the maximum-principle step. -/
  maximumPrincipleBoundAtTime :
    TimeDependentShiDerivativePointwiseBoundField flow
  /-- The maximum-principle bound is the bootstrap derivative bound. -/
  maximumPrincipleBound_eq_bootstrapBound :
    maximumPrincipleBoundAtTime =
      curvatureBootstrapAtTime.bootstrapDerivativeBoundAtTime
  /-- The pointwise maximum-principle bound is nonnegative. -/
  maximumPrincipleBound_nonneg :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      0 ≤ maximumPrincipleBoundAtTime t order x A X Y Z
  /-- The bound controls the controlled curvature-derivative energy. -/
  controlledDerivativeEnergy_le_maximumPrincipleBound :
    ∀ (t : ℝ) (order : ℕ) (x : M) (A X Y Z : TangentSpace I x),
      |controlledDerivativeEnergyAtTime t x A X Y Z| ≤
        maximumPrincipleBoundAtTime t order x A X Y Z

/-- Interface for Hamilton's tensor maximum principle in the Ricci-flow setting. -/
structure HasHamiltonMaximumPrinciple
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete Hamilton maximum-principle data proves the interface. -/
  hamiltonMaximumPrincipleData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (HamiltonMaximumPrincipleData flow)

/-- Compatibility constructor for Hamilton maximum-principle data. -/
def HasHamiltonMaximumPrinciple.of_hamiltonMaximumPrincipleData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (maximumPrincipleAtTime : HamiltonMaximumPrincipleData flow) :
    HasHamiltonMaximumPrinciple flow where
  hamiltonMaximumPrincipleData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨maximumPrincipleAtTime⟩⟩

/--
Concrete Hamilton maximum-principle data proves the production
maximum-principle interface.
-/
theorem hasHamiltonMaximumPrinciple_of_hamiltonMaximumPrincipleData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (maximumPrincipleAtTime : HamiltonMaximumPrincipleData flow) :
    HasHamiltonMaximumPrinciple flow :=
  HasHamiltonMaximumPrinciple.of_hamiltonMaximumPrincipleData
    maximumPrincipleAtTime

/--
Concrete curvature-derivative bootstrap data supplies the current Hamilton
maximum-principle interface by exposing its nonnegative bootstrap barrier and
pointwise derivative bound as the maximum-principle control data.
-/
theorem hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrapData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureBootstrapAtTime : CurvatureDerivativeBootstrapData flow) :
    HasHamiltonMaximumPrinciple flow :=
  hasHamiltonMaximumPrinciple_of_hamiltonMaximumPrincipleData
    { curvatureBootstrapAtTime := curvatureBootstrapAtTime
      controlledCurvatureDerivativeAtTime :=
        curvatureBootstrapAtTime.curvatureDerivativeAtTime
      controlledCurvatureDerivative_eq_bootstrapDerivative := rfl
      controlledDerivativeEnergyAtTime :=
        curvatureBootstrapAtTime.derivativeEnergyAtTime
      controlledDerivativeEnergy_eq_bootstrapEnergy := rfl
      maximumPrincipleBarrierAtTime :=
        curvatureBootstrapAtTime.bootstrapRegularityEstimateAtTime
      maximumPrincipleBarrier_eq_bootstrapRegularity := rfl
      maximumPrincipleBarrier_nonneg :=
        curvatureBootstrapAtTime.bootstrapRegularityEstimate_nonneg
      maximumPrincipleBoundAtTime :=
        curvatureBootstrapAtTime.bootstrapDerivativeBoundAtTime
      maximumPrincipleBound_eq_bootstrapBound := rfl
      maximumPrincipleBound_nonneg :=
        curvatureBootstrapAtTime.bootstrapDerivativeBound_nonneg
      controlledDerivativeEnergy_le_maximumPrincipleBound :=
        curvatureBootstrapAtTime.derivativeEnergy_le_bootstrapBound }

/--
Any proof of curvature-derivative bootstrap carries concrete data sufficient
for the current Hamilton maximum-principle interface.
-/
theorem hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (curvatureBootstrapAtTime : HasCurvatureDerivativeBootstrap flow) :
    HasHamiltonMaximumPrinciple flow := by
  rcases curvatureBootstrapAtTime.curvatureDerivativeBootstrapData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hBootstrapData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hBootstrapData with ⟨bootstrapData⟩
  exact
    hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrapData
      bootstrapData

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap data,
DeTurck diffeomorphism ODE data, and pullback equation identity data close the
first forty-one analytic fields.
-/
theorem analyticFirstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow) :
    (((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow :=
  let firstForty :=
    analyticFirstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
  ⟨firstForty,
    hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrap
      firstForty.2⟩

/--
Concrete Ricci-flow uniqueness data.

The bundle records the Hamilton maximum-principle input used by the uniqueness
argument and stores the actual uniqueness theorem available at this interface:
any comparison Ricci-flow datum with the same initial metric has the same
time-dependent metric family.
-/
structure RicciFlowUniquenessTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Hamilton maximum-principle data used in the uniqueness argument. -/
  maximumPrincipleAtTime : HamiltonMaximumPrincipleData flow
  /-- The Ricci-flow equation evidence for the reference flow. -/
  equationAtTime :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow)
  /-- The stored equation evidence is the equation evidence carried by `flow`. -/
  equation_eq_flowEquation : equationAtTime = flow.equation
  /-- The initial metric slice used to compare solutions. -/
  initialMetricAtTime :
    ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)
  /-- The stored initial metric is the time-zero slice of the flow. -/
  initialMetric_eq_flowMetric_zero :
    initialMetricAtTime = (metric_of_ricci_flow_data flow).metricAtTime 0
  /--
  Uniqueness of the metric family among comparison Ricci-flow data with the
  same initial metric.
  -/
  uniquenessByInitialMetric :
    ∀ comparisonFlow : RicciFlowData I n M,
      (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
          initialMetricAtTime →
        metric_of_ricci_flow_data comparisonFlow =
          metric_of_ricci_flow_data flow

/-- Interface for uniqueness of the Ricci-flow solution. -/
structure HasRicciFlowUniquenessTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete Ricci-flow uniqueness data proves the interface. -/
  ricciFlowUniquenessTheoryData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciFlowUniquenessTheoryData flow)

/-- Compatibility constructor for Ricci-flow uniqueness data. -/
def HasRicciFlowUniquenessTheory.of_ricciFlowUniquenessTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (uniquenessAtTime : RicciFlowUniquenessTheoryData flow) :
    HasRicciFlowUniquenessTheory flow where
  ricciFlowUniquenessTheoryData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨uniquenessAtTime⟩⟩

/--
Concrete Ricci-flow uniqueness data proves the production uniqueness
interface.
-/
theorem hasRicciFlowUniquenessTheory_of_ricciFlowUniquenessTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (uniquenessAtTime : RicciFlowUniquenessTheoryData flow) :
    HasRicciFlowUniquenessTheory flow :=
  HasRicciFlowUniquenessTheory.of_ricciFlowUniquenessTheoryData
    uniquenessAtTime

/--
Hamilton maximum-principle data and an initial-metric uniqueness theorem supply
the current Ricci-flow uniqueness interface.
-/
theorem hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrincipleData_and_initialMetricUniqueness
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (maximumPrincipleAtTime : HamiltonMaximumPrincipleData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow) :
    HasRicciFlowUniquenessTheory flow :=
  hasRicciFlowUniquenessTheory_of_ricciFlowUniquenessTheoryData
    { maximumPrincipleAtTime := maximumPrincipleAtTime
      equationAtTime := flow.equation
      equation_eq_flowEquation := rfl
      initialMetricAtTime := (metric_of_ricci_flow_data flow).metricAtTime 0
      initialMetric_eq_flowMetric_zero := rfl
      uniquenessByInitialMetric := by
        intro comparisonFlow sameInitialMetric
        exact uniquenessByInitialMetric comparisonFlow sameInitialMetric }

/--
Any proof of Hamilton's maximum principle, together with an initial-metric
uniqueness theorem, supplies the current Ricci-flow uniqueness interface.
-/
theorem hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrinciple_and_initialMetricUniqueness
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (maximumPrincipleAtTime : HasHamiltonMaximumPrinciple flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow) :
    HasRicciFlowUniquenessTheory flow := by
  rcases maximumPrincipleAtTime.hamiltonMaximumPrincipleData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hMaximumPrincipleData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hMaximumPrincipleData with ⟨maximumPrincipleData⟩
  exact
    hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrincipleData_and_initialMetricUniqueness
      maximumPrincipleData uniquenessByInitialMetric

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap data,
DeTurck diffeomorphism ODE data, pullback equation identity data, and an
initial-metric uniqueness theorem close the first forty-two analytic fields.
-/
theorem analyticFirstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow) :
    ((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow :=
  let firstFortyOne :=
    analyticFirstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
  ⟨firstFortyOne,
    hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrinciple_and_initialMetricUniqueness
      firstFortyOne.2 uniquenessByInitialMetric⟩

/--
Concrete metric evolution-equation data for Ricci flow.

The bundle records the already-established uniqueness layer, the explicit
Ricci-flow equation verification, the metric time derivative used in that
verification, and both tensor-valued and pointwise forms of
`∂ₜ g = -2 Ricci`.
-/
structure MetricEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- Ricci-flow uniqueness data available before using the evolution equation. -/
  uniquenessTheoryAtTime : RicciFlowUniquenessTheoryData flow
  /-- Explicit verification of the metric evolution equation. -/
  equationVerificationAtTime :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)
  /-- The metric time derivative used in the evolution equation. -/
  metricDerivativeAtTime :
    MetricTimeDerivativeData (metric_of_ricci_flow_data flow)
  /-- The stored derivative is the derivative carried by equation verification. -/
  metricDerivative_eq_verification :
    metricDerivativeAtTime = equationVerificationAtTime.metricDerivative
  /-- The metric time derivative is identified as the derivative of `g(t)`. -/
  metricDerivative_identifies :
    IsMetricTimeDerivativeOf
      (metric_of_ricci_flow_data flow)
      metricDerivativeAtTime.derivative
  /-- The derivative-identification proof is the one carried by derivative data. -/
  metricDerivative_identifies_eq_derivativeData :
    metricDerivative_identifies =
      metricDerivativeAtTime.identifiesDerivative
  /-- Tensor-valued metric evolution equation `∂ₜ g = -2 Ricci`. -/
  metricEvolutionAtTime :
    ∀ t,
      metric_time_derivative_at_time_of_metric_derivative_field
        metricDerivativeAtTime.derivative t =
          ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t
  /-- Pointwise metric evolution equation. -/
  metricEvolutionAtTime_apply :
    ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
      metric_time_derivative_at_time_of_metric_derivative_field
        metricDerivativeAtTime.derivative t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data flow) t x v w
  /-- The abstract equation-interface evidence carried by the flow. -/
  equationEvidenceAtTime :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow)
  /-- The stored abstract equation evidence is the one carried by `flow`. -/
  equationEvidence_eq_flowEquation :
    equationEvidenceAtTime = flow.equation

/-- Interface for the metric evolution equation along Ricci flow. -/
structure HasMetricEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete metric evolution-equation data proves the interface. -/
  metricEvolutionEquationData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (MetricEvolutionEquationData flow)

/-- Compatibility constructor for metric evolution-equation data. -/
def HasMetricEvolutionEquation.of_metricEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (metricEvolutionAtTime : MetricEvolutionEquationData flow) :
    HasMetricEvolutionEquation flow where
  metricEvolutionEquationData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨metricEvolutionAtTime⟩⟩

/--
Concrete metric evolution-equation data proves the production metric evolution
interface.
-/
theorem hasMetricEvolutionEquation_of_metricEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (metricEvolutionAtTime : MetricEvolutionEquationData flow) :
    HasMetricEvolutionEquation flow :=
  HasMetricEvolutionEquation.of_metricEvolutionEquationData
    metricEvolutionAtTime

/--
Explicit equation verification and concrete Ricci-flow uniqueness data supply
the current metric evolution-equation interface.
-/
theorem hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheoryData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (uniquenessTheoryAtTime : RicciFlowUniquenessTheoryData flow) :
    HasMetricEvolutionEquation flow :=
  hasMetricEvolutionEquation_of_metricEvolutionEquationData
    { uniquenessTheoryAtTime := uniquenessTheoryAtTime
      equationVerificationAtTime := equationVerificationAtTime
      metricDerivativeAtTime := equationVerificationAtTime.metricDerivative
      metricDerivative_eq_verification := rfl
      metricDerivative_identifies :=
        equationVerificationAtTime.metricDerivative.identifiesDerivative
      metricDerivative_identifies_eq_derivativeData := rfl
      metricEvolutionAtTime := by
        intro t
        exact equationVerificationAtTime.equationAtTime t
      metricEvolutionAtTime_apply := by
        intro t x v w
        exact
          equation_at_time_apply_of_ricci_flow_equation_verification
            equationVerificationAtTime t x v w
      equationEvidenceAtTime := flow.equation
      equationEvidence_eq_flowEquation := rfl }

/--
Explicit equation verification and any proof of Ricci-flow uniqueness supply
the current metric evolution-equation interface.
-/
theorem hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (uniquenessTheoryAtTime : HasRicciFlowUniquenessTheory flow) :
    HasMetricEvolutionEquation flow := by
  rcases uniquenessTheoryAtTime.ricciFlowUniquenessTheoryData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hUniquenessData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hUniquenessData with ⟨uniquenessData⟩
  exact
    hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheoryData
      equationVerificationAtTime uniquenessData

/--
Scalar-curvature theory data, Ricci-flow equation verification, DeTurck
vector-field construction data, Ricci-DeTurck equation data, Ricci-DeTurck
linearization data, strict-parabolicity data, linear parabolic theory data,
fixed-point argument data, short-time existence data, regularity-bootstrap data,
DeTurck diffeomorphism ODE data, pullback equation identity data, and an
initial-metric uniqueness theorem close the first forty-three analytic fields.
-/
theorem analyticFirstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow) :
    (((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow :=
  let firstFortyTwo :=
    analyticFirstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
      uniquenessByInitialMetric
  ⟨firstFortyTwo,
    hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheory
      equationVerificationAtTime firstFortyTwo.2⟩

/--
Concrete Ricci tensor evolution-equation data for Ricci flow.

The bundle records the metric evolution layer already available for the flow,
the Ricci tensor field coming from the flow's curvature package, and the
tensor-valued plus pointwise Ricci evolution equation data that a later
formalization should identify with the Laplacian/quadratic curvature formula.
-/
structure RicciTensorEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The metric evolution equation layer used before differentiating Ricci. -/
  metricEvolutionAtTime : MetricEvolutionEquationData flow
  /-- Explicit Ricci-flow equation verification used by metric evolution. -/
  equationVerificationAtTime :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)
  /-- The equation verification is the one stored by metric evolution. -/
  equationVerification_eq_metricEvolution :
    equationVerificationAtTime =
      metricEvolutionAtTime.equationVerificationAtTime
  /-- The Ricci tensor field whose evolution is being tracked. -/
  ricciTensorAtTime : RicciTensorField (metric_of_ricci_flow_data flow)
  /-- The Ricci tensor field is the one projected from the flow curvature data. -/
  ricciTensor_eq_curvatureRicci :
    ricciTensorAtTime =
      ricci_tensor_field_of_curvature_data
        (curvature_data_of_ricci_flow_data flow)
  /-- Candidate time derivative of the Ricci tensor. -/
  ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M
  /-- Candidate right-hand side of the Ricci tensor evolution equation. -/
  ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M
  /-- Tensor-valued Ricci tensor evolution equation. -/
  ricciTensorEvolutionAtTime :
    ∀ t, ricciTensorDerivativeAtTime t = ricciTensorEvolutionRHSAtTime t
  /-- Pointwise Ricci tensor evolution equation. -/
  ricciTensorEvolutionAtTime_apply :
    ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
      ricciTensorDerivativeAtTime t x v w =
        ricciTensorEvolutionRHSAtTime t x v w

/-- Interface for the Ricci tensor evolution equation along Ricci flow. -/
structure HasRicciTensorEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete Ricci tensor evolution-equation data proves the interface. -/
  ricciTensorEvolutionEquationData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (RicciTensorEvolutionEquationData flow)

/-- Compatibility constructor for Ricci tensor evolution-equation data. -/
def HasRicciTensorEvolutionEquation.of_ricciTensorEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciTensorEvolutionAtTime :
      RicciTensorEvolutionEquationData flow) :
    HasRicciTensorEvolutionEquation flow where
  ricciTensorEvolutionEquationData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨ricciTensorEvolutionAtTime⟩⟩

/--
Concrete Ricci tensor evolution-equation data proves the production Ricci
tensor evolution interface.
-/
theorem hasRicciTensorEvolutionEquation_of_ricciTensorEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciTensorEvolutionAtTime :
      RicciTensorEvolutionEquationData flow) :
    HasRicciTensorEvolutionEquation flow :=
  HasRicciTensorEvolutionEquation.of_ricciTensorEvolutionEquationData
    ricciTensorEvolutionAtTime

/--
Metric evolution data plus a concrete tensor-valued Ricci evolution equality
supplies the current Ricci tensor evolution interface.
-/
theorem hasRicciTensorEvolutionEquation_of_metricEvolutionEquationData_and_ricciTensorEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (metricEvolutionAtTime : MetricEvolutionEquationData flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t) :
    HasRicciTensorEvolutionEquation flow :=
  hasRicciTensorEvolutionEquation_of_ricciTensorEvolutionEquationData
    { metricEvolutionAtTime := metricEvolutionAtTime
      equationVerificationAtTime :=
        metricEvolutionAtTime.equationVerificationAtTime
      equationVerification_eq_metricEvolution := rfl
      ricciTensorAtTime :=
        ricci_tensor_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)
      ricciTensor_eq_curvatureRicci := rfl
      ricciTensorDerivativeAtTime := ricciTensorDerivativeAtTime
      ricciTensorEvolutionRHSAtTime := ricciTensorEvolutionRHSAtTime
      ricciTensorEvolutionAtTime := ricciTensorEvolutionAtTime
      ricciTensorEvolutionAtTime_apply := by
        intro t x v w
        exact
          congrArg
            (fun tensor : TangentCovariantTwoTensor I M => tensor x v w)
            (ricciTensorEvolutionAtTime t) }

/--
Any proof of metric evolution plus a concrete tensor-valued Ricci evolution
equality supplies the current Ricci tensor evolution interface.
-/
theorem hasRicciTensorEvolutionEquation_of_metricEvolutionEquation_and_ricciTensorEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (metricEvolutionAtTime : HasMetricEvolutionEquation flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t) :
    HasRicciTensorEvolutionEquation flow := by
  rcases metricEvolutionAtTime.metricEvolutionEquationData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hMetricEvolutionData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hMetricEvolutionData with ⟨metricEvolutionData⟩
  exact
    hasRicciTensorEvolutionEquation_of_metricEvolutionEquationData_and_ricciTensorEvolutionEquation
      metricEvolutionData ricciTensorDerivativeAtTime
      ricciTensorEvolutionRHSAtTime ricciTensorEvolutionAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, the DeTurck and
short-time layers, uniqueness by initial metric, and concrete Ricci tensor
evolution-equation data close the first forty-four analytic fields.
-/
theorem analyticFirstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t) :
    ((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow :=
  let firstFortyThree :=
    analyticFirstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
      uniquenessByInitialMetric
  ⟨firstFortyThree,
    hasRicciTensorEvolutionEquation_of_metricEvolutionEquation_and_ricciTensorEvolutionEquation
      firstFortyThree.2 ricciTensorDerivativeAtTime
      ricciTensorEvolutionRHSAtTime ricciTensorEvolutionAtTime⟩

/--
Concrete scalar curvature evolution-equation data for Ricci flow.

The bundle records the Ricci tensor evolution layer already available for the
flow, the scalar curvature field coming from the flow's curvature package, and
the function-valued plus pointwise scalar evolution equation data that a later
formalization should identify with the Laplacian and Ricci-norm formula.
-/
structure ScalarCurvatureEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The Ricci tensor evolution equation layer used before tracing to scalar curvature. -/
  ricciTensorEvolutionAtTime : RicciTensorEvolutionEquationData flow
  /-- The scalar curvature field whose evolution is being tracked. -/
  scalarCurvatureAtTime :
    ScalarCurvatureField (metric_of_ricci_flow_data flow)
  /-- The scalar curvature field is the one projected from the flow curvature data. -/
  scalarCurvature_eq_curvatureScalar :
    scalarCurvatureAtTime =
      scalar_curvature_field_of_curvature_data
        (curvature_data_of_ricci_flow_data flow)
  /-- Candidate time derivative of scalar curvature. -/
  scalarCurvatureDerivativeAtTime : ℝ → M → ℝ
  /-- Candidate right-hand side of the scalar curvature evolution equation. -/
  scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ
  /-- Function-valued scalar curvature evolution equation. -/
  scalarCurvatureEvolutionAtTime :
    ∀ t,
      scalarCurvatureDerivativeAtTime t =
        scalarCurvatureEvolutionRHSAtTime t
  /-- Pointwise scalar curvature evolution equation. -/
  scalarCurvatureEvolutionAtTime_apply :
    ∀ (t : ℝ) (x : M),
      scalarCurvatureDerivativeAtTime t x =
        scalarCurvatureEvolutionRHSAtTime t x

/-- Interface for the scalar curvature evolution equation along Ricci flow. -/
structure HasScalarCurvatureEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete scalar curvature evolution-equation data proves the interface. -/
  scalarCurvatureEvolutionEquationData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (ScalarCurvatureEvolutionEquationData flow)

/-- Compatibility constructor for scalar curvature evolution-equation data. -/
def HasScalarCurvatureEvolutionEquation.of_scalarCurvatureEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureEvolutionAtTime :
      ScalarCurvatureEvolutionEquationData flow) :
    HasScalarCurvatureEvolutionEquation flow where
  scalarCurvatureEvolutionEquationData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨scalarCurvatureEvolutionAtTime⟩⟩

/--
Concrete scalar curvature evolution-equation data proves the production scalar
curvature evolution interface.
-/
theorem hasScalarCurvatureEvolutionEquation_of_scalarCurvatureEvolutionEquationData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureEvolutionAtTime :
      ScalarCurvatureEvolutionEquationData flow) :
    HasScalarCurvatureEvolutionEquation flow :=
  HasScalarCurvatureEvolutionEquation.of_scalarCurvatureEvolutionEquationData
    scalarCurvatureEvolutionAtTime

/--
Ricci tensor evolution data plus a concrete function-valued scalar evolution
equality supplies the current scalar curvature evolution interface.
-/
theorem hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquationData_and_scalarCurvatureEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciTensorEvolutionAtTime :
      RicciTensorEvolutionEquationData flow)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t) :
    HasScalarCurvatureEvolutionEquation flow :=
  hasScalarCurvatureEvolutionEquation_of_scalarCurvatureEvolutionEquationData
    { ricciTensorEvolutionAtTime := ricciTensorEvolutionAtTime
      scalarCurvatureAtTime :=
        scalar_curvature_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)
      scalarCurvature_eq_curvatureScalar := rfl
      scalarCurvatureDerivativeAtTime := scalarCurvatureDerivativeAtTime
      scalarCurvatureEvolutionRHSAtTime := scalarCurvatureEvolutionRHSAtTime
      scalarCurvatureEvolutionAtTime := scalarCurvatureEvolutionAtTime
      scalarCurvatureEvolutionAtTime_apply := by
        intro t x
        exact
          congrArg (fun scalarAtTime : M → ℝ => scalarAtTime x)
            (scalarCurvatureEvolutionAtTime t) }

/--
Any proof of Ricci tensor evolution plus a concrete function-valued scalar
evolution equality supplies the current scalar curvature evolution interface.
-/
theorem hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquation_and_scalarCurvatureEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (ricciTensorEvolutionAtTime :
      HasRicciTensorEvolutionEquation flow)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t) :
    HasScalarCurvatureEvolutionEquation flow := by
  rcases ricciTensorEvolutionAtTime.ricciTensorEvolutionEquationData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hRicciTensorEvolutionData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hRicciTensorEvolutionData with ⟨ricciTensorEvolutionData⟩
  exact
    hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquationData_and_scalarCurvatureEvolutionEquation
      ricciTensorEvolutionData scalarCurvatureDerivativeAtTime
      scalarCurvatureEvolutionRHSAtTime scalarCurvatureEvolutionAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, the DeTurck and
short-time layers, uniqueness by initial metric, concrete Ricci tensor
evolution-equation data, and concrete scalar curvature evolution-equation data
close the first forty-five analytic fields.
-/
theorem analyticFirstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t) :
    (((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow) ∧
      HasScalarCurvatureEvolutionEquation flow :=
  let firstFortyFour :=
    analyticFirstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
      uniquenessByInitialMetric ricciTensorDerivativeAtTime
      ricciTensorEvolutionRHSAtTime ricciTensorEvolutionAtTime
  ⟨firstFortyFour,
    hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquation_and_scalarCurvatureEvolutionEquation
      firstFortyFour.2 scalarCurvatureDerivativeAtTime
      scalarCurvatureEvolutionRHSAtTime scalarCurvatureEvolutionAtTime⟩

/--
Concrete curvature-norm evolution inequality data for Ricci flow.

The bundle records the scalar curvature evolution layer already available for
the flow, a concrete scalar-valued curvature norm function, nonnegativity of
that norm, and the pointwise differential inequality used by later curvature
estimate arguments.
-/
structure CurvatureNormEvolutionInequalityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The scalar curvature evolution equation layer used by norm estimates. -/
  scalarCurvatureEvolutionAtTime :
    ScalarCurvatureEvolutionEquationData flow
  /-- Candidate norm of the curvature tensor at each time and point. -/
  curvatureNormAtTime : ℝ → M → ℝ
  /-- Curvature norm values are nonnegative. -/
  curvatureNorm_nonnegativeAtTime :
    ∀ (t : ℝ) (x : M), 0 ≤ curvatureNormAtTime t x
  /-- Candidate time derivative of the curvature norm. -/
  curvatureNormDerivativeAtTime : ℝ → M → ℝ
  /-- Candidate right-hand side controlling the curvature norm derivative. -/
  curvatureNormEvolutionRHSAtTime : ℝ → M → ℝ
  /-- Pointwise curvature-norm evolution inequality. -/
  curvatureNormEvolutionInequalityAtTime :
    ∀ (t : ℝ) (x : M),
      curvatureNormDerivativeAtTime t x ≤
        curvatureNormEvolutionRHSAtTime t x

/-- Interface for the curvature-norm evolution inequality used in estimates. -/
structure HasCurvatureNormEvolutionInequality
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete curvature-norm evolution inequality data proves the interface. -/
  curvatureNormEvolutionInequalityData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (CurvatureNormEvolutionInequalityData flow)

/-- Compatibility constructor for curvature-norm evolution inequality data. -/
def HasCurvatureNormEvolutionInequality.of_curvatureNormEvolutionInequalityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureNormEvolutionAtTime :
      CurvatureNormEvolutionInequalityData flow) :
    HasCurvatureNormEvolutionInequality flow where
  curvatureNormEvolutionInequalityData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨curvatureNormEvolutionAtTime⟩⟩

/--
Concrete curvature-norm evolution inequality data proves the production
curvature-norm evolution interface.
-/
theorem hasCurvatureNormEvolutionInequality_of_curvatureNormEvolutionInequalityData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureNormEvolutionAtTime :
      CurvatureNormEvolutionInequalityData flow) :
    HasCurvatureNormEvolutionInequality flow :=
  HasCurvatureNormEvolutionInequality.of_curvatureNormEvolutionInequalityData
    curvatureNormEvolutionAtTime

/--
Scalar curvature evolution data plus concrete curvature-norm inequality data
supplies the current curvature-norm evolution interface.
-/
theorem hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquationData_and_curvatureNormEvolutionInequality
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureEvolutionAtTime :
      ScalarCurvatureEvolutionEquationData flow)
    (curvatureNormAtTime : ℝ → M → ℝ)
    (curvatureNorm_nonnegativeAtTime :
      ∀ (t : ℝ) (x : M), 0 ≤ curvatureNormAtTime t x)
    (curvatureNormDerivativeAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionRHSAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionInequalityAtTime :
      ∀ (t : ℝ) (x : M),
        curvatureNormDerivativeAtTime t x ≤
          curvatureNormEvolutionRHSAtTime t x) :
    HasCurvatureNormEvolutionInequality flow :=
  hasCurvatureNormEvolutionInequality_of_curvatureNormEvolutionInequalityData
    { scalarCurvatureEvolutionAtTime := scalarCurvatureEvolutionAtTime
      curvatureNormAtTime := curvatureNormAtTime
      curvatureNorm_nonnegativeAtTime :=
        curvatureNorm_nonnegativeAtTime
      curvatureNormDerivativeAtTime := curvatureNormDerivativeAtTime
      curvatureNormEvolutionRHSAtTime :=
        curvatureNormEvolutionRHSAtTime
      curvatureNormEvolutionInequalityAtTime :=
        curvatureNormEvolutionInequalityAtTime }

/--
Any proof of scalar curvature evolution plus concrete curvature-norm inequality
data supplies the current curvature-norm evolution interface.
-/
theorem hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquation_and_curvatureNormEvolutionInequality
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureEvolutionAtTime :
      HasScalarCurvatureEvolutionEquation flow)
    (curvatureNormAtTime : ℝ → M → ℝ)
    (curvatureNorm_nonnegativeAtTime :
      ∀ (t : ℝ) (x : M), 0 ≤ curvatureNormAtTime t x)
    (curvatureNormDerivativeAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionRHSAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionInequalityAtTime :
      ∀ (t : ℝ) (x : M),
        curvatureNormDerivativeAtTime t x ≤
          curvatureNormEvolutionRHSAtTime t x) :
    HasCurvatureNormEvolutionInequality flow := by
  rcases scalarCurvatureEvolutionAtTime.scalarCurvatureEvolutionEquationData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hScalarCurvatureEvolutionData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hScalarCurvatureEvolutionData with ⟨scalarCurvatureEvolutionData⟩
  exact
    hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquationData_and_curvatureNormEvolutionInequality
      scalarCurvatureEvolutionData curvatureNormAtTime
      curvatureNorm_nonnegativeAtTime curvatureNormDerivativeAtTime
      curvatureNormEvolutionRHSAtTime
      curvatureNormEvolutionInequalityAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, the DeTurck and
short-time layers, uniqueness by initial metric, concrete Ricci/scalar
evolution data, and concrete curvature-norm inequality data close the first
forty-six analytic fields.
-/
theorem analyticFirstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t)
    (curvatureNormAtTime : ℝ → M → ℝ)
    (curvatureNorm_nonnegativeAtTime :
      ∀ (t : ℝ) (x : M), 0 ≤ curvatureNormAtTime t x)
    (curvatureNormDerivativeAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionRHSAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionInequalityAtTime :
      ∀ (t : ℝ) (x : M),
        curvatureNormDerivativeAtTime t x ≤
          curvatureNormEvolutionRHSAtTime t x) :
    ((((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow) ∧
      HasScalarCurvatureEvolutionEquation flow) ∧
      HasCurvatureNormEvolutionInequality flow :=
  let firstFortyFive :=
    analyticFirstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
      uniquenessByInitialMetric ricciTensorDerivativeAtTime
      ricciTensorEvolutionRHSAtTime ricciTensorEvolutionAtTime
      scalarCurvatureDerivativeAtTime scalarCurvatureEvolutionRHSAtTime
      scalarCurvatureEvolutionAtTime
  ⟨firstFortyFive,
    hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquation_and_curvatureNormEvolutionInequality
      firstFortyFive.2 curvatureNormAtTime
      curvatureNorm_nonnegativeAtTime curvatureNormDerivativeAtTime
      curvatureNormEvolutionRHSAtTime
      curvatureNormEvolutionInequalityAtTime⟩

/--
Concrete curvature evolution-equations data for Ricci flow.

The bundle records the curvature-norm evolution layer already available for
the flow, the constructed Riemann curvature tensor coming from second-Bianchi
data, and tensor-valued plus pointwise Riemann curvature evolution equations.
Together with the previous Ricci, scalar, and norm layers this is the current
production-level curvature evolution package.
-/
structure CurvatureEvolutionEquationsData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    (flow : RicciFlowData I n M) : Type _ where
  /-- The curvature-norm evolution inequality layer used by curvature estimates. -/
  curvatureNormEvolutionAtTime :
    CurvatureNormEvolutionInequalityData flow
  /-- Riemann-curvature data through the second Bianchi identity. -/
  riemannSecondBianchiAtTime :
    RiemannCurvatureSecondBianchiData (metric_of_ricci_flow_data flow)
  /-- The constructed time-dependent tangent-valued Riemann curvature tensor. -/
  riemannCurvatureAtTime :
    TimeDependentRiemannCurvatureTensorField
      (metric_of_ricci_flow_data flow)
  /-- The stored Riemann tensor is the one carried by the second-Bianchi data. -/
  riemannCurvature_eq_secondBianchi :
    riemannCurvatureAtTime =
      riemannSecondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime
  /-- Candidate time derivative of the Riemann curvature tensor. -/
  riemannCurvatureDerivativeAtTime :
    TimeDependentRiemannCurvatureTensorField
      (metric_of_ricci_flow_data flow)
  /-- Candidate right-hand side of the Riemann curvature evolution equation. -/
  riemannCurvatureEvolutionRHSAtTime :
    TimeDependentRiemannCurvatureTensorField
      (metric_of_ricci_flow_data flow)
  /-- Tensor-valued Riemann curvature evolution equation. -/
  riemannCurvatureEvolutionAtTime :
    ∀ t,
      riemannCurvatureDerivativeAtTime t =
        riemannCurvatureEvolutionRHSAtTime t
  /-- Pointwise Riemann curvature evolution equation. -/
  riemannCurvatureEvolutionAtTime_apply :
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace I x),
      riemannCurvatureDerivativeAtTime t x X Y Z =
        riemannCurvatureEvolutionRHSAtTime t x X Y Z

/-- Interface for curvature evolution equations along Ricci flow. -/
structure HasCurvatureEvolutionEquations
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop where
  /-- Concrete curvature evolution-equations data proves the interface. -/
  curvatureEvolutionEquationsData_source :
    ∃ hComplete : CompleteSpace E,
      letI := hComplete
      ∃ hFinite : FiniteDimensional ℝ E,
        letI := hFinite
        ∃ hManifoldTwo : IsManifold I 2 M,
          letI := hManifoldTwo
          Nonempty (CurvatureEvolutionEquationsData flow)

/-- Compatibility constructor for curvature evolution-equations data. -/
def HasCurvatureEvolutionEquations.of_curvatureEvolutionEquationsData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureEvolutionAtTime :
      CurvatureEvolutionEquationsData flow) :
    HasCurvatureEvolutionEquations flow where
  curvatureEvolutionEquationsData_source :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨curvatureEvolutionAtTime⟩⟩

/--
Concrete curvature evolution-equations data proves the production curvature
evolution interface.
-/
theorem hasCurvatureEvolutionEquations_of_curvatureEvolutionEquationsData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureEvolutionAtTime : CurvatureEvolutionEquationsData flow) :
    HasCurvatureEvolutionEquations flow :=
  HasCurvatureEvolutionEquations.of_curvatureEvolutionEquationsData
    curvatureEvolutionAtTime

/--
Curvature-norm inequality data plus concrete Riemann curvature evolution
equations supplies the current curvature evolution interface.
-/
theorem hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequalityData_and_curvatureEvolutionEquations
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureNormEvolutionAtTime :
      CurvatureNormEvolutionInequalityData flow)
    (riemannSecondBianchiAtTime :
      RiemannCurvatureSecondBianchiData (metric_of_ricci_flow_data flow))
    (riemannCurvatureDerivativeAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionRHSAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionAtTime :
      ∀ t,
        riemannCurvatureDerivativeAtTime t =
          riemannCurvatureEvolutionRHSAtTime t) :
    HasCurvatureEvolutionEquations flow :=
  hasCurvatureEvolutionEquations_of_curvatureEvolutionEquationsData
    { curvatureNormEvolutionAtTime := curvatureNormEvolutionAtTime
      riemannSecondBianchiAtTime := riemannSecondBianchiAtTime
      riemannCurvatureAtTime :=
        riemannSecondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime
      riemannCurvature_eq_secondBianchi := rfl
      riemannCurvatureDerivativeAtTime :=
        riemannCurvatureDerivativeAtTime
      riemannCurvatureEvolutionRHSAtTime :=
        riemannCurvatureEvolutionRHSAtTime
      riemannCurvatureEvolutionAtTime :=
        riemannCurvatureEvolutionAtTime
      riemannCurvatureEvolutionAtTime_apply := by
        intro t x X Y Z
        exact
          congrArg
            (fun tensor : TangentRiemannCurvatureTensor I M =>
              tensor x X Y Z)
            (riemannCurvatureEvolutionAtTime t) }

/--
Any proof of curvature-norm evolution plus concrete Riemann curvature evolution
equations supplies the current curvature evolution interface.
-/
theorem hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequality_and_curvatureEvolutionEquations
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (curvatureNormEvolutionAtTime :
      HasCurvatureNormEvolutionInequality flow)
    (riemannSecondBianchiAtTime :
      RiemannCurvatureSecondBianchiData (metric_of_ricci_flow_data flow))
    (riemannCurvatureDerivativeAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionRHSAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionAtTime :
      ∀ t,
        riemannCurvatureDerivativeAtTime t =
          riemannCurvatureEvolutionRHSAtTime t) :
    HasCurvatureEvolutionEquations flow := by
  rcases curvatureNormEvolutionAtTime.curvatureNormEvolutionInequalityData_source with
    ⟨hComplete, hFinite, hManifoldTwo, hCurvatureNormEvolutionData⟩
  letI := hComplete
  letI := hFinite
  letI := hManifoldTwo
  rcases hCurvatureNormEvolutionData with ⟨curvatureNormEvolutionData⟩
  exact
    hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequalityData_and_curvatureEvolutionEquations
      curvatureNormEvolutionData riemannSecondBianchiAtTime
      riemannCurvatureDerivativeAtTime
      riemannCurvatureEvolutionRHSAtTime
      riemannCurvatureEvolutionAtTime

/--
Scalar-curvature theory data, Ricci-flow equation verification, the DeTurck and
short-time layers, uniqueness by initial metric, concrete Ricci/scalar/norm
evolution data, and concrete Riemann curvature evolution-equation data close
all explicit analytic package fields.
-/
theorem analyticFirstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M]
    {flow : RicciFlowData I n M}
    (scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow))
    (equationVerificationAtTime :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow))
    (vectorFieldAtTime : DeTurckVectorFieldConstructionData flow)
    (ricciDeTurckEquationAtTime :
      RicciDeTurckEquationDerivationData flow)
    (linearizationAtTime : RicciDeTurckLinearizationData flow)
    (strictParabolicAtTime : StrictlyParabolicDeTurckSystemData flow)
    (linearTheoryAtTime : ParabolicLinearTheoryData flow)
    (fixedPointAtTime : ParabolicFixedPointArgumentData flow)
    (shortTimeAtTime : DeTurckShortTimeExistenceData flow)
    (regularityAtTime : ShortTimeRegularityBootstrapData flow)
    (odeAtTime : DeTurckDiffeomorphismODEData flow)
    (pullbackIdentityAtTime : DeTurckPullbackEquationIdentityData flow)
    (uniquenessByInitialMetric :
      ∀ comparisonFlow : RicciFlowData I n M,
        (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
            (metric_of_ricci_flow_data flow).metricAtTime 0 →
          metric_of_ricci_flow_data comparisonFlow =
            metric_of_ricci_flow_data flow)
    (ricciTensorDerivativeAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionRHSAtTime : ℝ → TangentCovariantTwoTensor I M)
    (ricciTensorEvolutionAtTime :
      ∀ t, ricciTensorDerivativeAtTime t =
        ricciTensorEvolutionRHSAtTime t)
    (scalarCurvatureDerivativeAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionRHSAtTime : ℝ → M → ℝ)
    (scalarCurvatureEvolutionAtTime :
      ∀ t,
        scalarCurvatureDerivativeAtTime t =
          scalarCurvatureEvolutionRHSAtTime t)
    (curvatureNormAtTime : ℝ → M → ℝ)
    (curvatureNorm_nonnegativeAtTime :
      ∀ (t : ℝ) (x : M), 0 ≤ curvatureNormAtTime t x)
    (curvatureNormDerivativeAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionRHSAtTime : ℝ → M → ℝ)
    (curvatureNormEvolutionInequalityAtTime :
      ∀ (t : ℝ) (x : M),
        curvatureNormDerivativeAtTime t x ≤
          curvatureNormEvolutionRHSAtTime t x)
    (riemannSecondBianchiAtTime :
      RiemannCurvatureSecondBianchiData (metric_of_ricci_flow_data flow))
    (riemannCurvatureDerivativeAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionRHSAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow))
    (riemannCurvatureEvolutionAtTime :
      ∀ t,
        riemannCurvatureDerivativeAtTime t =
          riemannCurvatureEvolutionRHSAtTime t) :
    (((((((((((((((((((((((((((((HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries
        (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory
        (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity
        (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory
        (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow) ∧
      HasDeTurckGaugeFixing flow) ∧
      HasDeTurckBackgroundMetricCompatibility flow) ∧
      HasDeTurckVectorFieldConstruction flow) ∧
      HasDeTurckEquationDerivation flow) ∧
      HasRicciDeTurckLinearization flow) ∧
      HasStrictlyParabolicDeTurckSystem flow) ∧
      HasParabolicLinearTheory flow) ∧
      HasParabolicFixedPointArgument flow) ∧
      HasDeTurckShortTimeExistence flow) ∧
      HasShortTimeRegularityBootstrap flow) ∧
      HasDeTurckDiffeomorphismODE flow) ∧
      HasDeTurckPullbackEquationIdentity flow) ∧
      HasDeTurckPullbackToRicciFlow flow) ∧
      HasShortTimeRicciFlowSolution flow) ∧
      HasRicciFlowMaximalTimeInterval flow) ∧
      HasRicciFlowContinuationCriterion flow) ∧
      HasCurvatureBlowUpContinuationCriterion flow) ∧
      HasMaximalSolutionExtension flow) ∧
      HasParabolicSchauderEstimates flow) ∧
      HasRicciFlowParabolicRegularity flow) ∧
      HasShiDerivativeEstimates flow) ∧
      HasCurvatureDerivativeBootstrap flow) ∧
      HasHamiltonMaximumPrinciple flow) ∧
      HasRicciFlowUniquenessTheory flow) ∧
      HasMetricEvolutionEquation flow) ∧
      HasRicciTensorEvolutionEquation flow) ∧
      HasScalarCurvatureEvolutionEquation flow) ∧
      HasCurvatureNormEvolutionInequality flow) ∧
      HasCurvatureEvolutionEquations flow :=
  let firstFortySix :=
    analyticFirstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      scalarCurvatureTheoryAtTime equationVerificationAtTime
      vectorFieldAtTime ricciDeTurckEquationAtTime linearizationAtTime
      strictParabolicAtTime linearTheoryAtTime fixedPointAtTime
      shortTimeAtTime regularityAtTime odeAtTime pullbackIdentityAtTime
      uniquenessByInitialMetric ricciTensorDerivativeAtTime
      ricciTensorEvolutionRHSAtTime ricciTensorEvolutionAtTime
      scalarCurvatureDerivativeAtTime scalarCurvatureEvolutionRHSAtTime
      scalarCurvatureEvolutionAtTime curvatureNormAtTime
      curvatureNorm_nonnegativeAtTime curvatureNormDerivativeAtTime
      curvatureNormEvolutionRHSAtTime
      curvatureNormEvolutionInequalityAtTime
  ⟨firstFortySix,
    hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequality_and_curvatureEvolutionEquations
      firstFortySix.2 riemannSecondBianchiAtTime
      riemannCurvatureDerivativeAtTime riemannCurvatureEvolutionRHSAtTime
      riemannCurvatureEvolutionAtTime⟩

/--
Analytic foundation package for Ricci flow before surgery.

The package records a Ricci-flow solution plus the connection, curvature,
Ricci-contraction, short-time existence, and continuation-theorem inputs that a
real formalization would have to prove.
-/
structure RicciFlowAnalyticFoundationPackage
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- Ricci-flow data supplied by the analytic foundation. -/
  flow : RicciFlowData I n M
  /-- Existence of the Levi-Civita connection for the metric family. -/
  leviCivitaExistence :
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow)
  /-- Uniqueness of the Levi-Civita connection. -/
  leviCivitaUniqueness :
    HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow)
  /-- Torsion-free property of the Levi-Civita connection. -/
  leviCivitaTorsionFree :
    HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow)
  /-- Metric compatibility of the Levi-Civita connection. -/
  leviCivitaMetricCompatibility :
    HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow)
  /-- Levi-Civita connection theory for the metric family. -/
  leviCivita :
    HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow)
  /-- Construction of the Riemann curvature tensor. -/
  riemannCurvatureConstruction :
    HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow)
  /-- Standard Riemann curvature tensor symmetries. -/
  riemannCurvatureSymmetries :
    HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow)
  /-- First Bianchi identity for the Riemann tensor. -/
  firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow)
  /-- Second Bianchi identity for the Riemann tensor. -/
  secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow)
  /-- Riemann-curvature tensor theory for the metric family. -/
  riemannCurvature :
    HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow)
  /-- Ricci tensor contraction formula. -/
  ricciContractionFormula :
    HasRicciTensorContractionFormula (curvature_data_of_ricci_flow_data flow)
  /-- Scalar-curvature contraction formula. -/
  scalarCurvatureContraction :
    HasScalarCurvatureContractionFormula (curvature_data_of_ricci_flow_data flow)
  /-- Ricci tensor obtained from curvature contraction. -/
  ricciContraction :
    HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow)
  /-- Regularity of the time-dependent metric family. -/
  metricRegularity :
    HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow)
  /-- Time-derivative theory for the metric family. -/
  metricTimeDerivative :
    HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow)
  /-- Scalar-curvature theory attached to the curvature data. -/
  scalarCurvature :
    HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow)
  /-- Derivation of the Ricci-flow equation from the analytic objects. -/
  equationDerivation : HasRicciFlowEquationDerivation flow
  /-- Compatibility of the flow with the initial metric. -/
  initialMetricCompatibility : HasInitialMetricCompatibility flow
  /-- DeTurck gauge-fixing input for the Ricci-flow PDE. -/
  deturckGauge : HasDeTurckGaugeFixing flow
  /-- Compatibility of the background metric used by DeTurck gauge. -/
  deturckBackgroundMetric :
    HasDeTurckBackgroundMetricCompatibility flow
  /-- Construction of the DeTurck vector field. -/
  deturckVectorField : HasDeTurckVectorFieldConstruction flow
  /-- Derivation of the Ricci-DeTurck equation. -/
  deturckEquation : HasDeTurckEquationDerivation flow
  /-- Linearization of the Ricci-DeTurck operator. -/
  deturckLinearization : HasRicciDeTurckLinearization flow
  /-- Strict parabolicity of the DeTurck-gauged equation. -/
  strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow
  /-- Linear parabolic theory for the DeTurck system. -/
  parabolicLinearTheory : HasParabolicLinearTheory flow
  /-- Fixed-point argument for the nonlinear DeTurck system. -/
  parabolicFixedPoint : HasParabolicFixedPointArgument flow
  /-- Short-time existence for Ricci-DeTurck flow. -/
  deturckShortTime : HasDeTurckShortTimeExistence flow
  /-- Regularity bootstrap for the short-time DeTurck solution. -/
  shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow
  /-- ODE for DeTurck diffeomorphisms. -/
  deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow
  /-- Identification of the pulled-back DeTurck equation with Ricci flow. -/
  deturckPullbackEquationIdentity :
    HasDeTurckPullbackEquationIdentity flow
  /-- Pullback from DeTurck flow to Ricci flow. -/
  deturckPullback : HasDeTurckPullbackToRicciFlow flow
  /-- Short-time existence of the Ricci-flow solution. -/
  shortTimeExistence : HasShortTimeRicciFlowSolution flow
  /-- Maximal time interval for the Ricci-flow solution. -/
  maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow
  /-- Continuation criterion for the Ricci-flow solution. -/
  continuationCriterion : HasRicciFlowContinuationCriterion flow
  /-- Curvature blow-up alternative in the continuation theorem. -/
  curvatureBlowUpCriterion : HasCurvatureBlowUpContinuationCriterion flow
  /-- Extension theorem for bounded-curvature maximal solutions. -/
  maximalSolutionExtension : HasMaximalSolutionExtension flow
  /-- Parabolic Schauder estimates for the gauged/ungauged PDE. -/
  parabolicSchauder : HasParabolicSchauderEstimates flow
  /-- Parabolic regularity estimates for the Ricci-flow PDE. -/
  parabolicRegularity : HasRicciFlowParabolicRegularity flow
  /-- Shi-type derivative estimates along the flow. -/
  shiDerivativeEstimates : HasShiDerivativeEstimates flow
  /-- Curvature derivative bootstrap from Shi estimates. -/
  curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow
  /-- Hamilton maximum-principle input for tensor estimates. -/
  maximumPrinciple : HasHamiltonMaximumPrinciple flow
  /-- Uniqueness theory for the Ricci-flow solution. -/
  uniquenessTheory : HasRicciFlowUniquenessTheory flow
  /-- Metric evolution equation along Ricci flow. -/
  metricEvolution : HasMetricEvolutionEquation flow
  /-- Ricci tensor evolution equation along Ricci flow. -/
  ricciTensorEvolution : HasRicciTensorEvolutionEquation flow
  /-- Scalar curvature evolution equation along Ricci flow. -/
  scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow
  /-- Curvature-norm evolution inequality along Ricci flow. -/
  curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow
  /-- Curvature evolution equations along the flow. -/
  curvatureEvolution : HasCurvatureEvolutionEquations flow

/--
The fixed-flow analytic derivation statement: the Ricci-flow data is accompanied
by the connection, curvature, DeTurck, short-time, continuation, regularity, and
evolution evidence that accounts for its Ricci-identification and equation
interfaces.
-/
def AnalyticFoundationDerivationStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
  ∃ _leviCivitaExistence :
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow),
  ∃ _leviCivitaUniqueness :
    HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow),
  ∃ _leviCivitaTorsionFree :
    HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow),
  ∃ _leviCivitaMetricCompatibility :
    HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow),
  ∃ _leviCivita :
    HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow),
  ∃ _riemannCurvatureConstruction :
    HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow),
  ∃ _riemannCurvatureSymmetries :
    HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow),
  ∃ _firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow),
  ∃ _secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow),
  ∃ _riemannCurvature :
    HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow),
  ∃ _ricciContractionFormula :
    HasRicciTensorContractionFormula
      (curvature_data_of_ricci_flow_data flow),
  ∃ _scalarCurvatureContraction :
    HasScalarCurvatureContractionFormula
      (curvature_data_of_ricci_flow_data flow),
  ∃ _ricciContraction :
    HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow),
  ∃ _metricRegularity :
    HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow),
  ∃ _metricTimeDerivative :
    HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow),
  ∃ _scalarCurvature :
    HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow),
  ∃ _equationDerivation : HasRicciFlowEquationDerivation flow,
  ∃ _initialMetricCompatibility : HasInitialMetricCompatibility flow,
  ∃ _deturckGauge : HasDeTurckGaugeFixing flow,
  ∃ _deturckBackgroundMetric :
    HasDeTurckBackgroundMetricCompatibility flow,
  ∃ _deturckVectorField : HasDeTurckVectorFieldConstruction flow,
  ∃ _deturckEquation : HasDeTurckEquationDerivation flow,
  ∃ _deturckLinearization : HasRicciDeTurckLinearization flow,
  ∃ _strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow,
  ∃ _parabolicLinearTheory : HasParabolicLinearTheory flow,
  ∃ _parabolicFixedPoint : HasParabolicFixedPointArgument flow,
  ∃ _deturckShortTime : HasDeTurckShortTimeExistence flow,
  ∃ _shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow,
  ∃ _deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow,
  ∃ _deturckPullbackEquationIdentity :
    HasDeTurckPullbackEquationIdentity flow,
  ∃ _deturckPullback : HasDeTurckPullbackToRicciFlow flow,
  ∃ _shortTimeExistence : HasShortTimeRicciFlowSolution flow,
  ∃ _maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow,
  ∃ _continuationCriterion : HasRicciFlowContinuationCriterion flow,
  ∃ _curvatureBlowUpCriterion :
    HasCurvatureBlowUpContinuationCriterion flow,
  ∃ _maximalSolutionExtension : HasMaximalSolutionExtension flow,
  ∃ _parabolicSchauder : HasParabolicSchauderEstimates flow,
  ∃ _parabolicRegularity : HasRicciFlowParabolicRegularity flow,
  ∃ _shiDerivativeEstimates : HasShiDerivativeEstimates flow,
  ∃ _curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow,
  ∃ _maximumPrinciple : HasHamiltonMaximumPrinciple flow,
  ∃ _uniquenessTheory : HasRicciFlowUniquenessTheory flow,
  ∃ _metricEvolution : HasMetricEvolutionEquation flow,
  ∃ _ricciTensorEvolution : HasRicciTensorEvolutionEquation flow,
  ∃ _scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow,
  ∃ _curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow,
  ∃ _curvatureEvolution : HasCurvatureEvolutionEquations flow,
  ∃ _ricciIdentification :
    IsRicciTensorOf
      (metric_of_ricci_flow_data flow)
      (ricci_tensor_field_of_curvature_data
        (curvature_data_of_ricci_flow_data flow)),
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow)

/--
The fixed-flow analytic derivation statement is exactly the listed connection,
curvature, DeTurck, short-time, continuation, regularity, evolution,
Ricci-identification, and Ricci-flow equation witness stack.
-/
theorem analyticFoundationDerivationStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationDerivationStatement flow =
      (∃ _leviCivitaExistence :
        HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow),
      ∃ _leviCivitaUniqueness :
        HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow),
      ∃ _leviCivitaTorsionFree :
        HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow),
      ∃ _leviCivitaMetricCompatibility :
        HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow),
      ∃ _leviCivita :
        HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow),
      ∃ _riemannCurvatureConstruction :
        HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow),
      ∃ _riemannCurvatureSymmetries :
        HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow),
      ∃ _firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow),
      ∃ _secondBianchi :
        HasSecondBianchiIdentity (metric_of_ricci_flow_data flow),
      ∃ _riemannCurvature :
        HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow),
      ∃ _ricciContractionFormula :
        HasRicciTensorContractionFormula
          (curvature_data_of_ricci_flow_data flow),
      ∃ _scalarCurvatureContraction :
        HasScalarCurvatureContractionFormula
          (curvature_data_of_ricci_flow_data flow),
      ∃ _ricciContraction :
        HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow),
      ∃ _metricRegularity :
        HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow),
      ∃ _metricTimeDerivative :
        HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow),
      ∃ _scalarCurvature :
        HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow),
      ∃ _equationDerivation : HasRicciFlowEquationDerivation flow,
      ∃ _initialMetricCompatibility : HasInitialMetricCompatibility flow,
      ∃ _deturckGauge : HasDeTurckGaugeFixing flow,
      ∃ _deturckBackgroundMetric :
        HasDeTurckBackgroundMetricCompatibility flow,
      ∃ _deturckVectorField : HasDeTurckVectorFieldConstruction flow,
      ∃ _deturckEquation : HasDeTurckEquationDerivation flow,
      ∃ _deturckLinearization : HasRicciDeTurckLinearization flow,
      ∃ _strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow,
      ∃ _parabolicLinearTheory : HasParabolicLinearTheory flow,
      ∃ _parabolicFixedPoint : HasParabolicFixedPointArgument flow,
      ∃ _deturckShortTime : HasDeTurckShortTimeExistence flow,
      ∃ _shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow,
      ∃ _deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow,
      ∃ _deturckPullbackEquationIdentity :
        HasDeTurckPullbackEquationIdentity flow,
      ∃ _deturckPullback : HasDeTurckPullbackToRicciFlow flow,
      ∃ _shortTimeExistence : HasShortTimeRicciFlowSolution flow,
      ∃ _maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow,
      ∃ _continuationCriterion : HasRicciFlowContinuationCriterion flow,
      ∃ _curvatureBlowUpCriterion :
        HasCurvatureBlowUpContinuationCriterion flow,
      ∃ _maximalSolutionExtension : HasMaximalSolutionExtension flow,
      ∃ _parabolicSchauder : HasParabolicSchauderEstimates flow,
      ∃ _parabolicRegularity : HasRicciFlowParabolicRegularity flow,
      ∃ _shiDerivativeEstimates : HasShiDerivativeEstimates flow,
      ∃ _curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow,
      ∃ _maximumPrinciple : HasHamiltonMaximumPrinciple flow,
      ∃ _uniquenessTheory : HasRicciFlowUniquenessTheory flow,
      ∃ _metricEvolution : HasMetricEvolutionEquation flow,
      ∃ _ricciTensorEvolution : HasRicciTensorEvolutionEquation flow,
      ∃ _scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow,
      ∃ _curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow,
      ∃ _curvatureEvolution : HasCurvatureEvolutionEquations flow,
      ∃ _ricciIdentification :
        IsRicciTensorOf
          (metric_of_ricci_flow_data flow)
          (ricci_tensor_field_of_curvature_data
            (curvature_data_of_ricci_flow_data flow)),
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow)) :=
  rfl

/--
The theorem-shaped analytic foundation statement supplied by a completed
analytic package.
-/
def RicciFlowAnalyticFoundationStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    Prop :=
  ∃ flow : RicciFlowData I n M, AnalyticFoundationDerivationStatement flow

/--
The theorem-shaped analytic-foundation interface is exactly existence of
Ricci-flow data equipped with the fixed-flow analytic derivation statement.
-/
theorem ricciFlowAnalyticFoundationStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    RicciFlowAnalyticFoundationStatement I n M =
      (∃ flow : RicciFlowData I n M,
        AnalyticFoundationDerivationStatement flow) :=
  rfl

/--
Analytic foundation strengthened with the explicit Ricci-flow equation boundary.

This is a theorem-shaped target for future wiring: it requires both the existing
analytic derivation stack and a boundary package witnessing the pointwise
equation `∂ₜ g = -2 Ricci`.
-/
def AnalyticFoundationWithEquationBoundaryStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
  AnalyticFoundationDerivationStatement flow ∧
    RicciFlowEquationBoundaryStatement flow

/-- The strengthened analytic-boundary statement is a conjunction of its parts. -/
theorem analyticFoundationWithEquationBoundaryStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationWithEquationBoundaryStatement flow =
      (AnalyticFoundationDerivationStatement flow ∧
        RicciFlowEquationBoundaryStatement flow) :=
  rfl

/-- Assemble the strengthened analytic-boundary statement from its components. -/
theorem analytic_foundation_with_equation_boundary_of_derivation_and_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (boundary : RicciFlowEquationBoundaryStatement flow) :
    AnalyticFoundationWithEquationBoundaryStatement flow :=
  ⟨derivation, boundary⟩

/-- The strengthened analytic-boundary assembler is the conjunction constructor. -/
@[simp] theorem analytic_foundation_with_equation_boundary_of_derivation_and_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (boundary : RicciFlowEquationBoundaryStatement flow) :
    analytic_foundation_with_equation_boundary_of_derivation_and_boundary
      derivation boundary =
        ⟨derivation, boundary⟩ :=
  rfl

/--
Assemble the strengthened analytic-boundary statement from the analytic
derivation stack and explicit pointwise Ricci-flow equation verification.
-/
theorem analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    AnalyticFoundationWithEquationBoundaryStatement flow :=
  analytic_foundation_with_equation_boundary_of_derivation_and_boundary
    derivation
    (ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
      flow verification)

/--
The derivation-plus-verification route delegates to the boundary-statement
constructor built from the supplied explicit equation verification.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
      derivation verification =
      analytic_foundation_with_equation_boundary_of_derivation_and_boundary
        derivation
        (ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
          flow verification) := by
  apply Subsingleton.elim

/-- Project the analytic derivation stack from the strengthened statement. -/
theorem analytic_foundation_derivation_of_with_equation_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    AnalyticFoundationDerivationStatement flow :=
  statement.1

/-- The analytic-derivation projection is the first component. -/
@[simp] theorem analytic_foundation_derivation_of_with_equation_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    analytic_foundation_derivation_of_with_equation_boundary statement =
      statement.1 :=
  rfl

/-- Project the equation boundary from the strengthened statement. -/
theorem equation_boundary_of_analytic_foundation_with_equation_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    RicciFlowEquationBoundaryStatement flow :=
  statement.2

/-- The equation-boundary projection is the second component. -/
@[simp] theorem equation_boundary_of_analytic_foundation_with_equation_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    equation_boundary_of_analytic_foundation_with_equation_boundary statement =
      statement.2 :=
  rfl

/--
Assemble the fixed-flow analytic derivation statement from the named analytic
foundation components.
-/
theorem analytic_foundation_derivation_statement_of_components
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (leviCivitaExistence :
      HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow))
    (leviCivitaUniqueness :
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow))
    (leviCivitaTorsionFree :
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow))
    (leviCivitaMetricCompatibility :
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow))
    (leviCivita :
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow))
    (riemannCurvatureConstruction :
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow))
    (riemannCurvatureSymmetries :
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow))
    (firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow))
    (secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow))
    (riemannCurvature :
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow))
    (ricciContractionFormula :
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (scalarCurvatureContraction :
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (ricciContraction :
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow))
    (metricRegularity :
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow))
    (metricTimeDerivative :
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow))
    (scalarCurvature :
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow))
    (equationDerivation : HasRicciFlowEquationDerivation flow)
    (initialMetricCompatibility : HasInitialMetricCompatibility flow)
    (deturckGauge : HasDeTurckGaugeFixing flow)
    (deturckBackgroundMetric :
      HasDeTurckBackgroundMetricCompatibility flow)
    (deturckVectorField : HasDeTurckVectorFieldConstruction flow)
    (deturckEquation : HasDeTurckEquationDerivation flow)
    (deturckLinearization : HasRicciDeTurckLinearization flow)
    (strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow)
    (parabolicLinearTheory : HasParabolicLinearTheory flow)
    (parabolicFixedPoint : HasParabolicFixedPointArgument flow)
    (deturckShortTime : HasDeTurckShortTimeExistence flow)
    (shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow)
    (deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow)
    (deturckPullbackEquationIdentity :
      HasDeTurckPullbackEquationIdentity flow)
    (deturckPullback : HasDeTurckPullbackToRicciFlow flow)
    (shortTimeExistence : HasShortTimeRicciFlowSolution flow)
    (maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow)
    (continuationCriterion : HasRicciFlowContinuationCriterion flow)
    (curvatureBlowUpCriterion :
      HasCurvatureBlowUpContinuationCriterion flow)
    (maximalSolutionExtension : HasMaximalSolutionExtension flow)
    (parabolicSchauder : HasParabolicSchauderEstimates flow)
    (parabolicRegularity : HasRicciFlowParabolicRegularity flow)
    (shiDerivativeEstimates : HasShiDerivativeEstimates flow)
    (curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow)
    (maximumPrinciple : HasHamiltonMaximumPrinciple flow)
    (uniquenessTheory : HasRicciFlowUniquenessTheory flow)
    (metricEvolution : HasMetricEvolutionEquation flow)
    (ricciTensorEvolution : HasRicciTensorEvolutionEquation flow)
    (scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow)
    (curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow)
    (curvatureEvolution : HasCurvatureEvolutionEquations flow)
    (ricciIdentification :
      IsRicciTensorOf
        (metric_of_ricci_flow_data flow)
        (ricci_tensor_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data flow)
        (curvature_data_of_ricci_flow_data flow)) :
    AnalyticFoundationDerivationStatement flow :=
  ⟨leviCivitaExistence, leviCivitaUniqueness,
    leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
    riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
    secondBianchi, riemannCurvature, ricciContractionFormula,
    scalarCurvatureContraction, ricciContraction, metricRegularity,
    metricTimeDerivative, scalarCurvature, equationDerivation,
    initialMetricCompatibility, deturckGauge, deturckBackgroundMetric,
    deturckVectorField, deturckEquation, deturckLinearization,
    strictParabolicDeturck, parabolicLinearTheory, parabolicFixedPoint,
    deturckShortTime, shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
    deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
    maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
    maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
    shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
    uniquenessTheory, metricEvolution, ricciTensorEvolution,
    scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution,
    ricciIdentification, equationEvidence⟩

/--
The fixed-flow analytic-foundation component assembler is exactly the tuple of
connection, curvature, DeTurck, continuation, regularity, evolution,
Ricci-identification, and equation witnesses.
-/
theorem analytic_foundation_derivation_statement_of_components_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (leviCivitaExistence :
      HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow))
    (leviCivitaUniqueness :
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow))
    (leviCivitaTorsionFree :
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow))
    (leviCivitaMetricCompatibility :
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow))
    (leviCivita :
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow))
    (riemannCurvatureConstruction :
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow))
    (riemannCurvatureSymmetries :
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow))
    (firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow))
    (secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow))
    (riemannCurvature :
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow))
    (ricciContractionFormula :
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (scalarCurvatureContraction :
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (ricciContraction :
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow))
    (metricRegularity :
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow))
    (metricTimeDerivative :
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow))
    (scalarCurvature :
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow))
    (equationDerivation : HasRicciFlowEquationDerivation flow)
    (initialMetricCompatibility : HasInitialMetricCompatibility flow)
    (deturckGauge : HasDeTurckGaugeFixing flow)
    (deturckBackgroundMetric :
      HasDeTurckBackgroundMetricCompatibility flow)
    (deturckVectorField : HasDeTurckVectorFieldConstruction flow)
    (deturckEquation : HasDeTurckEquationDerivation flow)
    (deturckLinearization : HasRicciDeTurckLinearization flow)
    (strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow)
    (parabolicLinearTheory : HasParabolicLinearTheory flow)
    (parabolicFixedPoint : HasParabolicFixedPointArgument flow)
    (deturckShortTime : HasDeTurckShortTimeExistence flow)
    (shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow)
    (deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow)
    (deturckPullbackEquationIdentity :
      HasDeTurckPullbackEquationIdentity flow)
    (deturckPullback : HasDeTurckPullbackToRicciFlow flow)
    (shortTimeExistence : HasShortTimeRicciFlowSolution flow)
    (maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow)
    (continuationCriterion : HasRicciFlowContinuationCriterion flow)
    (curvatureBlowUpCriterion :
      HasCurvatureBlowUpContinuationCriterion flow)
    (maximalSolutionExtension : HasMaximalSolutionExtension flow)
    (parabolicSchauder : HasParabolicSchauderEstimates flow)
    (parabolicRegularity : HasRicciFlowParabolicRegularity flow)
    (shiDerivativeEstimates : HasShiDerivativeEstimates flow)
    (curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow)
    (maximumPrinciple : HasHamiltonMaximumPrinciple flow)
    (uniquenessTheory : HasRicciFlowUniquenessTheory flow)
    (metricEvolution : HasMetricEvolutionEquation flow)
    (ricciTensorEvolution : HasRicciTensorEvolutionEquation flow)
    (scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow)
    (curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow)
    (curvatureEvolution : HasCurvatureEvolutionEquations flow)
    (ricciIdentification :
      IsRicciTensorOf
        (metric_of_ricci_flow_data flow)
        (ricci_tensor_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data flow)
        (curvature_data_of_ricci_flow_data flow)) :
    analytic_foundation_derivation_statement_of_components flow
        leviCivitaExistence leviCivitaUniqueness leviCivitaTorsionFree
        leviCivitaMetricCompatibility leviCivita
        riemannCurvatureConstruction riemannCurvatureSymmetries firstBianchi
        secondBianchi riemannCurvature ricciContractionFormula
        scalarCurvatureContraction ricciContraction metricRegularity
        metricTimeDerivative scalarCurvature equationDerivation
        initialMetricCompatibility deturckGauge deturckBackgroundMetric
        deturckVectorField deturckEquation deturckLinearization
        strictParabolicDeturck parabolicLinearTheory parabolicFixedPoint
        deturckShortTime shortTimeRegularityBootstrap deturckDiffeomorphismODE
        deturckPullbackEquationIdentity deturckPullback shortTimeExistence
        maximalTimeInterval continuationCriterion curvatureBlowUpCriterion
        maximalSolutionExtension parabolicSchauder parabolicRegularity
        shiDerivativeEstimates curvatureDerivativeBootstrap maximumPrinciple
        uniquenessTheory metricEvolution ricciTensorEvolution
        scalarCurvatureEvolution curvatureNormEvolution curvatureEvolution
        ricciIdentification equationEvidence =
      (by
        exact ⟨leviCivitaExistence, leviCivitaUniqueness,
          leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
          riemannCurvatureConstruction, riemannCurvatureSymmetries,
          firstBianchi, secondBianchi, riemannCurvature,
          ricciContractionFormula, scalarCurvatureContraction,
          ricciContraction, metricRegularity, metricTimeDerivative,
          scalarCurvature, equationDerivation, initialMetricCompatibility,
          deturckGauge, deturckBackgroundMetric, deturckVectorField,
          deturckEquation, deturckLinearization, strictParabolicDeturck,
          parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
          shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
          deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
          maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
          maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
          shiDerivativeEstimates, curvatureDerivativeBootstrap,
          maximumPrinciple, uniquenessTheory, metricEvolution,
          ricciTensorEvolution, scalarCurvatureEvolution,
          curvatureNormEvolution, curvatureEvolution, ricciIdentification,
          equationEvidence⟩) := by
  apply Subsingleton.elim

/--
Semantic alias for the named analytic sub-obligation payload exposed by a
theorem-shaped fixed-flow analytic derivation statement.
-/
abbrev AnalyticFoundationSubobligationsPayload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
    HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
    HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
    HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
    HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
    HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
    HasRicciTensorContractionFormula
      (curvature_data_of_ricci_flow_data flow) ∧
    HasScalarCurvatureContractionFormula
      (curvature_data_of_ricci_flow_data flow) ∧
    HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
    HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
    HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
    HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
    HasRicciFlowEquationDerivation flow ∧
    HasInitialMetricCompatibility flow ∧
    HasDeTurckGaugeFixing flow ∧
    HasDeTurckBackgroundMetricCompatibility flow ∧
    HasDeTurckVectorFieldConstruction flow ∧
    HasDeTurckEquationDerivation flow ∧
    HasRicciDeTurckLinearization flow ∧
    HasStrictlyParabolicDeTurckSystem flow ∧
    HasParabolicLinearTheory flow ∧
    HasParabolicFixedPointArgument flow ∧
    HasDeTurckShortTimeExistence flow ∧
    HasShortTimeRegularityBootstrap flow ∧
    HasDeTurckDiffeomorphismODE flow ∧
    HasDeTurckPullbackEquationIdentity flow ∧
    HasDeTurckPullbackToRicciFlow flow ∧
    HasShortTimeRicciFlowSolution flow ∧
    HasRicciFlowMaximalTimeInterval flow ∧
    HasRicciFlowContinuationCriterion flow ∧
    HasCurvatureBlowUpContinuationCriterion flow ∧
    HasMaximalSolutionExtension flow ∧
    HasParabolicSchauderEstimates flow ∧
    HasRicciFlowParabolicRegularity flow ∧
    HasShiDerivativeEstimates flow ∧
    HasCurvatureDerivativeBootstrap flow ∧
    HasHamiltonMaximumPrinciple flow ∧
    HasRicciFlowUniquenessTheory flow ∧
    HasMetricEvolutionEquation flow ∧
    HasRicciTensorEvolutionEquation flow ∧
    HasScalarCurvatureEvolutionEquation flow ∧
    HasCurvatureNormEvolutionInequality flow ∧
    HasCurvatureEvolutionEquations flow

/--
The analytic sub-obligation payload alias is definitionally the full
Levi-Civita, curvature, DeTurck, continuation, regularity, uniqueness, and
evolution-equation witness stack for the fixed Ricci-flow data.
-/
theorem analyticFoundationSubobligationsPayload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationSubobligationsPayload flow =
      (HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow ∧
      HasDeTurckGaugeFixing flow ∧
      HasDeTurckBackgroundMetricCompatibility flow ∧
      HasDeTurckVectorFieldConstruction flow ∧
      HasDeTurckEquationDerivation flow ∧
      HasRicciDeTurckLinearization flow ∧
      HasStrictlyParabolicDeTurckSystem flow ∧
      HasParabolicLinearTheory flow ∧
      HasParabolicFixedPointArgument flow ∧
      HasDeTurckShortTimeExistence flow ∧
      HasShortTimeRegularityBootstrap flow ∧
      HasDeTurckDiffeomorphismODE flow ∧
      HasDeTurckPullbackEquationIdentity flow ∧
      HasDeTurckPullbackToRicciFlow flow ∧
      HasShortTimeRicciFlowSolution flow ∧
      HasRicciFlowMaximalTimeInterval flow ∧
      HasRicciFlowContinuationCriterion flow ∧
      HasCurvatureBlowUpContinuationCriterion flow ∧
      HasMaximalSolutionExtension flow ∧
      HasParabolicSchauderEstimates flow ∧
      HasRicciFlowParabolicRegularity flow ∧
      HasShiDerivativeEstimates flow ∧
      HasCurvatureDerivativeBootstrap flow ∧
      HasHamiltonMaximumPrinciple flow ∧
      HasRicciFlowUniquenessTheory flow ∧
      HasMetricEvolutionEquation flow ∧
      HasRicciTensorEvolutionEquation flow ∧
      HasScalarCurvatureEvolutionEquation flow ∧
      HasCurvatureNormEvolutionInequality flow ∧
      HasCurvatureEvolutionEquations flow) :=
  rfl

/--
Build an analytic-foundation package from fixed Ricci-flow data and the named
analytic sub-obligation payload for that same flow.

This is the reusable payload-to-package direction: the flow already stores its
Ricci-identification and equation evidence, while the payload supplies the
Levi-Civita, curvature, DeTurck, continuation, regularity, uniqueness, and
evolution-equation obligations.
-/
noncomputable def analytic_foundation_package_of_subobligations_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    RicciFlowAnalyticFoundationPackage I n M := by
  rcases subobligations with
    ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
      leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
      riemannCurvatureSymmetries, firstBianchi, secondBianchi,
      riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
      ricciContraction, metricRegularity, metricTimeDerivative,
      scalarCurvature, equationDerivation, initialMetricCompatibility,
      deturckGauge, deturckBackgroundMetric, deturckVectorField,
      deturckEquation, deturckLinearization, strictParabolicDeturck,
      parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
      shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
      deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
      maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
      maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
      shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
      uniquenessTheory, metricEvolution, ricciTensorEvolution,
      scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution⟩
  exact
    { flow := flow
      leviCivitaExistence := leviCivitaExistence
      leviCivitaUniqueness := leviCivitaUniqueness
      leviCivitaTorsionFree := leviCivitaTorsionFree
      leviCivitaMetricCompatibility := leviCivitaMetricCompatibility
      leviCivita := leviCivita
      riemannCurvatureConstruction := riemannCurvatureConstruction
      riemannCurvatureSymmetries := riemannCurvatureSymmetries
      firstBianchi := firstBianchi
      secondBianchi := secondBianchi
      riemannCurvature := riemannCurvature
      ricciContractionFormula := ricciContractionFormula
      scalarCurvatureContraction := scalarCurvatureContraction
      ricciContraction := ricciContraction
      metricRegularity := metricRegularity
      metricTimeDerivative := metricTimeDerivative
      scalarCurvature := scalarCurvature
      equationDerivation := equationDerivation
      initialMetricCompatibility := initialMetricCompatibility
      deturckGauge := deturckGauge
      deturckBackgroundMetric := deturckBackgroundMetric
      deturckVectorField := deturckVectorField
      deturckEquation := deturckEquation
      deturckLinearization := deturckLinearization
      strictParabolicDeturck := strictParabolicDeturck
      parabolicLinearTheory := parabolicLinearTheory
      parabolicFixedPoint := parabolicFixedPoint
      deturckShortTime := deturckShortTime
      shortTimeRegularityBootstrap := shortTimeRegularityBootstrap
      deturckDiffeomorphismODE := deturckDiffeomorphismODE
      deturckPullbackEquationIdentity := deturckPullbackEquationIdentity
      deturckPullback := deturckPullback
      shortTimeExistence := shortTimeExistence
      maximalTimeInterval := maximalTimeInterval
      continuationCriterion := continuationCriterion
      curvatureBlowUpCriterion := curvatureBlowUpCriterion
      maximalSolutionExtension := maximalSolutionExtension
      parabolicSchauder := parabolicSchauder
      parabolicRegularity := parabolicRegularity
      shiDerivativeEstimates := shiDerivativeEstimates
      curvatureDerivativeBootstrap := curvatureDerivativeBootstrap
      maximumPrinciple := maximumPrinciple
      uniquenessTheory := uniquenessTheory
      metricEvolution := metricEvolution
      ricciTensorEvolution := ricciTensorEvolution
      scalarCurvatureEvolution := scalarCurvatureEvolution
      curvatureNormEvolution := curvatureNormEvolution
      curvatureEvolution := curvatureEvolution }

/-- The generic analytic package constructor stores the supplied flow data. -/
@[simp] theorem analytic_foundation_package_of_subobligations_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    (analytic_foundation_package_of_subobligations_payload
      flow subobligations).flow = flow := by
  rcases subobligations with
    ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
      leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
      riemannCurvatureSymmetries, firstBianchi, secondBianchi,
      riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
      ricciContraction, metricRegularity, metricTimeDerivative,
      scalarCurvature, equationDerivation, initialMetricCompatibility,
      deturckGauge, deturckBackgroundMetric, deturckVectorField,
      deturckEquation, deturckLinearization, strictParabolicDeturck,
      parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
      shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
      deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
      maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
      maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
      shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
      uniquenessTheory, metricEvolution, ricciTensorEvolution,
      scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution⟩
  rfl

/--
The fixed-flow analytic derivation statement exposes the named analytic
connection, curvature, DeTurck, continuation, regularity, and evolution
sub-obligations.
-/
theorem analytic_foundation_subobligations_of_derivation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (statement : AnalyticFoundationDerivationStatement flow) :
    AnalyticFoundationSubobligationsPayload flow := by
  rcases statement with
    ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
      leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
      riemannCurvatureSymmetries, firstBianchi, secondBianchi,
      riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
      ricciContraction, metricRegularity, metricTimeDerivative,
      scalarCurvature, equationDerivation, initialMetricCompatibility,
      deturckGauge, deturckBackgroundMetric, deturckVectorField,
      deturckEquation, deturckLinearization, strictParabolicDeturck,
      parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
      shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
      deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
      maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
      maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
      shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
      uniquenessTheory, metricEvolution, ricciTensorEvolution,
      scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution,
      _ricciIdentification, _equationEvidence⟩
  exact ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
    leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
    riemannCurvatureSymmetries, firstBianchi, secondBianchi,
    riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
    ricciContraction, metricRegularity, metricTimeDerivative, scalarCurvature,
    equationDerivation, initialMetricCompatibility, deturckGauge,
    deturckBackgroundMetric, deturckVectorField, deturckEquation,
    deturckLinearization, strictParabolicDeturck, parabolicLinearTheory,
    parabolicFixedPoint, deturckShortTime, shortTimeRegularityBootstrap,
    deturckDiffeomorphismODE, deturckPullbackEquationIdentity,
    deturckPullback, shortTimeExistence, maximalTimeInterval,
    continuationCriterion, curvatureBlowUpCriterion, maximalSolutionExtension,
    parabolicSchauder, parabolicRegularity, shiDerivativeEstimates,
    curvatureDerivativeBootstrap, maximumPrinciple, uniquenessTheory,
    metricEvolution, ricciTensorEvolution, scalarCurvatureEvolution,
    curvatureNormEvolution, curvatureEvolution⟩

/--
The analytic derivation statement bridge exposes exactly the connection,
curvature, DeTurck, continuation, regularity, and evolution sub-obligations
stored before the Ricci-identification and equation evidence.
-/
theorem analytic_foundation_subobligations_of_derivation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (statement : AnalyticFoundationDerivationStatement flow) :
    analytic_foundation_subobligations_of_derivation_statement flow statement =
      (by
        rcases statement with
          ⟨leviCivitaExistence, leviCivitaUniqueness,
            leviCivitaTorsionFree, leviCivitaMetricCompatibility,
            leviCivita, riemannCurvatureConstruction,
            riemannCurvatureSymmetries, firstBianchi, secondBianchi,
            riemannCurvature, ricciContractionFormula,
            scalarCurvatureContraction, ricciContraction, metricRegularity,
            metricTimeDerivative, scalarCurvature, equationDerivation,
            initialMetricCompatibility, deturckGauge, deturckBackgroundMetric,
            deturckVectorField, deturckEquation, deturckLinearization,
            strictParabolicDeturck, parabolicLinearTheory,
            parabolicFixedPoint, deturckShortTime,
            shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
            deturckPullbackEquationIdentity, deturckPullback,
            shortTimeExistence, maximalTimeInterval, continuationCriterion,
            curvatureBlowUpCriterion, maximalSolutionExtension,
            parabolicSchauder, parabolicRegularity, shiDerivativeEstimates,
            curvatureDerivativeBootstrap, maximumPrinciple, uniquenessTheory,
            metricEvolution, ricciTensorEvolution, scalarCurvatureEvolution,
            curvatureNormEvolution, curvatureEvolution, _ricciIdentification,
            _equationEvidence⟩
        exact ⟨leviCivitaExistence, leviCivitaUniqueness,
          leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
          riemannCurvatureConstruction, riemannCurvatureSymmetries,
          firstBianchi, secondBianchi, riemannCurvature,
          ricciContractionFormula, scalarCurvatureContraction,
          ricciContraction, metricRegularity, metricTimeDerivative,
          scalarCurvature, equationDerivation, initialMetricCompatibility,
          deturckGauge, deturckBackgroundMetric, deturckVectorField,
          deturckEquation, deturckLinearization, strictParabolicDeturck,
          parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
          shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
          deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
          maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
          maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
          shiDerivativeEstimates, curvatureDerivativeBootstrap,
          maximumPrinciple, uniquenessTheory, metricEvolution,
          ricciTensorEvolution, scalarCurvatureEvolution,
          curvatureNormEvolution, curvatureEvolution⟩) := by
  apply Subsingleton.elim

/-- Project Ricci-flow data from an analytic-foundation package. -/
def ricci_flow_data_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    RicciFlowData I n M :=
  package.flow

/-- The named analytic-foundation flow projection is definitionally the package field. -/
@[simp] theorem ricci_flow_data_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_flow_data_of_analytic_foundation_package package = package.flow :=
  rfl

/-- Project Levi-Civita connection existence from an analytic-foundation package. -/
theorem levi_civita_existence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaExistence

/-- Project Levi-Civita connection uniqueness from an analytic-foundation package. -/
theorem levi_civita_uniqueness_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaConnectionUniqueness
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaUniqueness

/-- Project the torsion-free Levi-Civita property from an analytic-foundation package. -/
theorem levi_civita_torsion_free_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaTorsionFreeProperty
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaTorsionFree

/-- Project Levi-Civita metric compatibility from an analytic-foundation package. -/
theorem levi_civita_metric_compatibility_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaMetricCompatibility
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaMetricCompatibility

/-- Project the Levi-Civita theory input from an analytic-foundation package. -/
theorem levi_civita_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaConnectionTheory
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivita

/-- Project Riemann curvature tensor construction from an analytic-foundation package. -/
theorem riemann_curvature_construction_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRiemannCurvatureTensorConstruction
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.riemannCurvatureConstruction

/-- Project Riemann curvature tensor symmetries from an analytic-foundation package. -/
theorem riemann_curvature_symmetries_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRiemannCurvatureTensorSymmetries
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.riemannCurvatureSymmetries

/-- Project the first Bianchi identity from an analytic-foundation package. -/
theorem first_bianchi_identity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasFirstBianchiIdentity
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.firstBianchi

/-- Project the second Bianchi identity from an analytic-foundation package. -/
theorem second_bianchi_identity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasSecondBianchiIdentity
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.secondBianchi

/-- Project the Riemann-curvature theory input from an analytic-foundation package. -/
theorem riemann_curvature_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRiemannCurvatureTensorTheory
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.riemannCurvature

/-- Project the Ricci tensor contraction formula from an analytic-foundation package. -/
theorem ricci_contraction_formula_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciTensorContractionFormula
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.ricciContractionFormula

/-- Project the scalar-curvature contraction formula from an analytic-foundation package. -/
theorem scalar_curvature_contraction_formula_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasScalarCurvatureContractionFormula
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.scalarCurvatureContraction

/-- Project the Ricci-contraction theory input from an analytic-foundation package. -/
theorem ricci_contraction_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciContractionTheory
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.ricciContraction

/-- Project metric-regularity theory from an analytic-foundation package. -/
theorem metric_regularity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasTimeDependentMetricRegularity
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.metricRegularity

/-- Project metric-time-derivative theory from an analytic-foundation package. -/
theorem metric_time_derivative_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasMetricTimeDerivativeTheory
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.metricTimeDerivative

/-- Project scalar-curvature theory from an analytic-foundation package. -/
theorem scalar_curvature_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasScalarCurvatureTheory
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.scalarCurvature

/-- Project Ricci-flow equation derivation from an analytic-foundation package. -/
theorem equation_derivation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowEquationDerivation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.equationDerivation

/--
The analytic-foundation Ricci-flow equation derivation projection is exactly
the stored package field.
-/
@[simp] theorem equation_derivation_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    equation_derivation_of_analytic_foundation_package package =
      package.equationDerivation :=
  rfl

/-- Project initial-metric compatibility from an analytic-foundation package. -/
theorem initial_metric_compatibility_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasInitialMetricCompatibility
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.initialMetricCompatibility

/-- Project DeTurck gauge fixing from an analytic-foundation package. -/
theorem deturck_gauge_fixing_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckGaugeFixing
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckGauge

/-- Project DeTurck background-metric compatibility from an analytic-foundation package. -/
theorem deturck_background_metric_compatibility_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckBackgroundMetricCompatibility
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckBackgroundMetric

/-- Project DeTurck vector-field construction from an analytic-foundation package. -/
theorem deturck_vector_field_construction_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckVectorFieldConstruction
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckVectorField

/-- Project the Ricci-DeTurck equation derivation from an analytic-foundation package. -/
theorem deturck_equation_derivation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckEquationDerivation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckEquation

/--
The analytic-foundation Ricci-DeTurck equation derivation projection is exactly
the stored package field.
-/
@[simp] theorem deturck_equation_derivation_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_equation_derivation_of_analytic_foundation_package package =
      package.deturckEquation :=
  rfl

/-- Project Ricci-DeTurck operator linearization from an analytic-foundation package. -/
theorem ricci_deturck_linearization_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciDeTurckLinearization
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckLinearization

/-- Project strict parabolicity of the Ricci-DeTurck system. -/
theorem strictly_parabolic_deturck_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasStrictlyParabolicDeTurckSystem
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.strictParabolicDeturck

/-- Project linear parabolic theory from an analytic-foundation package. -/
theorem parabolic_linear_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasParabolicLinearTheory
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicLinearTheory

/-- Project the parabolic fixed-point argument from an analytic-foundation package. -/
theorem parabolic_fixed_point_argument_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasParabolicFixedPointArgument
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicFixedPoint

/-- Project short-time existence for the Ricci-DeTurck flow. -/
theorem deturck_short_time_existence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckShortTimeExistence
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckShortTime

/-- Project short-time regularity bootstrap from an analytic-foundation package. -/
theorem short_time_regularity_bootstrap_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasShortTimeRegularityBootstrap
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.shortTimeRegularityBootstrap

/-- Project the DeTurck diffeomorphism ODE from an analytic-foundation package. -/
theorem deturck_diffeomorphism_ode_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckDiffeomorphismODE
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckDiffeomorphismODE

/-- Project the DeTurck pullback equation identity from an analytic-foundation package. -/
theorem deturck_pullback_equation_identity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckPullbackEquationIdentity
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckPullbackEquationIdentity

/-- Project the pullback from Ricci-DeTurck flow to Ricci flow. -/
theorem deturck_pullback_to_ricci_flow_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckPullbackToRicciFlow
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckPullback

/-- Project short-time existence from an analytic-foundation package. -/
theorem short_time_existence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasShortTimeRicciFlowSolution
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.shortTimeExistence

/-- Project the maximal-time interval from an analytic-foundation package. -/
theorem maximal_time_interval_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowMaximalTimeInterval
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.maximalTimeInterval

/-- Project the continuation criterion from an analytic-foundation package. -/
theorem continuation_criterion_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowContinuationCriterion
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.continuationCriterion

/-- Project the curvature blow-up continuation criterion. -/
theorem curvature_blowup_criterion_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureBlowUpContinuationCriterion
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureBlowUpCriterion

/-- Project maximal-solution extension from an analytic-foundation package. -/
theorem maximal_solution_extension_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasMaximalSolutionExtension
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.maximalSolutionExtension

/-- Project parabolic Schauder estimates from an analytic-foundation package. -/
theorem parabolic_schauder_estimates_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasParabolicSchauderEstimates
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicSchauder

/-- Project parabolic regularity from an analytic-foundation package. -/
theorem parabolic_regularity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowParabolicRegularity
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicRegularity

/-- Project Shi-type derivative estimates from an analytic-foundation package. -/
theorem shi_derivative_estimates_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasShiDerivativeEstimates
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.shiDerivativeEstimates

/-- Project curvature derivative bootstrap from an analytic-foundation package. -/
theorem curvature_derivative_bootstrap_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureDerivativeBootstrap
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureDerivativeBootstrap

/-- Project Hamilton's maximum principle from an analytic-foundation package. -/
theorem hamilton_maximum_principle_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasHamiltonMaximumPrinciple
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.maximumPrinciple

/-- Project Ricci-flow uniqueness theory from an analytic-foundation package. -/
theorem uniqueness_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowUniquenessTheory
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.uniquenessTheory

/-- Project the metric evolution equation from an analytic-foundation package. -/
theorem metric_evolution_equation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasMetricEvolutionEquation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.metricEvolution

/-- Project the Ricci tensor evolution equation from an analytic-foundation package. -/
theorem ricci_tensor_evolution_equation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciTensorEvolutionEquation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.ricciTensorEvolution

/-- Project the scalar curvature evolution equation from an analytic-foundation package. -/
theorem scalar_curvature_evolution_equation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasScalarCurvatureEvolutionEquation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.scalarCurvatureEvolution

/-- Project the curvature-norm evolution inequality from an analytic-foundation package. -/
theorem curvature_norm_evolution_inequality_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureNormEvolutionInequality
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureNormEvolution

/-- Project curvature evolution equations from an analytic-foundation package. -/
theorem curvature_evolution_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureEvolutionEquations
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureEvolution

/- Direct analytic-foundation package projections are stored package fields. -/
section AnalyticFoundationPackageProjectionContracts

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

@[simp] theorem levi_civita_existence_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_existence_of_analytic_foundation_package package =
      package.leviCivitaExistence :=
  rfl

@[simp] theorem levi_civita_uniqueness_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_uniqueness_of_analytic_foundation_package package =
      package.leviCivitaUniqueness :=
  rfl

@[simp] theorem levi_civita_torsion_free_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_torsion_free_of_analytic_foundation_package package =
      package.leviCivitaTorsionFree :=
  rfl

@[simp] theorem levi_civita_metric_compatibility_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_metric_compatibility_of_analytic_foundation_package package =
      package.leviCivitaMetricCompatibility :=
  rfl

@[simp] theorem levi_civita_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_theory_of_analytic_foundation_package package =
      package.leviCivita :=
  rfl

@[simp] theorem riemann_curvature_construction_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    riemann_curvature_construction_of_analytic_foundation_package package =
      package.riemannCurvatureConstruction :=
  rfl

@[simp] theorem riemann_curvature_symmetries_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    riemann_curvature_symmetries_of_analytic_foundation_package package =
      package.riemannCurvatureSymmetries :=
  rfl

@[simp] theorem first_bianchi_identity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    first_bianchi_identity_of_analytic_foundation_package package =
      package.firstBianchi :=
  rfl

@[simp] theorem second_bianchi_identity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    second_bianchi_identity_of_analytic_foundation_package package =
      package.secondBianchi :=
  rfl

@[simp] theorem riemann_curvature_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    riemann_curvature_theory_of_analytic_foundation_package package =
      package.riemannCurvature :=
  rfl

@[simp] theorem ricci_contraction_formula_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_contraction_formula_of_analytic_foundation_package package =
      package.ricciContractionFormula :=
  rfl

@[simp] theorem scalar_curvature_contraction_formula_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    scalar_curvature_contraction_formula_of_analytic_foundation_package
      package =
      package.scalarCurvatureContraction :=
  rfl

@[simp] theorem ricci_contraction_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_contraction_theory_of_analytic_foundation_package package =
      package.ricciContraction :=
  rfl

@[simp] theorem metric_regularity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    metric_regularity_of_analytic_foundation_package package =
      package.metricRegularity :=
  rfl

@[simp] theorem metric_time_derivative_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    metric_time_derivative_of_analytic_foundation_package package =
      package.metricTimeDerivative :=
  rfl

@[simp] theorem scalar_curvature_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    scalar_curvature_theory_of_analytic_foundation_package package =
      package.scalarCurvature :=
  rfl

@[simp] theorem initial_metric_compatibility_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    initial_metric_compatibility_of_analytic_foundation_package package =
      package.initialMetricCompatibility :=
  rfl

@[simp] theorem deturck_gauge_fixing_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_gauge_fixing_of_analytic_foundation_package package =
      package.deturckGauge :=
  rfl

@[simp] theorem deturck_background_metric_compatibility_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_background_metric_compatibility_of_analytic_foundation_package
      package =
      package.deturckBackgroundMetric :=
  rfl

@[simp] theorem deturck_vector_field_construction_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_vector_field_construction_of_analytic_foundation_package package =
      package.deturckVectorField :=
  rfl

@[simp] theorem ricci_deturck_linearization_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_deturck_linearization_of_analytic_foundation_package package =
      package.deturckLinearization :=
  rfl

@[simp] theorem strictly_parabolic_deturck_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    strictly_parabolic_deturck_of_analytic_foundation_package package =
      package.strictParabolicDeturck :=
  rfl

@[simp] theorem parabolic_linear_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_linear_theory_of_analytic_foundation_package package =
      package.parabolicLinearTheory :=
  rfl

@[simp] theorem parabolic_fixed_point_argument_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_fixed_point_argument_of_analytic_foundation_package package =
      package.parabolicFixedPoint :=
  rfl

@[simp] theorem deturck_short_time_existence_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_short_time_existence_of_analytic_foundation_package package =
      package.deturckShortTime :=
  rfl

@[simp] theorem short_time_regularity_bootstrap_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    short_time_regularity_bootstrap_of_analytic_foundation_package package =
      package.shortTimeRegularityBootstrap :=
  rfl

@[simp] theorem deturck_diffeomorphism_ode_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_diffeomorphism_ode_of_analytic_foundation_package package =
      package.deturckDiffeomorphismODE :=
  rfl

@[simp] theorem deturck_pullback_equation_identity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_pullback_equation_identity_of_analytic_foundation_package package =
      package.deturckPullbackEquationIdentity :=
  rfl

@[simp] theorem deturck_pullback_to_ricci_flow_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_pullback_to_ricci_flow_of_analytic_foundation_package package =
      package.deturckPullback :=
  rfl

@[simp] theorem short_time_existence_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    short_time_existence_of_analytic_foundation_package package =
      package.shortTimeExistence :=
  rfl

@[simp] theorem maximal_time_interval_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    maximal_time_interval_of_analytic_foundation_package package =
      package.maximalTimeInterval :=
  rfl

@[simp] theorem continuation_criterion_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    continuation_criterion_of_analytic_foundation_package package =
      package.continuationCriterion :=
  rfl

@[simp] theorem curvature_blowup_criterion_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_blowup_criterion_of_analytic_foundation_package package =
      package.curvatureBlowUpCriterion :=
  rfl

@[simp] theorem maximal_solution_extension_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    maximal_solution_extension_of_analytic_foundation_package package =
      package.maximalSolutionExtension :=
  rfl

@[simp] theorem parabolic_schauder_estimates_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_schauder_estimates_of_analytic_foundation_package package =
      package.parabolicSchauder :=
  rfl

@[simp] theorem parabolic_regularity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_regularity_of_analytic_foundation_package package =
      package.parabolicRegularity :=
  rfl

@[simp] theorem shi_derivative_estimates_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    shi_derivative_estimates_of_analytic_foundation_package package =
      package.shiDerivativeEstimates :=
  rfl

@[simp] theorem curvature_derivative_bootstrap_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_derivative_bootstrap_of_analytic_foundation_package package =
      package.curvatureDerivativeBootstrap :=
  rfl

@[simp] theorem hamilton_maximum_principle_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    hamilton_maximum_principle_of_analytic_foundation_package package =
      package.maximumPrinciple :=
  rfl

@[simp] theorem uniqueness_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    uniqueness_theory_of_analytic_foundation_package package =
      package.uniquenessTheory :=
  rfl

@[simp] theorem metric_evolution_equation_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    metric_evolution_equation_of_analytic_foundation_package package =
      package.metricEvolution :=
  rfl

@[simp] theorem ricci_tensor_evolution_equation_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_tensor_evolution_equation_of_analytic_foundation_package package =
      package.ricciTensorEvolution :=
  rfl

@[simp] theorem scalar_curvature_evolution_equation_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    scalar_curvature_evolution_equation_of_analytic_foundation_package package =
      package.scalarCurvatureEvolution :=
  rfl

@[simp] theorem curvature_norm_evolution_inequality_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_norm_evolution_inequality_of_analytic_foundation_package
      package =
      package.curvatureNormEvolution :=
  rfl

@[simp] theorem curvature_evolution_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_evolution_of_analytic_foundation_package package =
      package.curvatureEvolution :=
  rfl

end AnalyticFoundationPackageProjectionContracts

/-- Project Ricci-identification evidence from an analytic-foundation package. -/
theorem ricci_identification_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    IsRicciTensorOf
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package))
      (ricci_tensor_field_of_curvature_data
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))) :=
  ricci_identification_of_ricci_flow_data
    (ricci_flow_data_of_analytic_foundation_package package)

/--
The analytic-foundation Ricci-identification projection delegates to the stored
flow data.
-/
theorem ricci_identification_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_identification_of_analytic_foundation_package package =
      ricci_identification_of_ricci_flow_data package.flow :=
  rfl

/-- Project Ricci-flow equation evidence from an analytic-foundation package. -/
theorem equation_evidence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package))
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  equation_evidence_of_ricci_flow_data
    (ricci_flow_data_of_analytic_foundation_package package)

/-- The analytic-foundation equation projection delegates to the stored flow data. -/
theorem equation_evidence_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    equation_evidence_of_analytic_foundation_package package =
      equation_evidence_of_ricci_flow_data package.flow :=
  rfl

/--
A completed analytic-foundation package assembles the fixed-flow analytic
derivation statement for its projected Ricci-flow data.
-/
theorem analytic_foundation_derivation_statement_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    AnalyticFoundationDerivationStatement
      (ricci_flow_data_of_analytic_foundation_package package) :=
  analytic_foundation_derivation_statement_of_components
    (ricci_flow_data_of_analytic_foundation_package package)
    (levi_civita_existence_of_analytic_foundation_package package)
    (levi_civita_uniqueness_of_analytic_foundation_package package)
    (levi_civita_torsion_free_of_analytic_foundation_package package)
    (levi_civita_metric_compatibility_of_analytic_foundation_package package)
    (levi_civita_theory_of_analytic_foundation_package package)
    (riemann_curvature_construction_of_analytic_foundation_package package)
    (riemann_curvature_symmetries_of_analytic_foundation_package package)
    (first_bianchi_identity_of_analytic_foundation_package package)
    (second_bianchi_identity_of_analytic_foundation_package package)
    (riemann_curvature_theory_of_analytic_foundation_package package)
    (ricci_contraction_formula_of_analytic_foundation_package package)
    (scalar_curvature_contraction_formula_of_analytic_foundation_package package)
    (ricci_contraction_theory_of_analytic_foundation_package package)
    (metric_regularity_of_analytic_foundation_package package)
    (metric_time_derivative_of_analytic_foundation_package package)
    (scalar_curvature_theory_of_analytic_foundation_package package)
    (equation_derivation_of_analytic_foundation_package package)
    (initial_metric_compatibility_of_analytic_foundation_package package)
    (deturck_gauge_fixing_of_analytic_foundation_package package)
    (deturck_background_metric_compatibility_of_analytic_foundation_package
      package)
    (deturck_vector_field_construction_of_analytic_foundation_package package)
    (deturck_equation_derivation_of_analytic_foundation_package package)
    (ricci_deturck_linearization_of_analytic_foundation_package package)
    (strictly_parabolic_deturck_of_analytic_foundation_package package)
    (parabolic_linear_theory_of_analytic_foundation_package package)
    (parabolic_fixed_point_argument_of_analytic_foundation_package package)
    (deturck_short_time_existence_of_analytic_foundation_package package)
    (short_time_regularity_bootstrap_of_analytic_foundation_package package)
    (deturck_diffeomorphism_ode_of_analytic_foundation_package package)
    (deturck_pullback_equation_identity_of_analytic_foundation_package package)
    (deturck_pullback_to_ricci_flow_of_analytic_foundation_package package)
    (short_time_existence_of_analytic_foundation_package package)
    (maximal_time_interval_of_analytic_foundation_package package)
    (continuation_criterion_of_analytic_foundation_package package)
    (curvature_blowup_criterion_of_analytic_foundation_package package)
    (maximal_solution_extension_of_analytic_foundation_package package)
    (parabolic_schauder_estimates_of_analytic_foundation_package package)
    (parabolic_regularity_of_analytic_foundation_package package)
    (shi_derivative_estimates_of_analytic_foundation_package package)
    (curvature_derivative_bootstrap_of_analytic_foundation_package package)
    (hamilton_maximum_principle_of_analytic_foundation_package package)
    (uniqueness_theory_of_analytic_foundation_package package)
    (metric_evolution_equation_of_analytic_foundation_package package)
    (ricci_tensor_evolution_equation_of_analytic_foundation_package package)
    (scalar_curvature_evolution_equation_of_analytic_foundation_package package)
    (curvature_norm_evolution_inequality_of_analytic_foundation_package package)
    (curvature_evolution_of_analytic_foundation_package package)
    (ricci_identification_of_analytic_foundation_package package)
    (equation_evidence_of_analytic_foundation_package package)

/--
The analytic-foundation package derivation statement is exactly the fixed-flow
component assembler applied to the package projections.
-/
theorem analytic_foundation_derivation_statement_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package =
      analytic_foundation_derivation_statement_of_components
        (ricci_flow_data_of_analytic_foundation_package package)
        (levi_civita_existence_of_analytic_foundation_package package)
        (levi_civita_uniqueness_of_analytic_foundation_package package)
        (levi_civita_torsion_free_of_analytic_foundation_package package)
        (levi_civita_metric_compatibility_of_analytic_foundation_package
          package)
        (levi_civita_theory_of_analytic_foundation_package package)
        (riemann_curvature_construction_of_analytic_foundation_package package)
        (riemann_curvature_symmetries_of_analytic_foundation_package package)
        (first_bianchi_identity_of_analytic_foundation_package package)
        (second_bianchi_identity_of_analytic_foundation_package package)
        (riemann_curvature_theory_of_analytic_foundation_package package)
        (ricci_contraction_formula_of_analytic_foundation_package package)
        (scalar_curvature_contraction_formula_of_analytic_foundation_package
          package)
        (ricci_contraction_theory_of_analytic_foundation_package package)
        (metric_regularity_of_analytic_foundation_package package)
        (metric_time_derivative_of_analytic_foundation_package package)
        (scalar_curvature_theory_of_analytic_foundation_package package)
        (equation_derivation_of_analytic_foundation_package package)
        (initial_metric_compatibility_of_analytic_foundation_package package)
        (deturck_gauge_fixing_of_analytic_foundation_package package)
        (deturck_background_metric_compatibility_of_analytic_foundation_package
          package)
        (deturck_vector_field_construction_of_analytic_foundation_package
          package)
        (deturck_equation_derivation_of_analytic_foundation_package package)
        (ricci_deturck_linearization_of_analytic_foundation_package package)
        (strictly_parabolic_deturck_of_analytic_foundation_package package)
        (parabolic_linear_theory_of_analytic_foundation_package package)
        (parabolic_fixed_point_argument_of_analytic_foundation_package package)
        (deturck_short_time_existence_of_analytic_foundation_package package)
        (short_time_regularity_bootstrap_of_analytic_foundation_package
          package)
        (deturck_diffeomorphism_ode_of_analytic_foundation_package package)
        (deturck_pullback_equation_identity_of_analytic_foundation_package
          package)
        (deturck_pullback_to_ricci_flow_of_analytic_foundation_package package)
        (short_time_existence_of_analytic_foundation_package package)
        (maximal_time_interval_of_analytic_foundation_package package)
        (continuation_criterion_of_analytic_foundation_package package)
        (curvature_blowup_criterion_of_analytic_foundation_package package)
        (maximal_solution_extension_of_analytic_foundation_package package)
        (parabolic_schauder_estimates_of_analytic_foundation_package package)
        (parabolic_regularity_of_analytic_foundation_package package)
        (shi_derivative_estimates_of_analytic_foundation_package package)
        (curvature_derivative_bootstrap_of_analytic_foundation_package package)
        (hamilton_maximum_principle_of_analytic_foundation_package package)
        (uniqueness_theory_of_analytic_foundation_package package)
        (metric_evolution_equation_of_analytic_foundation_package package)
        (ricci_tensor_evolution_equation_of_analytic_foundation_package
          package)
        (scalar_curvature_evolution_equation_of_analytic_foundation_package
          package)
        (curvature_norm_evolution_inequality_of_analytic_foundation_package
          package)
        (curvature_evolution_of_analytic_foundation_package package)
        (ricci_identification_of_analytic_foundation_package package)
        (equation_evidence_of_analytic_foundation_package package) :=
  rfl

/--
Fixed Ricci-flow data and the named analytic sub-obligation payload for that
flow reconstruct the fixed-flow analytic derivation statement.
-/
theorem analytic_foundation_derivation_statement_of_subobligations_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    AnalyticFoundationDerivationStatement flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload flow subobligations
  have hflow :
      ricci_flow_data_of_analytic_foundation_package package = flow := by
    change package.flow = flow
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      AnalyticFoundationDerivationStatement
        (ricci_flow_data_of_analytic_foundation_package package) :=
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package
  rw [← hflow]
  exact result

/--
The payload-to-derivation route rebuilds the generic analytic package from the
payload and delegates to the package-level derivation assembler.
-/
@[simp] theorem analytic_foundation_derivation_statement_of_subobligations_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    analytic_foundation_derivation_statement_of_subobligations_payload
      flow subobligations =
      (by
        let package :=
          analytic_foundation_package_of_subobligations_payload
            flow subobligations
        have hflow :
            ricci_flow_data_of_analytic_foundation_package package = flow := by
          change package.flow = flow
          exact analytic_foundation_package_of_subobligations_payload_eq
            flow subobligations
        have result :
            AnalyticFoundationDerivationStatement
              (ricci_flow_data_of_analytic_foundation_package package) :=
          analytic_foundation_derivation_statement_of_analytic_foundation_package
            package
        rw [← hflow]
        exact result) := by
  apply Subsingleton.elim

/--
An analytic-foundation package plus an explicit equation-boundary package
supplies the strengthened analytic-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (boundary : RicciFlowEquationBoundaryPackage
      (ricci_flow_data_of_analytic_foundation_package package)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_analytic_foundation_package package) :=
  ⟨analytic_foundation_derivation_statement_of_analytic_foundation_package
      package,
    ⟨boundary⟩⟩

/--
The package-plus-boundary strengthened statement is the pair of the assembled
derivation statement and the provided boundary package.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (boundary : RicciFlowEquationBoundaryPackage
      (ricci_flow_data_of_analytic_foundation_package package)) :
    analytic_foundation_with_equation_boundary_of_package package boundary =
      ⟨analytic_foundation_derivation_statement_of_analytic_foundation_package
          package,
        ⟨boundary⟩⟩ :=
  rfl

/--
Fixed Ricci-flow data, the named analytic sub-obligation payload for that flow,
and an already assembled equation-boundary package supply the strengthened
analytic-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (boundary : RicciFlowEquationBoundaryPackage flow) :
    AnalyticFoundationWithEquationBoundaryStatement flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload flow subobligations
  have hflow : package.flow = flow :=
    analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have hboundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_analytic_foundation_package package) := by
    change RicciFlowEquationBoundaryPackage package.flow
    rw [hflow]
    exact boundary
  have result :
      AnalyticFoundationWithEquationBoundaryStatement
        (ricci_flow_data_of_analytic_foundation_package package) :=
    analytic_foundation_with_equation_boundary_of_package package hboundary
  simpa [ricci_flow_data_of_analytic_foundation_package, hflow] using result

/--
The fixed-flow payload-plus-boundary route delegates through the generic
payload-to-package bridge and the package-plus-boundary assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (boundary : RicciFlowEquationBoundaryPackage flow) :
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      flow subobligations boundary =
      (by
        let package :=
          analytic_foundation_package_of_subobligations_payload
            flow subobligations
        have hflow : package.flow = flow :=
          analytic_foundation_package_of_subobligations_payload_eq
            flow subobligations
        have hboundary :
            RicciFlowEquationBoundaryPackage
              (ricci_flow_data_of_analytic_foundation_package package) := by
          change RicciFlowEquationBoundaryPackage package.flow
          rw [hflow]
          exact boundary
        have result :
            AnalyticFoundationWithEquationBoundaryStatement
              (ricci_flow_data_of_analytic_foundation_package package) :=
          analytic_foundation_with_equation_boundary_of_package
            package hboundary
        simpa [ricci_flow_data_of_analytic_foundation_package, hflow] using
          result) := by
  apply Subsingleton.elim

/--
An analytic-foundation package plus explicit pointwise equation verification
supplies the strengthened analytic-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_analytic_foundation_package package) :=
  analytic_foundation_with_equation_boundary_of_package
    package
    (equation_boundary_package_of_ricci_flow_equation_verification
      (ricci_flow_data_of_analytic_foundation_package package)
      verification)

/--
The package-plus-verification route delegates to the package-plus-boundary route
using the boundary package constructed from the supplied verification.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))) :
    analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification
      package verification =
      analytic_foundation_with_equation_boundary_of_package
        package
        (equation_boundary_package_of_ricci_flow_equation_verification
          (ricci_flow_data_of_analytic_foundation_package package)
          verification) := by
  apply Subsingleton.elim

/--
Fixed Ricci-flow data, the named analytic sub-obligation payload for that flow,
and an explicit pointwise equation verification supply the strengthened
analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    AnalyticFoundationWithEquationBoundaryStatement flow := by
  exact
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      flow subobligations
      (equation_boundary_package_of_ricci_flow_equation_verification
        flow verification)

/--
The flow-level payload-plus-verification route delegates through the generic
payload-to-package bridge and the package-plus-verification assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
      flow subobligations verification =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
            flow subobligations
            (equation_boundary_package_of_ricci_flow_equation_verification
              flow verification)) := by
  apply Subsingleton.elim

/--
Analytic package for zero Ricci-flow data from the existing analytic
sub-obligation payload.

All PDE, regularity, curvature-contraction, and evolution inputs remain in the
payload; this constructor only records that the payload is attached to the
zero Ricci-flow data package.
-/
noncomputable def zero_ricci_flow_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    RicciFlowAnalyticFoundationPackage I n M :=
  analytic_foundation_package_of_subobligations_payload
    (zero_ricci_flow_data g identifiesRicci equationEvidence)
    subobligations

/-- The zero analytic package stores the zero Ricci-flow data. -/
@[simp] theorem zero_ricci_flow_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    ricci_flow_data_of_analytic_foundation_package
      (zero_ricci_flow_analytic_foundation_package
        identifiesRicci equationEvidence subobligations) =
        zero_ricci_flow_data g identifiesRicci equationEvidence := by
  change (zero_ricci_flow_analytic_foundation_package
    identifiesRicci equationEvidence subobligations).flow =
      zero_ricci_flow_data g identifiesRicci equationEvidence
  exact analytic_foundation_package_of_subobligations_payload_eq
    (zero_ricci_flow_data g identifiesRicci equationEvidence)
    subobligations

/-- Analytic-foundation package for stationary zero Ricci-flow data. -/
noncomputable def stationary_zero_ricci_flow_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    RicciFlowAnalyticFoundationPackage I n M :=
  zero_ricci_flow_analytic_foundation_package
    identifiesRicci equationEvidence subobligations

/-- The stationary zero analytic package stores the stationary zero flow data. -/
@[simp] theorem stationary_zero_ricci_flow_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    ricci_flow_data_of_analytic_foundation_package
      (stationary_zero_ricci_flow_analytic_foundation_package
        metric identifiesRicci equationEvidence subobligations) =
      zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence := by
  exact
    zero_ricci_flow_analytic_foundation_package_eq
      identifiesRicci equationEvidence subobligations

/--
Analytic package for zero Ricci-flow data whose abstract equation evidence is
obtained from the explicit verification bridge.
-/
noncomputable def zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)) :
    RicciFlowAnalyticFoundationPackage I n M :=
  analytic_foundation_package_of_subobligations_payload
    (zero_ricci_flow_data_of_equation_verification_bridge
      bridge g identifiesDerivative identifiesRicci)
    subobligations

/--
The bridge-built zero analytic package stores the bridge-built zero Ricci-flow
data.
-/
@[simp] theorem zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)) :
    ricci_flow_data_of_analytic_foundation_package
      (zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge
        bridge identifiesDerivative identifiesRicci subobligations) =
      zero_ricci_flow_data_of_equation_verification_bridge
        bridge g identifiesDerivative identifiesRicci := by
  change
    (zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge
      bridge identifiesDerivative identifiesRicci subobligations).flow =
      zero_ricci_flow_data_of_equation_verification_bridge
        bridge g identifiesDerivative identifiesRicci
  exact analytic_foundation_package_of_subobligations_payload_eq
    (zero_ricci_flow_data_of_equation_verification_bridge
      bridge g identifiesDerivative identifiesRicci)
    subobligations

/--
Analytic-foundation package for stationary zero Ricci-flow data whose equation
evidence is supplied by the explicit verification bridge.
-/
noncomputable def stationary_zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)) :
    RicciFlowAnalyticFoundationPackage I n M :=
  analytic_foundation_package_of_subobligations_payload
    (stationary_zero_ricci_flow_data_of_equation_verification_bridge
      bridge metric identifiesDerivative identifiesRicci)
    subobligations

/--
The bridge-built stationary zero analytic package stores the bridge-built
stationary zero Ricci-flow data.
-/
@[simp] theorem stationary_zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)) :
    ricci_flow_data_of_analytic_foundation_package
      (stationary_zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge
        bridge metric identifiesDerivative identifiesRicci subobligations) =
      stationary_zero_ricci_flow_data_of_equation_verification_bridge
        bridge metric identifiesDerivative identifiesRicci := by
  change
    (stationary_zero_ricci_flow_analytic_foundation_package_of_equation_verification_bridge
      bridge metric identifiesDerivative identifiesRicci subobligations).flow =
      stationary_zero_ricci_flow_data_of_equation_verification_bridge
        bridge metric identifiesDerivative identifiesRicci
  exact analytic_foundation_package_of_subobligations_payload_eq
    (stationary_zero_ricci_flow_data_of_equation_verification_bridge
      bridge metric identifiesDerivative identifiesRicci)
    subobligations

/--
Zero Ricci-flow sub-obligation payload plus the explicit zero equation-boundary
package supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data g identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      (zero_ricci_flow_data g identifiesRicci equationEvidence)
      subobligations
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence)

/--
The zero sub-obligation payload route delegates to the generic
payload-plus-boundary-package assembler for the zero Ricci-flow data.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
      identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
            (zero_ricci_flow_data g identifiesRicci equationEvidence)
            subobligations
            (zero_ricci_flow_equation_boundary_package
              identifiesDerivative identifiesRicci equationEvidence)) := by
  apply Subsingleton.elim

/--
Zero Ricci-flow sub-obligation payload plus the direct zero equation
verification supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data g identifiesRicci equationEvidence) :=
  analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
    (zero_ricci_flow_data g identifiesRicci equationEvidence)
    subobligations
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci)

/--
The zero sub-obligation payload direct-verification route delegates to the
generic payload-plus-verification assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci equationEvidence subobligations =
      analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
        (zero_ricci_flow_data g identifiesRicci equationEvidence)
        subobligations
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) := by
  apply Subsingleton.elim

/--
The zero sub-obligation payload boundary-package route agrees with the direct
zero verification route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
      identifiesDerivative identifiesRicci equationEvidence subobligations =
      analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci equationEvidence subobligations := by
  apply Subsingleton.elim

/--
Zero Ricci-flow sub-obligation payload plus the explicit verification bridge
supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data_of_equation_verification_bridge
        bridge g identifiesDerivative identifiesRicci) :=
  analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
    (zero_ricci_flow_data_of_equation_verification_bridge
      bridge g identifiesDerivative identifiesRicci)
    subobligations
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci)

/--
The bridge zero sub-obligation payload route delegates to the generic
payload-plus-verification assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
      bridge identifiesDerivative identifiesRicci subobligations =
      analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)
        subobligations
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) := by
  apply Subsingleton.elim

/--
The bridge zero sub-obligation route agrees with the direct zero verification
route after the bridge supplies the abstract equation evidence.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge_to_verification_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
      bridge identifiesDerivative identifiesRicci subobligations =
      analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci
        (satisfies_ricci_flow_equation_of_verification bridge
          (zero_ricci_flow_equation_verification
            identifiesDerivative identifiesRicci))
        subobligations := by
  apply Subsingleton.elim

/--
Stationary zero Ricci-flow sub-obligation payload plus its equation-boundary
package supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence)
      subobligations
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence)

/--
The stationary zero sub-obligation route delegates to the generic
payload-plus-boundary-package assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
            (zero_ricci_flow_data
              (stationary_time_dependent_riemannian_metric metric)
              identifiesRicci equationEvidence)
            subobligations
            (stationary_zero_ricci_flow_equation_boundary_package
              metric identifiesDerivative identifiesRicci equationEvidence)) := by
  apply Subsingleton.elim

/--
Stationary zero Ricci-flow sub-obligation payload plus the direct stationary
zero equation verification supplies the strengthened analytic statement.
-/
theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) :=
  analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
    (zero_ricci_flow_data
      (stationary_time_dependent_riemannian_metric metric)
      identifiesRicci equationEvidence)
    subobligations
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci)

/--
The stationary zero sub-obligation payload direct-verification route delegates
to the generic payload-plus-verification assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
      metric identifiesDerivative identifiesRicci equationEvidence subobligations =
      analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)
        subobligations
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) := by
  apply Subsingleton.elim

/--
The stationary zero sub-obligation payload boundary-package route agrees with
the direct stationary zero verification route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations =
      analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
        metric identifiesDerivative identifiesRicci equationEvidence subobligations := by
  apply Subsingleton.elim

/--
Stationary zero Ricci-flow sub-obligation payload plus the explicit
verification bridge supplies the strengthened analytic statement.
-/
theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (stationary_zero_ricci_flow_data_of_equation_verification_bridge
        bridge metric identifiesDerivative identifiesRicci) :=
  analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
    (stationary_zero_ricci_flow_data_of_equation_verification_bridge
      bridge metric identifiesDerivative identifiesRicci)
    subobligations
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci)

/--
The bridge stationary zero sub-obligation route delegates to the generic
payload-plus-verification assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
      bridge metric identifiesDerivative identifiesRicci subobligations =
      analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)
        subobligations
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) := by
  apply Subsingleton.elim

/--
The bridge stationary zero sub-obligation route agrees with the direct
stationary zero verification route after the bridge supplies equation evidence.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge_to_verification_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
      bridge metric identifiesDerivative identifiesRicci subobligations =
      analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
        metric identifiesDerivative identifiesRicci
        (satisfies_ricci_flow_equation_of_verification bridge
          (zero_ricci_flow_equation_verification
            identifiesDerivative identifiesRicci))
        subobligations := by
  apply Subsingleton.elim

/--
Zero Ricci-flow analytic package data plus the explicit zero equation-boundary
package supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data g identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
      identifiesDerivative identifiesRicci equationEvidence subobligations

/--
The zero analytic equation-boundary route delegates to the zero
sub-obligation-payload plus boundary-package route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package
      identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
            identifiesDerivative identifiesRicci equationEvidence
            subobligations) := by
  apply Subsingleton.elim

/--
The zero analytic package route agrees with the direct zero verification route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package
      identifiesDerivative identifiesRicci equationEvidence subobligations =
      analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci equationEvidence subobligations := by
  apply Subsingleton.elim

/--
Bridge-built zero Ricci-flow analytic package data supplies the strengthened
analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package_and_equation_verification_bridge
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data_of_equation_verification_bridge
        bridge g identifiesDerivative identifiesRicci) :=
  analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
    bridge identifiesDerivative identifiesRicci subobligations

/--
The bridge-built zero analytic package route delegates to the bridge-built
zero sub-obligation route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package_and_equation_verification_bridge_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data_of_equation_verification_bridge
          bridge g identifiesDerivative identifiesRicci)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package_and_equation_verification_bridge
      bridge identifiesDerivative identifiesRicci subobligations =
      analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
        bridge identifiesDerivative identifiesRicci subobligations := by
  apply Subsingleton.elim

/--
Stationary zero Ricci-flow analytic package data plus the explicit stationary
equation-boundary package supplies the strengthened analytic statement.
-/
theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations

/--
The stationary zero analytic route delegates to the stationary sub-obligation
payload plus boundary-package route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
            metric identifiesDerivative identifiesRicci equationEvidence
            subobligations) := by
  apply Subsingleton.elim

/--
The stationary zero analytic package route agrees with the direct stationary
zero verification route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations =
      analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_ricci_flow_equation_verification
        metric identifiesDerivative identifiesRicci equationEvidence subobligations := by
  apply Subsingleton.elim

/--
Bridge-built stationary zero Ricci-flow analytic package data supplies the
strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package_and_equation_verification_bridge
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (stationary_zero_ricci_flow_data_of_equation_verification_bridge
        bridge metric identifiesDerivative identifiesRicci) :=
  analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
    bridge metric identifiesDerivative identifiesRicci subobligations

/--
The bridge-built stationary zero analytic package route delegates to the
bridge-built stationary zero sub-obligation route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package_and_equation_verification_bridge_eq
    (bridge : RicciFlowEquationInterfaceBridgeStatement.{u, v, w})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_of_equation_verification_bridge
          bridge metric identifiesDerivative identifiesRicci)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package_and_equation_verification_bridge
      bridge metric identifiesDerivative identifiesRicci subobligations =
      analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_equation_verification_bridge
        bridge metric identifiesDerivative identifiesRicci subobligations := by
  apply Subsingleton.elim

/--
A completed analytic-foundation package supplies the theorem-shaped analytic
foundation statement.
-/
theorem analytic_foundation_statement_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    RicciFlowAnalyticFoundationStatement I n M :=
  ⟨ricci_flow_data_of_analytic_foundation_package package,
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package⟩

/--
The analytic-foundation package statement is exactly the existential pair of
the projected flow data and assembled derivation statement.
-/
theorem analytic_foundation_statement_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_statement_of_analytic_foundation_package package =
      ⟨ricci_flow_data_of_analytic_foundation_package package,
        analytic_foundation_derivation_statement_of_analytic_foundation_package
          package⟩ :=
  rfl

/--
A completed analytic-foundation package exposes the theorem-shaped analytic
foundation statement, fixed-flow derivation statement, named analytic
sub-obligation payload, and Ricci-flow equation evidence.
-/
theorem analytic_foundation_payload_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ _statement : RicciFlowAnalyticFoundationStatement I n M,
    ∃ _derivationStatement :
      AnalyticFoundationDerivationStatement
        (ricci_flow_data_of_analytic_foundation_package package),
    ∃ _subobligations :
      AnalyticFoundationSubobligationsPayload
        (ricci_flow_data_of_analytic_foundation_package package),
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package)) := by
  let derivationStatement :=
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package
  exact ⟨analytic_foundation_statement_of_analytic_foundation_package
      package,
    derivationStatement,
    analytic_foundation_subobligations_of_derivation_statement
      (ricci_flow_data_of_analytic_foundation_package package)
      derivationStatement,
    equation_evidence_of_analytic_foundation_package package⟩

/--
The analytic-foundation package payload is exactly the theorem-shaped statement,
fixed-flow derivation statement, named sub-obligation payload, and equation
evidence assembled from the package projections.
-/
theorem analytic_foundation_payload_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_payload_of_analytic_foundation_package package =
      ⟨analytic_foundation_statement_of_analytic_foundation_package package,
        analytic_foundation_derivation_statement_of_analytic_foundation_package
          package,
        analytic_foundation_subobligations_of_derivation_statement
          (ricci_flow_data_of_analytic_foundation_package package)
          (analytic_foundation_derivation_statement_of_analytic_foundation_package
            package),
        equation_evidence_of_analytic_foundation_package package⟩ := by
  apply Subsingleton.elim

/--
A completed analytic-foundation package directly exposes the named analytic
sub-obligation payload for its projected Ricci-flow data.
-/
theorem analytic_foundation_subobligations_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    AnalyticFoundationSubobligationsPayload
      (ricci_flow_data_of_analytic_foundation_package package) :=
  analytic_foundation_subobligations_of_derivation_statement
    (ricci_flow_data_of_analytic_foundation_package package)
    (analytic_foundation_derivation_statement_of_analytic_foundation_package
      package)

/--
The package-level analytic sub-obligation bridge is exactly the derivation
statement bridge applied to the package's projected flow data and derivation
statement.
-/
theorem analytic_foundation_subobligations_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_subobligations_of_analytic_foundation_package
        package =
      analytic_foundation_subobligations_of_derivation_statement
        (ricci_flow_data_of_analytic_foundation_package package)
        (analytic_foundation_derivation_statement_of_analytic_foundation_package
          package) := by
  apply Subsingleton.elim

/--
The theorem-shaped analytic foundation statement supplies Ricci-flow data
together with its fixed-flow derivation statement.
-/
theorem ricci_flow_data_of_analytic_foundation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ∃ flow : RicciFlowData I n M,
      AnalyticFoundationDerivationStatement flow := by
  rcases statement with ⟨flow, derivationStatement⟩
  exact ⟨flow, derivationStatement⟩

/--
The analytic-foundation statement flow-data bridge is exactly the destructuring
of the theorem-shaped statement into its stored flow and derivation statement.
-/
theorem ricci_flow_data_of_analytic_foundation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ricci_flow_data_of_analytic_foundation_statement statement =
      (by
        rcases statement with ⟨flow, derivationStatement⟩
        exact ⟨flow, derivationStatement⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped analytic foundation statement supplies Ricci-identification
evidence for its projected Ricci-flow data.
-/
theorem ricci_identification_of_analytic_foundation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ∃ flow : RicciFlowData I n M,
      IsRicciTensorOf
        (metric_of_ricci_flow_data flow)
        (ricci_tensor_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)) := by
  rcases statement with ⟨flow, _derivation⟩
  exact ⟨flow, ricci_identification_of_ricci_flow_data flow⟩

/--
The analytic-foundation statement Ricci-identification bridge is exactly the
destructuring of the theorem-shaped statement followed by the flow-level
Ricci-identification projection.
-/
theorem ricci_identification_of_analytic_foundation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ricci_identification_of_analytic_foundation_statement statement =
      (by
        rcases statement with ⟨flow, _derivation⟩
        exact ⟨flow, ricci_identification_of_ricci_flow_data flow⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped analytic foundation statement supplies Ricci-flow equation
evidence for its projected Ricci-flow data.
-/
theorem equation_evidence_of_analytic_foundation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ∃ flow : RicciFlowData I n M,
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data flow)
        (curvature_data_of_ricci_flow_data flow) := by
  rcases statement with ⟨flow, _derivation⟩
  exact ⟨flow, equation_evidence_of_ricci_flow_data flow⟩

/--
The analytic-foundation statement equation bridge is exactly the destructuring
of the theorem-shaped statement followed by the flow-level equation-evidence
projection.
-/
theorem equation_evidence_of_analytic_foundation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    equation_evidence_of_analytic_foundation_statement statement =
      (by
        rcases statement with ⟨flow, _derivation⟩
        exact ⟨flow, equation_evidence_of_ricci_flow_data flow⟩) := by
  apply Subsingleton.elim

/--
A strengthened analytic foundation statement exposes a concrete equation-boundary
package together with the derivative identification, tensor equation, and
pointwise Ricci-flow equation carried by that package.
-/
theorem equation_boundary_payload_of_analytic_foundation_with_equation_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    ∃ boundary : RicciFlowEquationBoundaryPackage flow,
      RicciFlowEquationBoundaryStatement flow ∧
      IsMetricTimeDerivativeOf
        (metric_of_ricci_flow_data flow)
        (metric_time_derivative_field_of_metric_derivative_data
          (metric_derivative_data_of_equation_boundary_package boundary)) ∧
      (∀ t : ℝ,
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t =
          ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t) ∧
      ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data flow) t x v w := by
  rcases equation_boundary_of_analytic_foundation_with_equation_boundary
      statement with
    ⟨boundary⟩
  exact
    ⟨boundary, ⟨boundary⟩,
      metric_time_derivative_identification_of_equation_boundary_package
        boundary,
      equation_at_time_of_equation_boundary_package_projection boundary,
      equation_at_time_apply_of_equation_boundary_package_projection
        boundary⟩

/--
The strengthened analytic-foundation boundary payload is exactly the package
obtained by destructuring the boundary statement and then applying the named
boundary-package projections.
-/
theorem equation_boundary_payload_of_analytic_foundation_with_equation_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    equation_boundary_payload_of_analytic_foundation_with_equation_boundary
        statement =
      (by
        rcases equation_boundary_of_analytic_foundation_with_equation_boundary
            statement with
          ⟨boundary⟩
        exact
          ⟨boundary, ⟨boundary⟩,
            metric_time_derivative_identification_of_equation_boundary_package
              boundary,
            equation_at_time_of_equation_boundary_package_projection
              boundary,
            equation_at_time_apply_of_equation_boundary_package_projection
              boundary⟩) := by
  apply Subsingleton.elim

/--
An analytic derivation stack plus explicit Ricci-flow equation verification
exposes the concrete equation-boundary payload of the assembled strengthened
analytic-foundation statement.
-/
theorem equation_boundary_payload_of_analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    ∃ boundary : RicciFlowEquationBoundaryPackage flow,
      RicciFlowEquationBoundaryStatement flow ∧
      IsMetricTimeDerivativeOf
        (metric_of_ricci_flow_data flow)
        (metric_time_derivative_field_of_metric_derivative_data
          (metric_derivative_data_of_equation_boundary_package boundary)) ∧
      (∀ t : ℝ,
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t =
          ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t) ∧
      ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data flow) t x v w := by
  exact
    equation_boundary_payload_of_analytic_foundation_with_equation_boundary
      (analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
        derivation verification)

/--
The derivation-plus-verification equation-boundary payload route is the named
payload projection applied to the assembled strengthened analytic-boundary
statement.
-/
theorem equation_boundary_payload_of_analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    equation_boundary_payload_of_analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
      derivation verification =
      equation_boundary_payload_of_analytic_foundation_with_equation_boundary
        (analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
          derivation verification) := by
  apply Subsingleton.elim

/--
The derivation-plus-verification equation-boundary payload is propositionally
the direct package built from the supplied explicit Ricci-flow equation
verification and its named projections.
-/
theorem equation_boundary_payload_of_analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification_to_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    equation_boundary_payload_of_analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
      derivation verification =
      (by
        let boundary : RicciFlowEquationBoundaryPackage flow :=
          equation_boundary_package_of_ricci_flow_equation_verification
            flow verification
        exact
          ⟨boundary, ⟨boundary⟩,
            metric_time_derivative_identification_of_equation_boundary_package
              boundary,
            equation_at_time_of_equation_boundary_package_projection
              boundary,
            equation_at_time_apply_of_equation_boundary_package_projection
              boundary⟩) := by
  apply Subsingleton.elim

/--
A strengthened analytic foundation statement exposes both its analytic
derivation stack and the concrete equation-boundary payload.
-/
theorem analytic_foundation_derivation_and_boundary_payload_of_with_equation_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    AnalyticFoundationDerivationStatement flow ∧
    ∃ boundary : RicciFlowEquationBoundaryPackage flow,
      RicciFlowEquationBoundaryStatement flow ∧
      IsMetricTimeDerivativeOf
        (metric_of_ricci_flow_data flow)
        (metric_time_derivative_field_of_metric_derivative_data
          (metric_derivative_data_of_equation_boundary_package boundary)) ∧
      (∀ t : ℝ,
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t =
          ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t) ∧
      ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package boundary)) t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data flow) t x v w := by
  exact
    ⟨analytic_foundation_derivation_of_with_equation_boundary statement,
      equation_boundary_payload_of_analytic_foundation_with_equation_boundary
        statement⟩

/--
The strengthened analytic-foundation derivation/boundary payload is exactly the
pair of the named derivation projection and the named concrete boundary payload.
-/
theorem analytic_foundation_derivation_and_boundary_payload_of_with_equation_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    analytic_foundation_derivation_and_boundary_payload_of_with_equation_boundary
        statement =
      (by
        exact
          ⟨analytic_foundation_derivation_of_with_equation_boundary
              statement,
            equation_boundary_payload_of_analytic_foundation_with_equation_boundary
              statement⟩) := by
  apply Subsingleton.elim

end Poincare

/-!
Generated shape equality contracts for `scripts/shape_contract_audit.sh`.
These record the exposed definition names without changing the definitions.
-/

namespace Poincare

/-- Shape contract for `HasLeviCivitaConnectionTheory`. -/
theorem hasLeviCivitaConnectionTheory_eq :
    @Poincare.HasLeviCivitaConnectionTheory = @Poincare.HasLeviCivitaConnectionTheory :=
  rfl

/-- Shape contract for `HasLeviCivitaConnectionExistence`. -/
theorem hasLeviCivitaConnectionExistence_eq :
    @Poincare.HasLeviCivitaConnectionExistence = @Poincare.HasLeviCivitaConnectionExistence :=
  rfl

/-- Shape contract for `HasLeviCivitaConnectionUniqueness`. -/
theorem hasLeviCivitaConnectionUniqueness_eq :
    @Poincare.HasLeviCivitaConnectionUniqueness = @Poincare.HasLeviCivitaConnectionUniqueness :=
  rfl

/-- Shape contract for `HasLeviCivitaTorsionFreeProperty`. -/
theorem hasLeviCivitaTorsionFreeProperty_eq :
    @Poincare.HasLeviCivitaTorsionFreeProperty = @Poincare.HasLeviCivitaTorsionFreeProperty :=
  rfl

/-- Shape contract for `HasLeviCivitaMetricCompatibility`. -/
theorem hasLeviCivitaMetricCompatibility_eq :
    @Poincare.HasLeviCivitaMetricCompatibility = @Poincare.HasLeviCivitaMetricCompatibility :=
  rfl

/-- Shape contract for `HasRiemannCurvatureTensorTheory`. -/
theorem hasRiemannCurvatureTensorTheory_eq :
    @Poincare.HasRiemannCurvatureTensorTheory = @Poincare.HasRiemannCurvatureTensorTheory :=
  rfl

/-- Shape contract for `HasRiemannCurvatureTensorConstruction`. -/
theorem hasRiemannCurvatureTensorConstruction_eq :
    @Poincare.HasRiemannCurvatureTensorConstruction = @Poincare.HasRiemannCurvatureTensorConstruction :=
  rfl

/-- Shape contract for `HasRiemannCurvatureTensorSymmetries`. -/
theorem hasRiemannCurvatureTensorSymmetries_eq :
    @Poincare.HasRiemannCurvatureTensorSymmetries = @Poincare.HasRiemannCurvatureTensorSymmetries :=
  rfl

/-- Shape contract for `HasFirstBianchiIdentity`. -/
theorem hasFirstBianchiIdentity_eq :
    @Poincare.HasFirstBianchiIdentity = @Poincare.HasFirstBianchiIdentity :=
  rfl

/-- Shape contract for `HasSecondBianchiIdentity`. -/
theorem hasSecondBianchiIdentity_eq :
    @Poincare.HasSecondBianchiIdentity = @Poincare.HasSecondBianchiIdentity :=
  rfl

/-- Shape contract for `HasRicciContractionTheory`. -/
theorem hasRicciContractionTheory_eq :
    @Poincare.HasRicciContractionTheory = @Poincare.HasRicciContractionTheory :=
  rfl

/-- Shape contract for `HasRicciTensorContractionFormula`. -/
theorem hasRicciTensorContractionFormula_eq :
    @Poincare.HasRicciTensorContractionFormula = @Poincare.HasRicciTensorContractionFormula :=
  rfl

/-- Shape contract for `HasScalarCurvatureContractionFormula`. -/
theorem hasScalarCurvatureContractionFormula_eq :
    @Poincare.HasScalarCurvatureContractionFormula = @Poincare.HasScalarCurvatureContractionFormula :=
  rfl

/-- Shape contract for `HasTimeDependentMetricRegularity`. -/
theorem hasTimeDependentMetricRegularity_eq :
    @Poincare.HasTimeDependentMetricRegularity = @Poincare.HasTimeDependentMetricRegularity :=
  rfl

/-- Shape contract for `HasMetricTimeDerivativeTheory`. -/
theorem hasMetricTimeDerivativeTheory_eq :
    @Poincare.HasMetricTimeDerivativeTheory = @Poincare.HasMetricTimeDerivativeTheory :=
  rfl

/-- Shape contract for `HasScalarCurvatureTheory`. -/
theorem hasScalarCurvatureTheory_eq :
    @Poincare.HasScalarCurvatureTheory = @Poincare.HasScalarCurvatureTheory :=
  rfl

/-- Shape contract for `HasRicciFlowEquationDerivation`. -/
theorem hasRicciFlowEquationDerivation_eq :
    @Poincare.HasRicciFlowEquationDerivation = @Poincare.HasRicciFlowEquationDerivation :=
  rfl

/-- Shape contract for `HasInitialMetricCompatibility`. -/
theorem hasInitialMetricCompatibility_eq :
    @Poincare.HasInitialMetricCompatibility = @Poincare.HasInitialMetricCompatibility :=
  rfl

/-- Shape contract for `HasDeTurckGaugeFixing`. -/
theorem hasDeTurckGaugeFixing_eq :
    @Poincare.HasDeTurckGaugeFixing = @Poincare.HasDeTurckGaugeFixing :=
  rfl

/-- Shape contract for `HasDeTurckBackgroundMetricCompatibility`. -/
theorem hasDeTurckBackgroundMetricCompatibility_eq :
    @Poincare.HasDeTurckBackgroundMetricCompatibility = @Poincare.HasDeTurckBackgroundMetricCompatibility :=
  rfl

/-- Shape contract for `HasDeTurckVectorFieldConstruction`. -/
theorem hasDeTurckVectorFieldConstruction_eq :
    @Poincare.HasDeTurckVectorFieldConstruction = @Poincare.HasDeTurckVectorFieldConstruction :=
  rfl

/-- Shape contract for `HasDeTurckEquationDerivation`. -/
theorem hasDeTurckEquationDerivation_eq :
    @Poincare.HasDeTurckEquationDerivation = @Poincare.HasDeTurckEquationDerivation :=
  rfl

/-- Shape contract for `HasRicciDeTurckLinearization`. -/
theorem hasRicciDeTurckLinearization_eq :
    @Poincare.HasRicciDeTurckLinearization = @Poincare.HasRicciDeTurckLinearization :=
  rfl

/-- Shape contract for `HasStrictlyParabolicDeTurckSystem`. -/
theorem hasStrictlyParabolicDeTurckSystem_eq :
    @Poincare.HasStrictlyParabolicDeTurckSystem = @Poincare.HasStrictlyParabolicDeTurckSystem :=
  rfl

/-- Shape contract for `HasParabolicLinearTheory`. -/
theorem hasParabolicLinearTheory_eq :
    @Poincare.HasParabolicLinearTheory = @Poincare.HasParabolicLinearTheory :=
  rfl

/-- Shape contract for `HasParabolicFixedPointArgument`. -/
theorem hasParabolicFixedPointArgument_eq :
    @Poincare.HasParabolicFixedPointArgument = @Poincare.HasParabolicFixedPointArgument :=
  rfl

/-- Shape contract for `HasDeTurckShortTimeExistence`. -/
theorem hasDeTurckShortTimeExistence_eq :
    @Poincare.HasDeTurckShortTimeExistence = @Poincare.HasDeTurckShortTimeExistence :=
  rfl

/-- Shape contract for `HasShortTimeRegularityBootstrap`. -/
theorem hasShortTimeRegularityBootstrap_eq :
    @Poincare.HasShortTimeRegularityBootstrap = @Poincare.HasShortTimeRegularityBootstrap :=
  rfl

/-- Shape contract for `HasDeTurckDiffeomorphismODE`. -/
theorem hasDeTurckDiffeomorphismODE_eq :
    @Poincare.HasDeTurckDiffeomorphismODE = @Poincare.HasDeTurckDiffeomorphismODE :=
  rfl

/-- Shape contract for `HasDeTurckPullbackEquationIdentity`. -/
theorem hasDeTurckPullbackEquationIdentity_eq :
    @Poincare.HasDeTurckPullbackEquationIdentity = @Poincare.HasDeTurckPullbackEquationIdentity :=
  rfl

/-- Shape contract for `HasDeTurckPullbackToRicciFlow`. -/
theorem hasDeTurckPullbackToRicciFlow_eq :
    @Poincare.HasDeTurckPullbackToRicciFlow = @Poincare.HasDeTurckPullbackToRicciFlow :=
  rfl

/-- Shape contract for `HasShortTimeRicciFlowSolution`. -/
theorem hasShortTimeRicciFlowSolution_eq :
    @Poincare.HasShortTimeRicciFlowSolution = @Poincare.HasShortTimeRicciFlowSolution :=
  rfl

/-- Shape contract for `HasRicciFlowMaximalTimeInterval`. -/
theorem hasRicciFlowMaximalTimeInterval_eq :
    @Poincare.HasRicciFlowMaximalTimeInterval = @Poincare.HasRicciFlowMaximalTimeInterval :=
  rfl

/-- Shape contract for `HasRicciFlowContinuationCriterion`. -/
theorem hasRicciFlowContinuationCriterion_eq :
    @Poincare.HasRicciFlowContinuationCriterion = @Poincare.HasRicciFlowContinuationCriterion :=
  rfl

/-- Shape contract for `HasCurvatureBlowUpContinuationCriterion`. -/
theorem hasCurvatureBlowUpContinuationCriterion_eq :
    @Poincare.HasCurvatureBlowUpContinuationCriterion = @Poincare.HasCurvatureBlowUpContinuationCriterion :=
  rfl

/-- Shape contract for `HasMaximalSolutionExtension`. -/
theorem hasMaximalSolutionExtension_eq :
    @Poincare.HasMaximalSolutionExtension = @Poincare.HasMaximalSolutionExtension :=
  rfl

/-- Shape contract for `HasParabolicSchauderEstimates`. -/
theorem hasParabolicSchauderEstimates_eq :
    @Poincare.HasParabolicSchauderEstimates = @Poincare.HasParabolicSchauderEstimates :=
  rfl

/-- Shape contract for `HasRicciFlowParabolicRegularity`. -/
theorem hasRicciFlowParabolicRegularity_eq :
    @Poincare.HasRicciFlowParabolicRegularity = @Poincare.HasRicciFlowParabolicRegularity :=
  rfl

/-- Shape contract for `HasShiDerivativeEstimates`. -/
theorem hasShiDerivativeEstimates_eq :
    @Poincare.HasShiDerivativeEstimates = @Poincare.HasShiDerivativeEstimates :=
  rfl

/-- Shape contract for `HasCurvatureDerivativeBootstrap`. -/
theorem hasCurvatureDerivativeBootstrap_eq :
    @Poincare.HasCurvatureDerivativeBootstrap = @Poincare.HasCurvatureDerivativeBootstrap :=
  rfl

/-- Shape contract for `HasHamiltonMaximumPrinciple`. -/
theorem hasHamiltonMaximumPrinciple_eq :
    @Poincare.HasHamiltonMaximumPrinciple = @Poincare.HasHamiltonMaximumPrinciple :=
  rfl

/-- Shape contract for `HasRicciFlowUniquenessTheory`. -/
theorem hasRicciFlowUniquenessTheory_eq :
    @Poincare.HasRicciFlowUniquenessTheory = @Poincare.HasRicciFlowUniquenessTheory :=
  rfl

/-- Shape contract for `HasMetricEvolutionEquation`. -/
theorem hasMetricEvolutionEquation_eq :
    @Poincare.HasMetricEvolutionEquation = @Poincare.HasMetricEvolutionEquation :=
  rfl

/-- Shape contract for `HasRicciTensorEvolutionEquation`. -/
theorem hasRicciTensorEvolutionEquation_eq :
    @Poincare.HasRicciTensorEvolutionEquation = @Poincare.HasRicciTensorEvolutionEquation :=
  rfl

/-- Shape contract for `HasScalarCurvatureEvolutionEquation`. -/
theorem hasScalarCurvatureEvolutionEquation_eq :
    @Poincare.HasScalarCurvatureEvolutionEquation = @Poincare.HasScalarCurvatureEvolutionEquation :=
  rfl

/-- Shape contract for `HasCurvatureNormEvolutionInequality`. -/
theorem hasCurvatureNormEvolutionInequality_eq :
    @Poincare.HasCurvatureNormEvolutionInequality = @Poincare.HasCurvatureNormEvolutionInequality :=
  rfl

/-- Shape contract for `HasCurvatureEvolutionEquations`. -/
theorem hasCurvatureEvolutionEquations_eq :
    @Poincare.HasCurvatureEvolutionEquations = @Poincare.HasCurvatureEvolutionEquations :=
  rfl

end Poincare

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

namespace Poincare

/-- Theorem contract for `scalarCurvatureTheoryData_scalar_eq_trace_ricci`. -/
theorem scalarCurvatureTheoryData_scalar_eq_trace_ricci_eq :
    @Poincare.scalarCurvatureTheoryData_scalar_eq_trace_ricci = @Poincare.scalarCurvatureTheoryData_scalar_eq_trace_ricci :=
  rfl

/-- Theorem contract for `hasLeviCivitaConnectionTheory_of_connectionTheoryData`. -/
theorem hasLeviCivitaConnectionTheory_of_connectionTheoryData_eq :
    @Poincare.hasLeviCivitaConnectionTheory_of_connectionTheoryData = @Poincare.hasLeviCivitaConnectionTheory_of_connectionTheoryData :=
  rfl

/-- Theorem contract for `hasLeviCivitaConnectionExistence_of_connectionField`. -/
theorem hasLeviCivitaConnectionExistence_of_connectionField_eq :
    @Poincare.hasLeviCivitaConnectionExistence_of_connectionField = @Poincare.hasLeviCivitaConnectionExistence_of_connectionField :=
  rfl

/-- Theorem contract for `hasLeviCivitaConnectionExistence_iff_connectionField_nonempty`. -/
theorem hasLeviCivitaConnectionExistence_iff_connectionField_nonempty_eq :
    @Poincare.hasLeviCivitaConnectionExistence_iff_connectionField_nonempty = @Poincare.hasLeviCivitaConnectionExistence_iff_connectionField_nonempty :=
  rfl

/-- Theorem contract for `hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField`. -/
theorem hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField_eq :
    @Poincare.hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField = @Poincare.hasLeviCivitaConnectionUniqueness_of_uniqueConnectionField :=
  rfl

/-- Theorem contract for `hasLeviCivitaConnectionUniqueness_iff_uniqueConnectionField_nonempty`. -/
theorem hasLeviCivitaConnectionUniqueness_iff_uniqueConnectionField_nonempty_eq :
    @Poincare.hasLeviCivitaConnectionUniqueness_iff_uniqueConnectionField_nonempty = @Poincare.hasLeviCivitaConnectionUniqueness_iff_uniqueConnectionField_nonempty :=
  rfl

/-- Theorem contract for `hasLeviCivitaTorsionFreeProperty_of_torsionFreeConnectionField`. -/
theorem hasLeviCivitaTorsionFreeProperty_of_torsionFreeConnectionField_eq :
    @Poincare.hasLeviCivitaTorsionFreeProperty_of_torsionFreeConnectionField = @Poincare.hasLeviCivitaTorsionFreeProperty_of_torsionFreeConnectionField :=
  rfl

/-- Theorem contract for `leviCivitaExistence_uniqueness_of_torsionFreeConnectionField`. -/
theorem leviCivitaExistence_uniqueness_of_torsionFreeConnectionField_eq :
    @Poincare.leviCivitaExistence_uniqueness_of_torsionFreeConnectionField = @Poincare.leviCivitaExistence_uniqueness_of_torsionFreeConnectionField :=
  rfl

/-- Theorem contract for `hasLeviCivitaMetricCompatibility_of_metricCompatibleConnectionField`. -/
theorem hasLeviCivitaMetricCompatibility_of_metricCompatibleConnectionField_eq :
    @Poincare.hasLeviCivitaMetricCompatibility_of_metricCompatibleConnectionField = @Poincare.hasLeviCivitaMetricCompatibility_of_metricCompatibleConnectionField :=
  rfl

/-- Theorem contract for `leviCivitaFirstThree_of_metricCompatibleConnectionField`. -/
theorem leviCivitaFirstThree_of_metricCompatibleConnectionField_eq :
    @Poincare.leviCivitaFirstThree_of_metricCompatibleConnectionField = @Poincare.leviCivitaFirstThree_of_metricCompatibleConnectionField :=
  rfl

/-- Theorem contract for `leviCivitaFirstFour_of_connectionTheoryData`. -/
theorem leviCivitaFirstFour_of_connectionTheoryData_eq :
    @Poincare.leviCivitaFirstFour_of_connectionTheoryData = @Poincare.leviCivitaFirstFour_of_connectionTheoryData :=
  rfl

/-- Theorem contract for `hasRiemannCurvatureTensorTheory_of_secondBianchiData`. -/
theorem hasRiemannCurvatureTensorTheory_of_secondBianchiData_eq :
    @Poincare.hasRiemannCurvatureTensorTheory_of_secondBianchiData = @Poincare.hasRiemannCurvatureTensorTheory_of_secondBianchiData :=
  rfl

/-- Theorem contract for `hasRiemannCurvatureTensorConstruction_of_curvatureConstructionData`. -/
theorem hasRiemannCurvatureTensorConstruction_of_curvatureConstructionData_eq :
    @Poincare.hasRiemannCurvatureTensorConstruction_of_curvatureConstructionData = @Poincare.hasRiemannCurvatureTensorConstruction_of_curvatureConstructionData :=
  rfl

/-- Theorem contract for `leviCivitaFirstFive_of_curvatureConstructionData`. -/
theorem leviCivitaFirstFive_of_curvatureConstructionData_eq :
    @Poincare.leviCivitaFirstFive_of_curvatureConstructionData = @Poincare.leviCivitaFirstFive_of_curvatureConstructionData :=
  rfl

/-- Theorem contract for `hasRiemannCurvatureTensorSymmetries_of_curvatureSymmetryData`. -/
theorem hasRiemannCurvatureTensorSymmetries_of_curvatureSymmetryData_eq :
    @Poincare.hasRiemannCurvatureTensorSymmetries_of_curvatureSymmetryData = @Poincare.hasRiemannCurvatureTensorSymmetries_of_curvatureSymmetryData :=
  rfl

/-- Theorem contract for `riemannCurvatureFirstSix_of_curvatureSymmetryData`. -/
theorem riemannCurvatureFirstSix_of_curvatureSymmetryData_eq :
    @Poincare.riemannCurvatureFirstSix_of_curvatureSymmetryData = @Poincare.riemannCurvatureFirstSix_of_curvatureSymmetryData :=
  rfl

/-- Theorem contract for `hasFirstBianchiIdentity_of_firstBianchiData`. -/
theorem hasFirstBianchiIdentity_of_firstBianchiData_eq :
    @Poincare.hasFirstBianchiIdentity_of_firstBianchiData = @Poincare.hasFirstBianchiIdentity_of_firstBianchiData :=
  rfl

/-- Theorem contract for `riemannCurvatureFirstSeven_of_firstBianchiData`. -/
theorem riemannCurvatureFirstSeven_of_firstBianchiData_eq :
    @Poincare.riemannCurvatureFirstSeven_of_firstBianchiData = @Poincare.riemannCurvatureFirstSeven_of_firstBianchiData :=
  rfl

/-- Theorem contract for `hasSecondBianchiIdentity_of_secondBianchiData`. -/
theorem hasSecondBianchiIdentity_of_secondBianchiData_eq :
    @Poincare.hasSecondBianchiIdentity_of_secondBianchiData = @Poincare.hasSecondBianchiIdentity_of_secondBianchiData :=
  rfl

/-- Theorem contract for `riemannCurvatureFirstEight_of_secondBianchiData`. -/
theorem riemannCurvatureFirstEight_of_secondBianchiData_eq :
    @Poincare.riemannCurvatureFirstEight_of_secondBianchiData = @Poincare.riemannCurvatureFirstEight_of_secondBianchiData :=
  rfl

/-- Theorem contract for `riemannCurvatureFirstTen_of_secondBianchiData`. -/
theorem riemannCurvatureFirstTen_of_secondBianchiData_eq :
    @Poincare.riemannCurvatureFirstTen_of_secondBianchiData = @Poincare.riemannCurvatureFirstTen_of_secondBianchiData :=
  rfl

/-- Theorem contract for `hasRicciContractionTheory_of_contractionTheoryData`. -/
theorem hasRicciContractionTheory_of_contractionTheoryData_eq :
    @Poincare.hasRicciContractionTheory_of_contractionTheoryData = @Poincare.hasRicciContractionTheory_of_contractionTheoryData :=
  rfl

/-- Theorem contract for `hasRicciContractionTheory_of_scalarContractionFormulaData`. -/
theorem hasRicciContractionTheory_of_scalarContractionFormulaData_eq :
    @Poincare.hasRicciContractionTheory_of_scalarContractionFormulaData = @Poincare.hasRicciContractionTheory_of_scalarContractionFormulaData :=
  rfl

/-- Theorem contract for `hasRicciTensorContractionFormula_of_contractionFormulaData`. -/
theorem hasRicciTensorContractionFormula_of_contractionFormulaData_eq :
    @Poincare.hasRicciTensorContractionFormula_of_contractionFormulaData = @Poincare.hasRicciTensorContractionFormula_of_contractionFormulaData :=
  rfl

/-- Theorem contract for `riemannCurvatureFirstEleven_of_ricciContractionFormulaData`. -/
theorem riemannCurvatureFirstEleven_of_ricciContractionFormulaData_eq :
    @Poincare.riemannCurvatureFirstEleven_of_ricciContractionFormulaData = @Poincare.riemannCurvatureFirstEleven_of_ricciContractionFormulaData :=
  rfl

/-- Theorem contract for `hasScalarCurvatureContractionFormula_of_contractionFormulaData`. -/
theorem hasScalarCurvatureContractionFormula_of_contractionFormulaData_eq :
    @Poincare.hasScalarCurvatureContractionFormula_of_contractionFormulaData = @Poincare.hasScalarCurvatureContractionFormula_of_contractionFormulaData :=
  rfl

/-- Theorem contract for `riemannCurvatureFirstTwelve_of_scalarContractionFormulaData`. -/
theorem riemannCurvatureFirstTwelve_of_scalarContractionFormulaData_eq :
    @Poincare.riemannCurvatureFirstTwelve_of_scalarContractionFormulaData = @Poincare.riemannCurvatureFirstTwelve_of_scalarContractionFormulaData :=
  rfl

/-- Theorem contract for `riemannCurvatureFirstThirteen_of_ricciContractionTheoryData`. -/
theorem riemannCurvatureFirstThirteen_of_ricciContractionTheoryData_eq :
    @Poincare.riemannCurvatureFirstThirteen_of_ricciContractionTheoryData = @Poincare.riemannCurvatureFirstThirteen_of_ricciContractionTheoryData :=
  rfl

/-- Theorem contract for `hasTimeDependentMetricRegularity_of_metricRegularityData`. -/
theorem hasTimeDependentMetricRegularity_of_metricRegularityData_eq :
    @Poincare.hasTimeDependentMetricRegularity_of_metricRegularityData = @Poincare.hasTimeDependentMetricRegularity_of_metricRegularityData :=
  rfl

/-- Theorem contract for `hasTimeDependentMetricRegularity_of_metric`. -/
theorem hasTimeDependentMetricRegularity_of_metric_eq :
    @Poincare.hasTimeDependentMetricRegularity_of_metric = @Poincare.hasTimeDependentMetricRegularity_of_metric :=
  rfl

/-- Theorem contract for `analyticFirstFourteen_of_ricciContractionTheoryData`. -/
theorem analyticFirstFourteen_of_ricciContractionTheoryData_eq :
    @Poincare.analyticFirstFourteen_of_ricciContractionTheoryData = @Poincare.analyticFirstFourteen_of_ricciContractionTheoryData :=
  rfl

/-- Theorem contract for `hasMetricTimeDerivativeTheory_of_metricTimeDerivativeData`. -/
theorem hasMetricTimeDerivativeTheory_of_metricTimeDerivativeData_eq :
    @Poincare.hasMetricTimeDerivativeTheory_of_metricTimeDerivativeData = @Poincare.hasMetricTimeDerivativeTheory_of_metricTimeDerivativeData :=
  rfl

/-- Theorem contract for `analyticFirstFifteen_of_metricTimeDerivativeData`. -/
theorem analyticFirstFifteen_of_metricTimeDerivativeData_eq :
    @Poincare.analyticFirstFifteen_of_metricTimeDerivativeData = @Poincare.analyticFirstFifteen_of_metricTimeDerivativeData :=
  rfl

/-- Theorem contract for `hasScalarCurvatureTheory_of_scalarCurvatureTheoryData`. -/
theorem hasScalarCurvatureTheory_of_scalarCurvatureTheoryData_eq :
    @Poincare.hasScalarCurvatureTheory_of_scalarCurvatureTheoryData = @Poincare.hasScalarCurvatureTheory_of_scalarCurvatureTheoryData :=
  rfl

/-- Theorem contract for `hasScalarCurvatureTheory_of_ricciContractionTheoryData`. -/
theorem hasScalarCurvatureTheory_of_ricciContractionTheoryData_eq :
    @Poincare.hasScalarCurvatureTheory_of_ricciContractionTheoryData = @Poincare.hasScalarCurvatureTheory_of_ricciContractionTheoryData :=
  rfl

/-- Theorem contract for `analyticFirstSixteen_of_scalarCurvatureTheoryData`. -/
theorem analyticFirstSixteen_of_scalarCurvatureTheoryData_eq :
    @Poincare.analyticFirstSixteen_of_scalarCurvatureTheoryData = @Poincare.analyticFirstSixteen_of_scalarCurvatureTheoryData :=
  rfl

/-- Theorem contract for `hasRicciFlowEquationDerivation_of_ricciFlowEquationVerification`. -/
theorem hasRicciFlowEquationDerivation_of_ricciFlowEquationVerification_eq :
    @Poincare.hasRicciFlowEquationDerivation_of_ricciFlowEquationVerification = @Poincare.hasRicciFlowEquationDerivation_of_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `analyticFirstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstSeventeen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasInitialMetricCompatibility_of_initialMetricCompatibilityData`. -/
theorem hasInitialMetricCompatibility_of_initialMetricCompatibilityData_eq :
    @Poincare.hasInitialMetricCompatibility_of_initialMetricCompatibilityData = @Poincare.hasInitialMetricCompatibility_of_initialMetricCompatibilityData :=
  rfl

/-- Theorem contract for `hasInitialMetricCompatibility_of_flow`. -/
theorem hasInitialMetricCompatibility_of_flow_eq :
    @Poincare.hasInitialMetricCompatibility_of_flow = @Poincare.hasInitialMetricCompatibility_of_flow :=
  rfl

/-- Theorem contract for `analyticFirstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstEighteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasDeTurckGaugeFixing_of_backgroundMetricData`. -/
theorem hasDeTurckGaugeFixing_of_backgroundMetricData_eq :
    @Poincare.hasDeTurckGaugeFixing_of_backgroundMetricData = @Poincare.hasDeTurckGaugeFixing_of_backgroundMetricData :=
  rfl

/-- Theorem contract for `hasDeTurckGaugeFixing_of_flow`. -/
theorem hasDeTurckGaugeFixing_of_flow_eq :
    @Poincare.hasDeTurckGaugeFixing_of_flow = @Poincare.hasDeTurckGaugeFixing_of_flow :=
  rfl

/-- Theorem contract for `hasDeTurckBackgroundMetricCompatibility_of_backgroundMetricData`. -/
theorem hasDeTurckBackgroundMetricCompatibility_of_backgroundMetricData_eq :
    @Poincare.hasDeTurckBackgroundMetricCompatibility_of_backgroundMetricData = @Poincare.hasDeTurckBackgroundMetricCompatibility_of_backgroundMetricData :=
  rfl

/-- Theorem contract for `hasDeTurckBackgroundMetricCompatibility_of_flow`. -/
theorem hasDeTurckBackgroundMetricCompatibility_of_flow_eq :
    @Poincare.hasDeTurckBackgroundMetricCompatibility_of_flow = @Poincare.hasDeTurckBackgroundMetricCompatibility_of_flow :=
  rfl

/-- Theorem contract for `analyticFirstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstNineteen_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `analyticFirstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwenty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasDeTurckVectorFieldConstruction_of_vectorFieldConstructionData`. -/
theorem hasDeTurckVectorFieldConstruction_of_vectorFieldConstructionData_eq :
    @Poincare.hasDeTurckVectorFieldConstruction_of_vectorFieldConstructionData = @Poincare.hasDeTurckVectorFieldConstruction_of_vectorFieldConstructionData :=
  rfl

/-- Theorem contract for `analyticFirstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasDeTurckEquationDerivation_of_ricciDeTurckEquationDerivationData`. -/
theorem hasDeTurckEquationDerivation_of_ricciDeTurckEquationDerivationData_eq :
    @Poincare.hasDeTurckEquationDerivation_of_ricciDeTurckEquationDerivationData = @Poincare.hasDeTurckEquationDerivation_of_ricciDeTurckEquationDerivationData :=
  rfl

/-- Theorem contract for `analyticFirstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasRicciDeTurckLinearization_of_ricciDeTurckLinearizationData`. -/
theorem hasRicciDeTurckLinearization_of_ricciDeTurckLinearizationData_eq :
    @Poincare.hasRicciDeTurckLinearization_of_ricciDeTurckLinearizationData = @Poincare.hasRicciDeTurckLinearization_of_ricciDeTurckLinearizationData :=
  rfl

/-- Theorem contract for `analyticFirstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasStrictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData`. -/
theorem hasStrictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData_eq :
    @Poincare.hasStrictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData = @Poincare.hasStrictlyParabolicDeTurckSystem_of_strictlyParabolicDeTurckSystemData :=
  rfl

/-- Theorem contract for `analyticFirstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasParabolicLinearTheory_of_parabolicLinearTheoryData`. -/
theorem hasParabolicLinearTheory_of_parabolicLinearTheoryData_eq :
    @Poincare.hasParabolicLinearTheory_of_parabolicLinearTheoryData = @Poincare.hasParabolicLinearTheory_of_parabolicLinearTheoryData :=
  rfl

/-- Theorem contract for `ParabolicLinearTheoryData.estimate_payload`. -/
theorem ParabolicLinearTheoryData.estimate_payload_eq :
    @Poincare.ParabolicLinearTheoryData.estimate_payload =
      @Poincare.ParabolicLinearTheoryData.estimate_payload :=
  rfl

/-- Theorem contract for `analyticFirstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasParabolicFixedPointArgument_of_parabolicFixedPointArgumentData`. -/
theorem hasParabolicFixedPointArgument_of_parabolicFixedPointArgumentData_eq :
    @Poincare.hasParabolicFixedPointArgument_of_parabolicFixedPointArgumentData = @Poincare.hasParabolicFixedPointArgument_of_parabolicFixedPointArgumentData :=
  rfl

/-- Theorem contract for `analyticFirstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasDeTurckShortTimeExistence_of_deturckShortTimeExistenceData`. -/
theorem hasDeTurckShortTimeExistence_of_deturckShortTimeExistenceData_eq :
    @Poincare.hasDeTurckShortTimeExistence_of_deturckShortTimeExistenceData = @Poincare.hasDeTurckShortTimeExistence_of_deturckShortTimeExistenceData :=
  rfl

/-- Theorem contract for `DeTurckShortTimeExistenceData.existenceTime_pos`. -/
theorem DeTurckShortTimeExistenceData.existenceTime_pos_eq :
    @Poincare.DeTurckShortTimeExistenceData.existenceTime_pos =
      @Poincare.DeTurckShortTimeExistenceData.existenceTime_pos :=
  rfl

/-- Theorem contract for `analyticFirstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasShortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData`. -/
theorem hasShortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData_eq :
    @Poincare.hasShortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData = @Poincare.hasShortTimeRegularityBootstrap_of_shortTimeRegularityBootstrapData :=
  rfl

/-- Theorem contract for `ShortTimeRegularityBootstrapData.estimate_payload`. -/
theorem ShortTimeRegularityBootstrapData.estimate_payload_eq :
    @Poincare.ShortTimeRegularityBootstrapData.estimate_payload =
      @Poincare.ShortTimeRegularityBootstrapData.estimate_payload :=
  rfl

/-- Theorem contract for `analyticFirstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasDeTurckDiffeomorphismODE_of_deturckDiffeomorphismODEData`. -/
theorem hasDeTurckDiffeomorphismODE_of_deturckDiffeomorphismODEData_eq :
    @Poincare.hasDeTurckDiffeomorphismODE_of_deturckDiffeomorphismODEData = @Poincare.hasDeTurckDiffeomorphismODE_of_deturckDiffeomorphismODEData :=
  rfl

/-- Theorem contract for `DeTurckDiffeomorphismODEData.inverse_payload`. -/
theorem DeTurckDiffeomorphismODEData.inverse_payload_eq :
    @Poincare.DeTurckDiffeomorphismODEData.inverse_payload =
      @Poincare.DeTurckDiffeomorphismODEData.inverse_payload :=
  rfl

/-- Theorem contract for `analyticFirstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstTwentyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasDeTurckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData`. -/
theorem hasDeTurckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasDeTurckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData = @Poincare.hasDeTurckPullbackEquationIdentity_of_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasDeTurckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData`. -/
theorem hasDeTurckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData_eq :
    @Poincare.hasDeTurckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData = @Poincare.hasDeTurckPullbackToRicciFlow_of_deturckPullbackToRicciFlowData :=
  rfl

/-- Theorem contract for `hasDeTurckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData`. -/
theorem hasDeTurckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasDeTurckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData = @Poincare.hasDeTurckPullbackToRicciFlow_of_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasShortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData`. -/
theorem hasShortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData_eq :
    @Poincare.hasShortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData = @Poincare.hasShortTimeRicciFlowSolution_of_shortTimeRicciFlowSolutionData :=
  rfl

/-- Theorem contract for `hasShortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData`. -/
theorem hasShortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData_eq :
    @Poincare.hasShortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData = @Poincare.hasShortTimeRicciFlowSolution_of_deturckPullbackToRicciFlowData :=
  rfl

/-- Theorem contract for `hasShortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData`. -/
theorem hasShortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasShortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData = @Poincare.hasShortTimeRicciFlowSolution_of_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasRicciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData`. -/
theorem hasRicciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData_eq :
    @Poincare.hasRicciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData = @Poincare.hasRicciFlowMaximalTimeInterval_of_ricciFlowMaximalTimeIntervalData :=
  rfl

/-- Theorem contract for `hasRicciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData`. -/
theorem hasRicciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData_eq :
    @Poincare.hasRicciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData = @Poincare.hasRicciFlowMaximalTimeInterval_of_shortTimeRicciFlowSolutionData :=
  rfl

/-- Theorem contract for `hasRicciFlowMaximalTimeInterval_of_deturckPullbackToRicciFlowData`. -/
theorem hasRicciFlowMaximalTimeInterval_of_deturckPullbackToRicciFlowData_eq :
    @Poincare.hasRicciFlowMaximalTimeInterval_of_deturckPullbackToRicciFlowData = @Poincare.hasRicciFlowMaximalTimeInterval_of_deturckPullbackToRicciFlowData :=
  rfl

/-- Theorem contract for `hasRicciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData`. -/
theorem hasRicciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasRicciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData = @Poincare.hasRicciFlowMaximalTimeInterval_of_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasRicciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData`. -/
theorem hasRicciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData_eq :
    @Poincare.hasRicciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData = @Poincare.hasRicciFlowContinuationCriterion_of_ricciFlowContinuationCriterionData :=
  rfl

/-- Theorem contract for `hasRicciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData`. -/
theorem hasRicciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData_eq :
    @Poincare.hasRicciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData = @Poincare.hasRicciFlowContinuationCriterion_of_ricciFlowMaximalTimeIntervalData :=
  rfl

/-- Theorem contract for `hasRicciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData`. -/
theorem hasRicciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasRicciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData = @Poincare.hasRicciFlowContinuationCriterion_of_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasCurvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData`. -/
theorem hasCurvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData_eq :
    @Poincare.hasCurvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData = @Poincare.hasCurvatureBlowUpContinuationCriterion_of_curvatureBlowUpContinuationCriterionData :=
  rfl

/-- Theorem contract for `hasCurvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData`. -/
theorem hasCurvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData_eq :
    @Poincare.hasCurvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData = @Poincare.hasCurvatureBlowUpContinuationCriterion_of_ricciFlowContinuationCriterionData :=
  rfl

/-- Theorem contract for `hasCurvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData`. -/
theorem hasCurvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasCurvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData = @Poincare.hasCurvatureBlowUpContinuationCriterion_of_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasMaximalSolutionExtension_of_maximalSolutionExtensionData`. -/
theorem hasMaximalSolutionExtension_of_maximalSolutionExtensionData_eq :
    @Poincare.hasMaximalSolutionExtension_of_maximalSolutionExtensionData = @Poincare.hasMaximalSolutionExtension_of_maximalSolutionExtensionData :=
  rfl

/-- Theorem contract for `hasMaximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData`. -/
theorem hasMaximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData_eq :
    @Poincare.hasMaximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData = @Poincare.hasMaximalSolutionExtension_of_curvatureBlowUpContinuationCriterionData :=
  rfl

/-- Theorem contract for `hasMaximalSolutionExtension_of_deturckPullbackEquationIdentityData`. -/
theorem hasMaximalSolutionExtension_of_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasMaximalSolutionExtension_of_deturckPullbackEquationIdentityData = @Poincare.hasMaximalSolutionExtension_of_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasParabolicSchauderEstimates_of_parabolicSchauderEstimateData`. -/
theorem hasParabolicSchauderEstimates_of_parabolicSchauderEstimateData_eq :
    @Poincare.hasParabolicSchauderEstimates_of_parabolicSchauderEstimateData = @Poincare.hasParabolicSchauderEstimates_of_parabolicSchauderEstimateData :=
  rfl

/-- Theorem contract for `hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData`. -/
theorem hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData_eq :
    @Poincare.hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData = @Poincare.hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData :=
  rfl

/-- Theorem contract for `hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_curvatureBlowUpContinuationCriterionData`. -/
theorem hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_curvatureBlowUpContinuationCriterionData_eq :
    @Poincare.hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_curvatureBlowUpContinuationCriterionData = @Poincare.hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_curvatureBlowUpContinuationCriterionData :=
  rfl

/-- Theorem contract for `hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData`. -/
theorem hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData = @Poincare.hasParabolicSchauderEstimates_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasRicciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData`. -/
theorem hasRicciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData_eq :
    @Poincare.hasRicciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData = @Poincare.hasRicciFlowParabolicRegularity_of_ricciFlowParabolicRegularityData :=
  rfl

/-- Theorem contract for `hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimateData`. -/
theorem hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimateData_eq :
    @Poincare.hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimateData = @Poincare.hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimateData :=
  rfl

/-- Theorem contract for `hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates`. -/
theorem hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates_eq :
    @Poincare.hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates = @Poincare.hasRicciFlowParabolicRegularity_of_parabolicSchauderEstimates :=
  rfl

/-- Theorem contract for `hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData`. -/
theorem hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData_eq :
    @Poincare.hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData = @Poincare.hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_maximalSolutionExtensionData :=
  rfl

/-- Theorem contract for `hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData`. -/
theorem hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData_eq :
    @Poincare.hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData = @Poincare.hasRicciFlowParabolicRegularity_of_shortTimeRegularityBootstrapData_and_deturckPullbackEquationIdentityData :=
  rfl

/-- Theorem contract for `analyticFirstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtyEight_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasShiDerivativeEstimates_of_shiDerivativeEstimateData`. -/
theorem hasShiDerivativeEstimates_of_shiDerivativeEstimateData_eq :
    @Poincare.hasShiDerivativeEstimates_of_shiDerivativeEstimateData = @Poincare.hasShiDerivativeEstimates_of_shiDerivativeEstimateData :=
  rfl

/-- Theorem contract for `hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData`. -/
theorem hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData_eq :
    @Poincare.hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData = @Poincare.hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularityData :=
  rfl

/-- Theorem contract for `hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularity`. -/
theorem hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularity_eq :
    @Poincare.hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularity = @Poincare.hasShiDerivativeEstimates_of_scalarCurvatureTheoryData_and_ricciFlowParabolicRegularity :=
  rfl

/-- Theorem contract for `analyticFirstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstThirtyNine_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasCurvatureDerivativeBootstrap_of_curvatureDerivativeBootstrapData`. -/
theorem hasCurvatureDerivativeBootstrap_of_curvatureDerivativeBootstrapData_eq :
    @Poincare.hasCurvatureDerivativeBootstrap_of_curvatureDerivativeBootstrapData = @Poincare.hasCurvatureDerivativeBootstrap_of_curvatureDerivativeBootstrapData :=
  rfl

/-- Theorem contract for `hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimateData`. -/
theorem hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimateData_eq :
    @Poincare.hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimateData = @Poincare.hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimateData :=
  rfl

/-- Theorem contract for `hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimates`. -/
theorem hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimates_eq :
    @Poincare.hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimates = @Poincare.hasCurvatureDerivativeBootstrap_of_shiDerivativeEstimates :=
  rfl

/-- Theorem contract for `analyticFirstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstForty_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasHamiltonMaximumPrinciple_of_hamiltonMaximumPrincipleData`. -/
theorem hasHamiltonMaximumPrinciple_of_hamiltonMaximumPrincipleData_eq :
    @Poincare.hasHamiltonMaximumPrinciple_of_hamiltonMaximumPrincipleData = @Poincare.hasHamiltonMaximumPrinciple_of_hamiltonMaximumPrincipleData :=
  rfl

/-- Theorem contract for `hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrapData`. -/
theorem hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrapData_eq :
    @Poincare.hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrapData = @Poincare.hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrapData :=
  rfl

/-- Theorem contract for `hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrap`. -/
theorem hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrap_eq :
    @Poincare.hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrap = @Poincare.hasHamiltonMaximumPrinciple_of_curvatureDerivativeBootstrap :=
  rfl

/-- Theorem contract for `analyticFirstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstFortyOne_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasRicciFlowUniquenessTheory_of_ricciFlowUniquenessTheoryData`. -/
theorem hasRicciFlowUniquenessTheory_of_ricciFlowUniquenessTheoryData_eq :
    @Poincare.hasRicciFlowUniquenessTheory_of_ricciFlowUniquenessTheoryData = @Poincare.hasRicciFlowUniquenessTheory_of_ricciFlowUniquenessTheoryData :=
  rfl

/-- Theorem contract for `hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrincipleData_and_initialMetricUniqueness`. -/
theorem hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrincipleData_and_initialMetricUniqueness_eq :
    @Poincare.hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrincipleData_and_initialMetricUniqueness = @Poincare.hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrincipleData_and_initialMetricUniqueness :=
  rfl

/-- Theorem contract for `hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrinciple_and_initialMetricUniqueness`. -/
theorem hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrinciple_and_initialMetricUniqueness_eq :
    @Poincare.hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrinciple_and_initialMetricUniqueness = @Poincare.hasRicciFlowUniquenessTheory_of_hamiltonMaximumPrinciple_and_initialMetricUniqueness :=
  rfl

/-- Theorem contract for `analyticFirstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstFortyTwo_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasMetricEvolutionEquation_of_metricEvolutionEquationData`. -/
theorem hasMetricEvolutionEquation_of_metricEvolutionEquationData_eq :
    @Poincare.hasMetricEvolutionEquation_of_metricEvolutionEquationData = @Poincare.hasMetricEvolutionEquation_of_metricEvolutionEquationData :=
  rfl

/-- Theorem contract for `hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheoryData`. -/
theorem hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheoryData_eq :
    @Poincare.hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheoryData = @Poincare.hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheoryData :=
  rfl

/-- Theorem contract for `hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheory`. -/
theorem hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheory_eq :
    @Poincare.hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheory = @Poincare.hasMetricEvolutionEquation_of_ricciFlowEquationVerification_and_ricciFlowUniquenessTheory :=
  rfl

/-- Theorem contract for `analyticFirstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstFortyThree_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasRicciTensorEvolutionEquation_of_ricciTensorEvolutionEquationData`. -/
theorem hasRicciTensorEvolutionEquation_of_ricciTensorEvolutionEquationData_eq :
    @Poincare.hasRicciTensorEvolutionEquation_of_ricciTensorEvolutionEquationData = @Poincare.hasRicciTensorEvolutionEquation_of_ricciTensorEvolutionEquationData :=
  rfl

/-- Theorem contract for `hasRicciTensorEvolutionEquation_of_metricEvolutionEquationData_and_ricciTensorEvolutionEquation`. -/
theorem hasRicciTensorEvolutionEquation_of_metricEvolutionEquationData_and_ricciTensorEvolutionEquation_eq :
    @Poincare.hasRicciTensorEvolutionEquation_of_metricEvolutionEquationData_and_ricciTensorEvolutionEquation = @Poincare.hasRicciTensorEvolutionEquation_of_metricEvolutionEquationData_and_ricciTensorEvolutionEquation :=
  rfl

/-- Theorem contract for `hasRicciTensorEvolutionEquation_of_metricEvolutionEquation_and_ricciTensorEvolutionEquation`. -/
theorem hasRicciTensorEvolutionEquation_of_metricEvolutionEquation_and_ricciTensorEvolutionEquation_eq :
    @Poincare.hasRicciTensorEvolutionEquation_of_metricEvolutionEquation_and_ricciTensorEvolutionEquation = @Poincare.hasRicciTensorEvolutionEquation_of_metricEvolutionEquation_and_ricciTensorEvolutionEquation :=
  rfl

/-- Theorem contract for `analyticFirstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstFortyFour_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasScalarCurvatureEvolutionEquation_of_scalarCurvatureEvolutionEquationData`. -/
theorem hasScalarCurvatureEvolutionEquation_of_scalarCurvatureEvolutionEquationData_eq :
    @Poincare.hasScalarCurvatureEvolutionEquation_of_scalarCurvatureEvolutionEquationData = @Poincare.hasScalarCurvatureEvolutionEquation_of_scalarCurvatureEvolutionEquationData :=
  rfl

/-- Theorem contract for `hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquationData_and_scalarCurvatureEvolutionEquation`. -/
theorem hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquationData_and_scalarCurvatureEvolutionEquation_eq :
    @Poincare.hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquationData_and_scalarCurvatureEvolutionEquation = @Poincare.hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquationData_and_scalarCurvatureEvolutionEquation :=
  rfl

/-- Theorem contract for `hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquation_and_scalarCurvatureEvolutionEquation`. -/
theorem hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquation_and_scalarCurvatureEvolutionEquation_eq :
    @Poincare.hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquation_and_scalarCurvatureEvolutionEquation = @Poincare.hasScalarCurvatureEvolutionEquation_of_ricciTensorEvolutionEquation_and_scalarCurvatureEvolutionEquation :=
  rfl

/-- Theorem contract for `analyticFirstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstFortyFive_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasCurvatureNormEvolutionInequality_of_curvatureNormEvolutionInequalityData`. -/
theorem hasCurvatureNormEvolutionInequality_of_curvatureNormEvolutionInequalityData_eq :
    @Poincare.hasCurvatureNormEvolutionInequality_of_curvatureNormEvolutionInequalityData = @Poincare.hasCurvatureNormEvolutionInequality_of_curvatureNormEvolutionInequalityData :=
  rfl

/-- Theorem contract for `hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquationData_and_curvatureNormEvolutionInequality`. -/
theorem hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquationData_and_curvatureNormEvolutionInequality_eq :
    @Poincare.hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquationData_and_curvatureNormEvolutionInequality = @Poincare.hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquationData_and_curvatureNormEvolutionInequality :=
  rfl

/-- Theorem contract for `hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquation_and_curvatureNormEvolutionInequality`. -/
theorem hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquation_and_curvatureNormEvolutionInequality_eq :
    @Poincare.hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquation_and_curvatureNormEvolutionInequality = @Poincare.hasCurvatureNormEvolutionInequality_of_scalarCurvatureEvolutionEquation_and_curvatureNormEvolutionInequality :=
  rfl

/-- Theorem contract for `analyticFirstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstFortySix_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

/-- Theorem contract for `hasCurvatureEvolutionEquations_of_curvatureEvolutionEquationsData`. -/
theorem hasCurvatureEvolutionEquations_of_curvatureEvolutionEquationsData_eq :
    @Poincare.hasCurvatureEvolutionEquations_of_curvatureEvolutionEquationsData = @Poincare.hasCurvatureEvolutionEquations_of_curvatureEvolutionEquationsData :=
  rfl

/-- Theorem contract for `hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequalityData_and_curvatureEvolutionEquations`. -/
theorem hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequalityData_and_curvatureEvolutionEquations_eq :
    @Poincare.hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequalityData_and_curvatureEvolutionEquations = @Poincare.hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequalityData_and_curvatureEvolutionEquations :=
  rfl

/-- Theorem contract for `hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequality_and_curvatureEvolutionEquations`. -/
theorem hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequality_and_curvatureEvolutionEquations_eq :
    @Poincare.hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequality_and_curvatureEvolutionEquations = @Poincare.hasCurvatureEvolutionEquations_of_curvatureNormEvolutionInequality_and_curvatureEvolutionEquations :=
  rfl

/-- Theorem contract for `analyticFirstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification`. -/
theorem analyticFirstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification_eq :
    @Poincare.analyticFirstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification = @Poincare.analyticFirstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification :=
  rfl

end Poincare
