import Poincare.Global.NormalizedFlowHausdorffAutomaticStokes
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Hausdorff Stokes from a finite subordinate coordinate partition

The per-piece flux package in `NormalizedFlowHausdorffAutomaticStokes` is a
useful strong special case, but it is stronger than the usual coordinate
proof of Stokes: the integral of a Laplacian need not vanish on each member
of a disjoint measurable partition.

This file gives the standard global-sum argument.  A finite smooth partition
of unity is subordinate to open Hausdorff charts.  For each partitioned
scalar `rho_i * f`, its zero-extended coordinate representative has compact
support in the coordinate domain.  The coordinate flux

`weight * g^{-1} * d(rho_i * f)`

is therefore compactly supported.  A product-rule calculation, the
contracted Christoffel identity, and the intrinsic coordinate formula prove
that its Euclidean divergence is the weighted pulled-back Laplacian.  After
integrating in each chart, finite additivity of the intrinsic Laplacian and
`sum rho_i = 1` give the global closed-manifold Stokes statement.

The geometric interface below contains the coordinate metric coefficients,
Christoffel contraction, smooth partition, measure equality, and zero
extensions.  It contains neither an integral cancellation field nor a
`ClosedLaplacianStokes` field.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section CoordinateMetricFlux

variable {n : ℕ}

local notation "E" => ClosedSmoothModel n

/-- The `j`-th Euclidean directional derivative in the standard coordinate
basis. -/
noncomputable def coordinateDirectionalDerivative
    (u : E → ℝ) (j : Fin n) (z : E) : ℝ :=
  fderiv ℝ u z (EuclideanSpace.single j (1 : ℝ))

/-- The iterated `(i,j)` coordinate derivative. -/
noncomputable def coordinateSecondDerivative
    (u : E → ℝ) (i j : Fin n) (z : E) : ℝ :=
  fderiv ℝ (coordinateDirectionalDerivative u j) z
    (EuclideanSpace.single i (1 : ℝ))

/-- Coordinate Laplacian written using inverse metric coefficients and the
contracted Christoffel drift. -/
noncomputable def contractedCoordinateLaplacian
    (inverseMetric : E → Fin n → Fin n → ℝ)
    (contractedChristoffel : E → Fin n → ℝ)
    (u : E → ℝ) (z : E) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n,
      inverseMetric z i j * coordinateSecondDerivative u i j z) +
    ∑ j : Fin n,
      contractedChristoffel z j * coordinateDirectionalDerivative u j z

/-- The conventional Christoffel-coordinate expression
`g^{ij} (partial_i partial_j u - Gamma^k_ij partial_k u)`. -/
noncomputable def christoffelCoordinateLaplacian
    (inverseMetric : E → Fin n → Fin n → ℝ)
    (christoffel : E → Fin n → Fin n → Fin n → ℝ)
    (u : E → ℝ) (z : E) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    inverseMetric z i j *
      (coordinateSecondDerivative u i j z -
        ∑ k : Fin n,
          christoffel z k i j * coordinateDirectionalDerivative u k z)

/-- The metric flux with density weight `w`: its `i`-th component is
`sum_j w g^{ij} partial_j u`. -/
noncomputable def coordinateMetricFluxComponent
    (weight : E → ℝ)
    (inverseMetric : E → Fin n → Fin n → ℝ)
    (u : E → ℝ) (i : Fin n) (z : E) : ℝ :=
  ∑ j : Fin n,
    (weight z * inverseMetric z i j) *
      coordinateDirectionalDerivative u j z

/-- A `C²` function has `C¹` coordinate first derivatives. -/
theorem coordinateDirectionalDerivative_contDiff_one
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (j : Fin n) :
    ContDiff ℝ 1 (coordinateDirectionalDerivative u j) := by
  unfold coordinateDirectionalDerivative
  exact (hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

/-- The coordinate metric flux is `C¹` when the weight and inverse metric
coefficients are `C¹` and the scalar is `C²`. -/
theorem coordinateMetricFluxComponent_contDiff_one
    {weight : E → ℝ}
    {inverseMetric : E → Fin n → Fin n → ℝ}
    {u : E → ℝ}
    (hweight : ContDiff ℝ 1 weight)
    (hinverse : ∀ i j, ContDiff ℝ 1 (fun z ↦ inverseMetric z i j))
    (hu : ContDiff ℝ 2 u) (i : Fin n) :
    ContDiff ℝ 1 (coordinateMetricFluxComponent weight inverseMetric u i) := by
  unfold coordinateMetricFluxComponent
  apply ContDiff.sum
  intro j _hj
  exact (hweight.mul (hinverse i j)).mul
    (coordinateDirectionalDerivative_contDiff_one hu j)

/-- Every coordinate metric-flux component is supported in the topological
support of the scalar representative. -/
theorem tsupport_coordinateMetricFluxComponent_subset
    (weight : E → ℝ)
    (inverseMetric : E → Fin n → Fin n → ℝ)
    (u : E → ℝ) (i : Fin n) :
    tsupport (coordinateMetricFluxComponent weight inverseMetric u i) ⊆
      tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hzu
  apply hz
  unfold coordinateMetricFluxComponent coordinateDirectionalDerivative
  rw [fderiv_of_notMem_tsupport ℝ hzu]
  simp

/-- Compact support of the scalar representative gives compact support of
each coordinate metric-flux component. -/
theorem coordinateMetricFluxComponent_hasCompactSupport
    {weight : E → ℝ}
    {inverseMetric : E → Fin n → Fin n → ℝ}
    {u : E → ℝ} (hu : HasCompactSupport u) (i : Fin n) :
    HasCompactSupport (coordinateMetricFluxComponent weight inverseMetric u i) :=
  hu.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_coordinateMetricFluxComponent_subset weight inverseMetric u i)

/-- Pointwise product-rule expansion for one directional derivative of a
coordinate metric-flux component. -/
theorem fderiv_coordinateMetricFluxComponent_apply
    {weight : E → ℝ}
    {inverseMetric : E → Fin n → Fin n → ℝ}
    {u : E → ℝ} {z : E}
    (hweight : DifferentiableAt ℝ weight z)
    (hinverse : ∀ i j,
      DifferentiableAt ℝ (fun y ↦ inverseMetric y i j) z)
    (hdu : ∀ j, DifferentiableAt ℝ (coordinateDirectionalDerivative u j) z)
    (i : Fin n) :
    fderiv ℝ (coordinateMetricFluxComponent weight inverseMetric u i) z
        (EuclideanSpace.single i (1 : ℝ)) =
      ∑ j : Fin n,
        ((weight z * inverseMetric z i j) *
            coordinateSecondDerivative u i j z +
          coordinateDirectionalDerivative u j z *
            fderiv ℝ (fun y ↦ weight y * inverseMetric y i j) z
              (EuclideanSpace.single i (1 : ℝ))) := by
  unfold coordinateMetricFluxComponent
  rw [fderiv_fun_sum]
  rw [ContinuousLinearMap.sum_apply]
  · apply Finset.sum_congr rfl
    intro j _hj
    have hcoefficient :
        DifferentiableAt ℝ (fun y ↦ weight y * inverseMetric y i j) z :=
      hweight.mul (hinverse i j)
    rw [fderiv_fun_mul hcoefficient (hdu j)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rfl
  · intro j _hj
    exact (hweight.mul (hinverse i j)).mul (hdu j)

/-- Divergence of the coordinate metric flux, expanded before using the
contracted metric-compatibility identity. -/
theorem euclideanCoordinateDivergence_coordinateMetricFluxComponent
    {weight : E → ℝ}
    {inverseMetric : E → Fin n → Fin n → ℝ}
    {u : E → ℝ} {z : E}
    (hweight : DifferentiableAt ℝ weight z)
    (hinverse : ∀ i j,
      DifferentiableAt ℝ (fun y ↦ inverseMetric y i j) z)
    (hdu : ∀ j, DifferentiableAt ℝ (coordinateDirectionalDerivative u j) z) :
    euclideanCoordinateDivergence
        (coordinateMetricFluxComponent weight inverseMetric u) z =
      ∑ i : Fin n, ∑ j : Fin n,
        ((weight z * inverseMetric z i j) *
            coordinateSecondDerivative u i j z +
          coordinateDirectionalDerivative u j z *
            fderiv ℝ (fun y ↦ weight y * inverseMetric y i j) z
              (EuclideanSpace.single i (1 : ℝ))) := by
  unfold euclideanCoordinateDivergence
  apply Finset.sum_congr rfl
  intro i _hi
  exact fderiv_coordinateMetricFluxComponent_apply
    hweight hinverse hdu i

/-- The contracted coefficient identity turns the product-rule expansion
into `weight *` the contracted coordinate Laplacian. -/
theorem euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
    {weight : E → ℝ}
    {inverseMetric : E → Fin n → Fin n → ℝ}
    {contractedChristoffel : E → Fin n → ℝ}
    {u : E → ℝ} {z : E}
    (hweight : DifferentiableAt ℝ weight z)
    (hinverse : ∀ i j,
      DifferentiableAt ℝ (fun y ↦ inverseMetric y i j) z)
    (hdu : ∀ j, DifferentiableAt ℝ (coordinateDirectionalDerivative u j) z)
    (hcontracted : ∀ j : Fin n,
      (∑ i : Fin n,
        fderiv ℝ (fun y ↦ weight y * inverseMetric y i j) z
          (EuclideanSpace.single i (1 : ℝ))) =
        weight z * contractedChristoffel z j) :
    euclideanCoordinateDivergence
        (coordinateMetricFluxComponent weight inverseMetric u) z =
      weight z *
        contractedCoordinateLaplacian inverseMetric contractedChristoffel u z := by
  rw [euclideanCoordinateDivergence_coordinateMetricFluxComponent
    hweight hinverse hdu]
  unfold contractedCoordinateLaplacian
  have hSecond :
      (∑ i : Fin n, ∑ j : Fin n,
        (weight z * inverseMetric z i j) *
          coordinateSecondDerivative u i j z) =
        weight z *
          (∑ i : Fin n, ∑ j : Fin n,
            inverseMetric z i j * coordinateSecondDerivative u i j z) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hDrift :
      (∑ i : Fin n, ∑ j : Fin n,
        coordinateDirectionalDerivative u j z *
          fderiv ℝ (fun y ↦ weight y * inverseMetric y i j) z
            (EuclideanSpace.single i (1 : ℝ))) =
        weight z *
          (∑ j : Fin n,
            contractedChristoffel z j * coordinateDirectionalDerivative u j z) := by
    rw [Finset.sum_comm]
    calc
      (∑ j : Fin n, ∑ i : Fin n,
          coordinateDirectionalDerivative u j z *
            fderiv ℝ (fun y ↦ weight y * inverseMetric y i j) z
              (EuclideanSpace.single i (1 : ℝ))) =
          ∑ j : Fin n,
            (∑ i : Fin n,
              fderiv ℝ (fun y ↦ weight y * inverseMetric y i j) z
                (EuclideanSpace.single i (1 : ℝ))) *
              coordinateDirectionalDerivative u j z := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = ∑ j : Fin n,
            (weight z * contractedChristoffel z j) *
              coordinateDirectionalDerivative u j z := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [hcontracted j]
      _ = weight z *
            (∑ j : Fin n,
              contractedChristoffel z j * coordinateDirectionalDerivative u j z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
  simp only [Finset.sum_add_distrib]
  rw [hSecond, hDrift]
  ring

/-- The conventional and contracted coordinate Laplacian formulas agree
when the contracted Christoffel coefficient has its defining contraction. -/
theorem contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
    (inverseMetric : E → Fin n → Fin n → ℝ)
    (christoffel : E → Fin n → Fin n → Fin n → ℝ)
    (contractedChristoffel : E → Fin n → ℝ)
    (u : E → ℝ) (z : E)
    (hcontracted : ∀ k : Fin n,
      contractedChristoffel z k =
        -(∑ i : Fin n, ∑ j : Fin n,
          inverseMetric z i j * christoffel z k i j)) :
    contractedCoordinateLaplacian inverseMetric contractedChristoffel u z =
      christoffelCoordinateLaplacian inverseMetric christoffel u z := by
  unfold contractedCoordinateLaplacian christoffelCoordinateLaplacian
  have hReindex :
      (∑ k : Fin n,
        (∑ i : Fin n, ∑ j : Fin n,
          inverseMetric z i j * christoffel z k i j) *
            coordinateDirectionalDerivative u k z) =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          inverseMetric z i j *
            (christoffel z k i j * coordinateDirectionalDerivative u k z) := by
    calc
      (∑ k : Fin n,
          (∑ i : Fin n, ∑ j : Fin n,
            inverseMetric z i j * christoffel z k i j) *
              coordinateDirectionalDerivative u k z) =
          ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            (inverseMetric z i j * christoffel z k i j) *
              coordinateDirectionalDerivative u k z := by
            simp only [Finset.sum_mul]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            (inverseMetric z i j * christoffel z k i j) *
              coordinateDirectionalDerivative u k z := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            inverseMetric z i j *
              (christoffel z k i j * coordinateDirectionalDerivative u k z) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  have hNeg :
      (∑ k : Fin n,
        -(∑ i : Fin n, ∑ j : Fin n,
          inverseMetric z i j * christoffel z k i j) *
            coordinateDirectionalDerivative u k z) =
        -(∑ k : Fin n,
          (∑ i : Fin n, ∑ j : Fin n,
            inverseMetric z i j * christoffel z k i j) *
              coordinateDirectionalDerivative u k z) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        inverseMetric z i j * coordinateSecondDerivative u i j z) +
        ∑ k : Fin n,
          contractedChristoffel z k * coordinateDirectionalDerivative u k z =
      (∑ i : Fin n, ∑ j : Fin n,
        inverseMetric z i j * coordinateSecondDerivative u i j z) -
        ∑ k : Fin n,
          (∑ i : Fin n, ∑ j : Fin n,
            inverseMetric z i j * christoffel z k i j) *
              coordinateDirectionalDerivative u k z := by
        simp_rw [hcontracted]
        rw [hNeg, sub_eq_add_neg]
    _ = (∑ i : Fin n, ∑ j : Fin n,
        inverseMetric z i j * coordinateSecondDerivative u i j z) -
          ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            inverseMetric z i j *
              (christoffel z k i j * coordinateDirectionalDerivative u k z) := by
        rw [hReindex]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        inverseMetric z i j *
          (coordinateSecondDerivative u i j z -
            ∑ k : Fin n,
              christoffel z k i j * coordinateDirectionalDerivative u k z) := by
        simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

end CoordinateMetricFlux

section FiniteSubordinatePartitionStokes

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Proof-bearing geometric data for the finite subordinate-partition proof
of closed-manifold Stokes for one scalar.

Unlike `FiniteChartCompactlySupportedLaplacianFluxAt`, this structure does
not ask the Laplacian of the original scalar to have zero flux separately on
the members of a disjoint measurable decomposition.  Its `i`-th coordinate
representative is the zero extension of the localized scalar `rho_i * f`.
The only analytic identities retained as fields are the standard intrinsic
coordinate formula and the density/contracted-Christoffel compatibility
identity.  Integrability and every integral cancellation are proved below. -/
structure FiniteSubordinateHausdorffLaplacianGeometry
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) where
  chartCount : ℕ
  coordinateDomain : Fin chartCount → Set E
  coordinateDomain_measurable : ∀ i, MeasurableSet (coordinateDomain i)
  inverseChart : (i : Fin chartCount) → coordinateDomain i → M
  inverseChart_measurable : ∀ i, Measurable (inverseChart i)
  chartRegion : Fin chartCount → Set M
  chartRegion_isOpen : ∀ i, IsOpen (chartRegion i)
  density : (i : Fin chartCount) → coordinateDomain i → ℝ
  density_nonneg : ∀ i,
    0 ≤ᵐ[coordinateLebesgueMeasure (coordinateDomain i)] density i
  density_integrable : ∀ i,
    Integrable (density i) (coordinateLebesgueMeasure (coordinateDomain i))
  chartMeasure : ∀ i,
    HausdorffChartDensityEquality g
      (coordinateDomain i) (inverseChart i) (chartRegion i) (density i)
  partition : SmoothPartitionOfUnity (Fin chartCount) I M Set.univ
  partition_subordinate : partition.IsSubordinate chartRegion
  f_contMDiff_two : ContMDiff I 𝓘(ℝ) 2 f
  coordinateRepresentative : Fin chartCount → E → ℝ
  coordinateRepresentative_eq : ∀ i (z : coordinateDomain i),
    coordinateRepresentative i z =
      partition i (inverseChart i z) * f (inverseChart i z)
  coordinateRepresentative_contDiff_two : ∀ i,
    ContDiff ℝ 2 (coordinateRepresentative i)
  coordinateRepresentative_hasCompactSupport : ∀ i,
    HasCompactSupport (coordinateRepresentative i)
  coordinateRepresentative_tsupport_subset_coordinateDomain : ∀ i,
    tsupport (coordinateRepresentative i) ⊆ coordinateDomain i
  weight : Fin chartCount → E → ℝ
  weight_contDiff_one : ∀ i, ContDiff ℝ 1 (weight i)
  weight_eq_density : ∀ i (z : coordinateDomain i),
    weight i z = (rawHausdorffLebesgueScale n : ℝ) * density i z
  inverseMetric : Fin chartCount → E → Fin n → Fin n → ℝ
  inverseMetric_contDiff_one : ∀ i a b,
    ContDiff ℝ 1 (fun z ↦ inverseMetric i z a b)
  christoffel : Fin chartCount → E → Fin n → Fin n → Fin n → ℝ
  contractedChristoffel : Fin chartCount → E → Fin n → ℝ
  contractedChristoffel_eq : ∀ i (z : coordinateDomain i) k,
    contractedChristoffel i z k =
      -(∑ a : Fin n, ∑ b : Fin n,
        inverseMetric i z a b * christoffel i z k a b)
  density_inverseMetric_compatibility : ∀ i
      (z : coordinateDomain i) (j : Fin n),
    (∑ a : Fin n,
      fderiv ℝ (fun y ↦ weight i y * inverseMetric i y a j) z
        (EuclideanSpace.single a (1 : ℝ))) =
      weight i z * contractedChristoffel i z j
  intrinsicCoordinateLaplacian_eq : ∀ i
      (z : coordinateDomain i),
    g.laplacianAt
        (fun x : M ↦ partition i x * f x) (inverseChart i z) =
      christoffelCoordinateLaplacian
        (inverseMetric i) (christoffel i)
          (coordinateRepresentative i) z
  localizedLaplacian_aestronglyMeasurable : ∀ i,
    AEStronglyMeasurable
      (fun x : M ↦
        g.laplacianAt (fun y : M ↦ partition i y * f y) x)
      (volumeMeasure g)

/-- The `i`-th partition-localized scalar. -/
noncomputable def FiniteSubordinateHausdorffLaplacianGeometry.localizedScalar
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) : M → ℝ :=
  fun x ↦ A.partition i x * f x

/-- Every localized scalar is globally `C²`. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedScalar_contMDiff_two
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) :
    ContMDiff I 𝓘(ℝ) 2 (A.localizedScalar i) := by
  unfold localizedScalar
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  exact ((A.partition i).contMDiff.of_le htwo_le_top).mul
    A.f_contMDiff_two

/-- Subordination puts the localized scalar's support inside its chart
region. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.tsupport_localizedScalar_subset_chartRegion
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) :
    tsupport (A.localizedScalar i) ⊆ A.chartRegion i := by
  exact (tsupport_mul_subset_left.trans (A.partition_subordinate i))

/-- The intrinsic Laplacian of a localized scalar vanishes outside its
subordinate chart.  This is derived from support and local congruence, rather
than retained as a field of the geometric package. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.laplacian_localizedScalar_eq_zero_of_not_mem
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) {x : M} (hx : x ∉ A.chartRegion i) :
    g.laplacianAt (A.localizedScalar i) x = 0 := by
  have hxt : x ∉ tsupport (A.localizedScalar i) :=
    fun hxt ↦ hx (A.tsupport_localizedScalar_subset_chartRegion i hxt)
  rw [notMem_tsupport_iff_eventuallyEq] at hxt
  calc
    g.laplacianAt (A.localizedScalar i) x =
        g.laplacianAt (fun _ : M ↦ (0 : ℝ)) x :=
      g.laplacianAt_congr_of_eventuallyEq hxt
        (g.mdifferentiableAt_gradient
          (A.localizedScalar_contMDiff_two i).contMDiffAt)
        (g.mdifferentiableAt_gradient contMDiffAt_const)
    _ = 0 := g.laplacianAt_const 0 x

/-- The actual coordinate metric flux attached to the `i`-th localized
scalar. -/
noncomputable def FiniteSubordinateHausdorffLaplacianGeometry.fluxComponent
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) (a : Fin n) : E → ℝ :=
  coordinateMetricFluxComponent (A.weight i) (A.inverseMetric i)
    (A.coordinateRepresentative i) a

/-- Coordinate metric-flux components are `C¹`, derived from the regularity
fields of the geometric package. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.fluxComponent_contDiff_one
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) (a : Fin n) :
    ContDiff ℝ 1 (A.fluxComponent i a) :=
  coordinateMetricFluxComponent_contDiff_one
    (A.weight_contDiff_one i) (A.inverseMetric_contDiff_one i)
      (A.coordinateRepresentative_contDiff_two i) a

/-- Coordinate metric-flux components have compact support, derived from
the compact support of the zero-extended localized scalar. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.fluxComponent_hasCompactSupport
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) (a : Fin n) :
    HasCompactSupport (A.fluxComponent i a) :=
  coordinateMetricFluxComponent_hasCompactSupport
    (A.coordinateRepresentative_hasCompactSupport i) a

/-- Every coordinate flux is supported in the corresponding coordinate
domain. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.tsupport_fluxComponent_subset_coordinateDomain
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) (a : Fin n) :
    tsupport (A.fluxComponent i a) ⊆ A.coordinateDomain i :=
  (tsupport_coordinateMetricFluxComponent_subset
    (A.weight i) (A.inverseMetric i)
      (A.coordinateRepresentative i) a).trans
        (A.coordinateRepresentative_tsupport_subset_coordinateDomain i)

/-- The density-weighted coordinate pullback of the localized intrinsic
Laplacian is the Euclidean divergence of the derived metric flux. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.coordinateLaplacianDensity_eq_divergence
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) (z : A.coordinateDomain i) :
    (rawHausdorffLebesgueScale n : ℝ) * A.density i z *
        g.laplacianAt (A.localizedScalar i) (A.inverseChart i z) =
      euclideanCoordinateDivergence (A.fluxComponent i) z := by
  have hdiv :=
    euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
      ((A.weight_contDiff_one i).differentiable one_ne_zero z)
      (fun a b ↦
        (A.inverseMetric_contDiff_one i a b).differentiable one_ne_zero z)
      (fun j ↦
        (coordinateDirectionalDerivative_contDiff_one
          (A.coordinateRepresentative_contDiff_two i) j).differentiable
            one_ne_zero z)
      (A.density_inverseMetric_compatibility i z)
  calc
    (rawHausdorffLebesgueScale n : ℝ) * A.density i z *
        g.laplacianAt (A.localizedScalar i) (A.inverseChart i z) =
      A.weight i z *
        christoffelCoordinateLaplacian
          (A.inverseMetric i) (A.christoffel i)
            (A.coordinateRepresentative i) z := by
          rw [A.weight_eq_density i z]
          exact congrArg (fun q : ℝ ↦
            ((rawHausdorffLebesgueScale n : ℝ) * A.density i z) * q)
              (A.intrinsicCoordinateLaplacian_eq i z)
    _ = A.weight i z *
        contractedCoordinateLaplacian
          (A.inverseMetric i) (A.contractedChristoffel i)
            (A.coordinateRepresentative i) z := by
          rw [contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
            (A.inverseMetric i) (A.christoffel i)
              (A.contractedChristoffel i) (A.coordinateRepresentative i) z
                (A.contractedChristoffel_eq i z)]
    _ = euclideanCoordinateDivergence (A.fluxComponent i) z := hdiv.symm

/-- The density-weighted pulled-back localized Laplacian is coordinate
Lebesgue integrable. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.coordinateLaplacianDensity_integrable
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) :
    Integrable
      (fun z : A.coordinateDomain i ↦
        (rawHausdorffLebesgueScale n : ℝ) * A.density i z *
          g.laplacianAt (A.localizedScalar i) (A.inverseChart i z))
      (coordinateLebesgueMeasure (A.coordinateDomain i)) := by
  have hDiv : Integrable
      (euclideanCoordinateDivergence (A.fluxComponent i)) :=
    euclideanCoordinateDivergence_integrable (A.fluxComponent i)
      (A.fluxComponent_contDiff_one i)
        (A.fluxComponent_hasCompactSupport i)
  have hDivOn : IntegrableOn
      (euclideanCoordinateDivergence (A.fluxComponent i))
      (A.coordinateDomain i) := hDiv.integrableOn
  have hSubtype : Integrable
      (fun z : A.coordinateDomain i ↦
        euclideanCoordinateDivergence (A.fluxComponent i) z)
      (coordinateLebesgueMeasure (A.coordinateDomain i)) := by
    simpa [coordinateLebesgueMeasure, Function.comp_def] using
      (integrableOn_iff_comap_subtypeVal
        (A.coordinateDomain_measurable i)).mp hDivOn
  apply hSubtype.congr
  exact Eventually.of_forall fun z ↦
    (A.coordinateLaplacianDensity_eq_divergence i z).symm

/-- The pulled-back localized Laplacian is integrable against the actual
raw-Hausdorff coordinate density. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.pulledBackLaplacian_integrable
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) :
    Integrable
      (fun z : A.coordinateDomain i ↦
        g.laplacianAt (A.localizedScalar i) (A.inverseChart i z))
      (rawHausdorffCoordinateDensityMeasure
        (A.coordinateDomain i) (A.density i)) := by
  let U := A.coordinateDomain i
  let μU := coordinateLebesgueMeasure U
  let c : ℝ := rawHausdorffLebesgueScale n
  let δ : U → ℝ := A.density i
  let w : U → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (c * δ z)
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hwMeas : AEMeasurable w μU := by
    exact (((A.density_integrable i).aestronglyMeasurable.const_mul c).aemeasurable).ennreal_ofReal
  have hwTop : ∀ᵐ z ∂μU, w z < (⊤ : ℝ≥0∞) :=
    Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top
  rw [rawHausdorffCoordinateDensityMeasure]
  refine (integrable_withDensity_iff_integrable_smul₀' hwMeas hwTop).2 ?_
  have hWeighted := A.coordinateLaplacianDensity_integrable i
  apply hWeighted.congr
  filter_upwards [A.density_nonneg i] with z hz
  have hwReal : (w z).toReal = c * δ z := by
    exact ENNReal.toReal_ofReal (mul_nonneg hc hz)
  rw [hwReal]
  simp only [smul_eq_mul]
  rfl

/-- The localized intrinsic Laplacian is integrable on its chart region. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedLaplacian_integrableOn_chartRegion
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) :
    IntegrableOn (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
      (A.chartRegion i) (volumeMeasure g) := by
  let ν := rawHausdorffCoordinateDensityMeasure
    (A.coordinateDomain i) (A.density i)
  have hMeasMap : AEStronglyMeasurable
      (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
      (Measure.map (A.inverseChart i) ν) := by
    rw [A.chartMeasure i]
    exact (A.localizedLaplacian_aestronglyMeasurable i).mono_measure
      Measure.restrict_le_self
  have hMap : Integrable
      (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
      (Measure.map (A.inverseChart i) ν) :=
    (integrable_map_measure hMeasMap
      (A.inverseChart_measurable i).aemeasurable).2
        (by simpa [ν, Function.comp_def] using
          A.pulledBackLaplacian_integrable i)
  rw [A.chartMeasure i] at hMap
  exact hMap

/-- Each localized intrinsic Laplacian is globally integrable, obtained by
extending its chart-restricted integrability by zero. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedLaplacian_integrable
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) :
    Integrable (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
      (volumeMeasure g) :=
  (A.localizedLaplacian_integrableOn_chartRegion i).integrable_of_forall_notMem_eq_zero
    fun _x hx ↦ A.laplacian_localizedScalar_eq_zero_of_not_mem i hx

/-- Each partition-localized Laplacian has zero global integral.  The proof
changes variables to its single subordinate chart and then applies the
whole-space compactly supported Euclidean divergence theorem. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedClosedLaplacianStokes
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
    (i : Fin A.chartCount) :
    ClosedLaplacianStokes g (A.localizedScalar i) := by
  have hLapInt := A.localizedLaplacian_integrable i
  refine ⟨hLapInt, ?_⟩
  calc
    (∫ x : M, g.laplacianAt (A.localizedScalar i) x
        ∂(volumeMeasure g)) =
        ∫ x in A.chartRegion i,
          g.laplacianAt (A.localizedScalar i) x
          ∂(volumeMeasure g) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦
          A.laplacian_localizedScalar_eq_zero_of_not_mem i hx)).symm
    _ = ∫ z : A.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * A.density i z *
            g.laplacianAt (A.localizedScalar i) (A.inverseChart i z)
          ∂(coordinateLebesgueMeasure (A.coordinateDomain i)) :=
      integral_restrict_eq_rawHausdorff_coordinateDensity g
        (A.inverseChart_measurable i) (A.chartMeasure i)
          (A.density_integrable i) (A.density_nonneg i)
            (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
              (A.localizedLaplacian_integrableOn_chartRegion i)
    _ = ∫ z : A.coordinateDomain i,
          euclideanCoordinateDivergence (A.fluxComponent i) z
          ∂(coordinateLebesgueMeasure (A.coordinateDomain i)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z ↦
        A.coordinateLaplacianDensity_eq_divergence i z
    _ = ∫ z in A.coordinateDomain i,
          euclideanCoordinateDivergence (A.fluxComponent i) z := by
      simpa [coordinateLebesgueMeasure] using
        integral_subtype_comap (A.coordinateDomain_measurable i)
          (euclideanCoordinateDivergence (A.fluxComponent i))
    _ = ∫ z : E,
          euclideanCoordinateDivergence (A.fluxComponent i) z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
        euclideanCoordinateDivergence_eq_zero_of_not_mem
          (A.fluxComponent i)
            (A.tsupport_fluxComponent_subset_coordinateDomain i) hz
    _ = 0 := integral_euclideanCoordinateDivergence_eq_zero
      (A.fluxComponent i) (A.fluxComponent_contDiff_one i)
        (A.fluxComponent_hasCompactSupport i)

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The intrinsic Laplacian commutes with a finite sum of globally `C²`
scalars. -/
theorem ClosedSmoothRiemannianMetric.laplacianAt_finsetSum
    {ι : Type*} [DecidableEq ι]
    (g : ClosedSmoothRiemannianMetric n M)
    (F : ι → M → ℝ) (s : Finset ι)
    (hF : ∀ i, ContMDiff I 𝓘(ℝ) 2 (F i)) (x : M) :
    g.laplacianAt (∑ i ∈ s, F i) x =
      ∑ i ∈ s, g.laplacianAt (F i) x := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using g.laplacianAt_const 0 x
  | @insert a s ha ih =>
      have hsum : ContMDiff I 𝓘(ℝ) 2 (∑ i ∈ s, F i) := by
        have hsum' : ContMDiff I 𝓘(ℝ) 2
            (fun y : M ↦ ∑ i ∈ s, F i y) := by
          apply ContMDiff.sum
          intro i _hi
          exact hF i
        have hfun : (∑ i ∈ s, F i) =
            (fun y : M ↦ ∑ i ∈ s, F i y) := by
          funext y
          simp only [Finset.sum_apply]
        rw [hfun]
        exact hsum'
      simp only [Finset.sum_insert ha]
      rw [g.laplacianAt_add'
        (fun y ↦ (hF a).contMDiffAt)
        (fun y ↦ hsum.contMDiffAt)]
      rw [ih]

/-- A finite partition of unity reconstructs the original scalar from its
localized summands. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.sum_localizedScalar_eq
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f) :
    (∑ i : Fin A.chartCount, A.localizedScalar i) = f := by
  funext x
  rw [Finset.sum_apply]
  change (∑ i : Fin A.chartCount, A.partition i x * f x) = f x
  rw [← Finset.sum_mul]
  have hpartition :
      (∑ i : Fin A.chartCount, A.partition i x) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      A.partition.sum_eq_one (mem_univ x)
  rw [hpartition, one_mul]

/-- Pointwise, the original scalar's Laplacian is the finite sum of the
localized Laplacians.  This is the global-sum identity missing from the old
per-disjoint-piece flux interface. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.laplacian_eq_sum_localized
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f) (x : M) :
    g.laplacianAt f x =
      ∑ i : Fin A.chartCount,
        g.laplacianAt (A.localizedScalar i) x := by
  calc
    g.laplacianAt f x =
        g.laplacianAt
          (∑ i : Fin A.chartCount, A.localizedScalar i) x :=
      congrArg (fun q : M → ℝ ↦ g.laplacianAt q x)
        A.sum_localizedScalar_eq.symm
    _ = ∑ i : Fin A.chartCount,
          g.laplacianAt (A.localizedScalar i) x :=
      g.laplacianAt_finsetSum
        (fun i : Fin A.chartCount ↦ A.localizedScalar i)
          Finset.univ A.localizedScalar_contMDiff_two x

/-- The corrected finite subordinate-partition interface proves the primary
closed-manifold Stokes statement by summing localized cancellations. -/
theorem FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes
    {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
    (A : FiniteSubordinateHausdorffLaplacianGeometry g f) :
    ClosedLaplacianStokes g f := by
  have hLocalizedInt : ∀ i : Fin A.chartCount,
      Integrable (fun x : M ↦ g.laplacianAt (A.localizedScalar i) x)
        (volumeMeasure g) :=
    A.localizedLaplacian_integrable
  have hSumInt : Integrable
      (fun x : M ↦ ∑ i : Fin A.chartCount,
        g.laplacianAt (A.localizedScalar i) x)
      (volumeMeasure g) :=
    integrable_finsetSum Finset.univ fun i _hi ↦ hLocalizedInt i
  have hLapInt : Integrable (fun x : M ↦ g.laplacianAt f x)
      (volumeMeasure g) := by
    apply hSumInt.congr
    exact Eventually.of_forall fun x ↦
      (A.laplacian_eq_sum_localized x).symm
  refine ⟨hLapInt, ?_⟩
  calc
    (∫ x : M, g.laplacianAt f x ∂(volumeMeasure g)) =
        ∫ x : M, (∑ i : Fin A.chartCount,
          g.laplacianAt (A.localizedScalar i) x)
          ∂(volumeMeasure g) := by
      apply integral_congr_ae
      exact Eventually.of_forall A.laplacian_eq_sum_localized
    _ = ∑ i : Fin A.chartCount,
          ∫ x : M, g.laplacianAt (A.localizedScalar i) x
            ∂(volumeMeasure g) :=
      integral_finsetSum Finset.univ fun i _hi ↦ hLocalizedInt i
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      exact (A.localizedClosedLaplacianStokes i).2

end FiniteSubordinatePartitionStokes

section GlobalSubordinatePartitionStokes

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- All-time finite subordinate coordinate geometry.  This is the corrected
replacement for `GlobalFiniteHausdorffChartLaplacianFlux`: it localizes the
scalar by a genuine smooth partition of unity and derives cancellation only
after the finite sum is reassembled. -/
structure GlobalFiniteSubordinateHausdorffLaplacianGeometry
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (f : ℝ → M → ℝ) where
  geometryAt : ∀ t : ℝ,
    FiniteSubordinateHausdorffLaplacianGeometry (gt t) (f t)

omit [SecondCountableTopology M] in
/-- The all-time subordinate-partition package supplies closed Laplacian
Stokes at every time. -/
theorem GlobalFiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {f : ℝ → M → ℝ}
    (A : GlobalFiniteSubordinateHausdorffLaplacianGeometry gt f) (t : ℝ) :
    ClosedLaplacianStokes (gt t) (f t) :=
  (A.geometryAt t).closedLaplacianStokes

end GlobalSubordinatePartitionStokes

section DimensionThreeSubordinatePartitionEndpoints

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- LSC compactness endpoint with Stokes derived from a genuine finite
subordinate coordinate partition. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_subordinateCoordinatePartition_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hGeometry : GlobalFiniteSubordinateHausdorffLaplacianGeometry
      gt (fun t y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_lscCompactness
      hFlow hHausdorff hLichnerowicz hGeometry.closedLaplacianStokes
      hFiniteDissipation hCompact hc hScalarLower

/-- Closed mean-energy-range endpoint with Stokes derived from the same
finite subordinate coordinate partition. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_subordinateCoordinatePartition_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hGeometry : GlobalFiniteSubordinateHausdorffLaplacianGeometry
      gt (fun t y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff hLichnerowicz hGeometry.closedLaplacianStokes
      hFiniteDissipation hRangeClosed hc hScalarLower

/-- Exponential-dissipation closed-range endpoint with Stokes derived from
the finite subordinate coordinate partition. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_subordinateCoordinatePartition_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hGeometry : GlobalFiniteSubordinateHausdorffLaplacianGeometry
      gt (fun t y ↦ (gt t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate c : ℝ} (hrate : 0 < rate) (hc : 0 < c)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff hLichnerowicz hGeometry.closedLaplacianStokes
      hDissipationMeasurable hrate hc hDecay hRangeClosed hScalarLower

end DimensionThreeSubordinatePartitionEndpoints

end Poincare
