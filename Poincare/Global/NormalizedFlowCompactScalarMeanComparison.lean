import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient

/-!
# Uniform scalar-to-mean comparison on a compact metric family

A positive uniform lower bound for the mean scalar curvature converts the
ordinary compact-family scalar bound into the multiplicative comparison
needed by the normalized traceless-Ricci reaction estimate.  Consequently a
compact realization of the forward flow does not need to store a separate
pointwise `R ≤ C * meanScalar` field.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- A compact metric-family realization, joint scalar continuity, and a
positive forward mean-scalar floor supply one uniform multiplicative
scalar-to-mean comparison along the realized flow.

The constant is constructed as `S / rho`, where `S` uniformly bounds
`|R|` on the compact family and `rho` is the mean-scalar floor. -/
theorem
    exists_pos_uniform_scalarAt_le_mul_meanScalar_of_compact_parameterization_of_meanLower
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    {rho : ℝ} (hrho : 0 < rho)
    (hMeanLower : ∀ t : Ici (0 : ℝ),
      rho ≤ meanScalar (gt t.1))
    (hJointScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).scalarAt x ≤ C * meanScalar (gt t.1) := by
  letI : Nonempty K := ⟨parameter ⟨0, by simp⟩⟩
  obtain ⟨S, hS, hScalarBound⟩ :=
    exists_pos_uniform_abs_scalarAt_bound_of_compact_joint_scalar
      metric hJointScalar
  let C : ℝ := S / rho
  have hC : 0 < C := div_pos hS hrho
  refine ⟨C, hC, ?_⟩
  intro t x
  have hScalarLe : (gt t.1).scalarAt x ≤ S := by
    calc
      (gt t.1).scalarAt x ≤ |(gt t.1).scalarAt x| := le_abs_self _
      _ = |(metric (parameter t)).scalarAt x| := by rw [hRealizes t]
      _ ≤ S := hScalarBound (parameter t) x
  have hScaledMean : S ≤ C * meanScalar (gt t.1) := by
    have hMul :=
      mul_le_mul_of_nonneg_left (hMeanLower t) (le_of_lt hC)
    have hCrho : C * rho = S := by
      dsimp [C]
      exact div_mul_cancel₀ S (ne_of_gt hrho)
    rw [hCrho] at hMul
    exact hMul
  exact hScalarLe.trans hScaledMean

end Poincare
