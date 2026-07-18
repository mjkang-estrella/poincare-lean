import Poincare.Global.NormalizedFlowEnergyCriticality

/-!
# Finite dissipation plus energy compactness closes the Hamilton endpoint

`NormalizedFlowEnergyCriticality` constructs an escaping sequence of
normalized-flow times on which the scalar variance and the total squared
traceless Ricci curvature both tend to zero.  This file isolates the exact
compactness transport still needed at that point.

It is enough to extract a smooth metric whose mean scalar and total
traceless-Ricci energy are the limits of those two scalar quantities.  No
independent convergence of the metric speed, Ricci components, or normalized
right-hand side remains in the endpoint below.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [SimplyConnectedSpace M]

/-- Sequential compactness only for the two scalar quantities used by the
energy endpoint.  The extracted object is an honest closed smooth metric;
the two fields identify its mean scalar and total traceless-Ricci energy with
the corresponding sampled limits. -/
structure NormalizedFlowScalarEnergySequentialCompactness
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) : Prop where
  extract : ∀ sample : ℕ → ℝ, Tendsto sample atTop atTop →
    ∃ gLimit : ClosedSmoothRiemannianMetric 3 M,
      Tendsto (fun i ↦ meanScalar (gt (sample i))) atTop
        (nhds (meanScalar gLimit)) ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop
        (nhds (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit)))

/-- Finite normalized-flow dissipation and scalar-energy sequential
compactness produce Hamilton's reduced positive-Einstein limit.

The analytic hypotheses preceding `hCompact` are exactly those already used
to derive the escaping zero-energy sequence.  The compactness premise then
transports only mean scalar and one integral to a smooth candidate limit.
-/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteDissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeanMono : Monotone (fun t ↦ meanScalar (gt t)))
    (hMeanBdd : BddAbove (Set.range fun t ↦ meanScalar (gt t)))
    (hDissipationContinuous :
      ContinuousOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    (hMeanSupPos : 0 < ⨆ t : ℝ, meanScalar (gt t)) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsampleAtTop, _hDerivativeZero, _hVarianceZero,
      hEnergyZero, hMeanSup⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_dissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hMeanMono hMeanBdd hDissipationContinuous hFiniteDissipation
  obtain ⟨gLimit, hMeanLimit, hEnergyLimit⟩ :=
    hCompact.extract sample hsampleAtTop
  have hLimitEnergy :
      (∫ x, gLimit.tracelessRicciNormSqAt x
        ∂(volumeMeasure gLimit)) = 0 :=
    tendsto_nhds_unique hEnergyLimit hEnergyZero
  have hLimitMean :
      meanScalar gLimit = ⨆ t : ℝ, meanScalar (gt t) :=
    tendsto_nhds_unique hMeanLimit hMeanSup
  have hMeanPos : 0 < meanScalar gLimit := by
    rw [hLimitMean]
    exact hMeanSupPos
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    gLimit hLimitEnergy hMeanPos

/-- A uniform positive mean-scalar lower bound supplies positivity of the
monotone supremum required by the finite-dissipation endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteDissipation_of_meanLower
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeanMono : Monotone (fun t ↦ meanScalar (gt t)))
    (hMeanBdd : BddAbove (Set.range fun t ↦ meanScalar (gt t)))
    (hDissipationContinuous :
      ContinuousOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c) (hMeanLower : ∀ t : ℝ, c ≤ meanScalar (gt t)) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteDissipation
    gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hMeanMono hMeanBdd hDissipationContinuous hFiniteDissipation hCompact
  have hle : meanScalar (gt 0) ≤ ⨆ t : ℝ, meanScalar (gt t) :=
    le_ciSup hMeanBdd (0 : ℝ)
  exact hc.trans_le ((hMeanLower 0).trans hle)

/-- A uniform positive pointwise scalar-curvature lower bound is a concrete
geometric source of the mean lower bound in the preceding endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteDissipation_of_scalarLower
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeanMono : Monotone (fun t ↦ meanScalar (gt t)))
    (hMeanBdd : BddAbove (Set.range fun t ↦ meanScalar (gt t)))
    (hDissipationContinuous :
      ContinuousOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteDissipation_of_meanLower
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hMeanMono hMeanBdd hDissipationContinuous hFiniteDissipation
        hCompact hc
  intro t
  exact le_meanScalar_of_forall_le_scalarAt (gt t) c (hScalarLower t)

end Poincare
