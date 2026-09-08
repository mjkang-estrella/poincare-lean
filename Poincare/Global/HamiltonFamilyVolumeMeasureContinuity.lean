import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
import Poincare.Global.HamiltonCompactFamilyInvariantContinuity
import Poincare.Global.HamiltonReactionCoreReduction
import Poincare.Global.HausdorffInverseChartGramContinuity
import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonFamilyVolumeMeasureContinuity

variable {n : ℕ} {M : Type u} {K : Type v}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [TopologicalSpace K]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/-- Value profiles at their own anchor give continuous intrinsic pairings
at each fixed manifold point and pair of tangent vectors. -/
theorem continuous_inner_of_thirdJetProfiles_continuous
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (a b : E) :
    Continuous (fun k ↦ (metric k).inner x a b) := by
  have h := (hjet (.value x a b)).comp
    (continuous_id.prodMk (continuous_const (y := extChartAt I x x)))
  simpa only [Function.comp_def, id_eq, metricEntryThirdJetProfile_value_anchor] using h

variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The pullback Gram matrix is continuous in the parameter at every genuine
coordinate, including coordinates outside the anchor's cutoff support. -/
theorem continuous_parameter_inverseChartPullbackGramMatrix
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (z : (extChartAt I x).target) :
    Continuous (fun k ↦ inverseChartPullbackGramMatrix (metric k) x z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_inner_of_thirdJetProfiles_continuous metric hjet _ _ _

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Every inverse-chart volume density is continuous in the metric parameter. -/
theorem continuous_parameter_inverseChartPullbackVolumeDensity
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (z : (extChartAt I x).target) :
    Continuous (fun k ↦ inverseChartPullbackVolumeDensity (metric k) x z) := by
  exact VolumeDensity.continuous_chartVolumeDensity
    (continuous_parameter_inverseChartPullbackGramMatrix metric hjet x z)

/-- On a fixed coordinate set where the anchor cutoff is one, the genuine
volume density is jointly continuous in the metric parameter and coordinate. -/
theorem continuous_inverseChartPullbackVolumeDensity_on_cutoffOne
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (S : Set E) (hS : S ⊆ (extChartAt I x).target)
    (hχ : ∀ z ∈ S, GeodesicTransport.cutoff (n := n) x z = 1) :
    Continuous (fun p : K × S ↦ inverseChartPullbackVolumeDensity
      (metric p.1) x ⟨p.2.1, hS p.2.2⟩) := by
  apply VolumeDensity.continuous_chartVolumeDensity
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hp : Continuous (fun p : K × S ↦ (p.1, (p.2 : E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h := (hjet (.value x (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))).comp hp
  apply h.congr
  intro p
  rw [inverseChartPullbackGramMatrix_eq_field]
  change CovariantDerivative.blendedChartMetric
      (GeodesicTransport.cutoff (n := n) x)
      (GeodesicTransport.backgroundMetric (n := n)) (metric p.1).inner x p.2.1 _ _ =
    CovariantDerivative.chartMetric (metric p.1).inner x p.2.1 _ _
  rw [CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    _ _ _ _ (hχ p.2.1 p.2.2)]

/-- Compact coordinate sets inside the cutoff-one region give continuous
weighted density integrals for an arbitrary topological parameter space.
Currying into continuous maps on the compact coordinate set gives uniform
control without a countability assumption on the parameter. -/
theorem continuous_integral_inverseChartPullbackVolumeDensity_on_compact
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (S : Set E) (hSc : IsCompact S)
    (hS : S ⊆ (extChartAt I x).target)
    (hχ : ∀ z ∈ S, GeodesicTransport.cutoff (n := n) x z = 1)
    (f : C(S, ℝ)) (A : Set S) :
    Continuous (fun k ↦ ∫ z : S, f z * inverseChartPullbackVolumeDensity
      (metric k) x ⟨z.1, hS z.2⟩ ∂(coordinateLebesgueMeasure S).restrict A) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let μ := coordinateLebesgueMeasure S
  letI : IsFiniteMeasure μ := ⟨by
    change Measure.comap ((↑) : S → E) volume univ < ⊤
    rw [(MeasurableEmbedding.subtype_coe hSc.measurableSet).comap_apply]
    simpa using hSc.measure_lt_top (μ := (volume : Measure E))⟩
  have hF : Continuous (fun p : K × S ↦ f p.2 * inverseChartPullbackVolumeDensity
      (metric p.1) x ⟨p.2.1, hS p.2.2⟩) :=
    (f.continuous.comp continuous_snd).mul
      (continuous_inverseChartPullbackVolumeDensity_on_cutoffOne metric hjet x S hS hχ)
  exact continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
    (fun _ : K ↦ (⟨μ.restrict A, inferInstance⟩ : FiniteMeasure S)) continuous_const
    (fun k z ↦ f z * inverseChartPullbackVolumeDensity
      (metric k) x ⟨z.1, hS z.2⟩) hF

/-- The landed area formula restricts to any compact coordinate set. -/
theorem compact_inverseChart_hausdorffChartDensityEquality
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (S : Set E) (hSc : IsCompact S) (hS : S ⊆ (extChartAt I x).target) :
    let ψ : S → M := fun z ↦ inverseExtendedChartParametrization x ⟨z.1, hS z.2⟩
    HausdorffChartDensityEquality g S ψ (range ψ)
      (fun z ↦ inverseChartPullbackVolumeDensity g x ⟨z.1, hS z.2⟩) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let T := (extChartAt I x).target
  let ι : S → T := Set.inclusion hS
  let ψ : T → M := inverseExtendedChartParametrization x
  have hι : Topology.IsEmbedding ι := Topology.IsEmbedding.inclusion hS
  have hψ : Topology.IsEmbedding ψ := inverseExtendedChartParametrization_isEmbedding x
  have hsmall : MeasurableSet (range (ψ ∘ ι)) :=
    (isCompact_range (hψ.continuous.comp hι.continuous)).measurableSet
  have hpre : ψ ⁻¹' range (ψ ∘ ι) = range ι := by
    ext z
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, hψ.injective hw⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
  have hsub : range (ψ ∘ ι) ⊆ range ψ := by
    rintro y ⟨z, rfl⟩
    exact ⟨ι z, rfl⟩
  change Measure.map (ψ ∘ ι)
      (rawHausdorffCoordinateDensityMeasure S
        (fun z ↦ inverseChartPullbackVolumeDensity g x (ι z))) =
    (volumeMeasure g).restrict (range (ψ ∘ ι))
  rw [← Measure.map_map hψ.continuous.measurable hι.continuous.measurable,
    map_rawHausdorffCoordinateDensityMeasure_inclusion
      (isOpen_extChartAt_target x).measurableSet hSc.measurableSet hS,
    ← hpre, ← Measure.restrict_map hψ.continuous.measurable hsmall]
  rw [show Measure.map ψ (rawHausdorffCoordinateDensityMeasure T
      (inverseChartPullbackVolumeDensity g x)) =
        (volumeMeasure g).restrict (range ψ) from
      inverseChart_hausdorffChartDensityEquality g x]
  exact Measure.restrict_restrict_of_subset hsub

/-- Volume integrals on a measurable piece of a compact cutoff-one chart
are continuous, with no regularity assumption on the boundary of the piece. -/
theorem continuous_integral_volumeMeasure_restrict_compact_chart
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (S : Set E) (hSc : IsCompact S)
    (hS : S ⊆ (extChartAt I x).target)
    (hχ : ∀ z ∈ S, GeodesicTransport.cutoff (n := n) x z = 1)
    (P : Set M) (hPm : MeasurableSet P)
    (hP : P ⊆ range (fun z : S ↦ inverseExtendedChartParametrization x ⟨z.1, hS z.2⟩))
    (f : C(M, ℝ)) :
    Continuous (fun k ↦ ∫ y in P, f y ∂volumeMeasure (metric k)) := by
  let ψ : S → M := fun z ↦ inverseExtendedChartParametrization x ⟨z.1, hS z.2⟩
  have hψ : Continuous ψ := (inverseExtendedChartParametrization_isEmbedding x).continuous.comp
    (continuous_subtype_val.subtype_mk fun z ↦ hS z.2)
  let c : ℝ := rawHausdorffLebesgueScale n
  let A : Set S := ψ ⁻¹' P
  let F : C(S, ℝ) := ⟨fun z ↦ c * f (ψ z), (f.continuous.comp hψ).const_mul c⟩
  have hcont := continuous_integral_inverseChartPullbackVolumeDensity_on_compact
    metric hjet x S hSc hS hχ F A
  apply hcont.congr
  intro k
  symm
  have hchart := compact_inverseChart_hausdorffChartDensityEquality (metric k) x S hSc hS
  change Measure.map ψ (rawHausdorffCoordinateDensityMeasure S
    (fun z ↦ inverseChartPullbackVolumeDensity (metric k) x ⟨z.1, hS z.2⟩)) =
      (volumeMeasure (metric k)).restrict (range ψ) at hchart
  rw [← Measure.restrict_restrict_of_subset hP, ← hchart,
    Measure.restrict_map hψ.measurable hPm,
    integral_map hψ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [rawHausdorffCoordinateDensityMeasure,
    restrict_withDensity (hPm.preimage hψ.measurable)]
  have hd : Continuous (fun z : S ↦ inverseChartPullbackVolumeDensity (metric k) x ⟨z.1, hS z.2⟩) :=
    (continuous_inverseChartPullbackVolumeDensity (metric k) x).comp
      (continuous_subtype_val.subtype_mk fun z ↦ hS z.2)
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((hd.const_mul c).measurable.ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z ↦ by
    have hn : 0 ≤ c * inverseChartPullbackVolumeDensity (metric k) x ⟨z.1, hS z.2⟩ :=
      mul_nonneg (by dsimp [c]; positivity)
        (inverseChartPullbackVolumeDensity_pos (metric k) x _).le
    dsimp only [F, ContinuousMap.coe_mk]
    rw [ENNReal.toReal_ofReal hn, smul_eq_mul]
    ring

/-- A finite shrunken cutoff-one cover assembles continuous chart integrals
into continuity of every intrinsic volume test integral. -/
theorem continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (f : C(M, ℝ)) :
    Continuous (fun k ↦ ∫ y, f y ∂volumeMeasure (metric k)) := by
  classical
  obtain ⟨C⟩ := exists_finiteFixedAnchorCutoffOneChartCover (n := n) (M := M)
  let a : Fin C.anchors.card → C.Index := C.anchors.equivFin.symm
  let U : Fin C.anchors.card → Set M := fun i ↦ C.innerDomain (a i)
  let P : Fin C.anchors.card → Set M := disjointed U
  have hU : (⋃ i, U i) = univ := by
    apply Subset.antisymm (subset_univ _)
    intro y _
    have hy : y ∈ ⋃ i, C.innerDomain i := by rw [C.innerDomain_cover]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨C.anchors.equivFin i, by simpa [U, a] using hi⟩
  have hPm : ∀ i, MeasurableSet (P i) := by
    intro i
    apply disjointedRec
    · intro t j ht
      exact ht.diff (C.isOpen_innerDomain (a j)).measurableSet
    · exact (C.isOpen_innerDomain (a i)).measurableSet
  have hPc : (⋃ i, P i) = univ := by
    change (⋃ i, disjointed U i) = univ
    rw [iUnion_disjointed, hU]
  have hpiece : ∀ i, Continuous (fun k ↦ ∫ y in P i, f y ∂volumeMeasure (metric k)) := by
    intro i
    apply continuous_integral_volumeMeasure_restrict_compact_chart metric hjet
      (a i : M) (C.compactCoordinateSet (a i))
      (C.isCompact_compactCoordinateSet (a i))
      (C.compactCoordinateSet_subset_chart_target (a i))
      (fun z hz ↦ (C.compactCoordinateSet_subset_cutoffOneGermLocus (a i) hz).self_of_nhds)
      (P i) (hPm i) _ f
    intro y hy
    have hyU : y ∈ C.innerDomain (a i) := disjointed_subset U i hy
    have hyC : y ∈ closure (C.innerDomain (a i)) := subset_closure hyU
    have hySource := (C.closure_innerDomain_subset_cutoffOneChartNeighborhood (a i) hyC).1
    refine ⟨⟨extChartAt I (a i : M) y, ⟨y, hyC, rfl⟩⟩, ?_⟩
    change (extChartAt I (a i : M)).symm (extChartAt I (a i : M) y) = y
    exact (extChartAt I (a i : M)).left_inv hySource
  have hsum := continuous_finsetSum Finset.univ (fun i _ ↦ hpiece i)
  apply hsum.congr
  intro k
  symm
  letI := volumeMeasure_isFiniteMeasure (metric k)
  have hf : Integrable f (volumeMeasure (metric k)) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ y, f y ∂volumeMeasure (metric k)) =
        ∫ y in ⋃ i, P i, f y ∂volumeMeasure (metric k) := by rw [hPc, setIntegral_univ]
    _ = _ := integral_iUnion_fintype hPm (disjoint_disjointed U)
      (fun _ ↦ hf.integrableOn)

end Poincare.HamiltonFamilyVolumeMeasureContinuity

namespace Poincare.HamiltonFamilyVolumeMeasureContinuity
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Joint scalar third-jet profiles imply weak continuity of the original
finite Riemannian volume measures. -/
theorem continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k)) := by
  rw [FiniteMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  exact continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous metric hjet f

end Poincare.HamiltonFamilyVolumeMeasureContinuity

namespace Poincare.HamiltonFamilyVolumeMeasureContinuity

/-- The reaction core with its three compact-family continuity clauses
replaced by joint scalar third-jet profile continuity. All flow existence,
reaction, positive-mean, and local domination requirements are retained. -/
def HamiltonReactionCore3Jet (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (c rate : ℝ),
      Continuous parameter ∧
      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
      0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
      0 < rate ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M,
        normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
          -rate * (gt t).tracelessRicciNormSqAt x) ∧
      (∀ slot : MetricEntryThirdJetSlot 3 M,
        Continuous (fun p : K × ClosedSmoothModel 3 ↦
          metricEntryThirdJetProfile (metric p.1) slot p.2)) ∧
      (let C := compactFiniteExtendedChartCover (n := 3) (M := M)
       ∀ t : ℝ, ∃ s ∈ 𝓝 t,
         ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
           (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
           (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
             ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z))


end Poincare.HamiltonFamilyVolumeMeasureContinuity

namespace Poincare.HamiltonFamilyVolumeMeasureContinuity
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The jet-form core reconstructs all three original family-continuity clauses. -/
theorem hamiltonReactionCore3_of_jet
    (h : HamiltonReactionCore3Jet.{u, v} M) : HamiltonReactionCore3.{u, v} M := by
  rcases h with ⟨K, topK, compactK, gt, metric, parameter, c, rate,
    hparam, hreal, hc, hlower, hflow, hjoint, hrate, hreaction, hjet, hbound⟩
  have hcurv := HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous
    K metric hjet
  exact ⟨K, topK, compactK, gt, metric, parameter, c, rate,
    hparam, hreal, hc, hlower, hflow, hjoint, hrate, hreaction,
    continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous K metric hjet,
    hcurv.1, hcurv.2, hbound⟩

end Poincare.HamiltonFamilyVolumeMeasureContinuity
