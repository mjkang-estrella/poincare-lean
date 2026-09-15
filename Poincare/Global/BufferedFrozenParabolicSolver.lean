import Poincare.Global.NearFrozenParabolicRightInverse
import Poincare.Global.ParabolicCutoffCommutator
import Poincare.Global.FiniteAtlasParabolicTensorSpace

noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology

namespace Poincare.BufferedFrozenParabolicSolver

open ParabolicHolder ParabolicSolutionGraph

/-- A bounded smooth spatial function has separate, time-uniform carrier bounds. -/
theorem exists_spatial_carrier_split {v : (ClosedSmoothModel 3) → ℝ}
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    {ε α : ℝ} (hε : 0 ≤ ε) (hb : ∀ x, ‖v x‖ ≤ ε)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, ∃ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ,
      (∀ p ∈ cylinder T, f p = v p.2) ∧
      supNorm (cylinder T) f ≤ ε ∧ holderSeminorm α (cylinder T) f ≤ Λ := by
  classical
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hv (by simp)
  have hh (x y : (ClosedSmoothModel 3)) : ‖v x - v y‖ ≤ (2 * ε + B) * ‖x-y‖ ^ α := by
    have h := ParabolicCutoffCommutator.scale_interpolation (L := 2*ε+B) (R := 1)
      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
      ((norm_sub_le (v x) (v y)).trans (by linarith [hb x, hb y, B.coe_nonneg]))
    simpa using h
  refine ⟨2*ε+B, by positivity, ?_⟩
  intro T
  let f : ℝ × (ClosedSmoothModel 3) → ℝ := fun p => if p ∈ cylinder T then v p.2 else 0
  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
    intro p hp; simp [f, hp]
  have hbound : ∀ p ∈ cylinder T, ‖f p‖ ≤ ε := by
    intro p hp; simpa [f, hp] using hb p.2
  have hholder : HasHolderBound α (cylinder T) f (2*ε+B) := by
    intro p hp q hq
    simp only [f, if_pos hp, if_pos hq]
    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by
        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le)
      (by positivity))
  let fY := ofFunction f hoff ⟨ε, hbound⟩ ⟨2*ε+B, hholder⟩
  refine ⟨fY, ?_, ?_, ?_⟩
  · intro p hp
    change f p = v p.2
    simp [f, hp]
  · rw [supNorm_eq]
    apply lp.norm_le_of_forall_le hε
    intro p
    change ‖f p‖ ≤ ε
    by_cases hp : p ∈ cylinder T
    · exact hbound p hp
    · simpa [hoff p hp] using hε
  · rw [holderSeminorm_eq]
    apply lp.norm_le_of_forall_le (by positivity)
    intro i
    rw [increment_norm]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (parabolicDist_pos i.2.2.2) α)).2
      (hholder _ i.2.1 _ i.2.2.1)

/-- Cutoff multiplication preserves the local oscillation bound globally. -/
theorem cutoff_entry_bound {ξ a : (ClosedSmoothModel 3) → ℝ} {A ε : ℝ}
    (hξ : ∀ x, ξ x ∈ Icc 0 1) (hε : 0 ≤ ε)
    (ha : ∀ x ∈ tsupport ξ, |a x - A| ≤ ε) (x : (ClosedSmoothModel 3)) :
    ‖ξ x * (a x - A)‖ ≤ ε := by
  by_cases hx : x ∈ tsupport ξ
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hξ x).1]
    exact (mul_le_mul_of_nonneg_left (ha x hx) (hξ x).1).trans
      (by nlinarith [(hξ x).2])
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
    exact hε

/-- Nine smooth coordinate entries extend with one constant chosen before time. -/
theorem oscillation_extension_entries {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {U : Set (ClosedSmoothModel 3)} (hU : IsOpen U) (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (anchor : (ClosedSmoothModel 3))
    {ξ : (ClosedSmoothModel 3) → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) (hξ01 : ∀ x, ξ x ∈ Icc 0 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ,
      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
        (∀ t ∈ Icc 0 T, ∀ x i j,
          b i j (t,x) = ξ x * (a x i j - a anchor i j)) ∧
        (∀ i j, supNorm (cylinder T) (b i j) ≤ ε) ∧
        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
  classical
  have hex (i j : Fin 3) := exists_spatial_carrier_split
    (ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul hU hξ hξU
      ((ha i j).sub contDiffOn_const)) hc.mul_right hε
    (cutoff_entry_bound hξ01 hε (fun x hx => hosc x hx i j)) hα hα1
  choose L hL b hb using hex
  refine ⟨∑ i, ∑ j, L i j, Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hL i j)), ?_⟩
  intro T
  refine ⟨fun i j => b i j T, ?_, fun i j => (hb i j T).2.1, ?_⟩
  · intro t ht x i j
    exact (hb i j T).1 (t,x) ⟨ht, mem_univ x⟩
  · intro i j
    apply (hb i j T).2.2.trans
    exact (Finset.single_le_sum (fun j _ => hL i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hL i j))
        (Finset.mem_univ i))

/-- The bilinear-field extension target, with its original short-time quantifiers. -/
theorem oscillationExtensionGoal :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set (ClosedSmoothModel 3)), IsOpen U →
    ∀ (a : (ClosedSmoothModel 3) → (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), ContDiffOn ℝ ∞ a U → ∀ (anchor : (ClosedSmoothModel 3)), anchor ∈ U →
    ∀ (ξ : (ClosedSmoothModel 3) → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
    (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
    (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
      |a x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) - a anchor ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)| ≤ ε) →
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
        (∀ t ∈ Icc 0 T, ∀ x i j,
          b i j (t,x) = ξ x * (a x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) - a anchor ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))) ∧
        (∀ i j, supNorm (cylinder T) (b i j) ≤ ε) ∧
        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
  intro α hα hα1 U hU a ha anchor _ ξ hξ hc hξU hξ01 ε hε hosc
  obtain ⟨Λ, hΛ, hb⟩ := oscillation_extension_entries hα hα1 hU
    (fun x i j => a x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
    (fun i j => (ha.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
    anchor hξ hc hξU hξ01 hε hosc
  exact ⟨Λ, hΛ, fun T _ _ => hb T⟩

/-- Compact coordinate sets have genuinely compactly supported smooth cutoffs. -/
theorem exists_buffered_cutoff {K U : Set (ClosedSmoothModel 3)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ξ : (ClosedSmoothModel 3) → ℝ, ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ U ∧
      (∀ x ∈ K, ∀ᶠ y in 𝓝 x, ξ y = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) := by
  obtain ⟨V, hV, hKV, hVU, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ξ, hξ, hξV, hone, hξ01⟩ :=
    ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact hK hV hKV
  exact ⟨ξ, hξ, hcV.of_isClosed_subset (isClosed_tsupport ξ)
    (hξV.trans subset_closure), hξV.trans (subset_closure.trans hVU), hone, hξ01⟩

/-- Continuity at the freezing point controls every entry on any sufficiently small patch. -/
theorem exists_oscillation_radius (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
    (ha : ∀ i j, ContinuousAt (fun x => a x i j) anchor)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ : (ClosedSmoothModel 3) → ℝ, tsupport ξ ⊆ Metric.ball anchor ρ →
      ∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε := by
  have hev : ∀ᶠ x in 𝓝 anchor, ∀ i j, |a x i j - a anchor i j| < ε := by
    simp only [Filter.eventually_all]
    intro i j
    simpa only [Real.dist_eq] using (Metric.continuousAt_iff'.mp (ha i j) ε hε)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨ρ, hρ, fun ξ hξ x hx i j => (hball (hξ hx) i j).le⟩

/-- The maximum entry oscillation on the closed cutoff support, including the empty case. -/
def patchOscillation (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) (ξ : (ClosedSmoothModel 3) → ℝ) : ℝ :=
  sSup (insert 0 ((fun x => ‖a x - a anchor‖) '' tsupport ξ))

/-- Compactness and continuity make the oscillation supremum a genuine bound. -/
theorem patchOscillation_bounds (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
    {ξ : (ClosedSmoothModel 3) → ℝ} (hc : HasCompactSupport ξ) (ha : ContinuousOn a (tsupport ξ)) :
    0 ≤ patchOscillation a anchor ξ ∧ ∀ x ∈ tsupport ξ, ∀ i j,
      |a x i j - a anchor i j| ≤ patchOscillation a anchor ξ := by
  have hbd : BddAbove (insert 0 ((fun x => ‖a x - a anchor‖) '' tsupport ξ)) :=
    ((hc.image_of_continuousOn (ha.sub continuousOn_const).norm).insert 0).bddAbove
  refine ⟨le_csSup hbd (mem_insert _ _), ?_⟩
  intro x hx i j
  have he : ‖(a x - a anchor) i j‖ ≤ ‖a x - a anchor‖ :=
    (norm_le_pi_norm ((a x - a anchor) i) j).trans (norm_le_pi_norm (a x - a anchor) i)
  exact he.trans (le_csSup hbd (mem_insert_of_mem _ (mem_image_of_mem _ hx)))

/-- A bound for all nine entries bounds the actual oscillation supremum. -/
theorem patchOscillation_le (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
    (ξ : (ClosedSmoothModel 3) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε) :
    patchOscillation a anchor ξ ≤ ε := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨x, hx, rfl⟩)
  · exact hε
  · exact (pi_norm_le_iff_of_nonneg hε).mpr fun i =>
      (pi_norm_le_iff_of_nonneg hε).mpr fun j => ha x hx i j

/-- The extension has sup bound equal to the actual patch oscillation. -/
theorem oscillation_extension_supremum {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {U : Set (ClosedSmoothModel 3)} (hU : IsOpen U) (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (anchor : (ClosedSmoothModel 3))
    {ξ : (ClosedSmoothModel 3) → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) (hξ01 : ∀ x, ξ x ∈ Icc 0 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ,
      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
        (∀ t ∈ Icc 0 T, ∀ x i j,
          b i j (t,x) = ξ x * (a x i j - a anchor i j)) ∧
        (∀ i j, supNorm (cylinder T) (b i j) ≤ patchOscillation a anchor ξ) ∧
        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
  have hcont : ContinuousOn a (tsupport ξ) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (ha i j).continuousOn.mono hξU
  obtain ⟨hω, hbound⟩ := patchOscillation_bounds a anchor hc hcont
  exact oscillation_extension_entries hα hα1 hU a ha anchor hξ hc hξU hξ01 hω hbound

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The extended entries are those of the genuine inverse metric in the host chart. -/
theorem inverse_metric_oscillation_extension
    (g : ClosedSmoothRiemannianMetric 3 M) (p : M)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (anchor : (ClosedSmoothModel 3))
    {ξ : (ClosedSmoothModel 3) → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).target)
    (hξ01 : ∀ x, ξ x ∈ Icc 0 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ x ∈ tsupport ξ, ∀ i j,
      |(inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
        (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j| ≤ ε) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ,
      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
        (∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x *
          ((inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
            (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j)) ∧
        (∀ i j, supNorm (cylinder T) (b i j) ≤ ε) ∧
        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
  exact oscillation_extension_entries hα hα1 (isOpen_extChartAt_target p)
    (fun x i j => (inverseChartPullbackGramMatrixField g p x)⁻¹ i j)
    (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p)
    anchor hξ hc hξU hξ01 hε hosc

/-- The genuine inverse entries have arbitrarily small oscillation at each target point. -/
theorem inverse_metric_oscillation_radius
    (g : ClosedSmoothRiemannianMetric 3 M) (p : M) (anchor : (ClosedSmoothModel 3))
    (hanchor : anchor ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ : (ClosedSmoothModel 3) → ℝ, tsupport ξ ⊆ Metric.ball anchor ρ →
      ∀ x ∈ tsupport ξ, ∀ i j,
        |(inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
          (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j| ≤ ε := by
  apply exists_oscillation_radius _ anchor _ hε
  intro i j
  exact ((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
    anchor hanchor).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hanchor) |>.continuousAt

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Each landed coordinate support has a compact buffer in its actual chart target. -/
theorem exists_atlas_cutoff (A : FiniteAtlasParabolicTensorSpace.AtlasData M)
    (i : Fin A.cover.chartCount) :
    ∃ ξ : (ClosedSmoothModel 3) → ℝ, ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧
      tsupport ξ ⊆ (extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)).target ∧
      (∀ x ∈ FiniteAtlasParabolicTensorSpace.coordSupport A i,
        ∀ᶠ y in 𝓝 x, ξ y = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) := by
  exact exists_buffered_cutoff (FiniteAtlasParabolicTensorSpace.isCompact_coordSupport A i)
    (isOpen_extChartAt_target (A.cover.anchor i))
    (FiniteAtlasParabolicTensorSpace.coordSupport_subset_target A i)

end Poincare.BufferedFrozenParabolicSolver

noncomputable section
open Set
open scoped Manifold ContDiff Topology
namespace Poincare.BufferedFrozenParabolicSolver
open ParabolicHolder ParabolicSolutionGraph

/-- The matrix coefficients act in the actual Euclidean host frame. -/
def matrixBilin (A : Matrix (Fin 3) (Fin 3) ℝ) : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ) :=
  ((innerSL ℝ).comp (Matrix.toEuclideanLin A).toContinuousLinearMap).flip

theorem matrixBilin_pairing (A : Matrix (Fin 3) (Fin 3) ℝ) (v w : (ClosedSmoothModel 3)) :
    matrixBilin A v w = star (WithLp.ofLp v) ⬝ᵥ A.mulVec (WithLp.ofLp w) := by
  change inner ℝ (Matrix.toEuclideanLin A w) v = _
  rw [real_inner_comm]
  simp [PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, RCLike.inner_apply, mul_comm]

theorem matrixBilin_entry (A : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    matrixBilin A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) = A i j := by
  rw [matrixBilin_pairing]
  simp [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem matrixBilin_symm {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian)
    (v w : (ClosedSmoothModel 3)) : matrixBilin A v w = matrixBilin A w v := by
  rw [FrozenEllipticHeatOperator.bilinear_expansion (matrixBilin A) v w,
    FrozenEllipticHeatOperator.bilinear_expansion (matrixBilin A) w v]
  simp_rw [matrixBilin_entry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : A j i = A i j := by simpa using congrFun (congrFun hA i) j
  rw [hij]
  ring

theorem matrixBilin_pos {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef)
    (v : (ClosedSmoothModel 3)) (hv : v ≠ 0) : 0 < matrixBilin A v v := by
  rw [matrixBilin_pairing]
  apply hA.dotProduct_mulVec_pos
  intro h
  apply hv
  exact WithLp.ofLp_injective 2 h

theorem matrixBilin_ellipticity {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef) :
    ∃ lam Λ : ℝ, 0 < lam ∧ lam ≤ Λ ∧
      (∀ v, lam * ‖v‖^2 ≤ matrixBilin A v v) ∧
      (∀ v, matrixBilin A v v ≤ Λ * ‖v‖^2) := by
  obtain ⟨lam, hlam, hlo⟩ := CompactCoefficientEllipticity.exists_uniform_coercivity
    (fun _ : Unit => matrixBilin A) continuous_const (fun _ => matrixBilin_pos hA)
  refine ⟨lam, max lam ‖matrixBilin A‖, hlam, le_max_left _ _, hlo (), ?_⟩
  intro v
  calc
    _ ≤ ‖matrixBilin A v v‖ := le_abs_self _
    _ ≤ ‖matrixBilin A‖ * ‖v‖ * ‖v‖ := (matrixBilin A).le_opNorm₂ v v
    _ ≤ max lam ‖matrixBilin A‖ * ‖v‖^2 := by
      nlinarith [mul_le_mul_of_nonneg_right (le_max_right lam ‖matrixBilin A‖) (sq_nonneg ‖v‖)]



/-- A bounded frozen inverse with its equation on the closed cylinder. -/
structure FrozenSolver (α T C_S : ℝ) (A0 : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)) where
  S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T
  bound : ‖S‖ ≤ C_S
  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
    (S f).ut (t,x) = f (t,x) + ∑ i : Fin 3, ∑ j : Fin 3,
      A0 ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)

/-- The landed conjugated heat inverse supplies the survey's frozen interface. -/
theorem frozenCLMGoal :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
    ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ), (∀ v w, A0 v w = A0 w v) →
    (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
    ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0) := by
  intro α hα hα1 lam Λ hlam hlamΛ
  obtain ⟨D, hD, hP⟩ := NearFrozenParabolicRightInverse.exists_frozen_operator_bound
    α hα hα1 lam Λ hlam hlamΛ
  refine ⟨D, hD, ?_⟩
  intro A0 hsym hlo hhi T hT hT1
  obtain ⟨P, hsolves, hbound⟩ := hP A0 hsym hlo hhi T hT hT1
  exact ⟨⟨P, hbound, hsolves⟩⟩

/-- The frozen solver and the constructed entry bounds give the exact multiplier estimate. -/
theorem frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)}
    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
    ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
      9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖ := by
  exact ParabolicHolderMultiplier.norm_error_le b S.S hα hT hb hbα S.bound

/-- Near-frozen inversion yields the genuine coordinate equation on the cutoff one-locus. -/
theorem exists_chart_operator :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λell : ℝ, 0 < lam → lam ≤ Λell →
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ (a : (ClosedSmoothModel 3) → Matrix (Fin 3) (Fin 3) ℝ) (anchor : (ClosedSmoothModel 3)) (ξ : (ClosedSmoothModel 3) → ℝ),
      (a anchor).IsHermitian →
      (∀ v, lam * ‖v‖^2 ≤ matrixBilin (a anchor) v v) →
      (∀ v, matrixBilin (a anchor) v v ≤ Λell * ‖v‖^2) →
    ∀ T : ℝ, 0 < T → T ≤ τ₀ →
    ∀ (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
      Λb * T ^ (α / 2) ≤ ε₀ →
      (∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j)) →
      ∃ S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
        ‖S‖ ≤ C ∧
        (∀ f t, t ∈ Icc 0 T → ∀ x,
          (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
            (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
        (∀ f t, t ∈ Icc 0 T → ∀ x, ξ x = 1 →
          (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
            a x i j * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) := by
  intro α hα hα1 lam Λell hlam hlamΛ
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hS⟩ :=
    NearFrozenParabolicRightInverse.exists_nearFrozen_operator α hα hα1 lam Λell hlam hlamΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro a anchor ξ hsym hlo hhi T hT hTτ b Λb hb hbα hΛb heq
  obtain ⟨S, hsolves, hbound⟩ := hS (matrixBilin (a anchor))
    (matrixBilin_symm hsym) hlo hhi T hT hTτ b Λb hb hbα hΛb
  simp_rw [matrixBilin_entry] at hsolves
  refine ⟨S, hbound, hsolves, ?_⟩
  intro f t ht x hx
  simpa only [heq t ht x, hx, one_mul, add_sub_cancel] using hsolves f t ht x

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Positivity of the genuine inverse matrix supplies the frozen ellipticity parameters. -/
theorem inverse_metric_ellipticity (g : ClosedSmoothRiemannianMetric 3 M)
    (p : M) (anchor : (ClosedSmoothModel 3))
    (hanchor : anchor ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target) :
    let A := (inverseChartPullbackGramMatrixField g p anchor)⁻¹
    A.IsHermitian ∧ ∃ lam Λ : ℝ, 0 < lam ∧ lam ≤ Λ ∧
      (∀ v, lam * ‖v‖^2 ≤ matrixBilin A v v) ∧
      (∀ v, matrixBilin A v v ≤ Λ * ‖v‖^2) := by
  have hpos := inverseChartPullbackGramMatrix_posDef g p ⟨anchor, hanchor⟩
  rw [inverseChartPullbackGramMatrix_eq_field] at hpos
  exact ⟨hpos.inv.isHermitian, matrixBilin_ellipticity hpos.inv⟩



/-- Smooth genuine inverse entries and the frozen solver assemble on a buffered chart. -/
theorem exists_inverse_metric_chart_operator
    (g : ClosedSmoothRiemannianMetric 3 M) (p : M) (anchor : (ClosedSmoothModel 3))
    (hanchor : anchor ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ ξ : (ClosedSmoothModel 3) → ℝ, ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).target →
      (∀ x, ξ x ∈ Icc 0 1) →
      (∀ x ∈ tsupport ξ, ∀ i j,
        |(inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
          (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j| ≤ ε₀) →
      ∃ Λb : ℝ, 0 ≤ Λb ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T ≤ τ₀ →
        Λb * T ^ (α / 2) ≤ ε₀ →
        ∃ S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
          ‖S‖ ≤ C ∧ ∀ f t, t ∈ Icc 0 T → ∀ x, ξ x = 1 →
            (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
              (inverseChartPullbackGramMatrixField g p x)⁻¹ i j *
                (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
  obtain ⟨hsym, lam, Λell, hlam, hlamΛ, hlo, hhi⟩ :=
    inverse_metric_ellipticity g p anchor hanchor
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hS⟩ :=
    exists_chart_operator α hα hα1 lam Λell hlam hlamΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro ξ hξ hc hξU hξ01 hosc
  obtain ⟨Λb, hΛb, hb⟩ := inverse_metric_oscillation_extension g p hα hα1
    anchor hξ hc hξU hξ01 hε₀.le hosc
  refine ⟨Λb, hΛb, ?_⟩
  intro T hT _ hTτ hsmall
  obtain ⟨b, heq, hsup, hholder⟩ := hb T
  obtain ⟨S, hbound, _, hsolves⟩ := hS
    (fun x => (inverseChartPullbackGramMatrixField g p x)⁻¹) anchor ξ
    hsym hlo hhi T hT hTτ b Λb hsup hholder hsmall heq
  exact ⟨S, hbound, hsolves⟩

end Poincare.BufferedFrozenParabolicSolver

noncomputable section
open Set
open scoped ContDiff
namespace Poincare.BufferedFrozenParabolicSolver
open ParabolicHolder ParabolicSolutionGraph

/-- The coefficient extension leaves a transition-region gap. -/
theorem cutoff_coefficient_gap (ψ a A : ℝ) :
    a - A - ψ * (a - A) = (1 - ψ) * (a - A) := by ring

/-- Agreement fails in a transition region whenever the coefficient has changed. -/
theorem cutoff_coefficient_gap_ne_zero {ψ a A : ℝ} (hψ : ψ ≠ 1) (ha : a ≠ A) :
    a - A - ψ * (a - A) ≠ 0 := by
  rw [cutoff_coefficient_gap]
  exact mul_ne_zero (sub_ne_zero.mpr hψ.symm) (sub_ne_zero.mpr ha)

/-- The exact remaining principal residual retains the transition-region term. -/
theorem nearFrozen_chart_residual {α T : ℝ}
    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) (ψ : (ClosedSmoothModel 3) → ℝ)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ψ x * (a x i j - a anchor i j))
    (hS : ∀ f t, t ∈ Icc 0 T → ∀ x,
      (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
        (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
    ∀ f t, t ∈ Icc 0 T → ∀ x,
      (S f).ut (t,x) - (∑ i, ∑ j, a x i j * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) - f (t,x) =
        -(∑ i, ∑ j, (1 - ψ x) * (a x i j - a anchor i j) *
          (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) := by
  intro f t ht x
  rw [hS f t ht x]
  simp only [heq t ht x, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring



set_option maxHeartbeats 1600000 in
/-- The actual cutoff graph has both the principal transition error and the commutator. -/
theorem exists_cutoff_chart_residual {α T : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) {ψ : (ClosedSmoothModel 3) → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ψ x * (a x i j - a anchor i j))
    (hS : ∀ f t, t ∈ Icc 0 T → ∀ x,
      (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
        (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
    ∃ C : Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
      ∀ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ, (∀ p, ψ p.2 * f p = f p) →
      ∀ t ∈ Icc 0 T, ∀ x,
        (C (S f)).ut (t,x) -
          (∑ i, ∑ j, a x i j * (C (S f)).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) - f (t,x) =
        -ψ x * (∑ i, ∑ j, (1 - ψ x) * (a x i j - a anchor i j) *
          (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
        (∑ i, ∑ j, a x i j *
          (fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
            (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
            (S f).u (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))) := by
  obtain ⟨C, hu, hjets⟩ := ParabolicCutoffCommutator.exists_cutoff_operator hψ hc hα hα1
  refine ⟨C, hu, ?_⟩
  intro f hf t ht x
  obtain ⟨hut, _, hddu⟩ := hjets (S f) t ht x
  rw [hut, hddu, hS f t ht x]
  simp only [heq t ht x, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have hf' := hf (t,x)
  dsimp only at hf'
  linear_combination hf'

end Poincare.BufferedFrozenParabolicSolver


noncomputable section
open Set
open scoped ContDiff Topology
namespace Poincare.BufferedFrozenParabolicSolver
open ParabolicHolder ParabolicSolutionGraph

/-- Two compact buffers separate the coefficient extension from the solution cutoff. -/
theorem exists_nested_cutoffs {K U : Set (ClosedSmoothModel 3)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (U₁ : Set (ClosedSmoothModel 3)) (ψ ξ : (ClosedSmoothModel 3) → ℝ),
      IsOpen U₁ ∧ IsCompact (closure U₁) ∧ closure U₁ ⊆ U ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U₁ ∧
      (∀ x ∈ K, ∀ᶠ y in 𝓝 x, ψ y = 1) ∧ (∀ x, ψ x ∈ Icc 0 1) ∧
      ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ U ∧
      (∀ x ∈ closure U₁, ξ x = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) ∧
      (∀ x ∈ tsupport ψ, ξ x = 1) := by
  obtain ⟨V, hV, hKV, hVU, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ψ, hψ, hcψ, hψV, hψK, hψ01⟩ := exists_buffered_cutoff hK hV hKV
  obtain ⟨ξ, hξ, hcξ, hξU, hξV, hξ01⟩ := exists_buffered_cutoff hcV hU hVU
  have hone : ∀ x ∈ closure V, ξ x = 1 := fun x hx => Filter.EventuallyEq.eq_of_nhds (hξV x hx)
  exact ⟨V, ψ, ξ, hV, hcV, hVU, hψ, hcψ, hψV, hψK, hψ01,
    hξ, hcξ, hξU, hone, hξ01, fun x hx => hone x (subset_closure (hψV hx))⟩

/-- The outer extension agrees with the original entries on the inner support. -/
theorem nested_coefficient_agreement {α T : ℝ}
    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
    (ψ ξ : (ClosedSmoothModel 3) → ℝ)
    (hnest : ∀ x ∈ tsupport ψ, ξ x = 1)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j)) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ tsupport ψ, ∀ i j,
      a anchor i j + b i j (t,x) = a x i j := by
  intro t ht x hx i j
  rw [heq t ht x i j, hnest x hx, one_mul, add_sub_cancel]

/-- Support in the cutoff one-set makes multiplication preserve the forcing. -/
theorem cutoff_forcing_eq {α T : ℝ} {K : Set (ClosedSmoothModel 3)}
    (ψ : (ClosedSmoothModel 3) → ℝ) (hone : ∀ x ∈ K, ψ x = 1)
    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hf : ∀ p, p.2 ∉ K → f p = 0) : ∀ p, ψ p.2 * f p = f p := by
  intro p
  by_cases hp : p.2 ∈ K
  · rw [hone p.2 hp, one_mul]
  · rw [hf p hp, mul_zero]

set_option maxHeartbeats 1600000 in
/-- Nested cutoffs remove the principal mismatch exactly. Oscillation is needed only
for existence of the near-frozen solver; it contributes no single-chart error term. -/
theorem exists_nested_cutoff_chart_residual {α T : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) {ψ : (ClosedSmoothModel 3) → ℝ}
    (ξ : (ClosedSmoothModel 3) → ℝ)
    (hnest : ∀ x ∈ tsupport ψ, ξ x = 1)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j))
    (hS : ∀ f t, t ∈ Icc 0 T → ∀ x,
      (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
        (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
    ∃ C : Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
      ∀ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ, (∀ p, ψ p.2 * f p = f p) →
      ∀ t ∈ Icc 0 T, ∀ x,
        (C (S f)).ut (t,x) -
          (∑ i, ∑ j, a x i j * (C (S f)).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) - f (t,x) =
        -(∑ i, ∑ j, a x i j *
          (fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
            (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
            (S f).u (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))) := by
  obtain ⟨C, hu, hjets⟩ := ParabolicCutoffCommutator.exists_cutoff_operator hψ hc hα hα1
  refine ⟨C, hu, ?_⟩
  intro f hf t ht x
  obtain ⟨hut, _, hddu⟩ := hjets (S f) t ht x
  have hweighted (i j : Fin 3) :
      ψ x * (a anchor i j + b i j (t,x)) = ψ x * a x i j := by
    by_cases hx : x ∈ tsupport ψ
    · rw [nested_coefficient_agreement a anchor ψ ξ hnest b heq t ht x hx i j]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  rw [hut, hddu, hS f t ht x]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have hmul (r s v : ℝ) : r * (s * v) = r * s * v := by ring
  simp only [mul_add, Finset.mul_sum, hmul, hweighted]
  have hf' := hf (t,x)
  dsimp only at hf'
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at *
  linear_combination hf'

end Poincare.BufferedFrozenParabolicSolver
