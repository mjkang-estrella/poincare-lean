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
