import Poincare.Global.TangentAlignmentExists
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compactness of a fixed Cartan tangent-alignment fiber

For fixed source and target anchors, a Cartan tangent alignment can be viewed
as a continuous linear endomorphism of the finite-dimensional model space.
This file realizes that fiber as the set of operators satisfying the metric
isometry equations.  Those equations cut out a closed set, while comparison
with a fixed Euclideanization of the target metric bounds the operator norm.
Consequently the fixed-anchor operator fiber is compact.

This is deliberately a fixed-anchor statement.  It does not assert continuity
of the chosen anchor charts, their metric coefficients, or their alignment
fibers as either anchor varies.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

universe u

namespace CartanMap

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The ambient Euclidean inner product, regarded as an algebraic bilinear form. -/
def euclideanBilinForm : LinearMap.BilinForm ℝ E :=
  continuousBilinFormToBilinForm (innerSL ℝ)

@[simp]
theorem euclideanBilinForm_apply (u v : E) :
    euclideanBilinForm u v = (innerSL ℝ u) v := by
  rfl

theorem euclideanBilinForm_symm (u v : E) :
    euclideanBilinForm u v = euclideanBilinForm v u := by
  simp only [euclideanBilinForm_apply]
  rw [innerSL_apply_apply, innerSL_apply_apply]
  exact real_inner_comm v u

theorem euclideanBilinForm_pos {v : E} (hv : v ≠ 0) :
    0 < euclideanBilinForm v v := by
  simp only [euclideanBilinForm_apply]
  rw [innerSL_apply_apply]
  exact (real_inner_self_pos).2 hv

/-- A fixed algebraic isometry from the target anchor metric to the ambient
Euclidean inner product. -/
def targetEuclideanAlignment (p₀ : RoundSphere3) :
    (targetAnchorBilinForm p₀).IsometryEquiv euclideanBilinForm :=
  positiveDefiniteBilinFormIsometryEquiv
    (targetAnchorBilinForm p₀) euclideanBilinForm
    (fun u v => by simpa using targetAnchorChartMetric_symm p₀ u v)
    (fun {_v} hv => by simpa using targetAnchorChartMetric_pos p₀ hv)
    euclideanBilinForm_symm
    (fun {_v} hv => euclideanBilinForm_pos hv)

/-- The continuous linear representative of the fixed target-to-Euclidean
alignment. -/
def targetEuclideanContinuousLinearEquiv (p₀ : RoundSphere3) :
    E ≃L[ℝ] E :=
  ((targetEuclideanAlignment p₀ : E ≃ₗ[ℝ] E).toContinuousLinearEquiv)

@[simp]
theorem targetEuclideanContinuousLinearEquiv_apply (p₀ : RoundSphere3) (v : E) :
    targetEuclideanContinuousLinearEquiv p₀ v = targetEuclideanAlignment p₀ v :=
  rfl

/-- A fixed algebraic isometry from the source anchor metric to the ambient
Euclidean inner product. -/
def sourceEuclideanAlignment
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    (sourceAnchorBilinForm g x₀).IsometryEquiv euclideanBilinForm :=
  positiveDefiniteBilinFormIsometryEquiv
    (sourceAnchorBilinForm g x₀) euclideanBilinForm
    (fun u v => by simpa using sourceAnchorChartMetric_symm g x₀ u v)
    (fun {_v} hv => by simpa using sourceAnchorChartMetric_pos g x₀ hv)
    euclideanBilinForm_symm
    (fun {_v} hv => euclideanBilinForm_pos hv)

/-- The continuous linear representative of the fixed source-to-Euclidean
alignment. -/
def sourceEuclideanContinuousLinearEquiv
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) : E ≃L[ℝ] E :=
  ((sourceEuclideanAlignment g x₀ : E ≃ₗ[ℝ] E).toContinuousLinearEquiv)

@[simp]
theorem sourceEuclideanContinuousLinearEquiv_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (v : E) :
    sourceEuclideanContinuousLinearEquiv g x₀ v =
      sourceEuclideanAlignment g x₀ v :=
  rfl

/-- Continuous linear operators obeying the source-target metric isometry
equations at one fixed pair of anchors. -/
def tangentAlignmentOperatorFiber
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    Set (E →L[ℝ] E) :=
  {A | ∀ u v,
    targetAnchorChartMetric p₀ (A u) (A v) =
      sourceAnchorChartMetric g x₀ u v}

/-- The underlying continuous linear map of every tangent alignment belongs to
the fixed-anchor operator fiber. -/
theorem tangentAlignment_toContinuousLinearMap_mem_operatorFiber
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) :
    L.toContinuousLinearEquiv.toContinuousLinearMap ∈
      tangentAlignmentOperatorFiber g x₀ p₀ := by
  intro u v
  exact L.map_app u v

/-- The fixed-anchor operator fiber is nonempty. -/
theorem tangentAlignmentOperatorFiber_nonempty
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    (tangentAlignmentOperatorFiber g x₀ p₀).Nonempty := by
  rcases tangentAlignment_nonempty g x₀ p₀ with ⟨L⟩
  exact ⟨L.toContinuousLinearEquiv.toContinuousLinearMap,
    tangentAlignment_toContinuousLinearMap_mem_operatorFiber g x₀ p₀ L⟩

/-- Every operator in the metric-equation fiber is injective.  This is the
point where positive-definiteness rules out the extra singular operators that
would otherwise occur in a closed algebraic locus. -/
theorem tangentAlignmentOperatorFiber_injective
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    {A : E →L[ℝ] E} (hA : A ∈ tangentAlignmentOperatorFiber g x₀ p₀) :
    Function.Injective A := by
  intro u v huv
  rw [← sub_eq_zero]
  by_contra huv₀
  have hpos : 0 < sourceAnchorChartMetric g x₀ (u - v) (u - v) :=
    sourceAnchorChartMetric_pos g x₀ huv₀
  have hmetric := hA (u - v) (u - v)
  have hmap : A (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hzero : sourceAnchorChartMetric g x₀ (u - v) (u - v) = 0 := by
    rw [hmap] at hmetric
    simpa using hmetric.symm
  exact (ne_of_gt hpos) hzero

/-- In finite dimension, an operator in the fixed-anchor metric fiber is
automatically bijective. -/
theorem tangentAlignmentOperatorFiber_bijective
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    {A : E →L[ℝ] E} (hA : A ∈ tangentAlignmentOperatorFiber g x₀ p₀) :
    Function.Bijective A := by
  have hinj : Function.Injective A :=
    tangentAlignmentOperatorFiber_injective g x₀ p₀ hA
  have hinj' : Function.Injective A.toLinearMap := hinj
  have hsurj' : Function.Surjective A.toLinearMap :=
    LinearMap.injective_iff_surjective.mp hinj'
  exact ⟨hinj, hsurj'⟩

/-- Reconstruct the algebraic tangent alignment carried by an operator in the
fixed-anchor metric fiber. -/
def tangentAlignmentOfOperator
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (A : E →L[ℝ] E) (hA : A ∈ tangentAlignmentOperatorFiber g x₀ p₀) :
    TangentAlignment g x₀ p₀ :=
  { LinearEquiv.ofBijective A.toLinearMap
      (tangentAlignmentOperatorFiber_bijective g x₀ p₀ hA) with
    map_app' := by
      intro u v
      exact hA u v }

@[simp]
theorem tangentAlignmentOfOperator_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (A : E →L[ℝ] E) (hA : A ∈ tangentAlignmentOperatorFiber g x₀ p₀)
    (v : E) :
    tangentAlignmentOfOperator g x₀ p₀ A hA v = A v :=
  rfl

/-- The canonical map from genuine tangent alignments into the compact
operator fiber. -/
def tangentAlignmentOperatorFiberMap
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    TangentAlignment g x₀ p₀ → tangentAlignmentOperatorFiber g x₀ p₀ :=
  fun L => ⟨L.toContinuousLinearEquiv.toContinuousLinearMap,
    tangentAlignment_toContinuousLinearMap_mem_operatorFiber g x₀ p₀ L⟩

theorem tangentAlignmentOperatorFiberMap_injective
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    Function.Injective (tangentAlignmentOperatorFiberMap g x₀ p₀) := by
  intro L K hLK
  apply DFunLike.coe_injective
  funext v
  have hmaps := congr_arg Subtype.val hLK
  exact DFunLike.congr_fun hmaps v

/-- No points were added by passing to the closed operator locus: every point
of the subtype comes from a genuine tangent alignment. -/
theorem tangentAlignmentOperatorFiberMap_surjective
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    Function.Surjective (tangentAlignmentOperatorFiberMap g x₀ p₀) := by
  intro A
  let L : TangentAlignment g x₀ p₀ :=
    tangentAlignmentOfOperator g x₀ p₀ A.1 A.2
  refine ⟨L, ?_⟩
  apply Subtype.ext
  ext v
  rfl

/-- Genuine tangent alignments are in bijection with the compact operator
fiber that represents them. -/
def tangentAlignmentOperatorFiberEquiv
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    TangentAlignment g x₀ p₀ ≃ tangentAlignmentOperatorFiber g x₀ p₀ :=
  Equiv.ofBijective (tangentAlignmentOperatorFiberMap g x₀ p₀)
    ⟨tangentAlignmentOperatorFiberMap_injective g x₀ p₀,
      tangentAlignmentOperatorFiberMap_surjective g x₀ p₀⟩

/-- Metric-preservation equations are closed in the operator-norm topology. -/
theorem isClosed_tangentAlignmentOperatorFiber
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    IsClosed (tangentAlignmentOperatorFiber g x₀ p₀) := by
  rw [show tangentAlignmentOperatorFiber g x₀ p₀ =
      ⋂ u, ⋂ v,
        {A : E →L[ℝ] E |
          targetAnchorChartMetric p₀ (A u) (A v) =
            sourceAnchorChartMetric g x₀ u v} by
    ext A
    simp only [tangentAlignmentOperatorFiber, mem_setOf_eq, mem_iInter]]
  refine isClosed_iInter fun u => isClosed_iInter fun v => ?_
  apply isClosed_eq
  · exact (targetAnchorChartMetric p₀).continuous₂.comp₂
      (ContinuousLinearMap.apply ℝ E u).continuous
      (ContinuousLinearMap.apply ℝ E v).continuous
  · exact continuous_const

/-- The operators satisfying the fixed-anchor metric equations have uniformly
bounded operator norm. -/
theorem isBounded_tangentAlignmentOperatorFiber
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    Bornology.IsBounded (tangentAlignmentOperatorFiber g x₀ p₀) := by
  let b := Module.finBasis ℝ E
  let L₀ : TangentAlignment g x₀ p₀ :=
    Classical.choice (tangentAlignment_nonempty g x₀ p₀)
  let Jalg := targetEuclideanAlignment p₀
  let J : E ≃L[ℝ] E := targetEuclideanContinuousLinearEquiv p₀
  let Jinv : E →L[ℝ] E := J.symm.toContinuousLinearMap
  let B : ℝ := ∑ i, ‖Jinv‖ * ‖J (L₀ (b i))‖
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨C, _hC, hbasis⟩ := b.exists_opNorm_le (F := E)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C * B, ?_⟩
  intro A hA
  apply hbasis hB
  intro i
  have hsq :
      ‖J (A (b i))‖ ^ 2 = ‖J (L₀ (b i))‖ ^ 2 := by
    calc
      ‖J (A (b i))‖ ^ 2 =
          euclideanBilinForm (J (A (b i))) (J (A (b i))) := by
            rw [euclideanBilinForm_apply, innerSL_apply_apply,
              real_inner_self_eq_norm_sq]
      _ = targetAnchorChartMetric p₀ (A (b i)) (A (b i)) := by
            simpa only [J, targetEuclideanContinuousLinearEquiv_apply,
              targetAnchorBilinForm_apply] using
              Jalg.map_app' (A (b i)) (A (b i))
      _ = sourceAnchorChartMetric g x₀ (b i) (b i) := hA (b i) (b i)
      _ = targetAnchorChartMetric p₀ (L₀ (b i)) (L₀ (b i)) :=
            (L₀.map_app (b i) (b i)).symm
      _ = euclideanBilinForm (J (L₀ (b i))) (J (L₀ (b i))) := by
            simpa only [J, targetEuclideanContinuousLinearEquiv_apply,
              targetAnchorBilinForm_apply] using
              (Jalg.map_app' (L₀ (b i)) (L₀ (b i))).symm
      _ = ‖J (L₀ (b i))‖ ^ 2 := by
            rw [euclideanBilinForm_apply, innerSL_apply_apply,
              real_inner_self_eq_norm_sq]
  have hnorm : ‖J (A (b i))‖ = ‖J (L₀ (b i))‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  calc
    ‖A (b i)‖ = ‖J.symm (J (A (b i)))‖ := by simp
    _ ≤ ‖Jinv‖ * ‖J (A (b i))‖ := Jinv.le_opNorm _
    _ = ‖Jinv‖ * ‖J (L₀ (b i))‖ := by rw [hnorm]
    _ ≤ B := by
      dsimp only [B]
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (norm_nonneg Jinv) (norm_nonneg (J (L₀ (b j)))))
        (Finset.mem_univ i)

/-- Heine-Borel compactness of the fixed-anchor tangent-alignment operator
fiber. -/
theorem isCompact_tangentAlignmentOperatorFiber
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    IsCompact (tangentAlignmentOperatorFiber g x₀ p₀) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_tangentAlignmentOperatorFiber g x₀ p₀)
    (isBounded_tangentAlignmentOperatorFiber g x₀ p₀)

/-- The operator-fiber subtype is a compact parameter space for genuine
tangent alignments at the fixed pair of anchors. -/
instance tangentAlignmentOperatorFiber_compactSpace
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    CompactSpace (tangentAlignmentOperatorFiber g x₀ p₀) :=
  isCompact_iff_compactSpace.mp
    (isCompact_tangentAlignmentOperatorFiber g x₀ p₀)

/-- Consumer form of fixed-anchor compactness: all genuine tangent alignments
have operator norm bounded by one positive constant. -/
theorem exists_pos_uniform_tangentAlignment_operatorNorm_bound
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    ∃ C > (0 : ℝ), ∀ L : TangentAlignment g x₀ p₀,
      ‖L.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ C := by
  rcases
      (isBounded_tangentAlignmentOperatorFiber g x₀ p₀).exists_pos_norm_le with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro L
  exact hbound L.toContinuousLinearEquiv.toContinuousLinearMap
    (tangentAlignment_toContinuousLinearMap_mem_operatorFiber g x₀ p₀ L)

/-- The inverse operators of all genuine fixed-anchor tangent alignments are
also uniformly bounded.  The proof compares their values on one finite basis
after Euclideanizing the fixed source metric. -/
theorem exists_pos_uniform_tangentAlignment_inverseOperatorNorm_bound
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    ∃ C > (0 : ℝ), ∀ L : TangentAlignment g x₀ p₀,
      ‖L.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ C := by
  let b := Module.finBasis ℝ E
  let L₀ : TangentAlignment g x₀ p₀ :=
    Classical.choice (tangentAlignment_nonempty g x₀ p₀)
  let L₀inv : E →L[ℝ] E :=
    L₀.toContinuousLinearEquiv.symm.toContinuousLinearMap
  let Jalg := sourceEuclideanAlignment g x₀
  let J : E ≃L[ℝ] E := sourceEuclideanContinuousLinearEquiv g x₀
  let Jinv : E →L[ℝ] E := J.symm.toContinuousLinearMap
  let B : ℝ := ∑ i, ‖Jinv‖ * ‖J (L₀inv (b i))‖
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨C, hC, hbasis⟩ := b.exists_opNorm_le (F := E)
  refine ⟨C * B + 1, by nlinarith, ?_⟩
  intro L
  let Linv : E →L[ℝ] E :=
    L.toContinuousLinearEquiv.symm.toContinuousLinearMap
  have hcore : ‖Linv‖ ≤ C * B := by
    apply hbasis hB
    intro i
    have hLinv_apply : L (Linv (b i)) = b i := by
      change L.toContinuousLinearEquiv
          (L.toContinuousLinearEquiv.symm (b i)) = b i
      exact L.toContinuousLinearEquiv.apply_symm_apply (b i)
    have hL₀inv_apply : L₀ (L₀inv (b i)) = b i := by
      change L₀.toContinuousLinearEquiv
          (L₀.toContinuousLinearEquiv.symm (b i)) = b i
      exact L₀.toContinuousLinearEquiv.apply_symm_apply (b i)
    have hsq :
        ‖J (Linv (b i))‖ ^ 2 = ‖J (L₀inv (b i))‖ ^ 2 := by
      calc
        ‖J (Linv (b i))‖ ^ 2 =
            euclideanBilinForm (J (Linv (b i))) (J (Linv (b i))) := by
              rw [euclideanBilinForm_apply, innerSL_apply_apply,
                real_inner_self_eq_norm_sq]
        _ = sourceAnchorChartMetric g x₀ (Linv (b i)) (Linv (b i)) := by
              simpa only [J, sourceEuclideanContinuousLinearEquiv_apply,
                sourceAnchorBilinForm_apply] using
                Jalg.map_app' (Linv (b i)) (Linv (b i))
        _ = targetAnchorChartMetric p₀ (b i) (b i) := by
              have hmetric := L.map_app (Linv (b i)) (Linv (b i))
              rw [hLinv_apply] at hmetric
              exact hmetric.symm
        _ = sourceAnchorChartMetric g x₀ (L₀inv (b i)) (L₀inv (b i)) := by
              have hmetric := L₀.map_app (L₀inv (b i)) (L₀inv (b i))
              rw [hL₀inv_apply] at hmetric
              exact hmetric
        _ = euclideanBilinForm (J (L₀inv (b i))) (J (L₀inv (b i))) := by
              simpa only [J, sourceEuclideanContinuousLinearEquiv_apply,
                sourceAnchorBilinForm_apply] using
                (Jalg.map_app' (L₀inv (b i)) (L₀inv (b i))).symm
        _ = ‖J (L₀inv (b i))‖ ^ 2 := by
              rw [euclideanBilinForm_apply, innerSL_apply_apply,
                real_inner_self_eq_norm_sq]
    have hnorm : ‖J (Linv (b i))‖ = ‖J (L₀inv (b i))‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    calc
      ‖Linv (b i)‖ = ‖J.symm (J (Linv (b i)))‖ := by simp
      _ ≤ ‖Jinv‖ * ‖J (Linv (b i))‖ := Jinv.le_opNorm _
      _ = ‖Jinv‖ * ‖J (L₀inv (b i))‖ := by rw [hnorm]
      _ ≤ B := by
        dsimp only [B]
        exact Finset.single_le_sum
          (fun j _ =>
            mul_nonneg (norm_nonneg Jinv) (norm_nonneg (J (L₀inv (b j)))))
          (Finset.mem_univ i)
  change ‖Linv‖ ≤ C * B + 1
  exact hcore.trans (by linarith)

end CartanMap
end Poincare
