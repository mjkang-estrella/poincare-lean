import Poincare.Global.BoundedUniformContinuousHeat
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Pointwise bounded bilinear operations on `BUC`

A bounded bilinear operation on the finite-dimensional value space lifts to a
bounded bilinear operation on bounded uniformly continuous functions.  This
is the concrete bridge needed to turn pointwise tensor contractions into the
quadratic nonlinearities used by semilinear heat fixed-point arguments.
-/

noncomputable section

open Set Function
open scoped NNReal BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

private theorem pointwise_bilinear_norm_le
    (B : F →L[ℝ] F →L[ℝ] F) (f g : BUC) (x : E) :
    ‖B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x)‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  calc
    ‖B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x)‖
        ≤ ‖B ((f : E →ᵇ F) x)‖ * ‖(g : E →ᵇ F) x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖B‖ * ‖(f : E →ᵇ F) x‖) * ‖(g : E →ᵇ F) x‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm B ((f : E →ᵇ F) x)
    _ ≤ (‖B‖ * ‖f‖) * ‖g‖ := by
      gcongr
      · exact BoundedContinuousFunction.norm_coe_le_norm (f : E →ᵇ F) x
      · exact BoundedContinuousFunction.norm_coe_le_norm (g : E →ᵇ F) x

/-- Pointwise application of a bounded bilinear value-space map preserves
bounded uniform continuity. -/
def pointwiseBUCApply (B : F →L[ℝ] F →L[ℝ] F) (f g : BUC) : BUC := by
  let c : C(E, F) :=
    ⟨fun x ↦ B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x),
      ((B.continuous.comp (f : E →ᵇ F).continuous).clm_apply
        (g : E →ᵇ F).continuous)⟩
  let bound : ℝ := 2 * ‖B‖ * ‖f‖ * ‖g‖
  have hbound : ∀ x y : E, dist (c x) (c y) ≤ bound := by
    intro x y
    rw [dist_eq_norm]
    calc
      ‖B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x) -
          B ((f : E →ᵇ F) y) ((g : E →ᵇ F) y)‖
          ≤ ‖B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x)‖ +
            ‖B ((f : E →ᵇ F) y) ((g : E →ᵇ F) y)‖ := norm_sub_le _ _
      _ ≤ (‖B‖ * ‖f‖ * ‖g‖) + (‖B‖ * ‖f‖ * ‖g‖) :=
        add_le_add (pointwise_bilinear_norm_le B f g x)
          (pointwise_bilinear_norm_le B f g y)
      _ = bound := by ring
  let bcf : E →ᵇ F := BoundedContinuousFunction.mkOfBound c bound hbound
  have hpair : UniformContinuous
      (fun x : E ↦ ((f : E →ᵇ F) x, (g : E →ᵇ F) x)) :=
    f.property.prodMk g.property
  let s : Set (F × F) :=
    Metric.closedBall (0 : F) ‖f‖ ×ˢ Metric.closedBall (0 : F) ‖g‖
  have hfcompact : IsCompact (Metric.closedBall (0 : F) ‖f‖) :=
    isCompact_closedBall (0 : F) ‖f‖
  have hgcompact : IsCompact (Metric.closedBall (0 : F) ‖g‖) :=
    isCompact_closedBall (0 : F) ‖g‖
  have hs : IsCompact s := hfcompact.prod hgcompact
  have hBcont : Continuous (fun p : F × F ↦ B p.1 p.2) :=
    (B.continuous.comp continuous_fst).clm_apply continuous_snd
  have hBon : UniformContinuousOn (fun p : F × F ↦ B p.1 p.2) s :=
    hs.uniformContinuousOn_of_continuous hBcont.continuousOn
  have hmaps : MapsTo
      (fun x : E ↦ ((f : E →ᵇ F) x, (g : E →ᵇ F) x)) Set.univ s := by
    intro x _hx
    constructor
    · simpa [Metric.mem_closedBall, dist_zero_right] using
        BoundedContinuousFunction.norm_coe_le_norm (f : E →ᵇ F) x
    · simpa [Metric.mem_closedBall, dist_zero_right] using
        BoundedContinuousFunction.norm_coe_le_norm (g : E →ᵇ F) x
  have hucOn := hBon.comp hpair.uniformContinuousOn hmaps
  have huc : UniformContinuous
      (fun x : E ↦ B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x)) := by
    rw [← uniformContinuousOn_univ]
    simpa [Function.comp_def] using hucOn
  exact ⟨bcf, by simpa [bcf, c] using huc⟩

@[simp]
theorem pointwiseBUCApply_apply
    (B : F →L[ℝ] F →L[ℝ] F) (f g : BUC) (x : E) :
    ((pointwiseBUCApply B f g : BUC) : E →ᵇ F) x =
      B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x) := by
  rfl

/-- The lifted pointwise operation satisfies the sharp uniform bilinear
bound. -/
theorem norm_pointwiseBUCApply_le
    (B : F →L[ℝ] F →L[ℝ] F) (f g : BUC) :
    ‖pointwiseBUCApply B f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  change ‖((pointwiseBUCApply B f g : BUC) : E →ᵇ F)‖ ≤ _
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  exact fun x ↦ pointwise_bilinear_norm_le B f g x

/-- Pointwise bounded bilinear operation as an iterated continuous linear map
on `BUC`. -/
def pointwiseBUCBilinear (B : F →L[ℝ] F →L[ℝ] F) :
    BUC →L[ℝ] BUC →L[ℝ] BUC :=
  let L : BUC →ₗ[ℝ] BUC →ₗ[ℝ] BUC := LinearMap.mk₂ ℝ
    (pointwiseBUCApply B)
    (fun f f' g ↦ by
      apply Subtype.ext
      ext x
      simp only [pointwiseBUCApply_apply, Submodule.coe_add,
        BoundedContinuousFunction.add_apply, map_add,
        ContinuousLinearMap.add_apply])
    (fun c f g ↦ by
      apply Subtype.ext
      ext x
      simp only [pointwiseBUCApply_apply, SetLike.val_smul,
        BoundedContinuousFunction.smul_apply, map_smul,
        ContinuousLinearMap.smul_apply])
    (fun f g g' ↦ by
      apply Subtype.ext
      ext x
      simp only [pointwiseBUCApply_apply, Submodule.coe_add,
        BoundedContinuousFunction.add_apply, map_add])
    (fun c f g ↦ by
      apply Subtype.ext
      ext x
      simp only [pointwiseBUCApply_apply, SetLike.val_smul,
        BoundedContinuousFunction.smul_apply, map_smul])
  L.mkContinuous₂ ‖B‖ (fun f g ↦ norm_pointwiseBUCApply_le B f g)

@[simp]
theorem pointwiseBUCBilinear_apply
    (B : F →L[ℝ] F →L[ℝ] F) (f g : BUC) (x : E) :
    (((pointwiseBUCBilinear (E := E) B) f g : BUC) : E →ᵇ F) x =
      B ((f : E →ᵇ F) x) ((g : E →ᵇ F) x) := by
  exact pointwiseBUCApply_apply B f g x

/-- The outer operator bound in the form consumed by the quadratic local
existence theorem. -/
theorem norm_pointwiseBUCBilinear_apply_le
    (B : F →L[ℝ] F →L[ℝ] F) (f : BUC) :
    ‖pointwiseBUCBilinear (E := E) B f‖ ≤ ‖B‖ * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg B) (norm_nonneg f))
  intro g
  change ‖pointwiseBUCApply B f g‖ ≤ (‖B‖ * ‖f‖) * ‖g‖
  simpa [mul_assoc] using norm_pointwiseBUCApply_le B f g

end Poincare
