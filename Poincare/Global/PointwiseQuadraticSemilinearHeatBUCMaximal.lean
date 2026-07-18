import Poincare.Global.QuadraticSemilinearHeatBUCMaximal
import Poincare.Global.PointwiseQuadraticSemilinearHeatBUC

/-!
# Maximal lifespan for pointwise fiber-quadratic heat equations

This module instantiates the compatible-family continuation and blow-up
theory with a bounded bilinear map on the finite-dimensional fiber.  The
constant is explicit and sharp at this abstraction level: the fiber operator
norm `‖B‖`.  Thus coordinate tensor contractions can use the maximal-lifespan
API without first repackaging a separate `BUC` bilinear estimate.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- The explicit nonnegative quadratic constant supplied by a fiber bilinear
operator. -/
def pointwiseBUCFiberBilinearNorm
    (B : F →L[ℝ] F →L[ℝ] F) : ℝ≥0 :=
  ⟨‖B‖, norm_nonneg B⟩

@[simp, norm_cast]
theorem coe_pointwiseBUCFiberBilinearNorm
    (B : F →L[ℝ] F →L[ℝ] F) :
    (pointwiseBUCFiberBilinearNorm B : ℝ) = ‖B‖ :=
  rfl

/-- The lifted pointwise bilinear map obeys the abstract quadratic hypothesis
with the explicit fiber operator norm. -/
theorem norm_pointwiseBUCBilinear_apply_le_fiberNorm
    (B : F →L[ℝ] F →L[ℝ] F) (f : BUC) :
    ‖pointwiseBUCBilinear (E := E) B f‖ ≤
      (pointwiseBUCFiberBilinearNorm B : ℝ) * ‖f‖ := by
  exact norm_pointwiseBUCBilinear_apply_le (E := E) B f

/-- Compatible compact family for the pointwise equation
`u_t = Δu + B(u,u)`. -/
abbrev PointwiseQuadraticSemilinearHeatBUCCompactFamily
    (Tmax : ℝ≥0) (B : F →L[ℝ] F →L[ℝ] F) (u₀ : BUC) :=
  QuadraticSemilinearHeatBUCCompactFamily Tmax
    (pointwiseBUCBilinear (E := E) B) u₀

/-- The uniform bounded-data lifespan specialized to the explicit fiber
operator norm. -/
def pointwiseQuadraticBUCUniformLifespan
    (B : F →L[ℝ] F →L[ℝ] F) (K : ℝ≥0) : ℝ≥0 :=
  quadraticBUCUniformLifespan (pointwiseBUCFiberBilinearNorm B) K

theorem pointwiseQuadraticBUCUniformLifespan_pos
    (B : F →L[ℝ] F →L[ℝ] F) (K : ℝ≥0) :
    0 < pointwiseQuadraticBUCUniformLifespan B K :=
  quadraticBUCUniformLifespan_pos _ _

/-- Every uniformly norm-bounded pointwise-quadratic family has a genuine
strict compatible extension. -/
theorem exists_pointwiseQuadraticSemilinearHeatBUC_strictExtension_of_bounded
    (Tmax K : ℝ≥0) (hTmax : 0 < Tmax)
    (B : F →L[ℝ] F →L[ℝ] F) (u₀ : BUC)
    (fam : PointwiseQuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hbound : fam.IsNormBoundedBy K) :
    ∃ (H : ℝ≥0)
      (fam' : PointwiseQuadraticSemilinearHeatBUCCompactFamily H B u₀),
      fam.IsStrictExtension fam' := by
  exact exists_strictExtension_of_isNormBoundedBy
    (E := E) (F := F) Tmax K hTmax
    (pointwiseBUCBilinear (E := E) B)
    (pointwiseBUCFiberBilinearNorm B)
    (norm_pointwiseBUCBilinear_apply_le_fiberNorm (E := E) B)
    u₀ fam hbound

/-- A maximal pointwise fiber-quadratic compatible family has unbounded
`BUC` norm on its finite lifespan. -/
theorem pointwiseQuadraticSemilinearHeatBUC_maximalTime_norm_unbounded
    (Tmax : ℝ≥0) (B : F →L[ℝ] F →L[ℝ] F) (u₀ : BUC)
    (fam : PointwiseQuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : QuadraticBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ := by
  exact quadraticSemilinearHeatBUC_maximalTime_norm_unbounded_of_maximal
    (E := E) (F := F) Tmax
    (pointwiseBUCBilinear (E := E) B)
    (pointwiseBUCFiberBilinearNorm B)
    (norm_pointwiseBUCBilinear_apply_le_fiberNorm (E := E) B)
    u₀ fam hmax

/-- Strong initial velocity of the pointwise fiber-quadratic equation. -/
def pointwiseQuadraticBUCInitialVelocity
    (B : F →L[ℝ] F →L[ℝ] F) (u₀ Au₀ : BUC) : BUC :=
  Au₀ + quadraticOfCLM (pointwiseBUCBilinear (E := E) B) u₀

@[simp]
theorem pointwiseQuadraticBUCInitialVelocity_apply
    (B : F →L[ℝ] F →L[ℝ] F) (u₀ Au₀ : BUC) (x : E) :
    ((pointwiseQuadraticBUCInitialVelocity (E := E) B u₀ Au₀ : BUC) :
        E →ᵇ F) x =
      ((Au₀ : E →ᵇ F) x) +
        B ((u₀ : E →ᵇ F) x) ((u₀ : E →ᵇ F) x) := by
  simp [pointwiseQuadraticBUCInitialVelocity,
    quadraticOfCLM_pointwiseBUCBilinear_apply]

/-- Every compact member of a compatible pointwise-quadratic family has the
expected strong right derivative at its common initial time whenever `u₀`
lies in the heat-generator domain. -/
theorem PointwiseQuadraticSemilinearHeatBUCCompactFamily.hasDerivWithinAt_zero
    (Tmax : ℝ≥0) (B : F →L[ℝ] F →L[ℝ] F) (u₀ Au₀ : BUC)
    (fam : PointwiseQuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) u₀ Au₀)
    (T : QuadraticBUCCompactTime Tmax) :
    HasDerivWithinAt
      (fun t : ℝ ↦ fam.path T
        (Set.projIcc 0 ((T : ℝ≥0) : ℝ) (T : ℝ≥0).property t))
      (pointwiseQuadraticBUCInitialVelocity (E := E) B u₀ Au₀)
      (Set.Icc 0 ((T : ℝ≥0) : ℝ)) 0 := by
  exact semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
    (E := E) (F := F) (T : ℝ≥0) u₀ Au₀
    (quadraticOfCLM (pointwiseBUCBilinear (E := E) B))
    (continuous_quadraticOfCLM (pointwiseBUCBilinear (E := E) B))
    (fam.path T) (fam.mild T) hu₀

end Poincare
