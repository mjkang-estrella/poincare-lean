import Poincare.Global.BoundedUniformContinuousHeat
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# One-sided chain rule for moving evaluation of a BUC path

A path differentiable in the global uniform norm may be evaluated along a
moving spatial point.  At the base time, only the initial spatial function
needs a Frechet derivative.  This is the analytic chain rule needed to pass
from a reconstructed `BUC` metric path to an inverse-gauge trajectory.
-/

noncomputable section

open Filter Set Function
open scoped Topology BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- One-sided moving-evaluation chain rule for a path differentiable in the
global `BUC` norm.  The time variation is controlled uniformly, while the
spatial variation uses only the Frechet derivative of the initial datum. -/
theorem hasDerivWithinAt_buc_apply_moving
    {g : ℝ → BUC} {g' : BUC}
    {phi : ℝ → E} {phi' : E}
    {s : Set ℝ} {t₀ : ℝ}
    {D : E →L[ℝ] F}
    (hg : HasDerivWithinAt g g' s t₀)
    (hphi : HasDerivWithinAt phi phi' s t₀)
    (hspace : HasFDerivAt (((g t₀).1 : E →ᵇ F) : E → F)
      D (phi t₀)) :
    HasDerivWithinAt
      (fun t : ℝ ↦ ((g t).1 : E →ᵇ F) (phi t))
      (((g').1 : E →ᵇ F) (phi t₀) + D phi') s t₀ := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  let l : Filter ℝ := nhdsWithin t₀ (s \ {t₀})
  have hgSlope : Tendsto (slope g t₀) l (nhds g') := by
    simpa only [l] using
      (hasDerivWithinAt_iff_tendsto_slope.mp hg)
  have hphiT : Tendsto phi l (nhds (phi t₀)) := by
    exact hphi.continuousWithinAt.mono_left
      (nhdsWithin_mono t₀ (Set.diff_subset))
  have hgSlopeBCF : Tendsto
      (fun t : ℝ ↦ (slope g t₀ t).1)
      l (nhds g'.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hgSlope
  have htime : Tendsto
      (fun t : ℝ ↦ ((slope g t₀ t).1 : E →ᵇ F) (phi t))
      l (nhds (((g').1 : E →ᵇ F) (phi t₀))) := by
    exact (continuous_eval.tendsto (g'.1, phi t₀)).comp
      (hgSlopeBCF.prodMk_nhds hphiT)
  have hspatial : HasDerivWithinAt
      (fun t : ℝ ↦ ((g t₀).1 : E →ᵇ F) (phi t))
      (D phi') s t₀ :=
    hspace.comp_hasDerivWithinAt t₀ hphi
  have hspatialSlope : Tendsto
      (slope (fun t : ℝ ↦ ((g t₀).1 : E →ᵇ F) (phi t)) t₀)
      l (nhds (D phi')) := by
    simpa only [l] using
      (hasDerivWithinAt_iff_tendsto_slope.mp hspatial)
  have hsum := htime.add hspatialSlope
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change
    ((slope g t₀ t).1 : E →ᵇ F) (phi t) +
        slope (fun r : ℝ ↦ ((g t₀).1 : E →ᵇ F) (phi r)) t₀ t =
      slope (fun r : ℝ ↦ ((g r).1 : E →ᵇ F) (phi r)) t₀ t
  simp only [slope]
  change
    (t - t₀)⁻¹ •
          (((g t).1 : E →ᵇ F) (phi t) -
            ((g t₀).1 : E →ᵇ F) (phi t)) +
        (t - t₀)⁻¹ •
          (((g t₀).1 : E →ᵇ F) (phi t) -
            ((g t₀).1 : E →ᵇ F) (phi t₀)) =
      (t - t₀)⁻¹ •
        (((g t).1 : E →ᵇ F) (phi t) -
          ((g t₀).1 : E →ᵇ F) (phi t₀))
  rw [← smul_add]
  congr 1
  abel

end Poincare
