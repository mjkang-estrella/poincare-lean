import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

universe u v

open Set Filter
open scoped Topology ContDiff

namespace Poincare.DeTurckParameterJet

local instance parameterJetSecondBoundedSMul {E : Type u} {B : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] :
    IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] B) :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)

/-- An affine family on a common open domain has the corresponding affine spatial
two-jet, so its parameter derivative at zero is the two-jet of the variation. -/
theorem twoJet_hasDerivAt_of_affine_on_open :
    ∀ (E : Type u) (B : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (V : Set E), IsOpen V → ∀ z : E, z ∈ V →
    ∀ ε : ℝ, 0 < ε → ∀ (G : ℝ → E → B) (G0 F : E → B),
    ContDiffOn ℝ 2 G0 V → ContDiffOn ℝ 2 F V →
    (∀ s : ℝ, |s| < ε → ∀ y ∈ V, G s y = G0 y + s • F y) →
    HasDerivAt
      (fun s => ((G s z, fderiv ℝ (G s) z), fderiv ℝ (fderiv ℝ (G s)) z))
      ((F z, fderiv ℝ F z), fderiv ℝ (fderiv ℝ F) z) 0 := by
  intro E B _ _ _ _ V hV z hz ε hε G G0 F hG0 hF hAffine
  have hDG0 : ContDiffOn ℝ 1 (fderiv ℝ G0) V :=
    hG0.fderiv_of_isOpen hV (by norm_num)
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) V :=
    hF.fderiv_of_isOpen hV (by norm_num)
  have dG0 (y : E) (hy : y ∈ V) : DifferentiableAt ℝ G0 y :=
    (hG0.differentiableOn (by norm_num) y hy).differentiableAt (hV.mem_nhds hy)
  have dF (y : E) (hy : y ∈ V) : DifferentiableAt ℝ F y :=
    (hF.differentiableOn (by norm_num) y hy).differentiableAt (hV.mem_nhds hy)
  have ddG0 : DifferentiableAt ℝ (fderiv ℝ G0) z :=
    (hDG0.differentiableOn (by norm_num) z hz).differentiableAt (hV.mem_nhds hz)
  have ddF : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hDF.differentiableOn (by norm_num) z hz).differentiableAt (hV.mem_nhds hz)
  have hjets (s : ℝ) (hs : |s| < ε) :
      fderiv ℝ (G s) z = fderiv ℝ G0 z + s • fderiv ℝ F z ∧
      fderiv ℝ (fderiv ℝ (G s)) z =
        fderiv ℝ (fderiv ℝ G0) z + s • fderiv ℝ (fderiv ℝ F) z := by
    have hEq : G s =ᶠ[𝓝 z] (fun y => G0 y + s • F y) := by
      filter_upwards [hV.mem_nhds hz] with y hy
      exact hAffine s hs y hy
    have hFirst : fderiv ℝ (G s) =ᶠ[𝓝 z]
        (fun y => fderiv ℝ G0 y + s • fderiv ℝ F y) := by
      refine (hEq.fderiv (𝕜 := ℝ)).trans ?_
      filter_upwards [hV.mem_nhds hz] with y hy
      rw [fderiv_fun_add (dG0 y hy) ((dF y hy).fun_const_smul s),
        fderiv_fun_const_smul (dF y hy) s]
    constructor
    · exact hFirst.eq_of_nhds
    · rw [hFirst.fderiv_eq,
        fderiv_fun_add ddG0 (ddF.fun_const_smul s), fderiv_fun_const_smul ddF s]
  have hS : ∀ᶠ s : ℝ in 𝓝 0, |s| < ε :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hε)
  have hv : HasDerivAt (fun s : ℝ => G0 z + s • F z) (F z) 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const (F z)).const_add (G0 z)
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ G0 z + s • fderiv ℝ F z)
      (fderiv ℝ F z) 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const (fderiv ℝ F z)).const_add (fderiv ℝ G0 z)
  have hdd : HasDerivAt (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ G0) z + s • fderiv ℝ (fderiv ℝ F) z)
      (fderiv ℝ (fderiv ℝ F) z) 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const (fderiv ℝ (fderiv ℝ F) z)).const_add
        (fderiv ℝ (fderiv ℝ G0) z)
  have hCurve : HasDerivAt
      (fun s : ℝ => ((G0 z + s • F z, fderiv ℝ G0 z + s • fderiv ℝ F z),
        fderiv ℝ (fderiv ℝ G0) z + s • fderiv ℝ (fderiv ℝ F) z))
      ((F z, fderiv ℝ F z), fderiv ℝ (fderiv ℝ F) z) 0 :=
    (hv.prodMk (G := E →L[ℝ] B) hd).prodMk (G := E →L[ℝ] E →L[ℝ] B) hdd
  refine hCurve.congr_of_eventuallyEq (𝕜 := ℝ)
    (F := (B × (E →L[ℝ] B)) × (E →L[ℝ] E →L[ℝ] B)) ?_
  filter_upwards [hS] with s hs
  rw [hAffine s hs z hz, (hjets s hs).1, (hjets s hs).2]

end Poincare.DeTurckParameterJet
