import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Differentiating a pullback metric germ

This module isolates the calculus core of the `hdiff` producer: an eventual
equality of scalar pullback functions has equal Frechet derivatives, and the
left derivative expands by the chain rule through the base map and the two
moving vector slots.
-/

noncomputable section

open Filter
open scoped Topology

namespace Poincare
namespace GeodesicTransport

/--
Differentiating an eventual metric-pullback identity gives the `hdiff` shape
used by the transported-Christoffel compatibility algebra.

Here `G0` is the source metric family, `G1` the target metric family, `sigma` the
base transition, and `D` its first-derivative field.  The hypothesis `hpull`
is the germ identity
`G1 (sigma q) (D q a) (D q b) = G0 q a b`; differentiating it at `z` yields the
three-term chain-rule expansion on the left.
-/
theorem differentiated_pullback_hdiff_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G0 G1 : E → E →L[ℝ] E →L[ℝ] ℝ) (sigma : E → E)
    (D : E → E →L[ℝ] E) {z : E}
    (hsigma : HasFDerivAt sigma (D z) z)
    (hD : HasFDerivAt D (fderiv ℝ D z) z)
    (hG0 : HasFDerivAt G0 (fderiv ℝ G0 z) z)
    (hG1 : HasFDerivAt G1 (fderiv ℝ G1 (sigma z)) (sigma z))
    (hpull : ∀ a b : E,
      (fun q : E => G1 (sigma q) (D q a) (D q b)) =ᶠ[𝓝 z]
        (fun q : E => G0 q a b)) :
    ∀ e a b : E,
      ((fderiv ℝ G1 (sigma z) (D z e)) (D z a) (D z b)) +
        G1 (sigma z) ((fderiv ℝ D z e) a) (D z b) +
        G1 (sigma z) (D z a) ((fderiv ℝ D z e) b) =
      ((fderiv ℝ G0 z e) a b) := by
  intro e a b
  let B : E →L[ℝ] E →L[ℝ] E := fderiv ℝ D z
  have hDa : HasFDerivAt (fun q : E => D q a) (B.flip a) z := by
    simpa [B] using hD.clm_apply (hasFDerivAt_const (x := z) (c := a))
  have hDb : HasFDerivAt (fun q : E => D q b) (B.flip b) z := by
    simpa [B] using hD.clm_apply (hasFDerivAt_const (x := z) (c := b))
  have hGsigma : HasFDerivAt (fun q : E => G1 (sigma q))
      ((fderiv ℝ G1 (sigma z)).comp (D z)) z := by
    simpa [Function.comp_def] using
      (HasFDerivAt.comp (𝕜 := ℝ) (f := sigma) (f' := D z)
        (g := G1) (g' := fderiv ℝ G1 (sigma z)) z hG1 hsigma)
  have hGsigmaDa : HasFDerivAt (fun q : E => G1 (sigma q) (D q a))
      ((G1 (sigma z)).comp (B.flip a) +
        ((fderiv ℝ G1 (sigma z)).comp (D z)).flip (D z a)) z := by
    simpa [B] using hGsigma.clm_apply hDa
  have hleft : HasFDerivAt
      (fun q : E => G1 (sigma q) (D q a) (D q b))
      ((G1 (sigma z) (D z a)).comp (B.flip b) +
        (((G1 (sigma z)).comp (B.flip a) +
          ((fderiv ℝ G1 (sigma z)).comp (D z)).flip (D z a)).flip (D z b))) z := by
    simpa [B] using hGsigmaDa.clm_apply hDb
  have hright : HasFDerivAt (fun q : E => G0 q a b)
      (((fderiv ℝ G0 z).flip a).flip b) z := by
    have hG0a : HasFDerivAt (fun q : E => G0 q a)
        ((fderiv ℝ G0 z).flip a) z := by
      simpa using hG0.clm_apply (hasFDerivAt_const (x := z) (c := a))
    simpa using hG0a.clm_apply (hasFDerivAt_const (x := z) (c := b))
  have hderiv_eq :
      fderiv ℝ (fun q : E => G1 (sigma q) (D q a) (D q b)) z e =
        fderiv ℝ (fun q : E => G0 q a b) z e := by
    exact congrArg (fun L : E →L[ℝ] ℝ => L e)
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (hpull a b))
  have hleft_eval :
      fderiv ℝ (fun q : E => G1 (sigma q) (D q a) (D q b)) z e =
        G1 (sigma z) (D z a) (B e b) +
          (G1 (sigma z) (B e a) (D z b) +
            (fderiv ℝ G1 (sigma z) (D z e)) (D z a) (D z b)) := by
    rw [hleft.fderiv]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  have hright_eval :
      fderiv ℝ (fun q : E => G0 q a b) z e =
        (fderiv ℝ G0 z e) a b := by
    rw [hright.fderiv]
    rfl
  rw [hleft_eval, hright_eval] at hderiv_eq
  simpa [B, add_assoc, add_comm, add_left_comm] using hderiv_eq

end GeodesicTransport
end Poincare
