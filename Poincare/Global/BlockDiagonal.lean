import Poincare.Global.CorrectedRadial

/-!
# Block-diagonal positive-scale endpoint upgrade

This module is the two-scale variant of `ScaledUpgrade`.  The endpoint
pullback need not be a single positive scalar multiple of the anchor metric:
it is enough for the radial and transverse Gram blocks to carry separate
positive scalars.  The direct decomposition
`radialPart + transversePart = id` then gives injectivity of the endpoint CLM.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace BlockDiagonal

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

private theorem inv_smul_ne_zero {T : ℝ} (hT : T ≠ 0) {x : E3}
    (hx : x ≠ 0) :
    T⁻¹ • x ≠ 0 := by
  intro h
  have hx0 : x = 0 := by
    calc
      x = T • (T⁻¹ • x) := by
        simp [smul_smul, hT]
      _ = 0 := by
        simp [h]
  exact hx hx0

private theorem self_nonneg_of_posDef
    {S : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    (hSpos : ∀ {u : E3}, u ≠ 0 → 0 < S u u) (u : E3) :
    0 ≤ S u u := by
  by_cases hu : u = 0
  · simp [hu]
  · exact le_of_lt (hSpos hu)

private theorem radialPart_or_transversePart_ne_zero
    {S : E3 →L[ℝ] E3 →L[ℝ] ℝ} {v u : E3} (hu : u ≠ 0) :
    CartanPullback.radialPart S v u ≠ 0 ∨
      CartanPullback.transversePart S v u ≠ 0 := by
  by_cases hr : CartanPullback.radialPart S v u = 0
  · right
    intro ht
    apply hu
    calc
      u = CartanPullback.radialPart S v u + CartanPullback.transversePart S v u := by
        exact (CartanPullback.radialPart_add_transversePart S v u).symm
      _ = 0 := by
        simp [hr, ht]
  · exact Or.inl hr

/--
A continuous linear endomorphism whose pullback pairing is block-diagonal
with positive radial and transverse scales has trivial kernel.  The pairings
are stated on the rescaled blocks used by the Cartan endpoint consumers.
-/
theorem injective_of_rescaled_blockDiagonal_pullback_posDef
    {D : E3 →L[ℝ] E3} {G S : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    {v : E3} {T cr ct : ℝ}
    (hT : T ≠ 0) (hcr : 0 < cr) (hct : 0 < ct)
    (hSpos : ∀ {u : E3}, u ≠ 0 → 0 < S u u)
    (hPullback : ∀ u u' : E3,
      G (D u) (D u') =
        cr * S (T⁻¹ • CartanPullback.radialPart S v u)
          (T⁻¹ • CartanPullback.radialPart S v u') +
        ct * S (T⁻¹ • CartanPullback.transversePart S v u)
          (T⁻¹ • CartanPullback.transversePart S v u')) :
    Function.Injective D := by
  have hker : ∀ u : E3, D u = 0 → u = 0 := by
    intro u hDu
    by_contra hu
    let r : E3 := CartanPullback.radialPart S v u
    let t : E3 := CartanPullback.transversePart S v u
    have hzero :
        cr * S (T⁻¹ • r) (T⁻¹ • r) +
          ct * S (T⁻¹ • t) (T⁻¹ • t) = 0 := by
      have hpull := hPullback u u
      simpa [r, t, hDu] using hpull.symm
    have hsum_pos :
        0 <
          cr * S (T⁻¹ • r) (T⁻¹ • r) +
            ct * S (T⁻¹ • t) (T⁻¹ • t) := by
      have hparts :=
        radialPart_or_transversePart_ne_zero (S := S) (v := v) (u := u) hu
      cases hparts with
      | inl hr =>
          have hr' : T⁻¹ • r ≠ 0 := inv_smul_ne_zero hT hr
          have hleft : 0 < cr * S (T⁻¹ • r) (T⁻¹ • r) :=
            mul_pos hcr (hSpos hr')
          have hright : 0 ≤ ct * S (T⁻¹ • t) (T⁻¹ • t) :=
            mul_nonneg hct.le (self_nonneg_of_posDef hSpos (T⁻¹ • t))
          exact add_pos_of_pos_of_nonneg hleft hright
      | inr ht =>
          have ht' : T⁻¹ • t ≠ 0 := inv_smul_ne_zero hT ht
          have hleft : 0 ≤ cr * S (T⁻¹ • r) (T⁻¹ • r) :=
            mul_nonneg hcr.le (self_nonneg_of_posDef hSpos (T⁻¹ • r))
          have hright : 0 < ct * S (T⁻¹ • t) (T⁻¹ • t) :=
            mul_pos hct (hSpos ht')
          exact add_pos_of_nonneg_of_pos hleft hright
    exact (ne_of_gt hsum_pos) hzero
  intro u u' huu'
  apply sub_eq_zero.mp
  apply hker (u - u')
  simp [map_sub, huu']

/--
Positive block-diagonal pullback pairing upgrades an endpoint CLM to a
continuous linear equivalence with the same underlying continuous linear map.
-/
theorem exists_continuousLinearEquiv_of_rescaled_blockDiagonal_pullback_posDef
    {D : E3 →L[ℝ] E3} {G S : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    {v : E3} {T cr ct : ℝ}
    (hT : T ≠ 0) (hcr : 0 < cr) (hct : 0 < ct)
    (hSpos : ∀ {u : E3}, u ≠ 0 → 0 < S u u)
    (hPullback : ∀ u u' : E3,
      G (D u) (D u') =
        cr * S (T⁻¹ • CartanPullback.radialPart S v u)
          (T⁻¹ • CartanPullback.radialPart S v u') +
        ct * S (T⁻¹ • CartanPullback.transversePart S v u)
          (T⁻¹ • CartanPullback.transversePart S v u')) :
    ∃ A : E3 ≃L[ℝ] E3, (A : E3 →L[ℝ] E3) = D := by
  have hDinj : Function.Injective D :=
    injective_of_rescaled_blockDiagonal_pullback_posDef
      (D := D) (G := G) (S := S) (v := v) (T := T)
      hT hcr hct hSpos hPullback
  let Aₗ : E3 ≃ₗ[ℝ] E3 := LinearEquiv.ofInjectiveEndo D.toLinearMap hDinj
  refine ⟨Aₗ.toContinuousLinearEquiv, ?_⟩
  ext u
  simp [Aₗ]

/-- Source-anchor specialization of the block-diagonal positive upgrade. -/
theorem exists_continuousLinearEquiv_of_sourceAnchor_rescaled_blockDiagonal_pullback
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {D : E3 →L[ℝ] E3} {G : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    {v : E3} {T cr ct : ℝ}
    (hT : T ≠ 0) (hcr : 0 < cr) (hct : 0 < ct)
    (hPullback : ∀ u u' : E3,
      G (D u) (D u') =
        cr * CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u') +
        ct * CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v u)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v u')) :
    ∃ A : E3 ≃L[ℝ] E3, (A : E3 →L[ℝ] E3) = D :=
  exists_continuousLinearEquiv_of_rescaled_blockDiagonal_pullback_posDef
    (D := D) (G := G) (S := CartanMap.sourceAnchorChartMetric g x0)
    (v := v) (T := T) hT hcr hct
    (fun hu => CartanMap.sourceAnchorChartMetric_pos g x0 hu)
    hPullback

/-- Target-anchor specialization of the block-diagonal positive upgrade. -/
theorem exists_continuousLinearEquiv_of_targetAnchor_rescaled_blockDiagonal_pullback
    (p0 : RoundSphere3)
    {D : E3 →L[ℝ] E3} {G : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    {v : E3} {T cr ct : ℝ}
    (hT : T ≠ 0) (hcr : 0 < cr) (hct : 0 < ct)
    (hPullback : ∀ u u' : E3,
      G (D u) (D u') =
        cr * CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u') +
        ct * CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v u)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v u')) :
    ∃ A : E3 ≃L[ℝ] E3, (A : E3 →L[ℝ] E3) = D :=
  exists_continuousLinearEquiv_of_rescaled_blockDiagonal_pullback_posDef
    (D := D) (G := G) (S := CartanMap.targetAnchorChartMetric p0)
    (v := v) (T := T) hT hcr hct
    (fun hu => CartanMap.targetAnchorChartMetric_pos p0 hu)
    hPullback

/-- Hosted source endpoint CLM upgrade from a positive block-diagonal pullback. -/
theorem exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {Psi : E3 → ℝ → E3 × E3} {v : E3} {T cr ct : ℝ}
    (hadd : ∀ w w' : E3,
      (Psi (w + w') T).1 = (Psi w T).1 + (Psi w' T).1)
    (hsmul : ∀ (a : ℝ) (w : E3),
      (Psi (a • w) T).1 = a • (Psi w T).1)
    {G : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    (hT : T ≠ 0) (hcr : 0 < cr) (hct : 0 < ct)
    (hEndpointPullback : ∀ u u' : E3,
      G (Psi u T).1 (Psi u' T).1 =
        cr * CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u') +
        ct * CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v u)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v u')) :
    ∃ A : E3 ≃L[ℝ] E3,
      (A : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Psi) T hadd hsmul := by
  refine
    exists_continuousLinearEquiv_of_sourceAnchor_rescaled_blockDiagonal_pullback
      (g := g) (x0 := x0)
      (D := linearizedEndpointCLM (Ψ := Psi) T hadd hsmul) (G := G)
      (v := v) (T := T) hT hcr hct ?_
  intro u u'
  calc
    G (linearizedEndpointCLM (Ψ := Psi) T hadd hsmul u)
        (linearizedEndpointCLM (Ψ := Psi) T hadd hsmul u') =
      G (Psi u T).1 (Psi u' T).1 :=
        PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
          (G := G) (Ψ := Psi) (T := T) hadd hsmul u u'
    _ = cr * CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u') +
        ct * CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v u)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v u') :=
        hEndpointPullback u u'

/-- Hosted target endpoint CLM upgrade from a positive block-diagonal pullback. -/
theorem exists_continuousLinearEquiv_of_target_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
    (p0 : RoundSphere3)
    {Psi : E3 → ℝ → E3 × E3} {v : E3} {T cr ct : ℝ}
    (hadd : ∀ w w' : E3,
      (Psi (w + w') T).1 = (Psi w T).1 + (Psi w' T).1)
    (hsmul : ∀ (a : ℝ) (w : E3),
      (Psi (a • w) T).1 = a • (Psi w T).1)
    {G : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    (hT : T ≠ 0) (hcr : 0 < cr) (hct : 0 < ct)
    (hEndpointPullback : ∀ u u' : E3,
      G (Psi u T).1 (Psi u' T).1 =
        cr * CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u') +
        ct * CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v u)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v u')) :
    ∃ A : E3 ≃L[ℝ] E3,
      (A : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Psi) T hadd hsmul := by
  refine
    exists_continuousLinearEquiv_of_targetAnchor_rescaled_blockDiagonal_pullback
      (p0 := p0)
      (D := linearizedEndpointCLM (Ψ := Psi) T hadd hsmul) (G := G)
      (v := v) (T := T) hT hcr hct ?_
  intro u u'
  calc
    G (linearizedEndpointCLM (Ψ := Psi) T hadd hsmul u)
        (linearizedEndpointCLM (Ψ := Psi) T hadd hsmul u') =
      G (Psi u T).1 (Psi u' T).1 :=
        PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
          (G := G) (Ψ := Psi) (T := T) hadd hsmul u u'
    _ = cr * CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u') +
        ct * CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v u)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v u') :=
        hEndpointPullback u u'

/-- The time-radial scale is positive away from zero time. -/
theorem timeRadialScale_pos_of_ne_zero {T : ℝ} (hT : T ≠ 0) :
    0 < CorrectedRadial.timeRadialScale T := by
  rw [CorrectedRadial.timeRadialScale_unfold]
  exact sq_pos_of_ne_zero hT

/-- The speed-pinned transverse scale is positive on a shrunk sine interval. -/
theorem speedPinnedScale_pos_of_mul_mem_Ioo
    {speed T : ℝ} (hspeed : speed ≠ 0)
    (hAngle : speed * T ∈ Ioo (0 : ℝ) Real.pi) :
    0 < JacobiNormSystem.speedPinnedScale speed T := by
  rw [JacobiNormSystem.speedPinnedScale]
  exact
    mul_pos
      (sq_pos_of_pos (Real.sin_pos_of_mem_Ioo hAngle))
      (inv_pos.mpr (sq_pos_of_ne_zero hspeed))

/--
Construct the endpoint equivalences from the block-diagonal source/target
pullbacks, then feed the corrected two-scale Cartan pairing consumer.
-/
theorem exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_time_radial_block_diagonal_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x0 : M} {p0 : RoundSphere3}
    (L : CartanMap.TangentAlignment g x0 p0)
    {v : E3} {PsiS PsiT : E3 → ℝ → E3 × E3} {speed T : ℝ}
    {hadds : ∀ w w' : E3,
      (PsiS (w + w') T).1 = (PsiS w T).1 + (PsiS w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E3),
      (PsiS (c • w) T).1 = c • (PsiS w T).1}
    {haddt : ∀ w w' : E3,
      (PsiT (w + w') T).1 = (PsiT w T).1 + (PsiT w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E3),
      (PsiT (c • w) T).1 = c • (PsiT w T).1}
    (hT : T ≠ 0)
    (hRadialScale : 0 < CorrectedRadial.timeRadialScale T)
    (hTransverseScale : 0 < JacobiNormSystem.speedPinnedScale speed T)
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0)
        (linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0)
        (linearizedEndpointCLM (Ψ := PsiT) T haddt hsmult) (L v))
    (u u' : E3)
    (hSourceRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v a'))
    (hSourceRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) = 0)
    (hSourceTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v a'))
    (hTargetRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) a'))
    (hTargetRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) = 0)
    (hTargetTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) a')) :
    ∃ A B : E3 ≃L[ℝ] E3,
      (A : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls ∧
      (B : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := PsiT) T haddt hsmult ∧
      HasStrictFDerivAt
          (CartanDifferential.cartanChartMap g x0 p0 L)
          (CartanLocalIsometry.cartanChartDifferential L A B)
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v) ∧
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            (CartanLocalIsometry.cartanChartDifferential L A B u)
            (CartanLocalIsometry.cartanChartDifferential L A B u') =
          CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            u u' := by
  let Gs : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric g.inner x0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
  let Gt : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric roundSphereMetric3.inner p0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p0) (L v))
  have hSourceBlock :
      ∀ a a' : E3,
        Gs (PsiS a T).1 (PsiS a' T).1 =
          CorrectedRadial.timeRadialScale T *
              CartanMap.sourceAnchorChartMetric g x0
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.sourceAnchorChartMetric g x0) v a)
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.sourceAnchorChartMetric g x0) v a') +
            JacobiNormSystem.speedPinnedScale speed T *
              CartanMap.sourceAnchorChartMetric g x0
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a)
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a') := by
    intro a a'
    exact
      CorrectedRadial.source_hosted_rescaled_endpoint_pairing_eq_of_time_radial_transverse_blocks
        (g := g) (x0 := x0) (Psi := PsiS) (v := v) (T := T) (speed := speed)
        hadds hSourceRadialRadial hSourceRadialTransverse
        hSourceTransverseTransverse a a'
  have hTargetBlock :
      ∀ a a' : E3,
        Gt (PsiT a T).1 (PsiT a' T).1 =
          CorrectedRadial.timeRadialScale T *
              CartanMap.targetAnchorChartMetric p0
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a)
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a') +
            JacobiNormSystem.speedPinnedScale speed T *
              CartanMap.targetAnchorChartMetric p0
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a)
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a') := by
    intro a a'
    exact
      CorrectedRadial.target_hosted_rescaled_endpoint_pairing_eq_of_time_radial_transverse_blocks
        (p0 := p0) (Psi := PsiT) (v := L v) (T := T) (speed := speed)
        haddt hTargetRadialRadial hTargetRadialTransverse
        hTargetTransverseTransverse a a'
  rcases
      exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
        (g := g) (x0 := x0) (Psi := PsiS) (v := v) (T := T)
        hadds hsmuls (G := Gs) hT hRadialScale hTransverseScale hSourceBlock with
    ⟨A, hA⟩
  rcases
      exists_continuousLinearEquiv_of_target_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
        (p0 := p0) (Psi := PsiT) (v := L v) (T := T)
        haddt hsmult (G := Gt) hT hRadialScale hTransverseScale hTargetBlock with
    ⟨B, hB⟩
  refine ⟨A, B, hA, hB, ?_⟩
  refine
    CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_time_radial_decomposed_blocks
      (g := g) (x0 := x0) (p0 := p0) L
      (v := v) (A := A) (B := B) (PsiS := PsiS) (PsiT := PsiT)
      (speed := speed) (T := T)
      hA hB hvsrc ?_ ?_ u u'
      hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
      hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse
  · simpa [hA] using hsourceDeriv
  · simpa [hB] using htargetDeriv

/--
Angle-interval specialization of the block-diagonal adapter.  The hypotheses
`T ≠ 0`, `speed ≠ 0`, and `speed * T ∈ (0, pi)` provide the two positive
scales used by the upgrade.
-/
theorem exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_angle_time_radial_block_diagonal_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x0 : M} {p0 : RoundSphere3}
    (L : CartanMap.TangentAlignment g x0 p0)
    {v : E3} {PsiS PsiT : E3 → ℝ → E3 × E3} {speed T : ℝ}
    {hadds : ∀ w w' : E3,
      (PsiS (w + w') T).1 = (PsiS w T).1 + (PsiS w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E3),
      (PsiS (c • w) T).1 = c • (PsiS w T).1}
    {haddt : ∀ w w' : E3,
      (PsiT (w + w') T).1 = (PsiT w T).1 + (PsiT w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E3),
      (PsiT (c • w) T).1 = c • (PsiT w T).1}
    (hT : T ≠ 0) (hspeed : speed ≠ 0)
    (hAngle : speed * T ∈ Ioo (0 : ℝ) Real.pi)
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0)
        (linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0)
        (linearizedEndpointCLM (Ψ := PsiT) T haddt hsmult) (L v))
    (u u' : E3)
    (hSourceRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v a'))
    (hSourceRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) = 0)
    (hSourceTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v a'))
    (hTargetRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) a'))
    (hTargetRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) = 0)
    (hTargetTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) a')) :
    ∃ A B : E3 ≃L[ℝ] E3,
      (A : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls ∧
      (B : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := PsiT) T haddt hsmult ∧
      HasStrictFDerivAt
          (CartanDifferential.cartanChartMap g x0 p0 L)
          (CartanLocalIsometry.cartanChartDifferential L A B)
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v) ∧
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            (CartanLocalIsometry.cartanChartDifferential L A B u)
            (CartanLocalIsometry.cartanChartDifferential L A B u') =
          CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            u u' :=
  exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_time_radial_block_diagonal_blocks
    (g := g) (x0 := x0) (p0 := p0) L
    (v := v) (PsiS := PsiS) (PsiT := PsiT) (speed := speed) (T := T)
    hT (timeRadialScale_pos_of_ne_zero hT)
    (speedPinnedScale_pos_of_mul_mem_Ioo hspeed hAngle)
    hvsrc hsourceDeriv htargetDeriv u u'
    hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
    hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse

end BlockDiagonal
end Poincare
