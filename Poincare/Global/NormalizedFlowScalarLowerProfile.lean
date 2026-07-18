import Poincare.Global.HamiltonScalarNegativeBarrier
import Poincare.Global.NormalizedFlowScalarRegularity

/-!
# Positive scalar lower profiles for normalized Ricci flow

For volume-normalized Ricci flow the scalar equation contains the spatially
constant damping term

`-(2 / 3) * meanScalar * R`.

Consequently an initially positive scalar curvature does not by itself give a
time-independent positive floor.  The natural preserved quantity uses the
normalization integrating factor.  This file proves the corresponding strict
parabolic comparison and records the precise extra condition under which it
does become a uniform positive floor: the normalization primitive must be
bounded above.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/-- The pointwise scalar equation for three-dimensional volume-normalized
Ricci flow. -/
def SatisfiesNormalizedHamiltonScalarEvolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) (x : M)
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1] :
    Prop :=
  HasDerivAt (fun s ↦ (gt s).scalarAt x)
    ((gt t).laplacianAt (fun y ↦ (gt t).scalarAt y) x +
      2 * (gt t).ricciNormSqAt x -
      (2 / 3 : ℝ) * meanScalar (gt t) * (gt t).scalarAt x) t

/-- The normalized metric equation plus the assembled Lichnerowicz scalar
variation proves the actual normalized scalar equation. -/
theorem satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t y)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt) :
    SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x := by
  have hScalarTwo : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t).scalarAt z) y :=
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      hFlow (hLichnerowicz.timeVariationEntries t)
  have hDerivative := hLichnerowicz.hasDerivAt_scalar_stokes t x
  rw [scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt_of_normalizedFlow
      hFlow (by norm_num) hScalarTwo,
    metricVariationRicciPairingAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      (hFlow x)] at hDerivative
  unfold SatisfiesNormalizedHamiltonScalarEvolutionAt
  convert hDerivative using 1
  ring

/-- Strict positivity of scalar curvature on one compact slice has a uniform
positive numerical floor. -/
theorem exists_pos_scalar_floor_of_forall_scalarAt_pos
    [Nonempty M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hScalarPos : ∀ x : M, 0 < g.scalarAt x) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ x : M, rho ≤ g.scalarAt x := by
  obtain ⟨xmin, _hxmin, hmin⟩ :=
    isCompact_univ.exists_isMinOn
      (Set.univ_nonempty)
      (fun y _ ↦ (scalarAt_continuous g).continuousAt.continuousWithinAt)
  exact ⟨g.scalarAt xmin, hScalarPos xmin, fun x ↦ hmin trivial⟩

/-- Strict comparison with any positive solution of the scalar normalization
ODE `phi' = -(2/3) meanScalar * phi` on one compact forward interval.

The positive `2 |Ric|²` reaction leaves a strictly positive `phi²` remainder
after factorization, so the strict minimum principle applies without an a
priori upper bound for scalar curvature or mean scalar curvature. -/
theorem normalizedFlow_scalarAt_gt_of_normalization_profile
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {t0 T : ℝ}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hT : 0 ≤ T)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt (t0 + tau)).scalarAt x))
    (hScalarEvolution : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
    (hScalarTwo : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).scalarAt y) x)
    (phi : ℝ → ℝ)
    (hphiContinuous : Continuous phi)
    (hphiPos : ∀ tau ∈ Icc (0 : ℝ) T, 0 < phi tau)
    (hphiDerivative : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivAt phi
        (-(2 / 3 : ℝ) * meanScalar (gt (t0 + tau)) * phi tau) tau)
    (hInitial : ∀ x : M, phi 0 < (gt t0).scalarAt x) :
    ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      phi tau < (gt (t0 + tau)).scalarAt x := by
  let a : ℝ := 2 / 3
  let R : ℝ → M → ℝ := fun tau x ↦ (gt (t0 + tau)).scalarAt x
  let r : ℝ → ℝ := fun tau ↦ meanScalar (gt (t0 + tau))
  let R' : ℝ → M → ℝ := fun tau x ↦
    (gt (t0 + tau)).laplacianAt (R tau) x +
      2 * (gt (t0 + tau)).ricciNormSqAt x -
      a * r tau * R tau x
  have ha : 0 < a := by norm_num [a]
  have hRd : ∀ x : M, ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' tau x) tau := by
    intro x tau htau
    have hbase : HasDerivAt (fun s ↦ (gt s).scalarAt x)
        (R' tau x) (t0 + tau) := by
      simpa [SatisfiesNormalizedHamiltonScalarEvolutionAt, a, R, r, R'] using
        hScalarEvolution tau htau x
    have hshift : HasDerivAt (fun s : ℝ ↦ t0 + s) 1 tau := by
      simpa using (hasDerivAt_id tau).const_add t0
    simpa [R] using hbase.comp tau hshift
  have hkey := closed_parabolic_min_principle_strict_var
    (lap := fun tau f x ↦ (gt (t0 + tau)).laplacianAt f x)
    (u := fun tau x ↦ R tau x - phi tau)
    (u' := fun tau x ↦
      R' tau x - (-(a * r tau * phi tau)))
    (c := fun tau x ↦ a * (R tau x + phi tau - r tau))
    (T := T)
    (by
      apply Continuous.sub hScalarContinuous
      exact hphiContinuous.comp continuous_fst)
    (by
      intro x tau htau
      have hphi := hphiDerivative tau htau
      have hphi' : HasDerivAt phi (-(a * r tau * phi tau)) tau := by
        simpa [a, r] using hphi
      exact (hRd x tau htau).sub hphi')
    (by
      intro tau htau x
      have hreaction := hamilton_scalar_reaction_bound_at
        (g := gt (t0 + tau)) x (by norm_num : 0 < (3 : ℝ))
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (R tau) y :=
        fun y ↦ hScalarTwo tau htau y
      have hconst : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
          (fun _ : M ↦ -(phi tau)) y := fun _ ↦ contMDiffAt_const
      have hlap :
          (gt (t0 + tau)).laplacianAt
              (fun y : M ↦ R tau y - phi tau) x =
            (gt (t0 + tau)).laplacianAt (R tau) x := by
        rw [show (fun y : M ↦ R tau y - phi tau) =
            (R tau) + fun _ : M ↦ -(phi tau) from by
              funext y
              change R tau y - phi tau = R tau y + -(phi tau)
              rw [sub_eq_add_neg]]
        rw [(gt (t0 + tau)).laplacianAt_add'
          (f := R tau) (h := fun _ : M ↦ -(phi tau))
          (x := x) hf hconst]
        rw [(gt (t0 + tau)).laplacianAt_const (-(phi tau)) x]
        ring
      change
        (gt (t0 + tau)).laplacianAt
              (fun y : M ↦ R tau y - phi tau) x +
            a * (R tau x + phi tau - r tau) *
              (R tau x - phi tau) <
          R' tau x - (-(a * r tau * phi tau))
      rw [hlap]
      have hphiSq : 0 < a * (phi tau) ^ 2 :=
        mul_pos ha (sq_pos_of_pos (hphiPos tau htau))
      have hreaction' :
          a * (gt (t0 + tau)).scalarAt x ^ 2 ≤
            2 * (gt (t0 + tau)).ricciNormSqAt x := by
        simpa [a] using hreaction
      have hgap :
          0 < 2 * (gt (t0 + tau)).ricciNormSqAt x -
              a * (gt (t0 + tau)).scalarAt x ^ 2 +
              a * (phi tau) ^ 2 := by
        nlinarith
      dsimp only [R', R, r]
      nlinarith [hgap])
    (by
      intro tau htau x hmin
      have hf : ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ R tau y - phi tau) x :=
        (hScalarTwo tau htau x).sub contMDiffAt_const
      exact laplacianAt_nonneg_of_isLocalMin
        (g := gt (t0 + tau))
        (f := fun y : M ↦ R tau y - phi tau)
        (x := x) hf
        ((gt (t0 + tau)).mdifferentiableAt_gradient hf)
        (hmin.isLocalMin Filter.univ_mem))
    (by
      intro x
      exact sub_pos.mpr (by simpa [R] using hInitial x))
  intro tau htau x
  have := hkey tau htau x
  simpa [R, sub_pos] using this

/-- An antiderivative of `(2/3) meanScalar` gives the canonical positive
normalization profile.  Starting from the non-strict floor `rho`, the half
floor is used to provide the strict initial comparison. -/
theorem normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {t0 T rho : ℝ}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hT : 0 ≤ T) (hrho : 0 < rho)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt (t0 + tau)).scalarAt x))
    (hScalarEvolution : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
    (hScalarTwo : ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).scalarAt y) x)
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt (t0 + tau))) tau)
    (hInitial : ∀ x : M, rho ≤ (gt t0).scalarAt x) :
    ∀ tau ∈ Icc (0 : ℝ) T, ∀ x : M,
      (rho / 2) * Real.exp
          (-(normalizationPrimitive tau - normalizationPrimitive 0)) <
        (gt (t0 + tau)).scalarAt x := by
  let phi : ℝ → ℝ := fun tau ↦
    (rho / 2) * Real.exp
      (-(normalizationPrimitive tau - normalizationPrimitive 0))
  apply normalizedFlow_scalarAt_gt_of_normalization_profile
    hT hScalarContinuous hScalarEvolution hScalarTwo phi
  · exact continuous_const.mul
      ((hPrimitiveContinuous.sub continuous_const).neg.rexp)
  · intro tau _htau
    exact mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _)
  · intro tau htau
    have hinner :=
      ((hPrimitiveDerivative tau htau).sub_const
        (normalizationPrimitive 0)).neg.exp.const_mul (rho / 2)
    convert hinner using 1 <;>
      simp only [phi, Pi.neg_apply, sub_eq_add_neg, neg_add_rev, neg_neg]
    ring
  · intro x
    have hhalf : rho / 2 < rho := by linarith
    simpa [phi] using hhalf.trans_le (hInitial x)

/-- Global forward-ray form of the normalization-primitive scalar profile. -/
theorem normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {t0 rho : ℝ}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hrho : 0 < rho)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt (t0 + tau)).scalarAt x))
    (hScalarEvolution : ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
    (hScalarTwo : ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).scalarAt y) x)
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt (t0 + tau))) tau)
    (hInitial : ∀ x : M, rho ≤ (gt t0).scalarAt x) :
    ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
      (rho / 2) * Real.exp
          (-(normalizationPrimitive tau - normalizationPrimitive 0)) <
        (gt (t0 + tau)).scalarAt x := by
  intro tau htau x
  exact normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive
    (T := tau) htau hrho hScalarContinuous
    (fun s hs ↦ hScalarEvolution s hs.1)
    (fun s hs ↦ hScalarTwo s hs.1)
    normalizationPrimitive hPrimitiveContinuous
    (fun s hs ↦ hPrimitiveDerivative s hs.1) hInitial
    tau ⟨htau, le_rfl⟩ x

/-- A bounded-above normalization primitive is exactly the additional input
which turns initial positive scalar curvature into a uniform positive scalar
floor on the normalized forward ray. -/
theorem exists_uniform_normalizedFlow_scalar_lower_of_normalizationPrimitive_bddAbove
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {t0 rho C : ℝ}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hrho : 0 < rho)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt (t0 + tau)).scalarAt x))
    (hScalarEvolution : ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
    (hScalarTwo : ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).scalarAt y) x)
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt (t0 + tau))) tau)
    (hPrimitiveUpper : ∀ tau ∈ Ici (0 : ℝ),
      normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
    (hInitial : ∀ x : M, rho ≤ (gt t0).scalarAt x) :
    ∃ rhoFloor : ℝ, 0 < rhoFloor ∧
      ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
        rhoFloor ≤ (gt (t0 + tau)).scalarAt x := by
  let rhoFloor : ℝ := (rho / 2) * Real.exp (-C)
  refine ⟨rhoFloor,
    mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _), ?_⟩
  intro tau htau x
  have hprofile :=
    normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
      hrho hScalarContinuous hScalarEvolution hScalarTwo
      normalizationPrimitive hPrimitiveContinuous hPrimitiveDerivative
      hInitial tau htau x
  have hexp : Real.exp (-C) ≤
      Real.exp (-(normalizationPrimitive tau - normalizationPrimitive 0)) :=
    Real.exp_le_exp.mpr (neg_le_neg (hPrimitiveUpper tau htau))
  exact (mul_le_mul_of_nonneg_left hexp (div_nonneg hrho.le (by norm_num))).trans
    hprofile.le

/-- Fully geometric initial-data form: pointwise positive scalar curvature on
the initial compact slice supplies the starting numerical floor internally.
The bounded normalization primitive remains explicit because it is the exact
condition that prevents the normalized lower profile from decaying to zero. -/
theorem exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {t0 C : ℝ}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt (t0 + tau)).scalarAt x))
    (hScalarEvolution : ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
      SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
    (hScalarTwo : ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + tau)).scalarAt y) x)
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt (t0 + tau))) tau)
    (hPrimitiveUpper : ∀ tau ∈ Ici (0 : ℝ),
      normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
    (hInitialPos : ∀ x : M, 0 < (gt t0).scalarAt x) :
    ∃ rhoFloor : ℝ, 0 < rhoFloor ∧
      ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
        rhoFloor ≤ (gt (t0 + tau)).scalarAt x := by
  obtain ⟨rho, hrho, hInitial⟩ :=
    exists_pos_scalar_floor_of_forall_scalarAt_pos (gt t0) hInitialPos
  exact
    exists_uniform_normalizedFlow_scalar_lower_of_normalizationPrimitive_bddAbove
      hrho hScalarContinuous hScalarEvolution hScalarTwo
      normalizationPrimitive hPrimitiveContinuous hPrimitiveDerivative
      hPrimitiveUpper hInitial

/-- Normalized-flow/Lichnerowicz wrapper for the strongest constant-floor
result.  Both the pointwise normalized scalar equation and spatial `C²`
regularity are derived internally. -/
theorem exists_uniform_normalizedFlow_scalar_lower_of_normalizedFlow_of_globalLichnerowicz_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {t0 C : ℝ}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt (t0 + tau)).scalarAt x))
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt (t0 + tau))) tau)
    (hPrimitiveUpper : ∀ tau ∈ Ici (0 : ℝ),
      normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
    (hInitialPos : ∀ x : M, 0 < (gt t0).scalarAt x) :
    ∃ rhoFloor : ℝ, 0 < rhoFloor ∧
      ∀ tau ∈ Ici (0 : ℝ), ∀ x : M,
        rhoFloor ≤ (gt (t0 + tau)).scalarAt x := by
  apply
    exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
      hScalarContinuous _ _ normalizationPrimitive hPrimitiveContinuous
      hPrimitiveDerivative hPrimitiveUpper hInitialPos
  · intro tau _htau x
    exact
      satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
        (hFlow (t0 + tau)) hLichnerowicz
  · intro tau _htau x
    exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      (hFlow (t0 + tau)) (hLichnerowicz.timeVariationEntries (t0 + tau)) x

end Poincare
