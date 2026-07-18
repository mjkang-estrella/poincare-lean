import Poincare.Global.GeodesicDerivative

/-!
# Compact-uniform Taylor remainders from local regularity

The residual/Gronwall endpoint theorem needs a Taylor remainder uniform on a
compact convex tube.  Global `ContDiff` is unnecessary: pointwise `C¹`
regularity on that tube already makes the derivative continuous there, and
the same Heine--Cantor/mean-value proof applies.  A second theorem extracts a
small closed ball with this property from one `ContDiffAt` hypothesis.
-/

noncomputable section

open Filter Function Metric Set
open scoped ContDiff Topology

namespace Poincare

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Uniform first-order Taylor remainder on a compact convex set from local
`C¹` regularity at every point of that set. -/
theorem uniform_taylor_remainder_norm_le_on_compact_convex_of_contDiffAt
    {f : X → Y} {K : Set X}
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x)
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) :
    ∀ epsilon > (0 : ℝ), ∃ delta > (0 : ℝ), ∀ x ∈ K, ∀ y ∈ K,
      ‖y - x‖ ≤ delta →
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ epsilon * ‖y - x‖ := by
  intro epsilon hepsilon
  have hdf_cont : ContinuousOn (fun x : X ↦ fderiv ℝ f x) K := by
    intro x hx
    exact
      (((hf x hx).fderiv_right (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  have hdf_uc : UniformContinuousOn (fun x : X ↦ fderiv ℝ f x) K :=
    hK_compact.uniformContinuousOn_of_continuous hdf_cont
  rcases (Metric.uniformContinuousOn_iff_le.mp hdf_uc) epsilon hepsilon with
    ⟨delta, hdelta, hdeltaProp⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x hx y hy hyx
  let A : X →L[ℝ] Y := fderiv ℝ f x
  let S : Set X := K ∩ closedBall x delta
  have hxS : x ∈ S := by
    refine ⟨hx, ?_⟩
    simp [hdelta.le]
  have hyS : y ∈ S := by
    refine ⟨hy, ?_⟩
    simpa [S, dist_eq_norm] using hyx
  have hSconvex : Convex ℝ S :=
    hK_convex.inter (convex_closedBall x delta)
  have hder : ∀ z ∈ S,
      HasFDerivWithinAt (fun z : X ↦ f z - A z)
        (fderiv ℝ f z - A) S z := by
    intro z hz
    have hfz : HasFDerivAt f (fderiv ℝ f z) z :=
      ((hf z hz.1).differentiableAt (by norm_num)).hasFDerivAt
    exact (hfz.sub A.hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ S, ‖fderiv ℝ f z - A‖ ≤ epsilon := by
    intro z hz
    have hzx : dist z x ≤ delta := by
      simpa [S] using hz.2
    simpa [A, dist_eq_norm] using hdeltaProp z hz.1 x hx hzx
  have hmvt :
      ‖(fun z : X ↦ f z - A z) y - (fun z : X ↦ f z - A z) x‖ ≤
        epsilon * ‖y - x‖ :=
    hSconvex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (𝕜 := ℝ) hder hbound hxS hyS
  have hrewrite :
      (f y - A y) - (f x - A x) = f y - f x - A (y - x) := by
    rw [map_sub]
    abel
  simpa [hrewrite] using hmvt

/-- One local `C¹` hypothesis yields a positive compact closed ball on
which the Taylor remainder is uniform. -/
theorem exists_closedBall_uniform_taylor_remainder_of_contDiffAt_one
    [ProperSpace X] {f : X → Y} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ r > (0 : ℝ),
      ∀ epsilon > (0 : ℝ), ∃ delta > (0 : ℝ),
        ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
          ‖y - x‖ ≤ delta →
            ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤
              epsilon * ‖y - x‖ := by
  have heventually : ∀ᶠ x in nhds x₀, ContDiffAt ℝ 1 f x :=
    hf.eventually (by norm_num)
  rcases Metric.mem_nhds_iff.mp heventually with
    ⟨R, hR, hRsub⟩
  let r : ℝ := R / 2
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hball : ∀ x ∈ closedBall x₀ r, ContDiffAt ℝ 1 f x := by
    intro x hx
    apply hRsub
    exact closedBall_subset_ball (by dsimp only [r]; linarith) hx
  refine ⟨r, hr, ?_⟩
  exact uniform_taylor_remainder_norm_le_on_compact_convex_of_contDiffAt
    hball (isCompact_closedBall x₀ r) (convex_closedBall x₀ r)

end Poincare
