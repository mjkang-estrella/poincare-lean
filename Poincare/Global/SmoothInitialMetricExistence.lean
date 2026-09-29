import Poincare.Global.SmoothInitialMetricPositiveCone
import Poincare.Global.SmoothInitialMetricLocalPullback
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Existence of a smooth initial metric

Tangent-trivialization pullbacks of the Euclidean inner product give smooth
local positive symmetric bilinear forms. A smooth partition of unity glues
them inside the convex positive cone. Finite dimensionality supplies the
bounded quadratic unit balls required by the metric structure.
-/

noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
universe u

namespace Poincare.SmoothInitialMetricExistence

open SmoothInitialMetricDefinitions SmoothInitialMetricPositiveCone
  SmoothInitialMetricLocalPullback

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Every compact Hausdorff smooth three-manifold has an actual smooth
Riemannian metric, with no metric or curvature hypothesis. -/
theorem exists_initial_metric [T2Space M] [CompactSpace M] :
    Nonempty (ClosedSmoothRiemannianMetric 3 M) := by
  letI : ∀ x : M, NormedAddCommGroup
      (TangentSpace (closedSmoothModelWithCorners 3) x) := fun _ =>
    inferInstanceAs (NormedAddCommGroup (ClosedSmoothModel 3))
  letI : ∀ x : M, NormedSpace ℝ
      (TangentSpace (closedSmoothModelWithCorners 3) x) := fun _ =>
    inferInstanceAs (NormedSpace ℝ (ClosedSmoothModel 3))
  letI : ∀ x : M, TopologicalSpace
      (TangentSpace (closedSmoothModelWithCorners 3) x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.topologicalSpace
  let V (x : M) :=
    TangentSpace (closedSmoothModelWithCorners 3) x →L[ℝ]
      TangentSpace (closedSmoothModelWithCorners 3) x →L[ℝ] ℝ
  let t (x : M) : Set (V x) :=
    positiveSymmetricBilinearForms
      (TangentSpace (closedSmoothModelWithCorners 3) x)
  have ht : ∀ x, Convex ℝ (t x) := fun x =>
    convex_positiveSymmetricBilinearForms
      (TangentSpace (closedSmoothModelWithCorners 3) x)
  have Hloc :
      ∀ p : M, ∃ U ∈ 𝓝 p, ∃ s_loc : (x : M) → V x,
        ContMDiffOn (closedSmoothModelWithCorners 3)
          ((closedSmoothModelWithCorners 3).prod
            𝓘(ℝ, ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ))
          ∞
          (fun x => TotalSpace.mk'
            (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
            x (s_loc x)) U ∧ ∀ x ∈ U, s_loc x ∈ t x := by
    intro p
    let e := trivializationAt (ClosedSmoothModel 3)
      (TangentSpace (closedSmoothModelWithCorners 3)) p
    refine ⟨e.baseSet, e.open_baseSet.mem_nhds ?_,
      localEuclideanInner p, localEuclideanInner_contMDiffOn p, ?_⟩
    · exact mem_baseSet_trivializationAt (ClosedSmoothModel 3)
        (TangentSpace (closedSmoothModelWithCorners 3)) p
    · intro x hx
      exact ⟨localEuclideanInner_symm p x,
        fun a ha => localEuclideanInner_pos p x hx a ha⟩
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (n := (⊤ : ℕ∞))
    (F_fiber := ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
    (closedSmoothModelWithCorners 3) V t ht Hloc
  refine ⟨{
    inner := fun x => s x
    symm := fun x => (hs x).1
    pos := fun x => (hs x).2
    isVonNBounded := ?_
    contMDiff := s.contMDiff }⟩
  intro x
  letI : FiniteDimensional ℝ (TangentSpace (closedSmoothModelWithCorners 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel 3))
  exact isVonNBounded_bilinear_unitBall (s x) (hs x).2

end Poincare.SmoothInitialMetricExistence
