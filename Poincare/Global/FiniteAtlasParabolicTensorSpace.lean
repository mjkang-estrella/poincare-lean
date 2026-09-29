import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.HausdorffFiniteAtlasChartFrameReduction
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T
abbrev Bilin := (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3) →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) (closedSmoothModelWithCorners 3) M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : (ClosedSmoothModel 3)) : (ClosedSmoothModel 3) :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) ((EuclideanSpace.basisFun (Fin 3) ℝ) a)) c

def evalY (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : (ClosedSmoothModel 3) // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × (ClosedSmoothModel 3)),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

def carrierClosedGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

variable (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ)

theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
    f ∈ supportSubmodule A ev ↔
      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
  simp only [supportSubmodule, Submodule.mem_iInf]
  constructor
  · intro h i a b t z hz
    exact h i a b t ⟨z, hz⟩
  · intro h i a b t z
    exact h i a b t z.val z.property

theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
    f ∈ symmetrySubmodule A ev ↔
      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
  simp only [symmetrySubmodule, Submodule.mem_iInf]
  constructor
  · intro h i a b p
    exact sub_eq_zero.mp (h i a b p)
  · intro h i a b p
    exact sub_eq_zero.mpr (h i a b p)

theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
    f ∈ overlapSubmodule A ev ↔
      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0 := by
  simp only [overlapSubmodule, Submodule.mem_iInf]
  constructor
  · intro h i j a b t x hx
    exact h i j a b t ⟨x, hx⟩
  · intro h i j a b t x
    exact h i j a b t x.val x.property

theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
    f ∈ tensorSubmodule A ev ↔
      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0) := by
  exact and_congr
    (and_congr (mem_supportSubmodule_iff A ev f) (mem_symmetrySubmodule_iff A ev f))
    (mem_overlapSubmodule_iff A ev f)

theorem isClosed_supportSubmodule :
    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [supportSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun t => isClosed_iInter fun z =>
      (evalLocal A ev i a b (t, z)).isClosed_ker

theorem isClosed_symmetrySubmodule :
    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
  simp only [symmetrySubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun p =>
      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker

theorem isClosed_overlapSubmodule :
    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [overlapSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
      (overlap A ev i j a b t x).isClosed_ker

theorem carrierClosed : carrierClosedGoal A ev :=
  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
    (isClosed_overlapSubmodule A ev)

instance instCompleteSpaceTensor [CompleteSpace H] :
    CompleteSpace ↥(tensorSubmodule A ev) :=
  (carrierClosed A ev).isComplete.completeSpace_coe

theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
  ⟨inferInstance, inferInstance⟩

def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
  toFun f :=
    { entries := f.val
      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩

theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
    ‖f.val k‖ ≤ ‖f‖ := norm_le_pi_norm f.val k

theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
    ‖f.val (i, a, b) p‖ ≤ ‖f‖ :=
  (ParabolicHolder.norm_le _ p).trans (norm_entry_le A (evalY α T) f (i, a, b))

theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
    ‖(f.val (i, a, b)).u p‖ ≤ ‖f‖ :=
  (ParabolicSolutionGraph.sup_u_le _ p).trans (norm_entry_le A (evalX α T) f (i, a, b))

theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
    (t : ℝ) (x : M) (f : LocalProduct A H) :
    overlap A ev i j a b t x f =
      A.partition j x * ev (t, chart A i x) (f (i, a, b)) -
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f (j, c, d)) := by
  simp [overlap, evalLocal]

theorem supported_entry (f : ↥(tensorSubmodule A ev))
    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (z : (ClosedSmoothModel 3))
    (hz : z ∉ coordSupport A i) : ev (t, z) (f.val (i, a, b)) = 0 :=
  ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1 i a b t z hz

theorem weighted_transition (f : ↥(tensorSubmodule A ev))
    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
    (hx : x ∈ (chart A i).source ∩ (chart A j).source) :
    A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) =
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f.val (j, c, d)) := by
  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
  rw [overlap_apply] at h
  exact sub_eq_zero.mp h

theorem partition_support_source (i : Fin A.cover.chartCount) :
    tsupport (A.partition i) ⊆ (chart A i).source :=
  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))

theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
    coordSupport A i ⊆ (chart A i).target :=
  image_subset_iff.mpr fun _ hx => (chart A i).map_source
    (partition_support_source A i hx)

theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
    IsCompact (coordSupport A i) := by
  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
  have hc : IsCompact (closure (A.region i)) := by
    have h := (A.coordinate_compact i).image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor i)).mono ht)
    change IsCompact ((chart A i).symm '' (chart A i '' closure (A.region i))) at h
    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
  have hs := hc.of_isClosed_subset (isClosed_tsupport _)
    ((A.subordinate i).trans subset_closure)
  exact hs.image_of_continuousOn
    ((continuousOn_extChartAt (A.cover.anchor i)).mono (partition_support_source A i))

end Poincare.FiniteAtlasParabolicTensorSpace
