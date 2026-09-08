import Poincare.Global.RiemannianMetricInstanceTransport
import Poincare.Global.ControlledChartInstance

/-!
# Geometric metric transport between compatible preferred charts

Every comparison of tangent fibers uses the derivative from the new preferred
chart to the old preferred chart. A common maximal atlas supplies the cocycle
law even when the two preferred-chart selections are unrelated.
-/

noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.RiemannianMetricInstanceTransportGeometric
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M]

/-- Enlarge only the atlas, keeping the original preferred charts. -/
@[implicit_reducible]
def commonCharts : ChartedSpace E M where
  atlas := IsManifold.maximalAtlas I ∞ M
  chartAt := inst.chartAt
  mem_chart_source := inst.mem_chart_source
  chart_mem_atlas := IsManifold.chart_mem_maximalAtlas

instance commonCharts_isManifold :
    (letI := commonCharts (inst := inst); IsManifold I ∞ M) :=
  (ControlledChartInstance.isManifold_and_maximalAtlas_eq
    (inst := inst) commonCharts (Subset.refl _)).1

/-- Derivative of a transition between any two charts in the common atlas. -/
def D (i j : IsManifold.maximalAtlas I ∞ M) (x : M) : E →L[ℝ] E :=
  letI := commonCharts (inst := inst)
  (tangentBundleCore I M).coordChange i j x

theorem D_comp (i j k : IsManifold.maximalAtlas I ∞ M) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (hk : x ∈ k.1.source) (v : E) :
    D j k x (D i j x v) = D i k x v := by
  letI := commonCharts (inst := inst)
  exact (tangentBundleCore I M).coordChange_comp i j k x ⟨⟨hi, hj⟩, hk⟩ v

theorem D_self (i : IsManifold.maximalAtlas I ∞ M) (x : M)
    (hi : x ∈ i.1.source) (v : E) : D i i x v = v := by
  letI := commonCharts (inst := inst)
  exact (tangentBundleCore I M).coordChange_self i x hi v

/-- The original preferred chart as a member of the common atlas. -/
def oldChart (x : M) : IsManifold.maximalAtlas I ∞ M :=
  ⟨inst.chartAt x, IsManifold.chart_mem_maximalAtlas x⟩

variable (inst' : ChartedSpace E M)
  (h : inst'.atlas ⊆ @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I))

local instance : ChartedSpace E M := inst

/-- The new preferred chart as a member of the original maximal atlas. -/
def newChart (x : M) : @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I) :=
  ⟨inst'.chartAt x, h (inst'.chart_mem_atlas x)⟩

/-- The geometric identification from new tangent coordinates to old ones. -/
def J (x : M) : E ≃L[ℝ] E :=
  { D (inst := inst) (newChart (inst := inst) inst' h x) (oldChart (inst := inst) x) x with
    invFun := D (inst := inst) (oldChart (inst := inst) x) (newChart (inst := inst) inst' h x) x
    left_inv := fun v ↦ by
      change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = v
      rw [D_comp (inst := inst) _ _ _ x (inst'.mem_chart_source x) (inst.mem_chart_source x)
        (inst'.mem_chart_source x), D_self (inst := inst) _ x (inst'.mem_chart_source x)]
    right_inv := fun v ↦ by
      change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = v
      rw [D_comp (inst := inst) _ _ _ x (inst.mem_chart_source x) (inst'.mem_chart_source x)
        (inst.mem_chart_source x), D_self (inst := inst) _ x (inst.mem_chart_source x)] }

/-- The identification is exactly the ordinary derivative of the chart transition. -/
theorem J_apply (x : M) (v : E) :
    J (inst := inst) inst' h x v =
      fderiv ℝ (inst.chartAt x ∘ (inst'.chartAt x).symm) (inst'.chartAt x x) v := by
  change fderivWithin ℝ _ _ _ v = _
  simp only [OpenPartialHomeomorph.extend, mfld_simps, fderivWithin_univ]
  rfl

/-- Inverse tangent trivializations intertwine through the fixed-anchor transition. -/
theorem J_inverse_trivialization (a x : M)
    (ha : x ∈ (inst.chartAt a).source) (ha' : x ∈ (inst'.chartAt a).source) (v : E) :
    J (inst := inst) inst' h x (D (inst := inst) (newChart (inst := inst) inst' h a) (newChart (inst := inst) inst' h x) x v) =
      D (inst := inst) (oldChart (inst := inst) a) (oldChart (inst := inst) x) x
        (D (inst := inst) (newChart (inst := inst) inst' h a) (oldChart (inst := inst) a) x v) := by
  change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = D (inst := inst) _ _ x (D (inst := inst) _ _ x v)
  rw [D_comp (inst := inst) _ _ _ x ha' (inst'.mem_chart_source x) (inst.mem_chart_source x),
    D_comp (inst := inst) _ _ _ x ha' ha (inst.mem_chart_source x)]

/-- Forward tangent trivializations satisfy the same change-of-anchor law. -/
theorem J_trivialization (a x : M)
    (ha : x ∈ (inst.chartAt a).source) (ha' : x ∈ (inst'.chartAt a).source) (v : E) :
    D (inst := inst) (oldChart (inst := inst) x) (oldChart (inst := inst) a) x (J (inst := inst) inst' h x v) =
      D (inst := inst) (newChart (inst := inst) inst' h a) (oldChart (inst := inst) a) x
        (D (inst := inst) (newChart (inst := inst) inst' h x) (newChart (inst := inst) inst' h a) x v) := by
  change D (inst := inst) _ _ x (D (inst := inst) _ _ x v) = D (inst := inst) _ _ x (D (inst := inst) _ _ x v)
  rw [D_comp (inst := inst) _ _ _ x (inst'.mem_chart_source x) (inst.mem_chart_source x) ha,
    D_comp (inst := inst) _ _ _ x (inst'.mem_chart_source x) ha' ha]

end Poincare.RiemannianMetricInstanceTransportGeometric
