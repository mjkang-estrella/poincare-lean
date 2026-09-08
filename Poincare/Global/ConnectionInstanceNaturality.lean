import Poincare.Global.CurvatureInstanceTransport

/-!
# Differential naturality across compatible chart instances

The identity map from the new atlas to the original atlas has derivative `J`.
-/

noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.ConnectionInstanceNaturality
open RiemannianMetricInstanceTransportGeometric CurvatureInstanceTransport
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M]
variable (inst' : ChartedSpace E M)
  (h : inst'.atlas ⊆ @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I))

include h in
/-- The identity between the two atlas choices is smooth, with its direction explicit. -/
theorem contMDiffAt_identity (x : M) :
    @ContMDiffAt ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst ∞ id x := by
  letI := inst
  have hc := contMDiffAt_extChartAt («I» := I) (n := ∞) (x := x)
  have hc' := (modelContMDiffAt_iff (inst := inst) inst' h _ x).1 hc
  apply (@contMDiffAt_iff ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst ∞ id x).2
  letI := inst'
  exact ⟨continuousAt_id, (contMDiffAt_iff.mp hc').2⟩

/-- The derivative of the identity from the new atlas to the old one is `J`. -/
theorem mfderiv_identity (x : M) :
    @mfderiv ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst id x =
      (J (inst := inst) inst' h x).toContinuousLinearMap := by
  letI := inst
  have hd := @ContMDiffAt.mdifferentiableAt ℝ _ E _ _ E _ I M _ inst' E _ _ E _ I M _ inst id x ∞
    (contMDiffAt_identity (inst := inst) inst' h x) (by simp)
  ext v
  rw [mfderiv, if_pos hd]
  change _ = J (inst := inst) inst' h x v
  rw [J_apply]
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    mfld_simps, fderivWithin_univ, Function.id_comp]
  rfl

end Poincare.ConnectionInstanceNaturality
