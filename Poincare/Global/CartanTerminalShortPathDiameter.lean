import Poincare.Global.CartanTerminalShortPathScheduleFree

/-!
# Diameter control from a terminal short path

The terminal certificate stores a bound on the length of the whole `C¹`
curve.  Every subarc has no larger length, so every two curve points are
strictly closer than the same mesh.  This is the whole-cell estimate needed
when a strict refinement inserts points into the final endpoint-to-overlap
edge.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology ENNReal

namespace Poincare
namespace CartanTerminalShortPathDiameter

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

open CartanCanonicalRootedEndpointAssembly

/-- Every two parameter values on a terminal short curve have distance less
than its certified mesh. -/
theorem TerminalShortPathCertificate.dist_curve_lt_mesh
    {g : ClosedSmoothRiemannianMetric 3 M} {y z : M} {mesh : ℝ}
    (certificate : TerminalShortPathCertificate g y z mesh)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    letI : MetricSpace M := g.toMetricSpace
    dist (certificate.curve a) (certificate.curve b) < mesh := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel 3)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  rcases le_total a b with hab | hba
  · have hsmooth : ContMDiffOn 𝓘(ℝ) I 1 certificate.curve
        (Set.Icc a b) :=
      certificate.curve_contMDiffOn.mono
        (Set.Icc_subset_Icc ha.1 hb.2)
    have hEd : edist (certificate.curve a) (certificate.curve b) ≤
        Manifold.pathELength I certificate.curve a b :=
      GeodesicTransport.induced_edist_le_pathELength g hsmooth rfl rfl hab
    have hsub : Manifold.pathELength I certificate.curve a b ≤
        Manifold.pathELength I certificate.curve 0 1 :=
      Manifold.pathELength_mono ha.1 hb.2
    exact edist_lt_ofReal.mp
      ((hEd.trans hsub).trans_lt certificate.curve_pathELength_lt)
  · have hsmooth : ContMDiffOn 𝓘(ℝ) I 1 certificate.curve
        (Set.Icc b a) :=
      certificate.curve_contMDiffOn.mono
        (Set.Icc_subset_Icc hb.1 ha.2)
    have hEd : edist (certificate.curve b) (certificate.curve a) ≤
        Manifold.pathELength I certificate.curve b a :=
      GeodesicTransport.induced_edist_le_pathELength g hsmooth rfl rfl hba
    have hsub : Manifold.pathELength I certificate.curve b a ≤
        Manifold.pathELength I certificate.curve 0 1 :=
      Manifold.pathELength_mono hb.1 ha.2
    rw [dist_comm]
    exact edist_lt_ofReal.mp
      ((hEd.trans hsub).trans_lt certificate.curve_pathELength_lt)

end CartanTerminalShortPathDiameter
end Poincare
