import Poincare.Global.UniformTangentAlignmentC2

/-!
# A common Cartan C2 radius for a finite family of anchors

The fixed-anchor radius in `UniformTangentAlignmentC2` is already uniform in
the tangent alignment.  A finite family of source/target anchor pairs therefore
admits one common positive radius, obtained by taking the minimum of the
fixed-anchor radii.  This is the compactness-free finite step used by a
discretized path or homotopy grid.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UniformTangentAlignmentFiniteFamily

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
For a finite nonempty family of fixed source/target anchors, one positive
normal-coordinate radius supplies the Cartan-map `C²` package for every
anchor pair and every tangent alignment over that pair.

The radius is selected before both the finite index and the alignment.  No
continuity of the anchor family and no global injectivity-radius theorem are
used.
-/
theorem exists_uniform_cartanChartMap_contDiffAt_two_on_finite_family
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : ι → M) (p : ι → RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ i : ι, ∀ L : CartanMap.TangentAlignment g (x i) (p i),
        ∃ Afield Bfield : E → E ≃L[ℝ] E,
        ∃ DF : E → E →L[ℝ] E,
          (∀ v : E,
            DF v =
              CartanLocalIsometry.cartanChartDifferential
                L (Afield v) (Bfield v)) ∧
          ∀ v : E, ‖v‖ < rho → v ≠ 0 →
            let eM :=
              GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) (x i)
            let eS :=
              GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) (p i)
            let F :=
              CartanDifferential.cartanChartMap g (x i) (p i) L
            v ∈ eM.source ∧
              L v ∈ eS.source ∧
              eM v ∈ (extChartAt I (x i)).target ∧
              eS (L v) ∈ (extChartAt I (p i)).target ∧
              HasStrictFDerivAt eM (Afield v : E →L[ℝ] E) v ∧
              ContDiffAt ℝ 2 F (eM v) := by
  have hlocal : ∀ i : ι,
      ∃ rho > (0 : ℝ),
        ∀ L : CartanMap.TangentAlignment g (x i) (p i),
          ∃ Afield Bfield : E → E ≃L[ℝ] E,
          ∃ DF : E → E →L[ℝ] E,
            (∀ v : E,
              DF v =
                CartanLocalIsometry.cartanChartDifferential
                  L (Afield v) (Bfield v)) ∧
            ∀ v : E, ‖v‖ < rho → v ≠ 0 →
              let eM :=
                GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) (x i)
              let eS :=
                GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) (p i)
              let F :=
                CartanDifferential.cartanChartMap g (x i) (p i) L
              v ∈ eM.source ∧
                L v ∈ eS.source ∧
                eM v ∈ (extChartAt I (x i)).target ∧
                eS (L v) ∈ (extChartAt I (p i)).target ∧
                HasStrictFDerivAt eM (Afield v : E →L[ℝ] E) v ∧
                ContDiffAt ℝ 2 F (eM v) := by
    intro i
    exact
      UniformTangentAlignmentC2.exists_uniform_cartanChartMap_contDiffAt_two_on_punctured_ball
        (g := g) hcurv (x₀ := x i) (p₀ := p i)
  choose radius hradius hpackage using hlocal
  let rho : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hrho : 0 < rho := by
    dsimp [rho]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius i
  refine ⟨rho, hrho, ?_⟩
  intro i L
  rcases hpackage i L with ⟨Afield, Bfield, DF, hDF, hlocalBall⟩
  refine ⟨Afield, Bfield, DF, hDF, ?_⟩
  intro v hv hvne
  exact hlocalBall v
    (hv.trans_le (Finset.inf'_le radius (Finset.mem_univ i))) hvne

end UniformTangentAlignmentFiniteFamily
end Poincare
