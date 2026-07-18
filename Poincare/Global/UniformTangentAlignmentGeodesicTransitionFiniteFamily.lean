import Poincare.Global.UniformTangentAlignmentGeodesicTransition

/-!
# A common geodesic-transition radius for finitely many anchors

The complete fixed-anchor Cartan transition is uniform in its tangent
alignment.  Taking a finite minimum upgrades this to one radius for every
anchor pair occurring in a finite discretized path or homotopy grid.
-/

noncomputable section

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UniformTangentAlignmentGeodesicTransitionFiniteFamily

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
One positive radius supplies the full Cartan Christoffel transition for every
member of a finite nonempty family of source/target anchors and every tangent
alignment over those anchors.  The radius is chosen before both the family
index and the alignment.
-/
theorem exists_uniform_cartanChartMap_chartChristoffelField_transition_on_finite_family
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
              ContDiffAt ℝ 2 F (eM v) ∧
              HasStrictFDerivAt F (DF v) (eM v) ∧
              (∀ᶠ q in nhds (eM v),
                GeodesicTransport.cutoff (n := 3) (x i) q = 1) ∧
              (∀ᶠ q in nhds (F (eM v)),
                GeodesicTransport.cutoff (n := 3) (p i) q = 1) ∧
              ∀ w : E,
                GeodesicTransport.chartChristoffelField
                    roundSphereMetric3 (p i) (F (eM v))
                    ((fderiv ℝ F (eM v)) w)
                    ((fderiv ℝ F (eM v)) w) =
                  (fderiv ℝ F (eM v))
                      (GeodesicTransport.chartChristoffelField
                        g (x i) (eM v) w w) -
                    ((fderiv ℝ (fun q : E => fderiv ℝ F q) (eM v)) w) w := by
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
                ContDiffAt ℝ 2 F (eM v) ∧
                HasStrictFDerivAt F (DF v) (eM v) ∧
                (∀ᶠ q in nhds (eM v),
                  GeodesicTransport.cutoff (n := 3) (x i) q = 1) ∧
                (∀ᶠ q in nhds (F (eM v)),
                  GeodesicTransport.cutoff (n := 3) (p i) q = 1) ∧
                ∀ w : E,
                  GeodesicTransport.chartChristoffelField
                      roundSphereMetric3 (p i) (F (eM v))
                      ((fderiv ℝ F (eM v)) w)
                      ((fderiv ℝ F (eM v)) w) =
                    (fderiv ℝ F (eM v))
                        (GeodesicTransport.chartChristoffelField
                          g (x i) (eM v) w w) -
                      ((fderiv ℝ (fun q : E => fderiv ℝ F q) (eM v)) w) w := by
    intro i
    exact
      UniformTangentAlignmentGeodesicTransition.exists_uniform_cartanChartMap_chartChristoffelField_self_F_transition_law
        (g := g) hcurv (x0 := x i) (p0 := p i)
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

end UniformTangentAlignmentGeodesicTransitionFiniteFamily
end Poincare
