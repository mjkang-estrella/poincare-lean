import Poincare.Global.DifferentialSuccessorNaturality

/-!
# Uniform successor germ naturality on finite anchor families

The fixed-anchor successor theorem chooses its predecessor-normal radius before
the tangent alignment.  Taking a finite minimum gives one radius for every
anchor pair and alignment occurring in a finite path or homotopy grid.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace DifferentialSuccessorNaturalityFiniteFamily

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
For a finite nonempty family of source/target anchors, one positive radius
supports differential-successor geodesic-germ naturality for every family
member, every tangent alignment, and every sufficiently small nonzero
successor datum.
-/
theorem exists_uniform_reanchoredChartMap_geodesicGerm_naturality_on_finite_family
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : ι → M) (p : ι → RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ i : ι, ∀ L : CartanMap.TangentAlignment g (x i) (p i),
        ∀ {x₁ : M}
            (d : DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk (x i) (p i) L) x₁),
          ‖d.v‖ < rho → d.v ≠ 0 → ∀ u : E,
            (fun t : ℝ ↦
              DifferentialInducedSuccessor.reanchoredChartMap
                (CartanChain.ChainState.mk (x i) (p i) L) x₁
                (GeodesicTransport.geodesicGermChartSolution g x₁ u t).1) =ᶠ[nhds (0 : ℝ)]
            (fun t : ℝ ↦
              (GeodesicTransport.geodesicGermChartSolution
                roundSphereMetric3
                ((CartanChain.ChainState.mk (x i) (p i) L).map x₁)
                (d.alignment u) t).1) := by
  have hlocal : ∀ i : ι,
      ∃ rho > (0 : ℝ),
        ∀ L : CartanMap.TangentAlignment g (x i) (p i),
          ∀ {x₁ : M}
              (d : DifferentialInducedSuccessor.Data
                (CartanChain.ChainState.mk (x i) (p i) L) x₁),
            ‖d.v‖ < rho → d.v ≠ 0 → ∀ u : E,
              (fun t : ℝ ↦
                DifferentialInducedSuccessor.reanchoredChartMap
                  (CartanChain.ChainState.mk (x i) (p i) L) x₁
                  (GeodesicTransport.geodesicGermChartSolution g x₁ u t).1) =ᶠ[nhds (0 : ℝ)]
              (fun t : ℝ ↦
                (GeodesicTransport.geodesicGermChartSolution
                  roundSphereMetric3
                  ((CartanChain.ChainState.mk (x i) (p i) L).map x₁)
                  (d.alignment u) t).1) := by
    intro i
    exact
      DifferentialSuccessorNaturality.exists_uniform_reanchoredChartMap_geodesicGerm_naturality_radius
        g hcurv (x i) (p i)
  choose radius hradius hpackage using hlocal
  let rho : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hrho : 0 < rho := by
    dsimp [rho]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius i
  refine ⟨rho, hrho, ?_⟩
  intro i L x₁ d hd hdne u
  exact hpackage i L d
    (hd.trans_le (Finset.inf'_le radius (Finset.mem_univ i))) hdne u

end DifferentialSuccessorNaturalityFiniteFamily
end Poincare
