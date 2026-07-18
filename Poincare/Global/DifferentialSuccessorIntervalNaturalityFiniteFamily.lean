import Poincare.Global.DifferentialSuccessorIntervalNaturality

/-!
# Uniform successor interval naturality on finite anchor families

Finite minima turn the fixed-anchor all-alignment predecessor radius into one
radius for every anchor pair in a finite path or homotopy grid.  The smaller
new-anchor normal ball produced by ODE uniqueness remains allowed to depend on
the chosen alignment and successor datum.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace DifferentialSuccessorIntervalNaturalityFiniteFamily

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
One positive predecessor-normal radius supports closed-interval exponential
naturality for every member of a finite nonempty anchor family and every
tangent alignment.  The output normal-ball radius is selected after the
alignment and successor datum.
-/
theorem exists_uniform_reanchoredChartMap_expAtChart_naturality_on_finite_family
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : ι → M) (p : ι → RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ i : ι, ∀ L : CartanMap.TangentAlignment g (x i) (p i),
        ∀ {x₁ : M}
            (d : DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk (x i) (p i) L) x₁),
          ‖d.v‖ < rho → d.v ≠ 0 →
            ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
              DifferentialInducedSuccessor.reanchoredChartMap
                  (CartanChain.ChainState.mk (x i) (p i) L) x₁
                  (GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := g) x₁ v) =
                GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3)
                  ((CartanChain.ChainState.mk (x i) (p i) L).map x₁)
                  (d.alignment v) := by
  have hlocal : ∀ i : ι,
      ∃ rho > (0 : ℝ),
        ∀ L : CartanMap.TangentAlignment g (x i) (p i),
          ∀ {x₁ : M}
              (d : DifferentialInducedSuccessor.Data
                (CartanChain.ChainState.mk (x i) (p i) L) x₁),
            ‖d.v‖ < rho → d.v ≠ 0 →
              ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
                DifferentialInducedSuccessor.reanchoredChartMap
                    (CartanChain.ChainState.mk (x i) (p i) L) x₁
                    (GeodesicTransport.expAtChartOpenPartialHomeomorph
                      (g := g) x₁ v) =
                  GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := roundSphereMetric3)
                    ((CartanChain.ChainState.mk (x i) (p i) L).map x₁)
                    (d.alignment v) := by
    intro i
    exact
      DifferentialSuccessorIntervalNaturality.exists_uniform_reanchoredChartMap_expAtChart_naturality_ball
        g hcurv (x i) (p i)
  choose radius hradius hpackage using hlocal
  let rho : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hrho : 0 < rho := by
    dsimp [rho]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius i
  refine ⟨rho, hrho, ?_⟩
  intro i L x₁ d hd hdne
  exact hpackage i L d
    (hd.trans_le (Finset.inf'_le radius (Finset.mem_univ i))) hdne

/--
For a finite nonempty anchor family, one positive radius gives an open local
equality neighborhood for every alignment and every successor datum in the
radius, including zero-vector re-anchors.
-/
theorem exists_uniform_local_eqOn_differentialSuccessor_all_on_finite_family
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : ι → M) (p : ι → RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ i : ι, ∀ L : CartanMap.TangentAlignment g (x i) (p i),
        ∀ {x₁ : M}
            (d : DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk (x i) (p i) L) x₁),
          ‖d.v‖ < rho →
            ∃ V : Set M, IsOpen V ∧ x₁ ∈ V ∧
              EqOn (CartanChain.ChainState.mk (x i) (p i) L).germ
                d.successor.germ
                (V ∩
                  ((CartanChain.ChainState.mk (x i) (p i) L).germ.source ∩
                    d.successor.germ.source)) := by
  have hlocal : ∀ i : ι,
      ∃ rho > (0 : ℝ),
        ∀ L : CartanMap.TangentAlignment g (x i) (p i),
          ∀ {x₁ : M}
              (d : DifferentialInducedSuccessor.Data
                (CartanChain.ChainState.mk (x i) (p i) L) x₁),
            ‖d.v‖ < rho →
              ∃ V : Set M, IsOpen V ∧ x₁ ∈ V ∧
                EqOn (CartanChain.ChainState.mk (x i) (p i) L).germ
                  d.successor.germ
                  (V ∩
                    ((CartanChain.ChainState.mk (x i) (p i) L).germ.source ∩
                      d.successor.germ.source)) := by
    intro i
    exact
      DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all
        g hcurv (x i) (p i)
  choose radius hradius hpackage using hlocal
  let rho : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hrho : 0 < rho := by
    dsimp [rho]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius i
  refine ⟨rho, hrho, ?_⟩
  intro i L x₁ d hd
  exact hpackage i L d
    (hd.trans_le (Finset.inf'_le radius (Finset.mem_univ i)))

end DifferentialSuccessorIntervalNaturalityFiniteFamily
end Poincare
