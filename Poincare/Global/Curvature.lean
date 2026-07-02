import Poincare.Global.LeviCivitaExistence
import Poincare.Global.LeviCivitaRegularity
import Poincare.CurvatureConditions

/-!
# Canonical curvature quantities for closed smooth Riemannian metrics

This module specializes the manifold-level curvature API to the canonical
Levi-Civita connection attached to a `ClosedSmoothRiemannianMetric`.

The global Koszul construction proves metric compatibility, zero torsion, and
now `C¹` covariant-derivative regularity for the canonical connection.  The
legacy wrappers below keep their explicit typeclass parameter, and the primed
Ricci symmetry theorem at the end demonstrates that the instance can supply it.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare
namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The canonical Levi-Civita connection of a closed smooth Riemannian metric. -/
def leviCivita (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative I E TM :=
  LeviCivitaExistence.closedLeviCivitaConnection g

/-- The canonical Levi-Civita connection has the regularity needed for curvature. -/
@[instance]
theorem leviCivita_contMDiff (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1 := by
  simpa [leviCivita] using
    LeviCivitaExistence.closedLeviCivitaConnection_contMDiff g

/-- The canonical connection is metric-compatible with the metric. -/
theorem leviCivita_metricCompatible (g : ClosedSmoothRiemannianMetric n M) :
    IsMetricCompatible g g.leviCivita := by
  simpa [leviCivita] using
    LeviCivitaExistence.closedLeviCivitaConnection_metricCompatible g

/-- The canonical connection has zero torsion tensor. -/
theorem leviCivita_torsion (g : ClosedSmoothRiemannianMetric n M) :
    g.leviCivita.torsion = 0 := by
  simpa [leviCivita] using
    LeviCivitaExistence.closedLeviCivitaConnection_torsion g

/-- Pointwise metric compatibility, in the curvature layer's namespace. -/
theorem leviCivita_metricCompatibleAt (g : ClosedSmoothRiemannianMetric n M)
    (x : M) :
    CovariantDerivative.MetricCompatibleAt g.inner g.leviCivita x := by
  intro Y Z hY hZ v
  exact g.leviCivita_metricCompatible
    (by simpa [MDiffAtTangentField] using hY)
    (by simpa [MDiffAtTangentField] using hZ) v

/-- Pointwise torsion-freeness, in the curvature layer's namespace. -/
theorem leviCivita_torsionFreeAt (g : ClosedSmoothRiemannianMetric n M)
    (x : M) :
    CovariantDerivative.TorsionFreeAt g.leviCivita x := by
  have ht := g.leviCivita_torsion
  rw [CovariantDerivative.torsion_eq_zero_iff] at ht
  intro X Y hX hY
  exact ht hX hY

/--
Any torsion-free metric-compatible covariant derivative agrees with the
canonical Levi-Civita connection on differentiable vector fields.
-/
theorem eq_leviCivita_of_metricCompatible_torsion
    (g : ClosedSmoothRiemannianMetric n M) {cov : CovariantDerivative I E TM}
    (hc : IsMetricCompatible g cov) (ht : cov.torsion = 0)
    {x : M} {X : ∀ y : M, TM y} (hX : MDiffAtTangentField X x) :
    cov X x = g.leviCivita X x :=
  levi_civita_unique g hc g.leviCivita_metricCompatible ht
    g.leviCivita_torsion hX

/-- The metric tensor at a point as the bilinear form expected by scalar curvature. -/
noncomputable def metricBilinAt (g : ClosedSmoothRiemannianMetric n M)
    (x : M) : LinearMap.BilinForm ℝ (TM x) :=
  LinearMap.mk₂ ℝ (fun v w ↦ g.inner x v w)
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)

theorem metricBilinAt_apply (g : ClosedSmoothRiemannianMetric n M)
    (x : M) (v w : TM x) :
    g.metricBilinAt x v w = g.inner x v w :=
  rfl

/-- Positive-definiteness of the metric gives nondegeneracy of `metricBilinAt`. -/
theorem metricBilinAt_nondegenerate (g : ClosedSmoothRiemannianMetric n M)
    (x : M) :
    (g.metricBilinAt x).Nondegenerate := by
  constructor
  · intro v hv
    exact LeviCivitaExistence.metric_nondegenerate g x v fun w ↦ by
      simpa [metricBilinAt] using hv w
  · intro w hw
    refine LeviCivitaExistence.metric_nondegenerate g x w fun v ↦ ?_
    rw [g.inner_symm x w v]
    simpa [metricBilinAt] using hw v

/-- First-order regularity of metric pairings from the smooth metric. -/
theorem metric_pairing_mdiffAt (g : ClosedSmoothRiemannianMetric n M)
    {x : M} {A B : ∀ y : M, TM y}
    (hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% A) x)
    (hB : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% B) x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ g.inner y (A y) (B y)) x :=
  LeviCivitaExistence.metric_pairing_mdiffAt g
    (by simpa [MDiffAtTangentField] using hA)
    (by simpa [MDiffAtTangentField] using hB)

/-- Second-order regularity of metric pairings from the smooth metric. -/
theorem metric_pairing_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M) {x : M}
    {A B : ∀ y : M, TM y}
    (hA : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% A) x)
    (hB : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% B) x) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.inner y (A y) (B y)) x := by
  letI : RiemannianBundle TM := g.toRiemannianBundle
  haveI : IsContMDiffRiemannianBundle I ∞ E TM :=
    g.toIsContMDiffRiemannianBundle
  have hinner : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ inner ℝ (A y) (B y)) x :=
    ContMDiffAt.inner_bundle hA hB
  simpa [ClosedSmoothRiemannianMetric.fiber_inner_eq] using hinner

section Curvature

variable (g : ClosedSmoothRiemannianMetric n M)
variable [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]

/-- The Ricci tensor of the canonical Levi-Civita connection. -/
noncomputable def ricciAt (x : M) (u w : TM x) : ℝ :=
  CovariantDerivative.ricciBilinearAt g.leviCivita x u w

/-- The scalar curvature of the canonical Levi-Civita connection. -/
noncomputable def scalarAt (x : M) : ℝ :=
  CovariantDerivative.scalarCurvatureAt g.leviCivita x
    (g.metricBilinAt x) (g.metricBilinAt_nondegenerate x)

/-- The Einstein condition for the canonical Levi-Civita connection. -/
def IsEinsteinAt (lam : ℝ) (x : M) : Prop :=
  CovariantDerivative.IsEinsteinAt g.leviCivita g.inner lam x

theorem isEinsteinAt_iff (lam : ℝ) (x : M) :
    g.IsEinsteinAt lam x ↔
      ∀ u w : TM x, g.ricciAt x u w = lam * g.inner x u w :=
  Iff.rfl

/-- An Einstein metric has scalar curvature `n * lam`. -/
theorem scalarAt_eq_nat_mul_of_isEinsteinAt {lam : ℝ} {x : M}
    (hEin : g.IsEinsteinAt lam x) :
    g.scalarAt x = n * lam := by
  have hscalar :=
    CovariantDerivative.scalarCurvatureAt_of_einstein
      (cov := g.leviCivita) (g := g.inner) (lam := lam) (x := x)
      (b := g.metricBilinAt x) (hb := g.metricBilinAt_nondegenerate x)
      (fun v w ↦ g.metricBilinAt_apply x v w) hEin
  calc
    g.scalarAt x = lam * Module.finrank ℝ E := by
      simpa [scalarAt] using hscalar
    _ = n * lam := by
      rw [finrank_euclideanSpace_fin]
      ring

/-- The canonical Ricci tensor is additive in its first argument. -/
theorem ricciAt_add_left (x : M) (u u' w : TM x) :
    g.ricciAt x (u + u') w = g.ricciAt x u w + g.ricciAt x u' w := by
  simpa [ricciAt] using
    CovariantDerivative.ricciBilinearAt_add_left g.leviCivita x u u' w

/-- The canonical Ricci tensor is homogeneous in its first argument. -/
theorem ricciAt_smul_left (x : M) (c : ℝ) (u w : TM x) :
    g.ricciAt x (c • u) w = c • g.ricciAt x u w := by
  simpa [ricciAt] using
    CovariantDerivative.ricciBilinearAt_smul_left g.leviCivita x c u w

/-- The canonical Ricci tensor is additive in its second argument. -/
theorem ricciAt_add_right (x : M) (u w w' : TM x) :
    g.ricciAt x u (w + w') = g.ricciAt x u w + g.ricciAt x u w' := by
  simpa [ricciAt] using
    CovariantDerivative.ricciBilinearAt_add_right g.leviCivita x u w w'

/-- The canonical Ricci tensor is homogeneous in its second argument. -/
theorem ricciAt_smul_right (x : M) (c : ℝ) (u w : TM x) :
    g.ricciAt x u (c • w) = c • g.ricciAt x u w := by
  simpa [ricciAt] using
    CovariantDerivative.ricciBilinearAt_smul_right g.leviCivita x c u w

/-- The canonical Ricci tensor is symmetric. -/
theorem ricciAt_symm (x : M) (u w : TM x) :
    g.ricciAt x u w = g.ricciAt x w u := by
  simpa [ricciAt] using
    CovariantDerivative.ricciBilinearAt_symm g.leviCivita
      (fun y ↦ g.leviCivita_torsionFreeAt y)
      (fun y ↦ g.leviCivita_metricCompatibleAt y)
      (fun v w ↦ g.inner_symm x v w)
      (fun v hv ↦ LeviCivitaExistence.metric_nondegenerate g x v hv)
      (fun A B hA hB ↦ metric_pairing_contMDiffAt_two g hA hB)
      (fun A B hA hB ↦ metric_pairing_mdiffAt g hA hB)
      u w

end Curvature

section CurvatureRegularityInstance

variable (g : ClosedSmoothRiemannianMetric n M)

/--
The canonical Ricci tensor is symmetric; the Levi-Civita regularity hypothesis
is supplied by the canonical instance.
-/
theorem ricciAt_symm' (x : M) (u w : TM x) :
    g.ricciAt x u w = g.ricciAt x w u := by
  exact g.ricciAt_symm x u w

end CurvatureRegularityInstance

end ClosedSmoothRiemannianMetric
end Poincare
