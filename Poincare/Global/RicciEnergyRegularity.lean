import Poincare.Global.VolumeMeasureOpenPositivity

/-!
# Automatic regularity of Ricci energies

The Ricci tensor of a closed smooth metric is differentiable in canonical
local extensions.  Finite Gram contractions therefore make `|Ric|²` and
`|Ric°|²` continuous.  Compactness and finite Riemannian volume then make
both functions integrable.  This removes the final regularity parameters from
the zero-traceless-energy Hamilton endpoint.
-/

noncomputable section

open Bundle FiberBundle Filter Set MeasureTheory
open scoped Manifold ContDiff MeasureTheory Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

private theorem continuousAt_finset_sum_real
    {ι : Type*} {x : M} (s : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : M ↦ (0 : ℝ)) x)
  | @insert a s ha ih =>
      have haCont : ContinuousAt (f a) x := hf a (Finset.mem_insert_self a s)
      have hsCont : ContinuousAt (fun y ↦ ∑ i ∈ s, f i y) x :=
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using haCont.add hsCont

/-- The squared Ricci norm of an arbitrary closed smooth metric is continuous
at every point. -/
theorem ricciNormSqAt_continuousAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ContinuousAt (fun y : M ↦ g.ricciNormSqAt y) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let rhs : M → ℝ := fun y ↦
    ∑ a, ∑ b', ∑ c, ∑ d,
      (gramMatrix g x y)⁻¹ a c *
        (gramMatrix g x y)⁻¹ b' d *
        g.ricciAt y (gramFrame x y a) (gramFrame x y b') *
        g.ricciAt y (gramFrame x y c) (gramFrame x y d)
  have hMetric : MetricExtContMDiffAt g x 2 :=
    metricExtContMDiffAt_two g x
  have hRic : CovTensor2ExtDifferentiableAt (ricciVariationField g) x :=
    covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x
  have hsum : ContinuousAt rhs x := by
    dsimp only [rhs]
    apply continuousAt_finset_sum_real Finset.univ
    intro a _ha
    apply continuousAt_finset_sum_real Finset.univ
    intro b' _hb
    apply continuousAt_finset_sum_real Finset.univ
    intro c _hc
    apply continuousAt_finset_sum_real Finset.univ
    intro d _hd
    have hac : ContinuousAt
        (fun y : M ↦ (gramMatrix g x y)⁻¹ a c) x :=
      (gramMatrix_inv_entry_contMDiffAt_two_of_metricExtContMDiffAt
        g x hMetric a c).continuousAt
    have hbd : ContinuousAt
        (fun y : M ↦ (gramMatrix g x y)⁻¹ b' d) x :=
      (gramMatrix_inv_entry_contMDiffAt_two_of_metricExtContMDiffAt
        g x hMetric b' d).continuousAt
    have hab : ContinuousAt
        (fun y : M ↦
          g.ricciAt y (gramFrame x y a) (gramFrame x y b')) x := by
      simpa [ricciVariationField, gramFrame, b] using
        (hRic (b a) (b b')).continuousAt
    have hcd : ContinuousAt
        (fun y : M ↦
          g.ricciAt y (gramFrame x y c) (gramFrame x y d)) x := by
      simpa [ricciVariationField, gramFrame, b] using
        (hRic (b c) (b d)).continuousAt
    exact (((hac.mul hbd).mul hab).mul hcd)
  exact hsum.congr_of_eventuallyEq
    ((gramMatrix_eventually_isUnit (g := g) x).mono fun y hy ↦ by
      calc
        g.ricciNormSqAt y =
            metricVariationRicciPairingAt g (ricciVariationField g) y :=
          (metricVariationRicciPairingAt_ricci g y).symm
        _ = rhs y := by
          simpa [rhs] using
            metricVariationRicciPairingAt_ricci_eq_sum_gram_inv g x y hy)

/-- Global continuity of the squared Ricci norm. -/
theorem ricciNormSqAt_continuous
    (g : ClosedSmoothRiemannianMetric n M) :
    Continuous (fun y : M ↦ g.ricciNormSqAt y) := by
  rw [continuous_iff_continuousAt]
  exact ricciNormSqAt_continuousAt g

/-- The squared traceless-Ricci norm is continuous. -/
theorem tracelessRicciNormSqAt_continuous
    (g : ClosedSmoothRiemannianMetric n M) :
    Continuous (fun y : M ↦ g.tracelessRicciNormSqAt y) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hRic := ricciNormSqAt_continuousAt g x
  have hScalar : ContinuousAt (fun y : M ↦ g.scalarAt y) x :=
    (scalarAt_continuous g).continuousAt
  have hInv : ContinuousAt (fun _ : M ↦ ((n : ℝ)⁻¹)) x :=
    continuousAt_const
  simpa [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt,
    pow_two, div_eq_mul_inv, mul_assoc] using
    hRic.sub ((hScalar.mul hScalar).mul hInv)

/-- The squared Ricci norm is integrable against Riemannian volume. -/
theorem ricciNormSqAt_integrable
    (g : ClosedSmoothRiemannianMetric n M) :
    Integrable (fun y : M ↦ g.ricciNormSqAt y) (volumeMeasure g) := by
  letI : IsFiniteMeasure (volumeMeasure g) := volumeMeasure_isFiniteMeasure g
  exact (ricciNormSqAt_continuous g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace (fun y : M ↦ g.ricciNormSqAt y))

/-- The squared traceless-Ricci norm is integrable against Riemannian volume. -/
theorem tracelessRicciNormSqAt_integrable
    (g : ClosedSmoothRiemannianMetric n M) :
    Integrable (fun y : M ↦ g.tracelessRicciNormSqAt y) (volumeMeasure g) := by
  letI : IsFiniteMeasure (volumeMeasure g) := volumeMeasure_isFiniteMeasure g
  exact (tracelessRicciNormSqAt_continuous g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace
      (fun y : M ↦ g.tracelessRicciNormSqAt y))

section DimensionThree

variable {N : Type u}
variable [TopologicalSpace N] [T2Space N] [CompactSpace N] [ConnectedSpace N]
variable [MeasurableSpace N] [BorelSpace N]
variable [SecondCountableTopology N] [SimplyConnectedSpace N]
variable [ChartedSpace (ClosedSmoothModel 3) N]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ N]

/-- Fully automatic energy endpoint: zero total traceless-Ricci energy and
positive mean scalar curvature imply Hamilton's reduced pinched limit. -/
theorem hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    [Nonempty N]
    (g : ClosedSmoothRiemannianMetric 3 N)
    (henergy :
      (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) = 0)
    (hmean : 0 < meanScalar g) :
    HamiltonConvergencePinchedLimit3Core N :=
  hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy
    g (tracelessRicciNormSqAt_continuous g)
      (tracelessRicciNormSqAt_integrable g) henergy hmean

end DimensionThree

end Poincare
