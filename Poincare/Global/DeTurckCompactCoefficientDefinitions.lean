import Poincare.Global.DeTurckActualSpatialCoefficients
import Poincare.Global.DeTurckTensorBasisReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100
open Set Filter
open scoped Manifold ContDiff Topology BigOperators
universe u
namespace Poincare.DeTurckCompactCoefficients
open DeTurckPrincipalSecondJet DeTurckCoefficients DeTurckJetLinearization

local instance : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
    (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace
local instance : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup
local instance : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace
local instance : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Bilin) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Bilin) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Jet1 →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Jet1) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Jet1 →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Jet1) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The actual chart zone with a fixed-anchor cutoff-one germ. -/
def zone (anchor : M) : Set E :=
  (extChartAt (closedSmoothModelWithCorners 3) anchor).target ∩
    {z | ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1}

/-- Actual zero-order field, retaining inverse variation against D2g0. -/
def field0 (g0 bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M)
    (z : E) : Bilin →L[ℝ] Bilin :=
  let G : E → Bilin := CovariantDerivative.chartMetric
    (I := closedSmoothModelWithCorners 3) g0.inner anchor
  let B : E → Background := GeodesicTransport.chartChristoffelField bg anchor
  DeTurckSpatialCoefficients.zeroOrder (B z) (fderiv ℝ B z)
    (G z) (fderiv ℝ G z) (fderiv ℝ (fderiv ℝ G) z)

/-- Actual first-order field of the metric first-jet variation. -/
def field1 (g0 bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M)
    (z : E) : Jet1 →L[ℝ] Bilin :=
  let G : E → Bilin := CovariantDerivative.chartMetric
    (I := closedSmoothModelWithCorners 3) g0.inner anchor
  let B : E → Background := GeodesicTransport.chartChristoffelField bg anchor
  DeTurckSpatialCoefficients.firstOrder (B z) (fderiv ℝ B z)
    (G z) (fderiv ℝ G z)

/-- Scalar entries of the actual zero-order action on every tensor slot. -/
def raw0 (g0 bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M)
    (a b c d : Fin 3) (z : E) : ℝ :=
  DeTurckInverseEntryDerivative.entryCLM c d
    (field0 g0 bg anchor z (DeTurckTensorBasis.tensor a b))

/-- Scalar entries of the actual first-order action on every direction/tensor slot. -/
def raw1 (g0 bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M)
    (p a b c d : Fin 3) (z : E) : ℝ :=
  DeTurckInverseEntryDerivative.entryCLM c d
    (field1 g0 bg anchor z (DeTurckTensorBasis.firstJet p a b))

end Poincare.DeTurckCompactCoefficients
