import Poincare.Global.DeTurckCompactCoefficientDefinitions
import Poincare.Global.ParabolicCutoffCommutator

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace Poincare.DeTurckCoupledForcing
open DeTurckPrincipalSecondJet

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- The original nine-entry Pi norm over the unchanged solution Graph. -/
abbrev Inputs (α T : ℝ) := (Fin 3 × Fin 3) → ParabolicSolutionGraph.Graph (E := E) α T
abbrev Coeff0 (α T : ℝ) := Fin 3 → Fin 3 → ParabolicHolder.Y (E := E) α T ℝ
abbrev Coeff1 (α T : ℝ) := Fin 3 → Fin 3 → Fin 3 → ParabolicHolder.Y (E := E) α T ℝ

/-- The actual whole tensor reconstructed from its scalar Graph entries. -/
def tensorValue {α T : ℝ} (W : Inputs α T) (q : ℝ × E) : Bilin :=
  ∑ a : Fin 3, ∑ b : Fin 3, (W (a,b)).u q • DeTurckTensorBasis.tensor a b

/-- The spatial jet reconstructed from the genuine Graph derivative carriers. -/
def tensorJet {α T : ℝ} (W : Inputs α T) (q : ℝ × E) : Jet1 :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    ((W (a,b)).du q).smulRight (DeTurckTensorBasis.tensor a b)

/-- Explicit scalar coupled action, retaining every input tensor and direction slot. -/
def value {α T : ℝ} (c0 : Coeff0 α T) (c1 : Coeff1 α T)
    (W : Inputs α T) (q : ℝ × E) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (c0 a b q * (W (a,b)).u q +
    ∑ p : Fin 3, c1 p a b q * (W (a,b)).du q (basis3 p))

/-- The existing interpolation constants keep the two distinct time powers. -/
def timeBound {α T : ℝ} (c0 : Coeff0 α T) (c1 : Coeff1 α T) : ℝ :=
  24 * ((∑ a : Fin 3, ∑ b : Fin 3, ∑ p : Fin 3, ‖c1 p a b‖) *
    T ^ ((1 - α) / 2) + (∑ a : Fin 3, ∑ b : Fin 3, ‖c0 a b‖) *
    T ^ (1 - α / 2))

end Poincare.DeTurckCoupledForcing
