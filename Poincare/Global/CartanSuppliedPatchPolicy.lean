import Poincare.Global.CartanSuppliedBufferedPairAgreement
import Poincare.Global.CartanSuppliedReachableChain

/-!
# Core selection and sticky supplied chains

The preferred label is external to the geometric state. Selection retains it
exactly while both anchors belong to its cores, and otherwise uses the cover.
The resulting policy supplies steps even at states outside its realized history.
-/

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain

namespace CartanSuppliedPatchPolicy
open CartanSuppliedFinitePatchCover CartanSuppliedUniformPatchSwitch

def fallback (B : QuantitativeCover g) (s : CartanChain.ChainState g) : B.Label :=
  (B.source.pick s.anchor, B.target.pick s.target)

def select (B : QuantitativeCover g) (preferred : B.Label)
    (s : CartanChain.ChainState g) : B.Label :=
  @ite _ (B.Valid preferred s) (Classical.propDecidable _) preferred (fallback B s)

def policy (B : QuantitativeCover g) (preferred : ℕ → B.Label) :
    ℕ → CartanChain.ChainState g → Interpretation g :=
  fun n s => B.interp (select B (preferred n) s)

def Sticky (B : QuantitativeCover g) (preferred : ℕ → B.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain (policy B preferred) nodes initial) : Prop :=
  ∀ n, preferred (n + 1) = select B (preferred n) (c.state n)

/-- Retaining a valid preference or choosing covering cores always gives valid anchors. -/
theorem select_valid : ∀ (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g), B.Valid (select B a s) s := by
  intro B a s
  classical
  unfold select
  split_ifs with h
  · exact h
  · exact ⟨Classical.choose_spec (B.source.covers s.anchor),
      Classical.choose_spec (B.target.covers s.target)⟩

end CartanSuppliedPatchPolicy
end Poincare
