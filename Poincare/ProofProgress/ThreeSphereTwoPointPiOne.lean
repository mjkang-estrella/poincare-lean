import Poincare.Statement

namespace Poincare

/--
The two-puncture complement in the standard three-sphere has trivial
fundamental group at every basepoint.
-/
theorem threeSphere_twoPointComplement_fundamentalGroup_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  letI : SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hab
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/--
The equivalent first homotopy group formulation of the two-puncture complement
triviality.
-/
theorem threeSphere_twoPointComplement_piOne_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  exact ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := (({a} ∪ {b})ᶜ : Set ThreeSphere)) (x := x)).subsingleton_congr).mpr
      (threeSphere_twoPointComplement_fundamentalGroup_subsingleton hab x)

end Poincare
