import Lean

/-!
# Audit guard commands

`#std_axioms c₁ c₂ …` resolves every identifier exactly like `#print axioms` does
(`realizeGlobalConstWithInfos`, so a missing or ambiguous name is an error) and then
fails elaboration unless the axiom closure of each constant is contained in
`{propext, Classical.choice, Quot.sound}`.  Nothing is logged on success, so a Lake
rebuild of a cached audit module replays no messages.

The error text is parsed by `scripts/axiom_audit.sh`, which maps a
`sorryAx`/placeholder dependency and a nonstandard axiom onto the same `FAIL:` lines the
legacy `#print axioms` text scan produced.
-/

namespace PoincareAudit

open Lean Elab Command

/-- Axioms accepted by the axiom footprint audit (mirrors the legacy allow-list). -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Fail unless every axiom in the closure of each named constant is standard. -/
elab "#std_axioms " ids:ident+ : command => do
  for id in ids do
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    for c in cs do
      let axioms ← collectAxioms c
      for a in axioms do
        unless standardAxioms.contains a do
          logErrorAt id m!"nonstandard axiom '{a}' in '{c}'"

end PoincareAudit
