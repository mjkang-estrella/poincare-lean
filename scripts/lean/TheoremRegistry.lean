import Lean

/-! Read declarations and dependencies from an imported Lean environment. -/

open Lean Meta

namespace TheoremRegistry

structure MatchRequest where
  id : String
  candidate : String := ""
  expected : String
  deriving FromJson

structure Request where
  modules : Array String
  names : Array String := #[]
  includeModuleDeclarations : Bool := true
  checks : Array MatchRequest := #[]
  deriving FromJson

def strings (xs : Array Name) : Json :=
  toJson ((xs.map Name.toString).qsort (· < ·))

partial def usedConstants (e : Expr) (seen : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => seen.insert n
  | .proj n _ e => usedConstants e (seen.insert n)
  | .app f a => usedConstants a (usedConstants f seen)
  | .lam _ t b _ | .forallE _ t b _ => usedConstants b (usedConstants t seen)
  | .letE _ t v b _ => usedConstants b (usedConstants v (usedConstants t seen))
  | .mdata _ e => usedConstants e seen
  | _ => seen

def dependencies (e : Expr) : Array Name := (usedConstants e).toArray

def computationDependencies : ConstantInfo → Array Name
  | .inductInfo i => i.all.toArray ++ i.ctors.toArray
  | .ctorInfo i => #[i.induct]
  | .recInfo i => i.all.toArray ++ (i.rules.toArray.flatMap fun r => #[r.ctor] ++ dependencies r.rhs)
  | _ => #[]

def computationMetadata : ConstantInfo → Json
  | .inductInfo i => Json.mkObj [
      ("num_parameters", toJson i.numParams), ("num_indices", toJson i.numIndices),
      ("mutual_types", toJson (i.all.map Name.toString)), ("num_nested", toJson i.numNested),
      ("is_recursive", toJson i.isRec), ("is_unsafe", toJson i.isUnsafe),
      ("is_reflexive", toJson i.isReflexive)]
  | .ctorInfo i => Json.mkObj [
      ("inductive", toJson i.induct.toString), ("constructor_index", toJson i.cidx),
      ("num_parameters", toJson i.numParams), ("num_fields", toJson i.numFields),
      ("is_unsafe", toJson i.isUnsafe)]
  | .recInfo i => Json.mkObj [
      ("mutual_types", toJson (i.all.map Name.toString)),
      ("num_parameters", toJson i.numParams), ("num_indices", toJson i.numIndices),
      ("num_motives", toJson i.numMotives), ("num_minors", toJson i.numMinors),
      ("k_reduction", toJson i.k), ("is_unsafe", toJson i.isUnsafe),
      ("rules", toJson (i.rules.map fun r => Json.mkObj [
        ("constructor", toJson r.ctor.toString), ("num_fields", toJson r.nfields),
        ("rhs", toJson (reprStr r.rhs))]))]
  | .defnInfo i => Json.mkObj [("safety", toJson (reprStr i.safety))]
  | .opaqueInfo i => Json.mkObj [("is_unsafe", toJson i.isUnsafe)]
  | .axiomInfo i => Json.mkObj [("is_unsafe", toJson i.isUnsafe)]
  | _ => Json.null

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def moduleOf (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some i => env.header.moduleNames[i]!.toString
  | none => ""

def pretty (e : Expr) : MetaM String :=
  return (← ppExpr e).pretty 120

def exportDeclaration (env : Environment) (name : Name) : MetaM Json := do
  let some ci := env.find? name | return Json.mkObj [("name", toJson name.toString), ("present", toJson false)]
  let binders ← forallTelescope ci.type fun xs body => do
    let mut result := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      result := result.push (Json.mkObj [
        ("name", toJson d.userName.toString),
        ("type", toJson (← pretty d.type)),
        ("binder_info", toJson (reprStr d.binderInfo)),
        ("is_proposition", toJson (← isProp d.type))])
    return (result, ← pretty body)
  let valueDeps := (ci.value? (allowOpaque := true)).map dependencies |>.getD #[]
  let sourceRange := (← findDeclarationRanges? name).map fun ranges =>
    Json.mkObj [("line", toJson ranges.range.pos.line),
      ("column", toJson ranges.range.pos.column),
      ("end_line", toJson ranges.range.endPos.line),
      ("end_column", toJson ranges.range.endPos.column)]
  return Json.mkObj [
    ("name", toJson name.toString), ("present", toJson true),
    ("kind", toJson (kind ci)), ("module", toJson (moduleOf env name)),
    ("is_unsafe", toJson ci.isUnsafe),
    ("is_partial", toJson ci.isPartial),
    ("source_range", toJson sourceRange),
    ("type", toJson (← pretty ci.type)), ("type_expr", toJson (reprStr ci.type)),
    ("universe_parameters", toJson (ci.levelParams.map Name.toString)),
    ("description", toJson ((← findDocString? env name).getD "")),
    ("binders", toJson binders.1), ("conclusion", toJson binders.2),
    ("is_proposition", toJson (← isProp ci.type)),
    ("statement_dependencies", strings (dependencies ci.type)),
    ("proof_dependencies", strings (if ← isProp ci.type then valueDeps else #[])),
    ("value_dependencies", strings valueDeps),
    ("axioms", strings (← collectAxioms name))]

/-- Semantic closure retains definition bodies and inductive constructors,
but proof bodies are intentionally excluded from statement fingerprints. -/
partial def semanticClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (records : Array Json := #[]) : MetaM (Array Json) := do
  match todo with
  | [] => return records
  | name :: rest =>
    if seen.contains name then return ← semanticClosure env rest seen records
    let seen := seen.insert name
    let some ci := env.find? name | throwError "Missing semantic dependency {name}"
    let proof ← if ci.isTheorem then pure true else isProp ci.type
    let value := if proof then none else ci.value? (allowOpaque := true)
    let ctors := match ci with | .inductInfo i => i.ctors.toArray | _ => #[]
    let deps := dependencies ci.type ++ (value.map dependencies |>.getD #[]) ++ computationDependencies ci
    let record := Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("is_unsafe", toJson ci.isUnsafe),
      ("is_partial", toJson ci.isPartial),
      ("module", toJson (moduleOf env name)),
      ("type_expr", toJson (reprStr ci.type)),
      ("universe_parameters", toJson (ci.levelParams.map Name.toString)),
      ("computation_metadata", computationMetadata ci),
      ("value_expr", toJson (value.map reprStr)),
      ("constructors", strings ctors),
      ("dependencies", strings deps)]
    semanticClosure env (deps.toList ++ rest) seen (records.push record)

def checkMatch (env : Environment) (req : MatchRequest) : MetaM Json := do
  let expected := req.expected.toName
  let some expectedInfo := env.find? expected | throwError "Unknown expected statement {expected}"
  let expectedExpr := mkConst expected (expectedInfo.levelParams.map Level.param)
  unless ← isProp expectedExpr do throwError "Expected symbol {expected} does not denote a closed proposition"
  let mut matched := false
  let mut candidatePresent := false
  if let some ci := env.find? req.candidate.toName then
    candidatePresent := true
    if ci.levelParams.length == expectedInfo.levelParams.length then
      let target := mkConst expected (ci.levelParams.map Level.param)
      matched ← withTransparency .all <| isDefEq ci.type target
  return Json.mkObj [
    ("id", toJson req.id), ("candidate", toJson req.candidate),
    ("expected", toJson req.expected), ("candidate_present", toJson candidatePresent),
    ("exact_type_match", toJson matched)]

def exportRequest (env : Environment) (req : Request) : MetaM Json := do
  let mut names : NameSet := {}
  for name in req.names do names := names.insert name.toName
  if req.includeModuleDeclarations then
    for (name, _) in env.constants.toList do
      if req.modules.contains (moduleOf env name) then names := names.insert name
  for m in req.checks do
    names := names.insert m.expected.toName
    if m.candidate != "" then names := names.insert m.candidate.toName
  let mut records := #[]
  for name in names.toArray.qsort (fun a b => a.toString < b.toString) do
    records := records.push (← exportDeclaration env name)
  let mut checks := #[]
  for req in req.checks do checks := checks.push (← checkMatch env req)
  let closure ← semanticClosure env (req.checks.toList.map fun r => r.expected.toName)
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("declarations", toJson records),
    ("matches", toJson checks), ("semantic_declarations", toJson closure),
    ("imported_modules", strings env.header.moduleNames)]

end TheoremRegistry

unsafe def main (args : List String) : IO UInt32 := do
  let [config] := args | throw (IO.userError "usage: lean --run TheoremRegistry.lean REQUEST.json")
  let raw ← IO.FS.readFile config
  let json ← IO.ofExcept (Json.parse raw)
  let req : TheoremRegistry.Request ← IO.ofExcept (fromJson? json)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (req.modules.map fun m => { module := m.toName }) {} (loadExts := true)
  let options := Options.empty.setBool `pp.all true |>.set `maxRecDepth (100000 : Nat)
    |>.set `maxHeartbeats (10000000 : Nat)
  let (result, _, _) ← (TheoremRegistry.exportRequest env req).toIO
    { fileName := "<theorem-registry>", fileMap := default, options := options } { env := env }
  IO.println result.compress
  return 0
