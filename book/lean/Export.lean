import Unfoldings.Cap.Abstract
import Unfoldings.Source.Abstract
import Lean

/-!
# Book export

Run from the Lean project root with

    BOOK_NAMES=names.txt BOOK_OUT=consts.json lake env lean book/lean/Export.lean

`BOOK_NAMES` lists one constant per line. For each, the script records the
kind, the signature as the editor hover would print it, the docstring, the
owning module and, for library declarations, the axioms it depends on.

Only the two abstract modules are imported, so the book needs `lake build` of
those modules, not of the whole library.
-/

open Lean Meta Elab Command

namespace BookExport

def kindOf (env : Environment) (n : Name) (inst : Bool) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "recursor"
  | .ctorInfo _ => "constructor"
  | .inductInfo _ =>
      if isClass env n then "class"
      else if isStructure env n then "structure" else "inductive"
  | .defnInfo _ =>
      if inst then "instance"
      else if (getStructureInfo? env n.getPrefix).any (·.fieldNames.contains n.getString!.toName)
        then "field" else "def"

def exportConst (n : Name) : MetaM (Option Json) := do
  let env ← getEnv
  let some info := env.find? n | return none
  let sig ← try
      pure ((← PrettyPrinter.ppSignature n).fmt.pretty 100)
    catch _ => pure s!"{n}"
  let doc ← findDocString? env n
  let mod := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => ""
  let isLocal := (`Unfoldings).isPrefixOf mod.toName
  let axioms ← if isLocal then
      pure <| some ((← collectAxioms n).map (·.toString)).toList
    else pure none
  -- Declaration ranges as LSP positions (zero-based lines, UTF-16 columns),
  -- like the .ilean files; used when an .ilean file omits a declaration.
  let rangeField ← match ← findDeclarationRanges? n with
    | some r => pure [("range", toJson [r.range.pos.line - 1, r.range.charUtf16,
        r.range.endPos.line - 1, r.range.endCharUtf16, r.selectionRange.pos.line - 1,
        r.selectionRange.charUtf16, r.selectionRange.endPos.line - 1,
        r.selectionRange.endCharUtf16])]
    | none => pure []
  let base := [("name", Json.str n.toString), ("kind", Json.str (kindOf env n (← isInstance n) info)),
    ("sig", Json.str sig), ("module", Json.str mod)] ++ rangeField
  let docField := match doc with | some d => [("doc", Json.str d)] | none => []
  let axField := match axioms with
    | some as => [("axioms", Json.arr (as.map Json.str).toArray)]
    | none => []
  return some (Json.mkObj (base ++ docField ++ axField))

/-! ## Dependencies

For each library constant: the constants a reader must understand to read it.
A theorem's statement, a definition's type and body, an inductive type's
constructors, and a structure's fields (also recorded per field). Proofs are
skipped: Lean checks them, so a reader never needs the definitions they use.
Compiler artefacts are mapped back to what the source mentions: constructors and
recursors to their inductive type, projections to their structure. -/

def isLibrary (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Unfoldings).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

/-- What a reference to `c` asks the reader to understand, if anything. -/
def normalize (c : Name) : MetaM (Option Name) := do
  let env ← getEnv
  match env.find? c with
  | none => return none
  | some (.thmInfo _) => return none
  | some (.ctorInfo i) => return some i.induct
  | some (.recInfo _) => return some c.getPrefix
  | some _ =>
    if isAuxRecursor env c || isNoConfusion env c then return some c.getPrefix
    if ← Meta.isMatcher c then return none
    if let some p := env.getProjectionFnInfo? c then return some p.ctorName.getPrefix
    return some c

def quickIsProof (e : Expr) : MetaM Bool := do
  try Meta.isProof e catch _ => pure false

partial def collect (e : Expr) : StateRefT NameSet MetaM Unit := do
  match e with
  | .const c _ => if let some n ← normalize c then modify (·.insert n)
  | .app .. =>
      if ← quickIsProof e then return
      e.withApp fun f args => do
        collect f
        for a in args do collect a
  | .lam n t b bi =>
      if ← quickIsProof e then return
      collect t
      Meta.withLocalDecl n bi t fun x => collect (b.instantiate1 x)
  | .forallE n t b bi =>
      collect t
      Meta.withLocalDecl n bi t fun x => collect (b.instantiate1 x)
  | .letE n t v b _ =>
      collect t; collect v
      Meta.withLetDecl n t v fun x => collect (b.instantiate1 x)
  | .mdata _ e => collect e
  | .proj s _ e => modify (·.insert s); collect e
  | _ => pure ()

def usesOf (e : Expr) : MetaM NameSet := do
  let ((), s) ← (collect e).run {}
  return s

/-- The body a reader sees: the unfolding equation for recursive definitions,
whose compiled values mention recursion combinators instead of the source. -/
def bodyOf (n : Name) (value : Expr) : MetaM Expr := do
  let compiled := value.find? fun e => match e with
    | .const c _ => c.isInternal || c == ``WellFounded.fix || c.getString! == "brecOn"
    | _ => false
  if compiled.isNone then return value
  match ← (try Meta.getUnfoldEqnFor? n (nonRec := true) catch _ => pure none) with
  | some eqn =>
      let some info := (← getEnv).find? eqn | return value
      return info.type
  | none => return value

def namesJson (s : NameSet) (self : Name) : Json :=
  Json.arr ((s.toList.filter (· != self)).map (Json.str ·.toString)).toArray

/-- Dependencies of one constant: `{kind, module, uses, fields?}`. -/
def depsOf (n : Name) : MetaM (Option (Json × NameSet)) := do
  let env ← getEnv
  let some info := env.find? n | return none
  let mod := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => ""
  let kind := kindOf env n (← isInstance n) info
  let mut uses ← usesOf info.type
  let mut fields : Array (String × Json) := #[]
  match info with
  | .defnInfo d => uses := uses.append (← usesOf (← bodyOf n d.value))
  | .inductInfo i =>
      for ctor in i.ctors do
        let some (.ctorInfo c) := env.find? ctor | continue
        uses := uses.append (← usesOf c.type)
      if let some s := getStructureInfo? env n then
        let some (.ctorInfo c) := env.find? i.ctors.head! | pure ()
        let names := s.fieldNames
        fields ← Meta.forallTelescope c.type fun xs _ => do
          let mut acc : Array (String × Json) := #[]
          for h : k in [0:names.size] do
            let some x := xs[c.numParams + k]? | continue
            let t ← Meta.inferType x
            acc := acc.push (names[k].toString, namesJson (← usesOf t) n)
          return acc
  | _ => pure ()
  let base := [("kind", Json.str kind), ("module", Json.str mod), ("uses", namesJson uses n)]
  let fieldsField := if fields.isEmpty then [] else [("fields", Json.mkObj fields.toList)]
  return some (Json.mkObj (base ++ fieldsField), uses)

/-- Dependencies of every library constant reachable from `roots`. -/
def dependencies (roots : Array Name) : MetaM Json := do
  let env ← getEnv
  let mut pending := roots.filter (isLibrary env)
  let mut seen : NameSet := {}
  let mut out : Array (String × Json) := #[]
  while h : pending.size > 0 do
    let n := pending.back
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some (j, uses) ← depsOf n | continue
    out := out.push (n.toString, j)
    for u in uses do
      if isLibrary env u && !seen.contains u then pending := pending.push u
  return Json.mkObj out.toList

end BookExport

-- The export processes every constant the abstract files mention in one command.
-- Give that batch its own finite budget without changing proof-checking limits.
open BookExport in
set_option maxHeartbeats 2000000 in
run_meta do
  let some namesPath ← IO.getEnv "BOOK_NAMES" | throwError "BOOK_NAMES is not set"
  let some outPath ← IO.getEnv "BOOK_OUT" | throwError "BOOK_OUT is not set"
  let names := (← IO.FS.lines namesPath).filter (· ≠ "")
  let mut out : Array Json := #[]
  let mut missing : Array String := #[]
  for line in names do
    match ← exportConst line.toName with
    | some j => out := out.push j
    | none => missing := missing.push line
  let deps ← dependencies (names.map (·.toName))
  IO.FS.writeFile outPath (Json.mkObj [("consts", Json.arr out),
    ("missing", toJson missing), ("deps", deps)]).compress
