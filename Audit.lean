module

import Unfoldings
import Lean.Util.CollectAxioms

/-! Reject unfinished proofs and nonstandard axioms in all public library dependencies.
The audit follows the same transitive-axiom approach as slef/EdgeUnfoldings. -/

open Lean in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut planarDeclarations : Nat := 0
  -- Inspect module data as well as exported signatures: the module system can
  -- expose a proved theorem as an opaque signature in the public environment.
  for i in [:environment.header.moduleNames.size] do
    let moduleName := environment.header.moduleNames[i]!
    let project := moduleName == `Unfoldings || moduleName.toString.startsWith "Unfoldings."
    let planar := moduleName == `Schoenflies || moduleName.toString.startsWith "Schoenflies."
    if project || planar then
      for info in environment.header.moduleData[i]!.constants do
        let name := info.name
        for dependency in (← collectAxioms name) do
          unless allowed.contains dependency do
            throwError "{name} depends on an unapproved axiom: {dependency}"
        if project then
          declarations := declarations + 1
        else
          planarDeclarations := planarDeclarations + 1
  if declarations == 0 then
    throwError "The unfolding library contains no audited declarations."
  logInfo (m!"Audited {declarations} unfolding and {planarDeclarations} pinned " ++
    m!"planar-topology declarations; only standard Lean axioms occur.")

-- Public abstract statements and definitions must be independent of implementation
-- declarations. Background libraries cannot depend on this project, so checking
-- every abstract declaration follows all possible transitive project references.
open Lean in
run_cmd do
  let environment ← getEnv
  let abstractNamespace := `Unfoldings.CapAbstract
  let mut checked : Nat := 0
  for i in [:environment.header.moduleNames.size] do
    if environment.header.moduleNames[i]! == `Unfoldings.Cap.Abstract then
      for info in environment.header.moduleData[i]!.constants do
        if abstractNamespace.isPrefixOf info.name then
          let mut dependencies := info.type.getUsedConstants
          unless info.isTheorem do
            if let some value := info.value? (allowOpaque := true) then
              dependencies := dependencies ++ value.getUsedConstants
          for dependency in dependencies do
            let project := (`Unfoldings).isPrefixOf dependency ||
              (`Schoenflies).isPrefixOf dependency
            if project && !abstractNamespace.isPrefixOf dependency then
              throwError "Abstract declaration {info.name} exposes implementation {dependency}"
          checked := checked + 1
  if checked == 0 then
    throwError "The independent cap abstract is missing from the default build."
  logInfo (m!"Audited {checked} cap abstract declarations; " ++
    m!"public definitions and statements are independent.")
