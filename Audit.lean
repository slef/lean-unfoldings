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
  -- Inspect module data as well as exported signatures: the module system can
  -- expose a proved theorem as an opaque signature in the public environment.
  for i in [:environment.header.moduleNames.size] do
    let moduleName := environment.header.moduleNames[i]!
    if moduleName == `Unfoldings || moduleName.toString.startsWith "Unfoldings." then
      for info in environment.header.moduleData[i]!.constants do
        let name := info.name
        for dependency in (← collectAxioms name) do
          unless allowed.contains dependency do
            throwError "{name} depends on an unapproved axiom: {dependency}"
        declarations := declarations + 1
  if declarations == 0 then
    throwError "The unfolding library contains no audited declarations."
  logInfo m!"Audited {declarations} unfolding declarations; only standard Lean axioms occur."
