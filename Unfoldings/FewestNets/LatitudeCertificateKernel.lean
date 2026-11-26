module

public import Unfoldings.FewestNets.LatitudeCertificateCover
public import Unfoldings.FewestNets.CheckedLatitudeCoefficient

/-! Produce reflexivity proofs whose interval arithmetic is reduced by the kernel. -/

public meta section

open Lean Elab Tactic

/-- Leave reduction of a Boolean equality to the kernel. The real angle may
remain a free variable because it occurs only in the enclosure proofs. -/
elab "latitude_certificate_rfl" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    goal.assign (← Meta.mkEqRefl (mkConst ``Bool.true))
  replaceMainGoal []

end
