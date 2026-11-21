module

public import Unfoldings.FewestNets.FiniteDevelopmentScalarBlocks
public import Mathlib.Tactic.FinCases

/-! Kernel checks of frequency-100 scalar blocks 16 through 23. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 16384 in
set_option maxHeartbeats 40000000 in
-- Each theorem reduces several blocks of exact interval checks.
theorem checkQ100DevelopmentScalarBlock_group3 (i : Fin 8) :
    checkQ100DevelopmentScalarBlock (16 + i.val) = true := by
  fin_cases i <;> decide +kernel

end Unfoldings.FewestNets
