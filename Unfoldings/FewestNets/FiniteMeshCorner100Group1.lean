module

public import Unfoldings.FewestNets.FiniteMeshCornerBlocks

/-! The first ten blocks of the frequency-100 interior corner checks. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
set_option maxHeartbeats 40000000 in
-- Check each twelve-key block separately so the interval intermediates stay bounded.
theorem checkQ100FaceCornerBlocks_0 (i : Fin 10) :
    checkFaceCornerBlock 100 12 i 700 107 = true := by
  fin_cases i <;> decide +kernel

end Unfoldings.FewestNets
