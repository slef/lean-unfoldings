module

public import Unfoldings.FewestNets.FiniteMeshCornerBlocks

/-! Frequency-400 interior corner blocks 238 through 251. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 65536 in
set_option maxHeartbeats 80000000 in
-- Check each 48-key block separately so the interval intermediates stay bounded.
theorem checkQ400FaceCornerBlocks_17 (i : Fin 14) :
    checkFaceCornerBlock 400 48 (i.val + 238) 2200 108 = true := by
  fin_cases i <;> decide +kernel

end Unfoldings.FewestNets
