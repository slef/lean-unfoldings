module

public import Unfoldings.FewestNets.FiniteMeshCornerBlocks

/-! Frequency-100 interior corner blocks 60 through 69. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
set_option maxHeartbeats 40000000 in
-- Check each twelve-key block separately so the interval intermediates stay bounded.
theorem checkQ100FaceCornerBlocks_6 (i : Fin 10) :
    checkFaceCornerBlock 100 12 (i.val + 60) 700 107 = true := by
  fin_cases i <;> decide +kernel

end Unfoldings.FewestNets
