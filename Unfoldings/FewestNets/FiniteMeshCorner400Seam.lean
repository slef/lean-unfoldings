module

public import Unfoldings.FewestNets.FiniteMeshCornerBlocks

/-! Frequency-400 seam and pentagon corner checks. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 65536 in
set_option maxHeartbeats 80000000 in
-- Check every seam block separately.
theorem checkQ400SeamCornerBlocks (i : Fin 5) :
    checkSeamCornerBlock 400 48 i 2200 108 = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 16384 in
-- Check the five corners of the original-vertex star.
theorem checkQ400PentagonCorners : checkPentagonCorners 400 2200 108 = true := by
  decide +kernel

end Unfoldings.FewestNets
