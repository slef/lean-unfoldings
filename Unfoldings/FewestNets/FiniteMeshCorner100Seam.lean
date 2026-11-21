module

public import Unfoldings.FewestNets.FiniteMeshCornerBlocks

/-! Frequency-100 seam and pentagon corner checks. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
set_option maxHeartbeats 40000000 in
-- Check every seam block separately.
theorem checkQ100SeamCornerBlocks (i : Fin 5) :
    checkSeamCornerBlock 100 12 i 700 107 = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 16384 in
-- Check the five corners of the original-vertex star.
theorem checkQ100PentagonCorners : checkPentagonCorners 100 700 107 = true := by
  decide +kernel

end Unfoldings.FewestNets
