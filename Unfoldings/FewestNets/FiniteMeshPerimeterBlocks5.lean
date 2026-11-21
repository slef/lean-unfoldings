module

public import Unfoldings.FewestNets.FiniteMeshPerimeterData

/-! Group 5 of the interior perimeter blocks at frequency 100. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
-- Reduce each twelve-key enclosure separately.
theorem checkQ100FacePerimeterBlocks_4 (i : Fin 10) :
    checkQ100FacePerimeterBlock (i.val + 40) = true := by
  fin_cases i <;> decide +kernel

end Unfoldings.FewestNets
