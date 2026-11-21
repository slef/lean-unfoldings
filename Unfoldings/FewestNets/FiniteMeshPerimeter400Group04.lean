module

public import Unfoldings.FewestNets.FiniteMeshPerimeter400Data

/-! Frequency-400 interior perimeter blocks 42 through 55. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 65536 in
set_option maxHeartbeats 40000000 in
-- Reduce each 48-key enclosure separately.
theorem checkQ400FacePerimeterBlocks_3 (i : Fin 14) :
    checkQ400FacePerimeterBlock (i.val + 42) = true := by
  fin_cases i <;> decide +kernel

end Unfoldings.FewestNets
