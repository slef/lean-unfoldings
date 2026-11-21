module

public import Unfoldings.FewestNets.FiniteMeshPerimeter400Data

/-! Frequency-400 seam and pentagon perimeter blocks. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 65536 in
set_option maxHeartbeats 40000000 in
-- Reduce each 48-key enclosure separately.
theorem checkQ400SeamPerimeterBlocks (i : Fin 5) :
    checkQ400SeamPerimeterBlock i = true := by
  fin_cases i <;> decide +kernel

theorem checkQ400PentagonPerimeter_eq : checkQ400PentagonPerimeter = true := by
  decide +kernel

end Unfoldings.FewestNets
