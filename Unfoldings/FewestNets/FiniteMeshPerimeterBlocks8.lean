module

public import Unfoldings.FewestNets.FiniteMeshPerimeterData

/-! The seam and pentagon perimeter blocks at frequency 100. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
-- Reduce each twelve-key enclosure separately.
theorem checkQ100SeamPerimeterBlocks (i : Fin 5) :
    checkQ100SeamPerimeterBlock i = true := by
  fin_cases i <;> decide +kernel

theorem checkQ100PentagonPerimeter_eq : checkQ100PentagonPerimeter = true := by
  decide +kernel

end Unfoldings.FewestNets
