module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group56
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group57
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group58
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group59
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group60
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group61
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group62
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group63

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup56_keys :
    q400DevelopmentScalarGroup56.flatten.map Prod.fst = ((meshRecordKeys 400).drop 8064).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup57_keys :
    q400DevelopmentScalarGroup57.flatten.map Prod.fst = ((meshRecordKeys 400).drop 8208).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup58_keys :
    q400DevelopmentScalarGroup58.flatten.map Prod.fst = ((meshRecordKeys 400).drop 8352).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup59_keys :
    q400DevelopmentScalarGroup59.flatten.map Prod.fst = ((meshRecordKeys 400).drop 8496).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup60_keys :
    q400DevelopmentScalarGroup60.flatten.map Prod.fst = ((meshRecordKeys 400).drop 8640).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup61_keys :
    q400DevelopmentScalarGroup61.flatten.map Prod.fst = ((meshRecordKeys 400).drop 8784).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup62_keys :
    q400DevelopmentScalarGroup62.flatten.map Prod.fst = ((meshRecordKeys 400).drop 8928).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup63_keys :
    q400DevelopmentScalarGroup63.flatten.map Prod.fst = ((meshRecordKeys 400).drop 9072).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
