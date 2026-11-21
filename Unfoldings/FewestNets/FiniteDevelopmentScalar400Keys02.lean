module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group16
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group17
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group18
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group19
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group20
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group21
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group22
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group23

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup16_keys :
    q400DevelopmentScalarGroup16.flatten.map Prod.fst = ((meshRecordKeys 400).drop 2304).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup17_keys :
    q400DevelopmentScalarGroup17.flatten.map Prod.fst = ((meshRecordKeys 400).drop 2448).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup18_keys :
    q400DevelopmentScalarGroup18.flatten.map Prod.fst = ((meshRecordKeys 400).drop 2592).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup19_keys :
    q400DevelopmentScalarGroup19.flatten.map Prod.fst = ((meshRecordKeys 400).drop 2736).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup20_keys :
    q400DevelopmentScalarGroup20.flatten.map Prod.fst = ((meshRecordKeys 400).drop 2880).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup21_keys :
    q400DevelopmentScalarGroup21.flatten.map Prod.fst = ((meshRecordKeys 400).drop 3024).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup22_keys :
    q400DevelopmentScalarGroup22.flatten.map Prod.fst = ((meshRecordKeys 400).drop 3168).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup23_keys :
    q400DevelopmentScalarGroup23.flatten.map Prod.fst = ((meshRecordKeys 400).drop 3312).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
