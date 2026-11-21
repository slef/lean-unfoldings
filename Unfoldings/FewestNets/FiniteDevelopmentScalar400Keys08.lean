module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group64
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group65
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group66
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group67
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group68
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group69
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group70
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group71

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup64_keys :
    q400DevelopmentScalarGroup64.flatten.map Prod.fst = ((meshRecordKeys 400).drop 9216).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup65_keys :
    q400DevelopmentScalarGroup65.flatten.map Prod.fst = ((meshRecordKeys 400).drop 9360).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup66_keys :
    q400DevelopmentScalarGroup66.flatten.map Prod.fst = ((meshRecordKeys 400).drop 9504).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup67_keys :
    q400DevelopmentScalarGroup67.flatten.map Prod.fst = ((meshRecordKeys 400).drop 9648).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup68_keys :
    q400DevelopmentScalarGroup68.flatten.map Prod.fst = ((meshRecordKeys 400).drop 9792).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup69_keys :
    q400DevelopmentScalarGroup69.flatten.map Prod.fst = ((meshRecordKeys 400).drop 9936).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup70_keys :
    q400DevelopmentScalarGroup70.flatten.map Prod.fst = ((meshRecordKeys 400).drop 10080).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup71_keys :
    q400DevelopmentScalarGroup71.flatten.map Prod.fst = ((meshRecordKeys 400).drop 10224).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
