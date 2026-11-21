module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group72
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group73
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group74
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group75
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group76
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group77
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group78
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group79

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup72_keys :
    q400DevelopmentScalarGroup72.flatten.map Prod.fst = ((meshRecordKeys 400).drop 10368).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup73_keys :
    q400DevelopmentScalarGroup73.flatten.map Prod.fst = ((meshRecordKeys 400).drop 10512).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup74_keys :
    q400DevelopmentScalarGroup74.flatten.map Prod.fst = ((meshRecordKeys 400).drop 10656).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup75_keys :
    q400DevelopmentScalarGroup75.flatten.map Prod.fst = ((meshRecordKeys 400).drop 10800).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup76_keys :
    q400DevelopmentScalarGroup76.flatten.map Prod.fst = ((meshRecordKeys 400).drop 10944).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup77_keys :
    q400DevelopmentScalarGroup77.flatten.map Prod.fst = ((meshRecordKeys 400).drop 11088).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup78_keys :
    q400DevelopmentScalarGroup78.flatten.map Prod.fst = ((meshRecordKeys 400).drop 11232).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup79_keys :
    q400DevelopmentScalarGroup79.flatten.map Prod.fst = ((meshRecordKeys 400).drop 11376).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
