module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group88
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group89
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group90
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group91
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group92
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group93

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup88_keys :
    q400DevelopmentScalarGroup88.flatten.map Prod.fst = ((meshRecordKeys 400).drop 12672).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup89_keys :
    q400DevelopmentScalarGroup89.flatten.map Prod.fst = ((meshRecordKeys 400).drop 12816).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup90_keys :
    q400DevelopmentScalarGroup90.flatten.map Prod.fst = ((meshRecordKeys 400).drop 12960).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup91_keys :
    q400DevelopmentScalarGroup91.flatten.map Prod.fst = ((meshRecordKeys 400).drop 13104).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup92_keys :
    q400DevelopmentScalarGroup92.flatten.map Prod.fst = ((meshRecordKeys 400).drop 13248).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup93_keys :
    q400DevelopmentScalarGroup93.flatten.map Prod.fst = ((meshRecordKeys 400).drop 13392).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
