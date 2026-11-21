module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group32
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group33
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group34
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group35
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group36
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group37
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group38
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group39

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup32_keys :
    q400DevelopmentScalarGroup32.flatten.map Prod.fst = ((meshRecordKeys 400).drop 4608).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup33_keys :
    q400DevelopmentScalarGroup33.flatten.map Prod.fst = ((meshRecordKeys 400).drop 4752).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup34_keys :
    q400DevelopmentScalarGroup34.flatten.map Prod.fst = ((meshRecordKeys 400).drop 4896).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup35_keys :
    q400DevelopmentScalarGroup35.flatten.map Prod.fst = ((meshRecordKeys 400).drop 5040).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup36_keys :
    q400DevelopmentScalarGroup36.flatten.map Prod.fst = ((meshRecordKeys 400).drop 5184).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup37_keys :
    q400DevelopmentScalarGroup37.flatten.map Prod.fst = ((meshRecordKeys 400).drop 5328).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup38_keys :
    q400DevelopmentScalarGroup38.flatten.map Prod.fst = ((meshRecordKeys 400).drop 5472).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup39_keys :
    q400DevelopmentScalarGroup39.flatten.map Prod.fst = ((meshRecordKeys 400).drop 5616).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
