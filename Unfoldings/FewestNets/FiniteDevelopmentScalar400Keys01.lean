module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group08
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group09
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group10
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group11
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group12
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group13
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group14
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group15

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup08_keys :
    q400DevelopmentScalarGroup08.flatten.map Prod.fst = ((meshRecordKeys 400).drop 1152).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup09_keys :
    q400DevelopmentScalarGroup09.flatten.map Prod.fst = ((meshRecordKeys 400).drop 1296).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup10_keys :
    q400DevelopmentScalarGroup10.flatten.map Prod.fst = ((meshRecordKeys 400).drop 1440).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup11_keys :
    q400DevelopmentScalarGroup11.flatten.map Prod.fst = ((meshRecordKeys 400).drop 1584).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup12_keys :
    q400DevelopmentScalarGroup12.flatten.map Prod.fst = ((meshRecordKeys 400).drop 1728).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup13_keys :
    q400DevelopmentScalarGroup13.flatten.map Prod.fst = ((meshRecordKeys 400).drop 1872).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup14_keys :
    q400DevelopmentScalarGroup14.flatten.map Prod.fst = ((meshRecordKeys 400).drop 2016).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup15_keys :
    q400DevelopmentScalarGroup15.flatten.map Prod.fst = ((meshRecordKeys 400).drop 2160).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
