module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group48
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group49
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group50
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group51
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group52
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group53
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group54
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group55

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup48_keys :
    q400DevelopmentScalarGroup48.flatten.map Prod.fst = ((meshRecordKeys 400).drop 6912).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup49_keys :
    q400DevelopmentScalarGroup49.flatten.map Prod.fst = ((meshRecordKeys 400).drop 7056).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup50_keys :
    q400DevelopmentScalarGroup50.flatten.map Prod.fst = ((meshRecordKeys 400).drop 7200).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup51_keys :
    q400DevelopmentScalarGroup51.flatten.map Prod.fst = ((meshRecordKeys 400).drop 7344).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup52_keys :
    q400DevelopmentScalarGroup52.flatten.map Prod.fst = ((meshRecordKeys 400).drop 7488).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup53_keys :
    q400DevelopmentScalarGroup53.flatten.map Prod.fst = ((meshRecordKeys 400).drop 7632).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup54_keys :
    q400DevelopmentScalarGroup54.flatten.map Prod.fst = ((meshRecordKeys 400).drop 7776).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup55_keys :
    q400DevelopmentScalarGroup55.flatten.map Prod.fst = ((meshRecordKeys 400).drop 7920).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
