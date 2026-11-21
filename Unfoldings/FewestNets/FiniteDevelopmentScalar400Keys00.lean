module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group00
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group01
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group02
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group03
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group04
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group05
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group06
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group07

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup00_keys :
    q400DevelopmentScalarGroup00.flatten.map Prod.fst = ((meshRecordKeys 400).drop 0).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup01_keys :
    q400DevelopmentScalarGroup01.flatten.map Prod.fst = ((meshRecordKeys 400).drop 144).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup02_keys :
    q400DevelopmentScalarGroup02.flatten.map Prod.fst = ((meshRecordKeys 400).drop 288).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup03_keys :
    q400DevelopmentScalarGroup03.flatten.map Prod.fst = ((meshRecordKeys 400).drop 432).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup04_keys :
    q400DevelopmentScalarGroup04.flatten.map Prod.fst = ((meshRecordKeys 400).drop 576).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup05_keys :
    q400DevelopmentScalarGroup05.flatten.map Prod.fst = ((meshRecordKeys 400).drop 720).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup06_keys :
    q400DevelopmentScalarGroup06.flatten.map Prod.fst = ((meshRecordKeys 400).drop 864).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup07_keys :
    q400DevelopmentScalarGroup07.flatten.map Prod.fst = ((meshRecordKeys 400).drop 1008).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
