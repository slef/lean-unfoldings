module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group40
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group41
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group42
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group43
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group44
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group45
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group46
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group47

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup40_keys :
    q400DevelopmentScalarGroup40.flatten.map Prod.fst = ((meshRecordKeys 400).drop 5760).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup41_keys :
    q400DevelopmentScalarGroup41.flatten.map Prod.fst = ((meshRecordKeys 400).drop 5904).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup42_keys :
    q400DevelopmentScalarGroup42.flatten.map Prod.fst = ((meshRecordKeys 400).drop 6048).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup43_keys :
    q400DevelopmentScalarGroup43.flatten.map Prod.fst = ((meshRecordKeys 400).drop 6192).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup44_keys :
    q400DevelopmentScalarGroup44.flatten.map Prod.fst = ((meshRecordKeys 400).drop 6336).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup45_keys :
    q400DevelopmentScalarGroup45.flatten.map Prod.fst = ((meshRecordKeys 400).drop 6480).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup46_keys :
    q400DevelopmentScalarGroup46.flatten.map Prod.fst = ((meshRecordKeys 400).drop 6624).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup47_keys :
    q400DevelopmentScalarGroup47.flatten.map Prod.fst = ((meshRecordKeys 400).drop 6768).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
