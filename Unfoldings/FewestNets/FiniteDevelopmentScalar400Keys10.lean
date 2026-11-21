module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group80
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group81
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group82
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group83
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group84
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group85
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group86
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group87

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup80_keys :
    q400DevelopmentScalarGroup80.flatten.map Prod.fst = ((meshRecordKeys 400).drop 11520).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup81_keys :
    q400DevelopmentScalarGroup81.flatten.map Prod.fst = ((meshRecordKeys 400).drop 11664).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup82_keys :
    q400DevelopmentScalarGroup82.flatten.map Prod.fst = ((meshRecordKeys 400).drop 11808).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup83_keys :
    q400DevelopmentScalarGroup83.flatten.map Prod.fst = ((meshRecordKeys 400).drop 11952).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup84_keys :
    q400DevelopmentScalarGroup84.flatten.map Prod.fst = ((meshRecordKeys 400).drop 12096).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup85_keys :
    q400DevelopmentScalarGroup85.flatten.map Prod.fst = ((meshRecordKeys 400).drop 12240).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup86_keys :
    q400DevelopmentScalarGroup86.flatten.map Prod.fst = ((meshRecordKeys 400).drop 12384).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup87_keys :
    q400DevelopmentScalarGroup87.flatten.map Prod.fst = ((meshRecordKeys 400).drop 12528).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
