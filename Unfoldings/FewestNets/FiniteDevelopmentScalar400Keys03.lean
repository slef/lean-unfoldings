module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group24
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group25
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group26
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group27
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group28
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group29
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group30
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Group31

/-! Exact canonical-key slices for the frequency-400 scalar records. -/

@[expose] public section

namespace Unfoldings.FewestNets

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup24_keys :
    q400DevelopmentScalarGroup24.flatten.map Prod.fst = ((meshRecordKeys 400).drop 3456).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup25_keys :
    q400DevelopmentScalarGroup25.flatten.map Prod.fst = ((meshRecordKeys 400).drop 3600).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup26_keys :
    q400DevelopmentScalarGroup26.flatten.map Prod.fst = ((meshRecordKeys 400).drop 3744).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup27_keys :
    q400DevelopmentScalarGroup27.flatten.map Prod.fst = ((meshRecordKeys 400).drop 3888).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup28_keys :
    q400DevelopmentScalarGroup28.flatten.map Prod.fst = ((meshRecordKeys 400).drop 4032).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup29_keys :
    q400DevelopmentScalarGroup29.flatten.map Prod.fst = ((meshRecordKeys 400).drop 4176).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup30_keys :
    q400DevelopmentScalarGroup30.flatten.map Prod.fst = ((meshRecordKeys 400).drop 4320).take 144 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem q400DevelopmentScalarGroup31_keys :
    q400DevelopmentScalarGroup31.flatten.map Prod.fst = ((meshRecordKeys 400).drop 4464).take 144 := by
  decide +kernel

end Unfoldings.FewestNets
