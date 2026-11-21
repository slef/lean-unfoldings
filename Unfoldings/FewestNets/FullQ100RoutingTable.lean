module

public import Unfoldings.FewestNets.VerifiedRoutingEndpoints
public import Unfoldings.FewestNets.Geometry100.Routing100Block00000
public import Unfoldings.FewestNets.Geometry100.Routing100Block00024
public import Unfoldings.FewestNets.Geometry100.Routing100Block00048
public import Unfoldings.FewestNets.Geometry100.Routing100Block00072
public import Unfoldings.FewestNets.Geometry100.Routing100Block00096
public import Unfoldings.FewestNets.Geometry100.Routing100Block00120
public import Unfoldings.FewestNets.Geometry100.Routing100Block00144
public import Unfoldings.FewestNets.Geometry100.Routing100Block00168
public import Unfoldings.FewestNets.Geometry100.Routing100Block00192
public import Unfoldings.FewestNets.Geometry100.Routing100Block00216
public import Unfoldings.FewestNets.Geometry100.Routing100Block00240
public import Unfoldings.FewestNets.Geometry100.Routing100Block00264
public import Unfoldings.FewestNets.Geometry100.Routing100Block00288
public import Unfoldings.FewestNets.Geometry100.Routing100Block00312
public import Unfoldings.FewestNets.Geometry100.Routing100Block00336
public import Unfoldings.FewestNets.Geometry100.Routing100Block00360
public import Unfoldings.FewestNets.Geometry100.Routing100Block00384
public import Unfoldings.FewestNets.Geometry100.Routing100Block00408
public import Unfoldings.FewestNets.Geometry100.Routing100Block00432
public import Unfoldings.FewestNets.Geometry100.Routing100Block00456
public import Unfoldings.FewestNets.Geometry100.Routing100Block00480
public import Unfoldings.FewestNets.Geometry100.Routing100Block00504
public import Unfoldings.FewestNets.Geometry100.Routing100Block00528
public import Unfoldings.FewestNets.Geometry100.Routing100Block00552
public import Unfoldings.FewestNets.Geometry100.Routing100Block00576
public import Unfoldings.FewestNets.Geometry100.Routing100Block00600
public import Unfoldings.FewestNets.Geometry100.Routing100Block00624
public import Unfoldings.FewestNets.Geometry100.Routing100Block00648
public import Unfoldings.FewestNets.Geometry100.Routing100Block00672
public import Unfoldings.FewestNets.Geometry100.Routing100Block00696
public import Unfoldings.FewestNets.Geometry100.Routing100Block00720
public import Unfoldings.FewestNets.Geometry100.Routing100Block00744
public import Unfoldings.FewestNets.Geometry100.Routing100Block00768
public import Unfoldings.FewestNets.Geometry100.Routing100Block00792
public import Unfoldings.FewestNets.Geometry100.Routing100Block00816
public import Unfoldings.FewestNets.Geometry100.Routing100Block00840
public import Unfoldings.FewestNets.Geometry100.Routing100Block00864

/-! The complete exact geometric routing table at frequency 100. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

def q100GeometricRoutingRecords :
    List (Σ key, {row : MeshRoutingRecord 100 key // row.Verified 81}) :=
    Routing100Block00000 ++
    Routing100Block00024 ++
    Routing100Block00048 ++
    Routing100Block00072 ++
    Routing100Block00096 ++
    Routing100Block00120 ++
    Routing100Block00144 ++
    Routing100Block00168 ++
    Routing100Block00192 ++
    Routing100Block00216 ++
    Routing100Block00240 ++
    Routing100Block00264 ++
    Routing100Block00288 ++
    Routing100Block00312 ++
    Routing100Block00336 ++
    Routing100Block00360 ++
    Routing100Block00384 ++
    Routing100Block00408 ++
    Routing100Block00432 ++
    Routing100Block00456 ++
    Routing100Block00480 ++
    Routing100Block00504 ++
    Routing100Block00528 ++
    Routing100Block00552 ++
    Routing100Block00576 ++
    Routing100Block00600 ++
    Routing100Block00624 ++
    Routing100Block00648 ++
    Routing100Block00672 ++
    Routing100Block00696 ++
    Routing100Block00720 ++
    Routing100Block00744 ++
    Routing100Block00768 ++
    Routing100Block00792 ++
    Routing100Block00816 ++
    Routing100Block00840 ++
    Routing100Block00864

set_option maxRecDepth 32768 in
theorem q100GeometricRoutingRecords_keys :
    q100GeometricRoutingRecords.map Sigma.fst = meshRecordKeys 100 := by
  decide +kernel

theorem q100_verified_routing_table : HasVerifiedRoutingTable 100 81 :=
  hasVerifiedRoutingTable_of_keys q100GeometricRoutingRecords q100GeometricRoutingRecords_keys

end Unfoldings.FewestNets.Icosahedron
