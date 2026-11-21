module

public import Unfoldings.FewestNets.FullQ100RoutingTable

/-! The original-edge net partition bound at mesh frequency 100. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets.Icosahedron Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P in
/-- At most 81 degrees per original corner gives fewer than 11,300,000 nets. -/
theorem exists_netPartition_lt_q100
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ 81 * π / 180) :
    ∃ n < 11300000, C.HasNetPartition n :=
  exists_netPartition_lt_q100_of_verified_routingTable P P.supportingNormals
    q100_verified_routing_table angles

end Unfoldings.SpatialFolding.ConvexBoundary
