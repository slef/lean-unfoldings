module

public import Unfoldings.FewestNets.FullQ400RoutingTable

/-! The original-edge net partition bound at mesh frequency 400. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets.Icosahedron Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P in
/-- At most 83.2067 degrees per original corner gives fewer than 200,700,000 nets. -/
theorem exists_netPartition_lt_q400
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ 83.2067 * π / 180) :
    ∃ n < 200700000, C.HasNetPartition n :=
  exists_netPartition_lt_q400_of_verified_routingTable P P.supportingNormals
    q400_verified_routing_table angles

end Unfoldings.SpatialFolding.ConvexBoundary
