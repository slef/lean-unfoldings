module

public import Unfoldings.FewestNets.EndpointNetBounds
public import Unfoldings.FewestNets.IcosahedronFrequency100Network
public import Unfoldings.FewestNets.IcosahedronNetworkPerimeter
public import Unfoldings.FewestNets.IcosahedronEdgeCount

/-! The first endpoint count with the actual mesh, conditional on component development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets FewestNets.Icosahedron SpatialRotation Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- With component developments, the actual frequency-100 network gives the paper's first
net partition bound. The mesh geometry, arc count, and perimeter are already verified. -/
theorem exists_netPartition_lt_q100_of_component_nets
    (corners : ∀ f i, (C.triangle f).cornerAngle i ≤ 81 * π / 180)
    (nets : ∀ (g : SpatialRotation) (label : Face → meshSites 100),
      (∀ f, N.normal f ∈ strictVoronoiCone (fun a : meshSites 100 => linear g (a : Space))
        (label f)) →
      ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.HasOriginalEdgeNet c.supp) :
    ∃ n < 11300000, C.HasNetPartition n := by
  let : Nonempty (meshSites 100) := ⟨referenceVertexSite (by decide)⟩
  let : Fintype (MeshEdge 100) := Fintype.ofFinite _
  have card : Fintype.card (MeshEdge 100) = 300000 :=
    Nat.card_eq_fintype_card.symm.trans card_meshEdge_q100
  apply P.exists_netPartition_lt_q100_of_network N voronoiNetwork_q100
    card networkLength_q100_lt.le corners
  intro g regular c
  exact nets g (fun f => voronoiLabel (fun a : meshSites 100 => (a : Space)) (N.normal f) g)
    regular c

end Unfoldings.SpatialFolding.ConvexBoundary
