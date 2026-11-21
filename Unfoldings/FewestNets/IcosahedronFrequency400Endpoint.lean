module

public import Unfoldings.FewestNets.EndpointNetBounds
public import Unfoldings.FewestNets.IcosahedronFrequency400Network
public import Unfoldings.FewestNets.IcosahedronNetworkPerimeter
public import Unfoldings.FewestNets.IcosahedronEdgeCount

/-! The second endpoint count with the actual mesh, conditional on component development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets FewestNets.Icosahedron SpatialRotation Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- With component developments, the actual frequency-400 network gives the paper's second
net partition bound. The mesh geometry, arc count, and perimeter are already verified. -/
theorem exists_netPartition_lt_q400_of_component_nets
    (corners : ∀ f i, (C.triangle f).cornerAngle i ≤ 83.2067 * π / 180)
    (nets : ∀ (g : SpatialRotation) (label : Face → meshSites 400),
      (∀ f, N.normal f ∈ strictVoronoiCone (fun a : meshSites 400 => linear g (a : Space))
        (label f)) →
      ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.HasOriginalEdgeNet c.supp) :
    ∃ n < 200700000, C.HasNetPartition n := by
  let : Nonempty (meshSites 400) := ⟨referenceVertexSite (by decide)⟩
  let : Fintype (MeshEdge 400) := Fintype.ofFinite _
  have card : Fintype.card (MeshEdge 400) = 4800000 :=
    Nat.card_eq_fintype_card.symm.trans card_meshEdge_q400
  apply P.exists_netPartition_lt_q400_of_network N voronoiNetwork_q400
    card networkLength_q400_lt.le corners
  intro g regular c
  exact nets g (fun f => voronoiLabel (fun a : meshSites 400 => (a : Space)) (N.normal f) g)
    regular c

end Unfoldings.SpatialFolding.ConvexBoundary
