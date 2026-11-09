module

public import Unfoldings.Cone.ParametrizedChart
public import Unfoldings.Geometry.SpatialHinge

/-! Construct intrinsic tangent isometries from entire spatial support hinges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ}
  {T U : Triangle} {e f : Fin 3} {identify : T.Edge e ≃ᵢ U.Edge f}
  {H : HingePlacement T U e f identify}

def tangentParametrizationOfHinge (S : SpatialHinge H)
    (image : Set.range (F.tangentToSpace Set.univ v) = S.carrier) :
    F.TangentParametrization v where
  count := 2
  pieces := S.pieces
  closed := S.pieces_closed
  convex := S.pieces_convex
  cover := S.pieces_cover
  place := S.places
  map := S.map
  agrees := S.pieces_agree
  injective := S.map_injective
  range_eq := S.range_map.trans image.symm

theorem isRegularPoint_of_spatial_hinge (embedded : F.IsEmbedded) (S : SpatialHinge H)
    (image : Set.range (F.tangentToSpace Set.univ v) = S.carrier) :
    C.IsRegularPoint Set.univ (C.vertexPoint Set.univ v) :=
  (tangentParametrizationOfHinge S image).isRegularPoint embedded

end Unfoldings.SpatialFolding
