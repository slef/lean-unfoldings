module

public import Unfoldings.Roof.SpatialEnvelopeVertexFibers
public import Unfoldings.Polyhedron.BoundaryChainGeometry

/-! Original projected vertices and whole physical traces of retained boundary chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance spatialBoundaryChainIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable {retain : Set T.pairedComplex.Seam} {n : ℕ}
  (chain : (T.pairedComplex.boundarySystem retain).Chain n)

/-- The actual physical chain projected in its original horizontal coordinates. -/
def projectedBoundaryChain : PolygonalChain Plane (n + 1) :=
  (T.pairedFolding.boundarySpatialChain chain).affineMap Cap.horizontal.toAffineMap

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (clip family Z)).Nonempty)

theorem projectedBoundaryChain_vertex_castSucc (i : Fin (n + 1)) :
    (T.projectedBoundaryChain chain).vertex i.castSucc =
      (T.roof conforming inside).projectedVertex
        (T.pairedComplex.vertexForgetCuts (Set.subset_univ retain)
          (T.pairedComplex.boundaryEndVertex retain (chain.point i))) := by
  change Cap.horizontal ((T.pairedFolding.boundarySpatialChain chain).vertex i.castSucc) = _
  rw [T.pairedFolding.boundarySpatialChain_vertex_castSucc]
  exact (T.roof_projectedVertex_vertexForgetCuts conforming inside retain _).symm

theorem projectedBoundaryChain_vertex_succ (i : Fin (n + 1)) :
    (T.projectedBoundaryChain chain).vertex i.succ =
      (T.roof conforming inside).projectedVertex
        (T.pairedComplex.vertexForgetCuts (Set.subset_univ retain)
          (T.pairedComplex.boundaryEndVertex retain
            (T.pairedComplex.boundaryTurn retain (chain.point i)))) := by
  change Cap.horizontal ((T.pairedFolding.boundarySpatialChain chain).vertex i.succ) = _
  rw [T.pairedFolding.boundarySpatialChain_vertex_succ]
  exact (T.roof_projectedVertex_vertexForgetCuts conforming inside retain _).symm

/-- The entire projected physical path retains precisely the original intrinsic trace. -/
theorem projectedBoundaryChain_path_range :
    Set.range (T.projectedBoundaryChain chain).path =
      (fun x => Cap.horizontal (T.pairedFolding.toSpace retain x)) ''
        T.pairedComplex.boundaryChainTrace chain := by
  rw [projectedBoundaryChain, PolygonalChain.affineMap_path_range,
    T.pairedFolding.boundarySpatialChain_path_range, Set.image_image]
  rfl

end Unfoldings.SpatialEnvelope.Triangulation
