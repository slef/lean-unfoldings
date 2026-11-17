module

public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Polyhedron.ProjectedBoundaryChain

/-! Cap bank projections are the common physical folded-chain projections. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- The cap comparison chain has exactly its actual spatial folding projection. -/
theorem projectedBoundaryChain_eq_folding (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) :
    K.projectedBoundaryChain U chain =
      (K.folding.restrictFaces U).projectedBoundaryChain chain := by
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact (K.projectedBoundaryChain_vertex_last U chain).trans
      ((K.folding.restrictFaces U).projectedBoundaryChain_vertex_last chain).symm
  · exact (K.projectedBoundaryChain_vertex_castSucc U chain i).trans
      ((K.folding.restrictFaces U).projectedBoundaryChain_vertex_castSucc chain i).symm

end Unfoldings.ConvexCap
