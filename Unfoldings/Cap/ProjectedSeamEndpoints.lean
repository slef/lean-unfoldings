module

public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Cap.ProjectedOpening
public import Unfoldings.Complex.SeamGraph

/-! An actual projected vertex on a seam edge is one of that seam's intrinsic endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem vertex_eq_seamEndpoint_of_projected_edge (v : C.Vertex Set.univ) (s : C.Seam)
    (member : K.projectedVertex v ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge) :
    ∃ b, v = C.seamVertex s b := by
  obtain ⟨i, at_corner⟩ := K.projected_corner_of_vertex_mem v (C.left s).face
    ((K.projectedTriangle (C.left s).face).edge_subset (C.left s).edge member)
  have vertex : (K.projectedTriangle (C.left s).face).IsVertex (K.projectedVertex v) :=
    ⟨i, at_corner⟩
  rcases ((K.projectedTriangle (C.left s).face).edge_vertex_iff (C.left s).edge
    ⟨K.projectedVertex v, member⟩).mp vertex with first | last
  · refine ⟨false, K.projectedVertex_injective ?_⟩
    exact first
  · refine ⟨true, K.projectedVertex_injective ?_⟩
    exact last

end Unfoldings.ConvexCap
