module

public import Unfoldings.Roof.SeamEmbedding

/-! An actual seam link determines exactly its closed projected segment. -/

@[expose] public section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projected_link_segment {s : C.Seam} {v w : C.Vertex Set.univ}
    (link : C.seamGraph.IsLink s v w) :
    segment ℝ (K.projectedVertex v) (K.projectedVertex w) =
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
  rcases link with ⟨first, last⟩ | ⟨first, last⟩
  · rw [first, last]
    rfl
  · rw [first, last]
    exact segment_symm ℝ _ _

end Unfoldings.ConvexRoof
