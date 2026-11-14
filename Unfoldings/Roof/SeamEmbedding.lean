module

public import Unfoldings.Complex.SeamEmbedding
public import Unfoldings.Topology.GraphEmbedding
public import Unfoldings.Geometry.StraightGraph
public import Unfoldings.Roof.VertexProgress

/-! Original seam graphs embed as their exact straight projected edges on convex roofs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

def seamEmbedding : FiniteEmbeddedGraph (C.Vertex Set.univ) C.Seam Plane :=
  (C.seamEmbedding K.folding).mapEmbedding
    ⟨fun x => Cap.horizontal (K.folding.toSpace Set.univ x),
      Cap.horizontalCLM.continuous.comp (K.folding.toSpace_lipschitz Set.univ).continuous⟩
    K.projection_injective

@[simp] theorem seamEmbedding_vertex (v : C.Vertex Set.univ) :
    K.seamEmbedding.vertex v = K.projectedVertex v := rfl

@[simp] theorem seamEmbedding_graph : K.seamEmbedding.graph = C.seamGraph := rfl

theorem seamEmbedding_straight : K.seamEmbedding.IsStraight := by
  intro s t
  change K.projectFace (C.left s).face
    (AffineMap.lineMap ((C.triangle (C.left s).face).vertex (C.left s).edge)
      ((C.triangle (C.left s).face).vertex (Triangle.next (C.left s).edge)) (t : ℝ)) = _
  exact (K.projectFace (C.left s).face).apply_lineMap _ _ _

end Unfoldings.ConvexRoof
