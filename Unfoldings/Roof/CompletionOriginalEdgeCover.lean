module

public import Unfoldings.Roof.CompletionOriginalPieces
public import Unfoldings.Geometry.WholeEdgeSubdivision

/-! Original whole edges are exact unions of physical completion edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

theorem original_edge_eq_union_subedges (f : Face) (e : Fin 3) :
    (K.projectedTriangle f).edge e =
      ⋃ a : {a : E.mesh.Index × Fin 3 //
          (E.mesh.projectedTriangle a.1).edge a.2 ⊆ (K.projectedTriangle f).edge e},
        (E.mesh.projectedTriangle a.val.1).edge a.val.2 := by
  let := E.mesh.finite
  have cover : (K.projectedTriangle f).edge e ⊆
      ⋃ i, (E.mesh.projectedTriangle i).carrier := by
    intro p member
    exact E.mesh.cover.subset (interior_subset (E.covers (Or.inl
      (K.projectedTriangle_subset_footprint f ((K.projectedTriangle f).edge_subset e member)))))
  exact TriangleFamily.edge_eq_union_subedges E.mesh.projectedTriangle
    (K.projectedTriangle f) e cover (fun i k => E.mesh.signs i (f, k))
    (fun i k p member => E.mesh.constrained i p member (f, k))

end Unfoldings.ConvexRoof.CompletionMesh
