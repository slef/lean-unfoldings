module

public import Unfoldings.Roof.CompletionOriginalSubdivision
public import Unfoldings.Roof.ProjectedConformity

/-! Fine seams between different original parents lie on their common whole original edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (L : K.CompletionMesh φ region K.originalEdgeEquations)

local instance originalAdjacencyIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem original_seam_parent_edge (s : L.originalComplex.Seam)
    (different : L.originalParent (L.originalComplex.left s).face ≠
      L.originalParent (L.originalComplex.right s).face) :
    ∃ e f : Fin 3,
      (K.projectedTriangle (L.originalParent (L.originalComplex.left s).face)).edge e =
        (K.projectedTriangle (L.originalParent (L.originalComplex.right s).face)).edge f ∧
      (L.partition.projectedTriangle (L.originalComplex.left s).face.val).edge
          (L.originalComplex.left s).edge ⊆
        (K.projectedTriangle (L.originalParent (L.originalComplex.left s).face)).edge e := by
  let a := (L.originalComplex.left s).face
  let b := (L.originalComplex.right s).face
  let T := L.partition.projectedTriangle a.val
  let e := (L.originalComplex.left s).edge
  have contained : T.edge e ⊆ (K.projectedTriangle (L.originalParent a)).carrier ∩
      (K.projectedTriangle (L.originalParent b)).carrier := by
    intro p member
    exact ⟨L.originalParent_contains a (T.edge_subset e member),
      L.originalParent_contains b ((L.partition.projectedTriangle b.val).edge_subset _
        ((L.partition.paired_seam_projected_edge s.val).subset member))⟩
  have first := contained (left_mem_segment ℝ (T.vertex e) (T.vertex (Triangle.next e)))
  have last := contained (right_mem_segment ℝ (T.vertex e) (T.vertex (Triangle.next e)))
  rcases TriangleFamily.Conforming.intersection_cases K.projectedTriangle
      K.projectedTriangles_conforming
      (fun _ _ different => K.projectedTriangles_nonoverlapping different) different with
    empty | ⟨p, _first_vertex, _last_vertex, singleton⟩ | ⟨f, g, shared, intersection⟩
  · rw [empty] at first
    exact first.elim
  · rw [singleton] at first last
    exact (T.edge_endpoints_ne e
      ((Set.mem_singleton_iff.mp first).trans (Set.mem_singleton_iff.mp last).symm)).elim
  · exact ⟨f, g, shared, contained.trans intersection.subset⟩

end Unfoldings.ConvexRoof.CompletionMesh
