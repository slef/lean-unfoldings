module

public import Unfoldings.Complex.CutSeamGraph
public import Unfoldings.Geometry.Corner

/-!
# The original internal-edge graph with every vertex retained

Original seams name edges; original boundary vertices and other isolated
vertices remain in the vertex set. Local face-edge incidence transfers to the
actual seam endpoints, independent of the direction of its seam identification.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

def seamVertex (s : C.Seam) (side : Bool) : C.Vertex Set.univ :=
  C.vertexOfCorner Set.univ (C.germOfEndpoint (C.left s) side).1

def seamGraph : Graph (C.Vertex Set.univ) C.Seam where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink s a b :=
    (a = C.seamVertex s false ∧ b = C.seamVertex s true) ∨
      (a = C.seamVertex s true ∧ b = C.seamVertex s false)
  isLink_symm := by
    intro s _
    constructor
    intro a b link
    exact link.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  eq_or_eq_of_isLink_of_isLink := by
    intro s a b c d first last
    rcases first with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases last with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp
  edge_mem_iff_exists_isLink s :=
    ⟨fun _ => ⟨_, _, Or.inl ⟨rfl, rfl⟩⟩, fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := fun _ _ _ _ => Set.mem_univ _

theorem seamGraph_side_link (s : C.Seam) (side : Bool) :
    C.seamGraph.IsLink s
      (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s side) false).1)
      (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s side) true).1) :=
  C.cutSeamGraph_side_link ∅ ⟨s, by simp⟩ side

/-- Every unpaired-free local edge is an actual seam with these endpoint classes. -/
theorem exists_seamGraph_link_of_not_boundary (edge : EdgeRef Face)
    (paired : ¬ C.IsBoundaryEdge Set.univ edge) :
    ∃ s, C.seamGraph.IsLink s
      (C.vertexOfCorner Set.univ (edge.face, edge.edge))
      (C.vertexOfCorner Set.univ (edge.face, Triangle.next edge.edge)) := by
  classical
  obtain ⟨s, _, incident⟩ := not_not.mp paired
  rcases incident with rfl | rfl
  · exact ⟨s, C.seamGraph_side_link s false⟩
  · exact ⟨s, C.seamGraph_side_link s true⟩

/-- An edge incident to an interior vertex is paired, hence available as an original seam cut. -/
theorem exists_seamGraph_link_at_interior_corner (f : Face) (i : Fin 3)
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ (f, i))) :
    (∃ s, C.seamGraph.IsLink s (C.vertexOfCorner Set.univ (f, i))
      (C.vertexOfCorner Set.univ (f, Triangle.next i))) ∧
    (∃ s, C.seamGraph.IsLink s (C.vertexOfCorner Set.univ (f, i))
      (C.vertexOfCorner Set.univ (f, Triangle.next (Triangle.next i)))) := by
  constructor
  · apply C.exists_seamGraph_link_of_not_boundary ⟨f, i⟩
    intro boundary
    exact internal ⟨⟨f, i⟩, boundary, Or.inl rfl⟩
  · have paired : ¬ C.IsBoundaryEdge Set.univ ⟨f, Triangle.next (Triangle.next i)⟩ := by
      intro boundary
      apply internal
      refine ⟨⟨f, Triangle.next (Triangle.next i)⟩, boundary, Or.inr ?_⟩
      rw [Triangle.next_next_next]
    obtain ⟨s, link⟩ := C.exists_seamGraph_link_of_not_boundary _ paired
    rw [Triangle.next_next_next] at link
    exact ⟨s, link.symm⟩

end Unfoldings.TriangleComplex
