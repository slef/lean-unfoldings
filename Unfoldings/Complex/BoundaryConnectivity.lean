module

public import Unfoldings.Complex.BoundaryComponentDescent

/-!
# A connected primal cut forest has connected bank boundary

Boundary-component labels descend to original vertices and remain constant
along every actual cut edge. Connectedness of the primal graph forces them
all to agree, so the actual boundary multigraph has just one component.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (closed : ∀ e, ¬ C.IsBoundaryEdge Set.univ e)
  (forest : (C.cutSeamGraph retain).IsAcyclic)

theorem originalBoundaryComponent_cutSeam (s : C.CutSeam retain) :
    C.originalVertexBoundaryComponent retain closed forest (C.cutSeamVertex retain s false) =
      C.originalVertexBoundaryComponent retain closed forest (C.cutSeamVertex retain s true) := by
  let G := C.boundaryGraph retain
  let bank := C.cutBank retain s false
  have reachable : G.graph.Reaches (G.left bank) (G.right bank) :=
    Graph.Reaches.of_isLink (show G.graph.IsLink bank (G.left bank) (G.right bank)
      from Or.inl ⟨rfl, rfl⟩)
  change C.originalVertexBoundaryComponent retain closed forest
      (C.vertexForgetCuts (Set.subset_univ retain) (G.left bank).val) =
    C.originalVertexBoundaryComponent retain closed forest
      (C.vertexForgetCuts (Set.subset_univ retain) (G.right bank).val)
  rw [C.originalVertexBoundaryComponent_forget, C.originalVertexBoundaryComponent_forget]
  exact C.vertexBoundaryComponent_eq_of_reaches retain reachable

theorem originalBoundaryComponent_cutLink {s : C.CutSeam retain} {u v : C.Vertex Set.univ}
    (link : (C.cutSeamGraph retain).IsLink s u v) :
    C.originalVertexBoundaryComponent retain closed forest u =
      C.originalVertexBoundaryComponent retain closed forest v := by
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact C.originalBoundaryComponent_cutSeam retain closed forest s
  · exact (C.originalBoundaryComponent_cutSeam retain closed forest s).symm

include closed forest in
theorem boundaryGraph_connected_of_cutTree (connected : (C.cutSeamGraph retain).Connected) :
    (C.boundaryGraph retain).adjacencyGraph.Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro u v
    have original := connected.reaches (C.cutSeamGraph_preserves_vertex retain closed u)
      (C.cutSeamGraph_preserves_vertex retain closed v)
    obtain ⟨edges, walk⟩ := original
    have labels := walk.eq_of_link_invariant
      (C.originalVertexBoundaryComponent retain closed forest)
      (fun {_ _ _} link => C.originalBoundaryComponent_cutLink retain closed forest link)
    change C.originalVertexBoundaryComponent retain closed forest
        (C.vertexForgetCuts (Set.subset_univ retain) u.val) =
      C.originalVertexBoundaryComponent retain closed forest
        (C.vertexForgetCuts (Set.subset_univ retain) v.val) at labels
    rw [C.originalVertexBoundaryComponent_forget, C.originalVertexBoundaryComponent_forget,
      C.vertexBoundaryComponent_boundary, C.vertexBoundaryComponent_boundary] at labels
    exact SimpleGraph.ConnectedComponent.eq.mp (Option.some_injective _ labels)
  · obtain ⟨v, member⟩ := connected.1
    obtain ⟨s, _side, _equal⟩ := member
    exact ⟨(C.boundaryGraph retain).left (C.cutBank retain s false)⟩

end Unfoldings.TriangleComplex
