module

public import Unfoldings.Complex.SelectedCuts

/-!
# Parent selections with unused isolated vertices

The parent structure may also mark vertices outside the cutting graph as roots.
If every marked root actually occurring in the relative cutting graph is an
original boundary vertex, the selected cuts still form the required rooted forest.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- A selected route starting in the actual cutting graph remains in that graph. -/
theorem selectedCut_reaches_of_selection_from {a b : C.Vertex Set.univ}
    (member : a ∈ (C.relativeCutGraph (C.selectedRetain S) Set.univ).vertexSet)
    (reach : S.graph.Reaches a b) :
    (C.relativeCutGraph (C.selectedRetain S) Set.univ).Reaches a b := by
  obtain ⟨edges, walk⟩ := reach
  induction walk with
  | nil _ => exact Graph.Reaches.refl member
  | @cons a b c e edges link rest ih =>
    have original := S.graph_isLink_iff.mp link
    let s : C.RelativeCutSeam (C.selectedRetain S) Set.univ :=
      ⟨e, Set.mem_univ _, not_not.mpr original.1⟩
    have actual := (C.selectedCut_link_iff S s a b).mpr original.2
    exact (Graph.Reaches.of_isLink actual).trans (ih actual.right_mem)

/-- Roots outside the actual cut graph do not change its boundary-rooted forest property. -/
theorem selectedCut_rootedForest_of_root_support
    (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
    (root_support : ∀ v ∈ P.roots,
      v ∈ (C.relativeCutGraph (C.selectedRetain S) Set.univ).vertexSet →
        v ∈ C.relativeCutRoots Set.univ) :
    (C.relativeCutGraph (C.selectedRetain S) Set.univ).IsRootedForest
      (C.relativeCutRoots Set.univ) := by
  refine ⟨C.selectedCut_acyclic S, fun v member => ?_⟩
  obtain ⟨r, ⟨root, reach⟩, unique⟩ := S.graph_rootedForest.2 v (Set.mem_univ _)
  have actual := C.selectedCut_reaches_of_selection_from S member reach
  refine ⟨r, ⟨root_support r root actual.right_mem, actual⟩, ?_⟩
  rintro q ⟨marked, edges, walk⟩
  have mapped := walk.mapAlong (fun v => v) Subtype.val (fun _ _ => Set.mem_univ _)
    (fun {_ _ _} link => C.selectedCut_to_selection_link S link)
  exact unique q ⟨boundary_roots marked, ⟨_, mapped⟩⟩

end Unfoldings.TriangleComplex
