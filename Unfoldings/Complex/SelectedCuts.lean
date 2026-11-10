module

public import Unfoldings.Complex.SeamGraph
public import Unfoldings.Complex.RelativeCutForest
public import Unfoldings.Topology.SelectedForest

/-!
# Selected original parent edges as actual cut seams

The complementary retained-seam set has exactly the selected rooted forest as
its canonical relative cut graph, up to the mandatory seam subtype. All vertex
classes, including isolated boundary roots, are accounted for. The disk-cut
criterion then constructs an actual cut-disk homeomorphism.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

def selectedRetain : Set C.Seam := (Set.range S.edge)ᶜ

theorem selectedCut_link_iff (s : C.RelativeCutSeam (C.selectedRetain S) Set.univ)
    (a b : C.Vertex Set.univ) :
    (C.relativeCutGraph (C.selectedRetain S) Set.univ).IsLink s a b ↔
      C.seamGraph.IsLink s.val a b := Iff.rfl

theorem selectedCut_to_selection_link {s : C.RelativeCutSeam (C.selectedRetain S) Set.univ}
    {a b : C.Vertex Set.univ}
    (link : (C.relativeCutGraph (C.selectedRetain S) Set.univ).IsLink s a b) :
    S.graph.IsLink s.val a b := by
  apply S.graph_isLink_iff.mpr
  exact ⟨not_not.mp s.property.2, (C.selectedCut_link_iff S s a b).mp link⟩

theorem selectedCut_acyclic : (C.relativeCutGraph (C.selectedRetain S) Set.univ).IsAcyclic :=
  S.graph_acyclic.of_mapAlong (fun v => v) Subtype.val (fun _ _ => Set.mem_univ _)
    (fun {_ _ _} link => C.selectedCut_to_selection_link S link) Subtype.val_injective

variable (roots : P.roots = C.relativeCutRoots Set.univ)

include roots

/-- Every original vertex is either an original boundary root or incident to its selected edge. -/
theorem selectedCut_vertex_mem (v : C.Vertex Set.univ) :
    v ∈ (C.relativeCutGraph (C.selectedRetain S) Set.univ).vertexSet := by
  by_cases root : v ∈ P.roots
  · exact Or.inl (roots ▸ root)
  · let a : {v : C.Vertex Set.univ // v ∉ P.roots} := ⟨v, root⟩
    let s : C.RelativeCutSeam (C.selectedRetain S) Set.univ :=
      ⟨S.edge a, Set.mem_univ _, fun outside => outside ⟨a, rfl⟩⟩
    have link : (C.relativeCutGraph (C.selectedRetain S) Set.univ).IsLink s v (P.parent v) :=
      (C.selectedCut_link_iff S s v (P.parent v)).mpr (S.link a)
    exact link.left_mem

theorem selectedCut_reaches_of_selection {a b : C.Vertex Set.univ} (reach : S.graph.Reaches a b) :
    (C.relativeCutGraph (C.selectedRetain S) Set.univ).Reaches a b := by
  obtain ⟨edges, walk⟩ := reach
  apply walk.mapReachability (fun v => v) (fun v _ => C.selectedCut_vertex_mem S roots v)
  intro e _ a b link
  have original := S.graph_isLink_iff.mp link
  let s : C.RelativeCutSeam (C.selectedRetain S) Set.univ :=
    ⟨e, Set.mem_univ _, not_not.mpr original.1⟩
  exact Graph.Reaches.of_isLink ((C.selectedCut_link_iff S s a b).mpr original.2)

theorem selectedCut_rootedForest :
    (C.relativeCutGraph (C.selectedRetain S) Set.univ).IsRootedForest
      (C.relativeCutRoots Set.univ) := by
  refine ⟨C.selectedCut_acyclic S, fun v _ => ?_⟩
  obtain ⟨r, ⟨root, reach⟩, unique⟩ := S.graph_rootedForest.2 v (Set.mem_univ _)
  refine ⟨r, ⟨roots ▸ root, C.selectedCut_reaches_of_selection S roots reach⟩, ?_⟩
  rintro q ⟨marked, edges, walk⟩
  have mapped := walk.mapAlong (fun v => v) Subtype.val (fun _ _ => Set.mem_univ _)
    (fun {_ _ _} link => C.selectedCut_to_selection_link S link)
  exact unique q ⟨roots.symm ▸ marked, ⟨_, mapped⟩⟩

/-- Every cut vertex copy is a boundary vertex when every original nonroot selects an edge. -/
theorem selectedCut_all_vertices_boundary (w : C.Vertex (C.selectedRetain S)) :
    C.IsBoundaryVertex (C.selectedRetain S) w := by
  let inclusion := Set.subset_univ (C.selectedRetain S)
  let v := C.vertexForgetCuts inclusion w
  apply (C.vertexPoint_mem_bankBoundary_iff (C.selectedRetain S) w).mp
  by_cases root : v ∈ P.roots
  · apply C.bankBoundary_preimage_forgetCuts inclusion
    change C.forgetCuts inclusion (C.vertexPoint (C.selectedRetain S) w) ∈ C.bankBoundary Set.univ
    rw [← C.vertexPoint_vertexForgetCuts]
    have boundary := root
    rw [roots] at boundary
    exact (C.vertexPoint_mem_bankBoundary_iff Set.univ v).mpr boundary
  · let a : {v : C.Vertex Set.univ // v ∉ P.roots} := ⟨v, root⟩
    let s := S.edge a
    have cut : s ∉ C.selectedRetain S := fun outside => outside ⟨a, rfl⟩
    have endpoint_boundary (b : Bool) (endpoint : v = C.seamVertex s b) :
        C.vertexPoint (C.selectedRetain S) w ∈ C.bankBoundary (C.selectedRetain S) := by
      let y := C.vertexOfCorner (C.selectedRetain S) (C.germOfEndpoint (C.left s) b).1
      have boundary : C.IsBoundaryVertex (C.selectedRetain S) y := by
        cases b
        · exact C.bank_start_isBoundaryVertex _ (C.leftBank _ s cut)
        · exact C.bank_finish_isBoundaryVertex _ (C.leftBank _ s cut)
      have original : C.vertexForgetCuts inclusion y = v := by
        change C.vertexForgetCuts inclusion
          (C.vertexOfCorner (C.selectedRetain S) (C.germOfEndpoint (C.left s) b).1) = v
        rw [C.vertexForgetCuts_vertexOfCorner]
        exact endpoint.symm
      have equal : C.forgetCuts inclusion (C.vertexPoint (C.selectedRetain S) y) =
          C.forgetCuts inclusion (C.vertexPoint (C.selectedRetain S) w) := by
        rw [← C.vertexPoint_vertexForgetCuts, ← C.vertexPoint_vertexForgetCuts, original]
      have present := (C.vertexPoint_mem_bankBoundary_iff (C.selectedRetain S) y).mpr boundary
      rcases C.forgetCuts_fiber_eq_or_boundary inclusion _ _ equal with same | both
      · exact same ▸ present
      · exact both.2
    have link := S.link a
    rcases link with first | last
    · exact endpoint_boundary false first.1
    · exact endpoint_boundary true last.1

/-- The selected original edges really cut the intrinsic disk into one disk. -/
def selectedCutDisk (F : SpatialFolding C)
    (original : C.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1) :
    C.Realization (C.selectedRetain S) ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  F.cutDiskHomeomorphOfRootedForest (Set.subset_univ _) original
    (C.selectedCut_rootedForest S roots)

end Unfoldings.TriangleComplex
