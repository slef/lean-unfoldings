module

public import Unfoldings.Topology.GraphDrawing
public import Unfoldings.Topology.GraphEmbedding

/-! Plane graph images may identify vertices while keeping open edges separate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {V E X : Type*} [TopologicalSpace X]
  (G : FiniteEmbeddedGraph V E X) (f : C(X, Schoenflies.Plane))

/-- The distinct actual images of the original graph vertices. -/
abbrev ImageVertex := Set.range (f ∘ G.vertex)

/-- Identifying vertex images still gives an embedded graph when all open edges remain
injective, avoid every vertex image, and remain mutually disjoint. -/
def identifyVertices
    (injective : ∀ e, Set.InjOn (f ∘ G.edge e) (Set.Ioo 0 1))
    (avoids : ∀ e t, 0 < t → t < 1 → ∀ v, f (G.edge e t) ≠ f (G.vertex v))
    (disjoint : ∀ e g, e ≠ g →
      Disjoint ((f ∘ G.edge e) '' Set.Ioo 0 1) ((f ∘ G.edge g) '' Set.Ioo 0 1)) :
    FiniteEmbeddedGraph (G.ImageVertex f) E Schoenflies.Plane where
  finite_vertices := by
    let := G.finite_vertices
    exact Set.finite_range (f ∘ G.vertex) |>.to_subtype
  finite_edges := G.finite_edges
  vertex := Subtype.val
  vertex_injective := Subtype.val_injective
  left e := ⟨f (G.vertex (G.left e)), G.left e, rfl⟩
  right e := ⟨f (G.vertex (G.right e)), G.right e, rfl⟩
  edge e := f.comp (G.edge e)
  edge_zero e := congrArg f (G.edge_zero e)
  edge_one e := congrArg f (G.edge_one e)
  edge_injective := injective
  edge_avoids_vertices := by
    rintro e t positive small ⟨_, v, rfl⟩ equal
    exact avoids e t positive small v equal
  disjoint_open_edges := disjoint

variable
  (injective : ∀ e, Set.InjOn (f ∘ G.edge e) (Set.Ioo 0 1))
  (avoids : ∀ e t, 0 < t → t < 1 → ∀ v, f (G.edge e t) ≠ f (G.vertex v))
  (disjoint : ∀ e g, e ≠ g →
    Disjoint ((f ∘ G.edge e) '' Set.Ioo 0 1) ((f ∘ G.edge g) '' Set.Ioo 0 1))

/-- The vertex identification preserves each original edge name and link. -/
theorem identifyVertices_isLink {e : E} {u v : V} (link : G.graph.IsLink e u v) :
    (G.identifyVertices f injective avoids disjoint).graph.IsLink e
      ⟨f (G.vertex u), u, rfl⟩ ⟨f (G.vertex v), v, rfl⟩ := by
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- Identifying vertices cannot turn a cyclic graph into a forest when edge names are preserved. -/
theorem identifyVertices_not_acyclic (cyclic : ¬ G.graph.IsAcyclic) :
    ¬ (G.identifyVertices f injective avoids disjoint).graph.IsAcyclic := by
  intro forest
  apply cyclic
  exact forest.of_mapAlong
    (fun v => (⟨f (G.vertex v), v, rfl⟩ : G.ImageVertex f)) id
    (fun _ _ => Set.mem_univ _)
    (fun link => G.identifyVertices_isLink f injective avoids disjoint link)
    Function.injective_id

include injective avoids disjoint in
/-- A cyclic graph whose image only identifies vertices contains a genuine Jordan curve
in its actual planar image. No injectivity at the original vertices is required. -/
theorem exists_Jordan_subset_of_vertex_identifications
    (edge_injective : ∀ e, Function.Injective (f ∘ G.edge e)) (cyclic : ¬ G.graph.IsAcyclic) :
    ∃ J : Set Schoenflies.Plane, Schoenflies.IsJordanCurve J ∧ J ⊆ f '' G.carrier := by
  let H := G.identifyVertices f injective avoids disjoint
  have not_forest := G.identifyVertices_not_acyclic f injective avoids disjoint cyclic
  have cycle : ∃ e, H.graph.LiesOnCycle e := by
    by_contra none
    apply not_forest
    intro e _member on_cycle
    exact none ⟨e, on_cycle⟩
  obtain ⟨e, u, v, detour, actual⟩ := cycle
  refine ⟨Graph.edgesCover H.drawing (e :: detour),
    H.cycle_isJordanCurve edge_injective actual, ?_⟩
  intro p member
  obtain ⟨bank, _, on_edge⟩ := Graph.mem_edgesCover_iff.mp member
  rw [H.drawing_edgeArc] at on_edge
  obtain ⟨t, rfl⟩ := on_edge
  exact ⟨G.edge bank t, G.mem_carrier_edge bank t, rfl⟩

/-- Singleton fibers at every open-edge point suffice to extract a Jordan curve from
an image of a cyclic graph. Closed edges must also retain their distinct endpoints. -/
theorem exists_Jordan_subset_of_open_edge_fibers
    (edge_injective : ∀ e, Function.Injective (f ∘ G.edge e))
    (fibers : ∀ e t, 0 < t → t < 1 → ∀ y : X, f (G.edge e t) = f y → G.edge e t = y)
    (cyclic : ¬ G.graph.IsAcyclic) :
    ∃ J : Set Schoenflies.Plane, Schoenflies.IsJordanCurve J ∧ J ⊆ f '' G.carrier := by
  apply G.exists_Jordan_subset_of_vertex_identifications f
    (fun e => (edge_injective e).injOn) _ _ edge_injective cyclic
  · intro e t positive small v same
    exact G.edge_avoids_vertices e t positive small v (fibers e t positive small _ same)
  · intro e g different
    apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, same⟩
    have equal := fibers e s hs.1 hs.2 _ same.symm
    exact Set.disjoint_left.mp (G.disjoint_open_edges e g different)
      ⟨s, hs, rfl⟩ ⟨t, ht, equal.symm⟩

end Unfoldings.FiniteEmbeddedGraph
