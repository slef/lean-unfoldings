module

public import Unfoldings.Geometry.ConvexPolygonPartition

/-!
# Center triangles using a prescribed shared boundary subdivision

Only whole edges of the supplied global embedded graph are used as triangle
bases. Thus later polygons can share the same refined edge labels, while the
coverage and disjoint-interior proofs remain purely geometric.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge : Type*} (G : FiniteEmbeddedGraph Vertex Edge Plane) {S : Set Plane}

abbrev SubdividedBoundaryEdge := {e : Edge // Set.range (G.edge e) ⊆ frontier S}

def subdividedBoundaryTriangle (straight : G.IsStraight) (compact : IsCompact S)
    (convex : Convex ℝ S) {q : Plane} (inside : q ∈ interior S)
    (e : G.SubdividedBoundaryEdge (S := S)) : Triangle :=
  convexBoundaryTriangle compact convex inside (G.vertex_injective.ne (straight.endpoints_ne e.val))
    (by rw [← straight.range_edge G e.val]; exact e.property)

theorem subdividedBoundaryTriangle_subset (straight : G.IsStraight) (compact : IsCompact S)
    (convex : Convex ℝ S) {q : Plane} (inside : q ∈ interior S)
    (e : G.SubdividedBoundaryEdge (S := S)) :
    (G.subdividedBoundaryTriangle straight compact convex inside e).carrier ⊆ S :=
  convexBoundaryTriangle_subset compact convex inside
    (G.vertex_injective.ne (straight.endpoints_ne e.val)) _

theorem subdividedBoundaryTriangle_separated (straight : G.IsStraight) (compact : IsCompact S)
    (convex : Convex ℝ S) {q : Plane} (inside : q ∈ interior S) :
    Pairwise (fun e f : G.SubdividedBoundaryEdge (S := S) =>
      Disjoint (interior (G.subdividedBoundaryTriangle straight compact convex inside e).carrier)
        (interior (G.subdividedBoundaryTriangle straight compact convex inside f).carrier)) := by
  intro e f different
  apply convexBoundaryTriangle_disjoint compact convex inside
    (G.vertex_injective.ne (straight.endpoints_ne e.val)) _
    (G.vertex_injective.ne (straight.endpoints_ne f.val)) _
  rw [← straight.open_edge_image e.val, ← straight.open_edge_image f.val]
  exact G.disjoint_open_edges e.val f.val (fun equal => different (Subtype.ext equal))

/-- Exact coverage using only the prescribed shared boundary edges. -/
theorem subdividedBoundaryTriangle_cover (straight : G.IsStraight) (compact : IsCompact S)
    (convex : Convex ℝ S) {q : Plane} (inside : q ∈ interior S)
    (covers : ∀ x ∈ frontier S, (∃ v, G.vertex v = x) ∨
      ∃ e, Set.range (G.edge e) ⊆ frontier S ∧ x ∈ Set.range (G.edge e)) :
    S = ⋃ e : G.SubdividedBoundaryEdge (S := S),
      (G.subdividedBoundaryTriangle straight compact convex inside e).carrier := by
  classical
  let := G.finite_vertices
  let := G.finite_edges
  let V := {v : Vertex // G.vertex v ∈ frontier S}
  let E := G.SubdividedBoundaryEdge (S := S)
  let first : V ⊕ E → Plane := Sum.elim (fun v => G.vertex v.val)
    (fun e => G.vertex (G.left e.val))
  let last : V ⊕ E → Plane := Sum.elim (fun v => G.vertex v.val)
    (fun e => G.vertex (G.right e.val))
  have on_boundary (i : V ⊕ E) : segment ℝ (first i) (last i) ⊆ frontier S := by
    cases i with
    | inl v => simpa only [first, last, Sum.elim_inl, segment_same,
        Set.singleton_subset_iff] using v.property
    | inr e => exact (straight.range_edge G e.val) ▸ e.property
  have covered (x : Plane) (boundary : x ∈ frontier S) :
      ∃ i : V ⊕ E, x ∈ segment ℝ (first i) (last i) := by
    rcases covers x boundary with ⟨v, equal⟩ | ⟨e, included, member⟩
    · refine ⟨Sum.inl ⟨v, equal.symm ▸ boundary⟩, ?_⟩
      change x ∈ segment ℝ (G.vertex v) (G.vertex v)
      simpa only [segment_same, Set.mem_singleton_iff] using equal.symm
    · refine ⟨Sum.inr ⟨e, included⟩, ?_⟩
      exact (straight.range_edge G e) ▸ member
  have nonempty : Nonempty (V ⊕ E) := by
    let x := q + EuclideanSpace.single 0 1
    have different : x ≠ q := by
      intro equal
      have coordinate := congrArg (fun p : Plane => p 0) equal
      simp only [x, PiLp.add_apply, EuclideanSpace.single,
        PiLp.single_apply, ite_true] at coordinate
      linarith
    obtain ⟨a, _positive, boundary⟩ :=
      exists_frontier_on_positive_ray compact convex inside different
    obtain ⟨i, _member⟩ := covered _ boundary
    exact ⟨i⟩
  let := nonempty
  have fan_cover := polygonFanTriangle_cover compact convex inside first last on_boundary covered
  apply Set.Subset.antisymm _ (Set.iUnion_subset (fun e =>
    G.subdividedBoundaryTriangle_subset straight compact convex inside e))
  intro x member
  rw [fan_cover] at member
  obtain ⟨⟨i, genuine⟩, in_triangle⟩ := Set.mem_iUnion.mp member
  cases i with
  | inl v => exact (genuine rfl).elim
  | inr e => exact Set.mem_iUnion.mpr ⟨e, in_triangle⟩

end Unfoldings.FiniteEmbeddedGraph
