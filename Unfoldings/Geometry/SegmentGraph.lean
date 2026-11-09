module

public import Unfoldings.Geometry.SegmentCells
public import Unfoldings.Topology.FiniteEmbeddedGraph
public import Unfoldings.Geometry.StraightGraph

/-!
# Every finite straight network has an actual finite embedded graph

All crossings and overlap endpoints are marked first. Consecutive marked
points on original segments give the new edges. Index edges by their closed
carriers so that coincident or oppositely oriented pieces are represented once.
Degenerate original segments survive as vertices. The carrier is unchanged.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_finite_embedded_straight_segment_graph
    (segments : Set (E × E)) (finite : segments.Finite) :
    ∃ (Vertex Edge : Type u) (G : FiniteEmbeddedGraph Vertex Edge E),
      G.IsStraight ∧ G.carrier = segmentCarrier segments ∧
        ∀ e : Edge, ∃ p ∈ segments, Set.range (G.edge e) ⊆ segment ℝ p.1 p.2 := by
  classical
  obtain ⟨V, finite_V, vertices_inside, endpoints, intersections⟩ :=
    exists_finite_segment_vertices segments finite
  let := finite_V.fintype
  let good := {p : V × V | p.1.val ≠ p.2.val ∧
    (∃ e ∈ segments, segment ℝ p.1.val p.2.val ⊆ segment ℝ e.1 e.2) ∧
      Disjoint V (openSegment ℝ p.1.val p.2.val)}
  let carriers := (fun p : V × V => segment ℝ p.1.val p.2.val) '' good
  have finite_carriers : carriers.Finite := (Set.toFinite good).image _
  let := finite_carriers.fintype
  have choices (e : carriers) : ∃ a b : V, a.val ≠ b.val ∧
      e.val = segment ℝ a.val b.val ∧
      (∃ p ∈ segments, segment ℝ a.val b.val ⊆ segment ℝ p.1 p.2) ∧
        Disjoint V (openSegment ℝ a.val b.val) := by
    obtain ⟨p, hp, equal⟩ := e.property
    exact ⟨p.1, p.2, hp.1, equal.symm, hp.2.1, hp.2.2⟩
  choose left right different exact_carrier parent gaps using choices
  let edge (e : carriers) : C(unitInterval, E) :=
    ⟨fun t => AffineMap.lineMap (left e).val (right e).val (t : ℝ),
      AffineMap.lineMap_continuous.comp continuous_subtype_val⟩
  have open_member (e : carriers) (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
      edge e t ∈ openSegment ℝ (left e).val (right e).val :=
    lineMap_mem_openSegment ℝ _ _ ht
  let G : FiniteEmbeddedGraph V carriers E :=
    { finite_vertices := inferInstance
      finite_edges := inferInstance
      vertex := Subtype.val
      vertex_injective := Subtype.val_injective
      left := left
      right := right
      edge := edge
      edge_zero := fun e => AffineMap.lineMap_apply_zero _ _
      edge_one := fun e => AffineMap.lineMap_apply_one _ _
      edge_injective := by
        intro e t ht s hs equal
        apply Subtype.ext
        exact AffineMap.lineMap_injective ℝ (different e) equal
      edge_avoids_vertices := by
        intro e t ht before v equal
        have on_edge := open_member e t ⟨ht, before⟩
        exact Set.disjoint_left.mp (gaps e) v.property (equal ▸ on_edge)
      disjoint_open_edges := by
        intro e f unequal
        apply Set.disjoint_left.mpr
        rintro x ⟨t, ht, rfl⟩ ⟨s, hs, equal⟩
        have first_open := open_member e t ht
        have second_open : edge e t ∈ openSegment ℝ (left f).val (right f).val :=
          equal ▸ open_member f s hs
        obtain ⟨p, hp, first_parent⟩ := parent e
        obtain ⟨q, hq, second_parent⟩ := parent f
        have nonempty : (segment ℝ p.1 p.2 ∩ segment ℝ q.1 q.2).Nonempty :=
          ⟨edge e t, first_parent (openSegment_subset_segment ℝ _ _ first_open),
            second_parent (openSegment_subset_segment ℝ _ _ second_open)⟩
        obtain ⟨u, hu, v, hv, intersection⟩ := intersections p hp q hq nonempty
        have same := unmarked_segments_eq_of_parent_intersection
          (left e).property (right e).property (left f).property (right f).property
          (different e) (different f) (gaps e) (gaps f) first_parent second_parent
          hu hv intersection first_open second_open
        apply unequal
        apply Subtype.ext
        exact (exact_carrier e).trans (same.trans (exact_carrier f).symm) }
  have edge_range (e : carriers) : Set.range (edge e) = e.val := by
    rw [exact_carrier e, segment_eq_image_lineMap]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, t.property, rfl⟩
    · rintro ⟨t, ht, equal⟩
      exact ⟨⟨t, ht⟩, equal⟩
  refine ⟨V, carriers, G, (fun _ _ => rfl), Set.Subset.antisymm ?_ ?_, ?_⟩
  · intro x member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    cases i with
    | inl v =>
      change x = v.val at hi
      exact vertices_inside (hi ▸ v.property)
    | inr e =>
      obtain ⟨p, hp, included⟩ := parent e
      have range_member : x ∈ Set.range (edge e) := hi
      rw [edge_range e, exact_carrier e] at range_member
      exact Set.mem_iUnion₂.mpr ⟨p, hp, included range_member⟩
  · intro x member
    by_cases marked : x ∈ V
    · exact G.mem_carrier_vertex ⟨x, marked⟩
    obtain ⟨p, hp, on_parent⟩ := Set.mem_iUnion₂.mp member
    obtain ⟨a, ha, b, hb, distinct, on_open, included, gap⟩ :=
      exists_unmarked_subsegment finite_V (endpoints p hp).1 (endpoints p hp).2 on_parent marked
    let e : carriers := ⟨segment ℝ a b, (⟨(⟨a, ha⟩, ⟨b, hb⟩),
      ⟨distinct, ⟨p, hp, included⟩, gap⟩, rfl⟩)⟩
    have in_range : x ∈ Set.range (edge e) := by
      rw [edge_range e]
      exact openSegment_subset_segment ℝ a b on_open
    obtain ⟨t, equal⟩ := in_range
    exact equal ▸ G.mem_carrier_edge e t
  · intro e
    obtain ⟨p, hp, included⟩ := parent e
    refine ⟨p, hp, ?_⟩
    change Set.range (edge e) ⊆ _
    rw [edge_range e, exact_carrier e]
    exact included

theorem exists_finite_embedded_segment_graph (segments : Set (E × E)) (finite : segments.Finite) :
    ∃ (Vertex Edge : Type u) (G : FiniteEmbeddedGraph Vertex Edge E),
      G.carrier = segmentCarrier segments ∧
        ∀ e : Edge, ∃ p ∈ segments, Set.range (G.edge e) ⊆ segment ℝ p.1 p.2 := by
  obtain ⟨Vertex, Edge, G, _, cover, refines⟩ :=
    exists_finite_embedded_straight_segment_graph segments finite
  exact ⟨Vertex, Edge, G, cover, refines⟩

end Unfoldings
