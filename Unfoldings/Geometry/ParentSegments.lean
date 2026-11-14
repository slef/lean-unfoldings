module

public import Unfoldings.Geometry.StraightGraph
public import Unfoldings.Topology.ParentPaths
public import Unfoldings.Topology.GraphForestMap

/-! Realize increasing parent forests as embedded graphs of their actual straight segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V X : Type*} [Finite V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  (P : AscendingParents V) (point : V → X) (injective : Function.Injective point)
  (avoids : ∀ v ∉ P.roots, ∀ w, point w ∉ openSegment ℝ (point v) (point (P.parent v)))
  (separated : Pairwise (fun v w : {v : V // v ∉ P.roots} =>
    Disjoint (openSegment ℝ (point v.val) (point (P.parent v.val)))
      (openSegment ℝ (point w.val) (point (P.parent w.val)))))

def segmentEmbedding : FiniteEmbeddedGraph V {v // v ∉ P.roots} X where
  finite_vertices := inferInstance
  finite_edges := inferInstance
  vertex := point
  vertex_injective := injective
  left v := v.val
  right v := P.parent v.val
  edge v := ⟨fun t => AffineMap.lineMap (point v.val) (point (P.parent v.val)) (t : ℝ),
    AffineMap.lineMap_continuous.comp continuous_subtype_val⟩
  edge_zero _ := AffineMap.lineMap_apply_zero _ _
  edge_one _ := AffineMap.lineMap_apply_one _ _
  edge_injective v := by
    have different : point v.val ≠ point (P.parent v.val) := by
      intro equal
      have same := injective equal
      have strict := P.ascending v.val v.property
      rw [← same] at strict
      exact lt_irrefl _ strict
    intro t _ht s _hs equal
    exact Subtype.ext (AffineMap.lineMap_injective ℝ different equal)
  edge_avoids_vertices v t ht hs w equal := by
    apply avoids v.val v.property w
    rw [openSegment_eq_image_lineMap]
    exact ⟨t.val, ⟨ht, hs⟩, equal⟩
  disjoint_open_edges v w different := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ ⟨s, hs, equal⟩
    apply Set.disjoint_left.mp (separated different)
    · rw [openSegment_eq_image_lineMap]
      exact ⟨t.val, ht, rfl⟩
    · rw [openSegment_eq_image_lineMap]
      exact ⟨s.val, hs, equal⟩

theorem segmentEmbedding_straight :
    (P.segmentEmbedding point injective avoids separated).IsStraight :=
  fun _ _ => rfl

theorem segmentEmbedding_reaches_of_ancestor {v w : V} (ancestor : P.Ancestor v w) :
    (P.segmentEmbedding point injective avoids separated).graph.Reaches v w := by
  obtain ⟨n, rfl⟩ := ancestor
  induction n with
  | zero => exact Graph.Reaches.refl (Set.mem_univ _)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases root : P.parent^[n] v ∈ P.roots
    · rwa [P.fixed_root _ root]
    · exact ih.trans (Graph.Reaches.of_isLink (e := ⟨_, root⟩) (Or.inl ⟨rfl, rfl⟩))

theorem segmentEmbedding_rootedForest :
    (P.segmentEmbedding point injective avoids separated).graph.IsRootedForest P.roots := by
  refine ⟨?_, ?_⟩
  · apply P.graph_acyclic.of_mapAlong
      (G := (P.segmentEmbedding point injective avoids separated).graph) (fun v => v)
      Subtype.val (fun _ _ => Set.mem_univ _) _ Subtype.val_injective
    intro e v w link
    exact ⟨e.property, link⟩
  · intro v _
    refine ⟨P.root v, ⟨P.root_mem v,
      P.segmentEmbedding_reaches_of_ancestor point injective avoids separated
        (P.ancestor_root v)⟩, ?_⟩
    rintro r ⟨root, _edges, walk⟩
    have same : P.root v = P.root r := walk.eq_of_link_invariant P.root (by
      intro e x y link
      have equal := P.root_eq_of_ancestor (P.ancestor_parent e.val)
      rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact equal
      · exact equal.symm)
    exact (same.trans (P.root_of_root root)).symm

end Unfoldings.AscendingParents
