module

public import Unfoldings.Convex.ExteriorPieces
public import Unfoldings.Geometry.StraightGraph
public import Unfoldings.Topology.GraphForestMap

/-! First-contact exterior segments form an actual embedded straight rooted forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} [Finite V] (R : E.ExteriorPlan V)

abbrev Edge := {v : V // v ∉ R.terminal}

def contactTime (e : R.Edge) : ℝ := (R.next_spec e.property).1.choose

theorem contactTime_pos (e : R.Edge) : 0 < R.contactTime e :=
  (R.next_spec e.property).1.choose_spec.1

theorem next_eq_ray (e : R.Edge) : R.point (R.next e.val) = R.ray e.val (R.contactTime e) :=
  (R.next_spec e.property).1.choose_spec.2

theorem lineMap_eq_ray (e : R.Edge) (t : ℝ) :
    AffineMap.lineMap (R.point e.val) (R.point (R.next e.val)) t =
      R.ray e.val (t * R.contactTime e) := by
  rw [R.next_eq_ray, AffineMap.lineMap_apply_module']
  dsimp [ray]
  module

theorem open_edge_mem_openPiece (e : R.Edge) {t : ℝ} (ht : 0 < t) (before : t < 1) :
    AffineMap.lineMap (R.point e.val) (R.point (R.next e.val)) t ∈ R.openPiece e.val := by
  rw [R.lineMap_eq_ray]
  exact R.before_first_contact e.property (R.next_eq_ray e) (R.contactTime_pos e)
    (mul_pos ht (R.contactTime_pos e)) (by nlinarith [R.contactTime_pos e])

/-- All prescribed roots, including isolated terminals, and actual first-contact segments. -/
def embedding : FiniteEmbeddedGraph V R.Edge Plane where
  finite_vertices := inferInstance
  finite_edges := inferInstance
  vertex := R.point
  vertex_injective := R.point_injective
  left e := e.val
  right e := R.next e.val
  edge e := ⟨fun t => AffineMap.lineMap (R.point e.val) (R.point (R.next e.val)) (t : ℝ),
    AffineMap.lineMap_continuous.comp continuous_subtype_val⟩
  edge_zero e := AffineMap.lineMap_apply_zero _ _
  edge_one e := AffineMap.lineMap_apply_one _ _
  edge_injective e := by
    intro t _ht s _hs equal
    have different : R.point e.val ≠ R.point (R.next e.val) := by
      intro same
      have strict := R.contact_height_lt (R.next_spec e.property).1
      rw [same] at strict
      exact lt_irrefl _ strict
    exact Subtype.ext (AffineMap.lineMap_injective ℝ different equal)
  edge_avoids_vertices e t ht hs v equal :=
    R.openPiece_avoids_roots e.val v (equal ▸ R.open_edge_mem_openPiece e ht hs)
  disjoint_open_edges e d different := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ ⟨s, hs, equal⟩
    exact Set.disjoint_left.mp
      (R.openPieces_pairwise_disjoint (fun same => different (Subtype.ext same)))
      (R.open_edge_mem_openPiece e ht.1 ht.2)
      (equal ▸ R.open_edge_mem_openPiece d hs.1 hs.2)

theorem embedding_straight : R.embedding.IsStraight := fun _ _ => rfl

theorem embedding_parent_link (e : R.Edge) : R.embedding.graph.IsLink e e.val (R.next e.val) :=
  Or.inl ⟨rfl, rfl⟩

theorem embedding_reaches_of_ancestor {v w : V} (ancestor : R.parents.Ancestor v w) :
    R.embedding.graph.Reaches v w := by
  obtain ⟨n, rfl⟩ := ancestor
  induction n with
  | zero => exact Graph.Reaches.refl (Set.mem_univ _)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases root : R.parents.parent^[n] v ∈ R.parents.roots
    · rwa [R.parents.fixed_root _ root]
    · exact ih.trans (Graph.Reaches.of_isLink (R.embedding_parent_link ⟨_, root⟩))

theorem embedding_rootedForest : R.embedding.graph.IsRootedForest R.terminal := by
  refine ⟨?_, ?_⟩
  · apply R.parents.graph_acyclic.of_mapAlong (G := R.embedding.graph) (fun v => v)
      Subtype.val (fun _ _ => Set.mem_univ _) _ Subtype.val_injective
    intro e v w link
    exact ⟨e.property, link⟩
  · intro v _
    refine ⟨R.parents.root v,
      ⟨R.parents.root_mem v, R.embedding_reaches_of_ancestor (R.parents.ancestor_root v)⟩, ?_⟩
    rintro r ⟨root, _edges, walk⟩
    have same : R.parents.root v = R.parents.root r := walk.eq_of_link_invariant R.parents.root (by
      intro e x y link
      have equal := R.parents.root_eq_of_ancestor (R.parents.ancestor_parent e.val)
      rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact equal
      · exact equal.symm)
    exact (same.trans (R.parents.root_of_root root)).symm

end Unfoldings.SlopeEnvelope.ExteriorPlan
