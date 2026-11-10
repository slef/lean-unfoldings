module

public import Unfoldings.Topology.AscendingForest

/-!
# Original-edge forests from increasing parent choices

Selected edges keep their original names. Strict ascent proves that distinct
nonroot vertices select distinct undirected edges, and proves acyclicity and
unique roots for the actual selected subgraph.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V E : Type*} (P : AscendingParents V) (G : Graph V E)

structure EdgeSelection where
  edge : {v : V // v ∉ P.roots} → E
  link : ∀ v, G.IsLink (edge v) v.val (P.parent v.val)

namespace EdgeSelection

variable {P G} (S : P.EdgeSelection G)

theorem edge_injective : Function.Injective S.edge := by
  intro v w equal
  have last := S.link w
  rw [← equal] at last
  rcases (S.link v).eq_and_eq_or_eq_and_eq last with same | reversed
  · exact Subtype.ext same.1
  · have first := P.ascending v.val v.property
    have second := P.ascending w.val w.property
    rw [← reversed.1] at second
    rw [reversed.2] at first
    exact (lt_asymm first second).elim

/-- The selected graph has original edge names and all original vertices. -/
def graph : Graph V E where
  vertexSet := Set.univ
  edgeSet := Set.range S.edge
  IsLink e a b := ∃ v : {v : V // v ∉ P.roots}, S.edge v = e ∧
    ((a = v.val ∧ b = P.parent v.val) ∨ (a = P.parent v.val ∧ b = v.val))
  isLink_symm := by
    intro e _
    constructor
    rintro a b ⟨v, equal, endpoints⟩
    exact ⟨v, equal, endpoints.elim (fun h => Or.inr ⟨h.2, h.1⟩)
      (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e a b c d ⟨v, first, endpoints⟩ ⟨w, last, other⟩
    have same : v = w := S.edge_injective (first.trans last.symm)
    subst w
    rcases endpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases other with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun ⟨v, equal⟩ => ⟨v.val, P.parent v.val, v, equal, Or.inl ⟨rfl, rfl⟩⟩,
      fun ⟨_, _, v, equal, _⟩ => ⟨v, equal⟩⟩
  left_mem_of_isLink := fun _ _ _ _ => Set.mem_univ _

theorem parent_link (v : {v : V // v ∉ P.roots}) :
    S.graph.IsLink (S.edge v) v.val (P.parent v.val) :=
  ⟨v, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Every selected edge is an actual original edge with exactly its original ends. -/
theorem graph_le (vertices : G.vertexSet = Set.univ) : S.graph ≤ G where
  vertexSet_mono := by rw [vertices]; exact Set.Subset.rfl
  isLink_mono := by
    rintro e a b ⟨v, rfl, endpoints⟩
    rcases endpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.link v
    · exact (S.link v).symm

theorem graph_acyclic : S.graph.IsAcyclic := by
  intro e member cycle
  obtain ⟨v, rfl⟩ := member
  obtain ⟨edges, walk⟩ := cycle.deleteEdges_reaches (S.parent_link v)
  have invariant : P.Ancestor v.val v.val = P.Ancestor (P.parent v.val) v.val :=
    walk.eq_of_link_invariant (fun a => P.Ancestor a v.val) (by
      intro f a b link
      have original : S.graph.IsLink f a b ∧ f ∉ ({S.edge v} : Set E) := link
      obtain ⟨w, named, endpoints⟩ := original.1
      have different : w.val ≠ v.val := by
        intro same
        have tags : w = v := Subtype.ext same
        exact original.2 (by simpa only [Set.mem_singleton_iff, tags] using named.symm)
      have equivalent := P.ancestor_parent_iff different
      rcases endpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact propext equivalent
      · exact (propext equivalent).symm)
  exact P.not_ancestor_parent_self v.property (invariant ▸ P.ancestor_refl v.val)

theorem reaches_of_ancestor {v w : V} (related : P.Ancestor v w) : S.graph.Reaches v w := by
  obtain ⟨n, rfl⟩ := related
  induction n with
  | zero => exact Graph.Reaches.refl (Set.mem_univ _)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases root : P.parent^[n] v ∈ P.roots
    · rwa [P.fixed_root _ root]
    · exact ih.trans (Graph.Reaches.of_isLink (S.parent_link ⟨_, root⟩))

variable [Finite V]

/-- The forest consists of the selected original edges, retaining their names. -/
theorem graph_rootedForest : S.graph.IsRootedForest P.roots := by
  refine ⟨S.graph_acyclic, fun v _ => ?_⟩
  refine ⟨P.root v, ⟨P.root_mem v, S.reaches_of_ancestor (P.ancestor_root v)⟩, ?_⟩
  rintro r ⟨marked, edges, walk⟩
  have invariant : P.root v = P.root r := walk.eq_of_link_invariant P.root (by
    rintro e a b ⟨w, _, endpoints⟩
    have same := P.root_eq_of_ancestor (P.ancestor_parent w.val)
    rcases endpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact same
    · exact same.symm)
  exact (invariant.trans (P.root_of_root marked)).symm

end EdgeSelection
end Unfoldings.AscendingParents
