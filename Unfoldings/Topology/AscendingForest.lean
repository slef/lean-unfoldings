module

public import Unfoldings.Topology.GraphRootExtension
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Function.Iterate

/-!
# Forests selected by increasing parents

Choose one outgoing edge at each nonroot vertex, strictly increasing a real
potential. The resulting undirected multigraph is a forest. For finite vertex
sets every component has exactly one marked root. This combinatorial result
makes no geometric noncrossing assumption.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable (V : Type*)

structure AscendingParents where
  roots : Set V
  parent : V → V
  height : V → ℝ
  fixed_root : ∀ v ∈ roots, parent v = v
  ascending : ∀ v ∉ roots, height v < height (parent v)

namespace AscendingParents

variable {V} (P : AscendingParents V)

/-- A forward parent orbit, including the starting vertex. -/
def Ancestor (v w : V) : Prop := ∃ n : ℕ, P.parent^[n] v = w

theorem ancestor_refl (v : V) : P.Ancestor v v := ⟨0, rfl⟩

theorem ancestor_parent (v : V) : P.Ancestor v (P.parent v) := ⟨1, rfl⟩

theorem Ancestor.trans {v w z : V} (first : P.Ancestor v w) (last : P.Ancestor w z) :
    P.Ancestor v z := by
  obtain ⟨n, first⟩ := first
  obtain ⟨m, last⟩ := last
  exact ⟨m + n, by rw [Function.iterate_add_apply, first, last]⟩

theorem height_parent (v : V) : P.height v ≤ P.height (P.parent v) := by
  by_cases root : v ∈ P.roots
  · rw [P.fixed_root v root]
  · exact (P.ascending v root).le

theorem Ancestor.height_le {v w : V} (related : P.Ancestor v w) : P.height v ≤ P.height w := by
  obtain ⟨n, rfl⟩ := related
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (P.height_parent _)

theorem ancestor_parent_iff {v e : V} (different : v ≠ e) :
    P.Ancestor v e ↔ P.Ancestor (P.parent v) e := by
  constructor
  · rintro ⟨n, reaches⟩
    cases n with
    | zero => exact (different reaches).elim
    | succ n => exact ⟨n, by simpa only [Function.iterate_succ_apply] using reaches⟩
  · rintro ⟨n, reaches⟩
    exact ⟨n + 1, by simpa only [Function.iterate_succ_apply] using reaches⟩

theorem not_ancestor_parent_self {e : V} (nonroot : e ∉ P.roots) :
    ¬ P.Ancestor (P.parent e) e := by
  intro related
  exact (not_lt_of_ge (Ancestor.height_le P related)) (P.ascending e nonroot)

/-- Each nonroot vertex names its selected edge, retaining edge identities. -/
def graph : Graph V V where
  vertexSet := Set.univ
  edgeSet := P.rootsᶜ
  IsLink e a b := e ∉ P.roots ∧
    ((a = e ∧ b = P.parent e) ∨ (a = P.parent e ∧ b = e))
  isLink_symm := by
    intro e _
    constructor
    intro a b link
    exact ⟨link.1, link.2.elim (fun h => Or.inr ⟨h.2, h.1⟩)
      (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e a b c d first last
    rcases first.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases last.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun member => ⟨e, P.parent e, member, Or.inl ⟨rfl, rfl⟩⟩,
      fun ⟨_, _, link⟩ => link.1⟩
  left_mem_of_isLink := fun _ _ _ _ => Set.mem_univ _

theorem graph_parent_link {e : V} (nonroot : e ∉ P.roots) :
    P.graph.IsLink e e (P.parent e) := ⟨nonroot, Or.inl ⟨rfl, rfl⟩⟩

/-- Deleting the selected edge at `e` separates its descendants from its parent. -/
theorem graph_acyclic : P.graph.IsAcyclic := by
  intro e nonroot cycle
  have link := P.graph_parent_link nonroot
  obtain ⟨edges, walk⟩ := cycle.deleteEdges_reaches link
  have invariant : P.Ancestor e e = P.Ancestor (P.parent e) e :=
    walk.eq_of_link_invariant (fun v => P.Ancestor v e) (by
      intro f a b other
      have named : P.graph.IsLink f a b ∧ f ∉ ({e} : Set V) := other
      have different : f ≠ e := by simpa using named.2
      have equivalent := P.ancestor_parent_iff different
      rcases named.1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact propext equivalent
      · exact (propext equivalent).symm)
  exact P.not_ancestor_parent_self nonroot (invariant ▸ P.ancestor_refl e)

theorem Ancestor.reaches {v w : V} (related : P.Ancestor v w) : P.graph.Reaches v w := by
  obtain ⟨n, rfl⟩ := related
  induction n with
  | zero => exact Graph.Reaches.refl (Set.mem_univ _)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases root : P.parent^[n] v ∈ P.roots
    · rwa [P.fixed_root _ root]
    · exact ih.trans (Graph.Reaches.of_isLink (P.graph_parent_link root))

theorem ancestor_root_unique {v r s : V} (first : P.Ancestor v r) (last : P.Ancestor v s)
    (rroot : r ∈ P.roots) (sroot : s ∈ P.roots) : r = s := by
  obtain ⟨n, first⟩ := first
  obtain ⟨m, last⟩ := last
  have compare {a b : ℕ} {r s : V} (ordered : a ≤ b)
      (first : P.parent^[a] v = r) (last : P.parent^[b] v = s)
      (root : r ∈ P.roots) : r = s := by
    have same : P.parent^[b] v = r := by
      rw [← Nat.sub_add_cancel ordered, Function.iterate_add_apply, first,
        Function.iterate_fixed (P.fixed_root r root)]
    exact same.symm.trans last
  rcases le_total n m with ordered | ordered
  · exact compare ordered first last rroot
  · exact (compare ordered last first sroot).symm

variable [Finite V]

theorem exists_ancestor_root (v : V) : ∃ r ∈ P.roots, P.Ancestor v r := by
  classical
  let := Fintype.ofFinite V
  let orbit : Finset V := Finset.univ.filter (P.Ancestor v)
  have member (w : V) : w ∈ orbit ↔ P.Ancestor v w := by simp [orbit]
  obtain ⟨r, present, maximal⟩ := orbit.exists_max_image P.height
    ⟨v, (member v).mpr (P.ancestor_refl v)⟩
  have ancestor := (member r).mp present
  refine ⟨r, ?_, ancestor⟩
  by_contra nonroot
  have next := maximal (P.parent r)
    ((member _).mpr (Ancestor.trans P ancestor (P.ancestor_parent r)))
  exact (not_lt_of_ge next) (P.ascending r nonroot)

def root (v : V) : V := (P.exists_ancestor_root v).choose

theorem root_mem (v : V) : P.root v ∈ P.roots := (P.exists_ancestor_root v).choose_spec.1

theorem ancestor_root (v : V) : P.Ancestor v (P.root v) :=
  (P.exists_ancestor_root v).choose_spec.2

theorem root_eq_of_ancestor {v w : V} (related : P.Ancestor v w) : P.root v = P.root w :=
  P.ancestor_root_unique (P.ancestor_root v)
    (Ancestor.trans P related (P.ancestor_root w)) (P.root_mem v) (P.root_mem w)

theorem root_of_root {v : V} (root : v ∈ P.roots) : P.root v = v :=
  P.ancestor_root_unique (P.ancestor_root v) (P.ancestor_refl v) (P.root_mem v) root

/-- Strict ascent on a finite vertex set constructs an actual boundary-rooted forest. -/
theorem graph_rootedForest : P.graph.IsRootedForest P.roots := by
  refine ⟨P.graph_acyclic, fun v _ => ?_⟩
  refine ⟨P.root v, ⟨P.root_mem v, Ancestor.reaches P (P.ancestor_root v)⟩, ?_⟩
  rintro r ⟨marked, edges, walk⟩
  have invariant : P.root v = P.root r := walk.eq_of_link_invariant P.root (by
    intro e a b link
    have same := P.root_eq_of_ancestor (P.ancestor_parent e)
    rcases link.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact same
    · exact same.symm)
  exact (invariant.trans (P.root_of_root marked)).symm

end AscendingParents
end Unfoldings
