module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Rooted forests and adjoining an outside vertex

Adjoin a new vertex and an edge to each marked root. The resulting graph is a
tree exactly when the original graph is a forest and each component contains
exactly one marked root. The vertex type may be empty, so the empty forest is
included. This is the combinatorial reduction for cuts on a disk.
-/

@[expose] public section

noncomputable section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

def rootExtension (roots : Set V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | none, none => False
    | none, some v => v ∈ roots
    | some v, none => v ∈ roots
    | some v, some w => G.Adj v w
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    intro a h
    cases a
    · exact h
    · exact G.ne_of_adj h rfl

@[simp] theorem rootExtension_adj_some_some (roots : Set V) (v w : V) :
    (G.rootExtension roots).Adj (some v) (some w) ↔ G.Adj v w := Iff.rfl

@[simp] theorem rootExtension_adj_none_some (roots : Set V) (v : V) :
    (G.rootExtension roots).Adj none (some v) ↔ v ∈ roots := Iff.rfl

@[simp] theorem rootExtension_adj_some_none (roots : Set V) (v : V) :
    (G.rootExtension roots).Adj (some v) none ↔ v ∈ roots := Iff.rfl

@[simp] theorem rootExtension_not_adj_none_none (roots : Set V) :
    ¬ (G.rootExtension roots).Adj none none := id

def rootExtensionInclusion (roots : Set V) : G →g G.rootExtension roots where
  toFun := some
  map_rel' := fun h => h

theorem rootExtension_reachable_none_iff (roots : Set V) (v : V) :
    (G.rootExtension roots).Reachable none (some v) ↔ ∃ r ∈ roots, G.Reachable r v := by
  let marked : Option V → Prop
    | none => True
    | some w => ∃ r ∈ roots, G.Reachable r w
  have step {a b : Option V} (adj : (G.rootExtension roots).Adj a b) : marked a → marked b := by
    cases a with
    | none =>
      cases b with
      | none => exact fun _ => True.intro
      | some b => exact fun _ => ⟨b, adj, Reachable.rfl⟩
    | some a =>
      cases b with
      | none => exact fun _ => True.intro
      | some b =>
        rintro ⟨r, hr, reachable⟩
        exact ⟨r, hr, reachable.trans (Adj.reachable adj)⟩
  constructor
  · rintro ⟨walk⟩
    have walk_preserves {a b : Option V} (p : (G.rootExtension roots).Walk a b) :
        marked a → marked b := by
      induction p with
      | nil => exact id
      | cons adj tail ih => exact fun h => ih (step adj h)
    exact walk_preserves walk True.intro
  · rintro ⟨r, hr, reachable⟩
    have adjacent : (G.rootExtension roots).Adj none (some r) := hr
    exact adjacent.reachable.trans (reachable.map (G.rootExtensionInclusion roots))

theorem rootExtension_connected_iff (roots : Set V) :
    (G.rootExtension roots).Connected ↔ ∀ v, ∃ r ∈ roots, G.Reachable r v := by
  constructor
  · intro connected v
    exact (G.rootExtension_reachable_none_iff roots v).mp (connected.preconnected none (some v))
  · intro covered
    have reaches (v : Option V) : (G.rootExtension roots).Reachable none v := by
      cases v with
      | none => exact Reachable.rfl
      | some v => exact (G.rootExtension_reachable_none_iff roots v).mpr (covered v)
    exact { nonempty := ⟨none⟩, preconnected := fun a b => (reaches a).symm.trans (reaches b) }

theorem rootExtension_insert (roots : Set V) (r : V) :
    G.rootExtension (insert r roots) = G.rootExtension roots ⊔ edge none (some r) := by
  ext a b
  cases a <;> cases b <;> simp [rootExtension, edge_adj, eq_comm, or_comm]

theorem rootExtension_empty_acyclic (forest : G.IsAcyclic) : (G.rootExtension ∅).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b adjacent
  cases a with
  | none => cases b <;> simp [rootExtension] at adjacent
  | some u =>
    cases b with
    | none => simp [rootExtension] at adjacent
    | some v =>
      have bridge := (isAcyclic_iff_forall_adj_isBridge.mp forest) adjacent
      rw [isBridge_iff] at bridge ⊢
      intro reachable
      let collapse : ((G.rootExtension ∅).deleteEdges {s(some u, some v)}) →g
          G.deleteEdges {s(u, v)} :=
        { toFun := fun x => x.getD u
          map_rel' := by
            intro x y h
            cases x <;> cases y <;>
              simp_all [rootExtension, deleteEdges_adj] }
      exact bridge (reachable.map collapse)

theorem rootExtension_acyclic_roots_separated (roots : Set V)
    (forest : (G.rootExtension roots).IsAcyclic) {r s : V}
    (hr : r ∈ roots) (hs : s ∈ roots) (reachable : G.Reachable r s) : r = s := by
  classical
  by_contra different
  have adjacent : (G.rootExtension roots).Adj none (some r) := hr
  have bridge := (isAcyclic_iff_forall_adj_isBridge.mp forest) adjacent
  rw [isBridge_iff] at bridge
  let inclusion : G →g (G.rootExtension roots).deleteEdges {s(none, some r)} :=
    { toFun := some
      map_rel' := by
        intro u v h
        exact deleteEdges_adj.mpr ⟨h, by simp⟩ }
  have other : ((G.rootExtension roots).deleteEdges {s(none, some r)}).Adj none (some s) := by
    apply deleteEdges_adj.mpr
    exact ⟨hs, by simp [Ne.symm different]⟩
  exact bridge (other.reachable.trans (reachable.symm.map inclusion))

theorem rootExtension_acyclic_of_separated (roots : Set V) (finite : roots.Finite)
    (forest : G.IsAcyclic)
    (separated : ∀ r ∈ roots, ∀ s ∈ roots, G.Reachable r s → r = s) :
    (G.rootExtension roots).IsAcyclic := by
  classical
  revert separated
  induction roots, finite using Set.Finite.induction_on with
  | empty => exact fun _ => G.rootExtension_empty_acyclic forest
  | @insert r roots absent finite ih =>
    intro separated
    have base := ih (fun a ha b hb reach =>
      separated a (Set.mem_insert_of_mem _ ha) b (Set.mem_insert_of_mem _ hb) reach)
    have not_reachable : ¬ (G.rootExtension roots).Reachable none (some r) := by
      rw [G.rootExtension_reachable_none_iff]
      rintro ⟨s, hs, reach⟩
      have same := separated s (Set.mem_insert_of_mem _ hs) r (Set.mem_insert _ _) reach
      exact absent (same ▸ hs)
    rw [G.rootExtension_insert]
    exact base.sup_edge_of_not_reachable not_reachable

theorem rootExtension_acyclic_iff (roots : Set V) (finite : roots.Finite) :
    (G.rootExtension roots).IsAcyclic ↔ G.IsAcyclic ∧
      ∀ r ∈ roots, ∀ s ∈ roots, G.Reachable r s → r = s := by
  constructor
  · intro forest
    exact ⟨forest.comap (G.rootExtensionInclusion roots) (Option.some_injective V),
      fun r hr s hs reach => G.rootExtension_acyclic_roots_separated roots forest hr hs reach⟩
  · rintro ⟨forest, separated⟩
    exact G.rootExtension_acyclic_of_separated roots finite forest separated

/-- A forest with exactly one marked root in every component, allowing no vertices. -/
def IsRootedForest (roots : Set V) : Prop :=
  G.IsAcyclic ∧ ∀ v, ∃! r, r ∈ roots ∧ G.Reachable v r

theorem rootExtension_tree_iff (roots : Set V) (finite : roots.Finite) :
    (G.rootExtension roots).IsTree ↔ G.IsRootedForest roots := by
  rw [isTree_iff, G.rootExtension_connected_iff, G.rootExtension_acyclic_iff roots finite]
  constructor
  · rintro ⟨covered, forest, separated⟩
    refine ⟨forest, ?_⟩
    intro v
    obtain ⟨r, hr, reachable⟩ := covered v
    refine ⟨r, ⟨hr, reachable.symm⟩, ?_⟩
    rintro s ⟨hs, reach⟩
    exact separated s hs r hr (reach.symm.trans reachable.symm)
  · rintro ⟨forest, unique⟩
    refine ⟨?_, forest, ?_⟩
    · intro v
      obtain ⟨r, ⟨hr, reachable⟩, _⟩ := unique v
      exact ⟨r, hr, reachable.symm⟩
    · intro r hr s hs reachable
      obtain ⟨root, _, only⟩ := unique r
      exact (only r ⟨hr, Reachable.rfl⟩).trans (only s ⟨hs, reachable⟩).symm

variable {G}

theorem IsRootedForest.roots_separated {roots : Set V} (rooted : G.IsRootedForest roots)
    {r s : V} (hr : r ∈ roots) (hs : s ∈ roots) (reachable : G.Reachable r s) : r = s := by
  obtain ⟨root, _, only⟩ := rooted.2 r
  exact (only r ⟨hr, Reachable.rfl⟩).trans (only s ⟨hs, reachable⟩).symm

theorem IsRootedForest.roots_bijective_components {roots : Set V}
    (rooted : G.IsRootedForest roots) :
    Function.Bijective (fun r : roots => G.connectedComponentMk r.val) := by
  constructor
  · intro r s equal
    exact Subtype.ext
      (rooted.roots_separated r.property s.property (ConnectedComponent.eq.mp equal))
  · intro component
    refine component.ind (fun v => ?_)
    obtain ⟨r, ⟨hr, reachable⟩, _⟩ := rooted.2 v
    exact ⟨⟨r, hr⟩, ConnectedComponent.eq.mpr reachable.symm⟩

def IsRootedForest.rootsComponentEquiv {roots : Set V} (rooted : G.IsRootedForest roots) :
    roots ≃ G.ConnectedComponent :=
  Equiv.ofBijective (fun r : roots => G.connectedComponentMk r.val)
    rooted.roots_bijective_components

theorem isRootedForest_iff_acyclic_and_bijective_roots (roots : Set V) :
    G.IsRootedForest roots ↔ G.IsAcyclic ∧
      Function.Bijective (fun r : roots => G.connectedComponentMk r.val) := by
  constructor
  · exact fun rooted => ⟨rooted.1, rooted.roots_bijective_components⟩
  · rintro ⟨forest, injective, onto⟩
    refine ⟨forest, ?_⟩
    intro v
    obtain ⟨r, component⟩ := onto (G.connectedComponentMk v)
    refine ⟨r.val, ⟨r.property, (ConnectedComponent.eq.mp component).symm⟩, ?_⟩
    rintro s ⟨hs, reachable⟩
    have same : G.connectedComponentMk s = G.connectedComponentMk r.val :=
      (ConnectedComponent.eq.mpr reachable.symm).trans component.symm
    exact congrArg Subtype.val (injective (show
      (fun q : roots => G.connectedComponentMk q.val) ⟨s, hs⟩ =
        (fun q : roots => G.connectedComponentMk q.val) r from same))

theorem isRootedForest_empty_iff : G.IsRootedForest ∅ ↔ IsEmpty V := by
  constructor
  · intro rooted
    constructor
    intro v
    obtain ⟨r, ⟨hr, _⟩, _⟩ := rooted.2 v
    exact hr
  · intro empty
    let := empty
    constructor
    · intro v
      exact isEmptyElim v
    · intro v
      exact isEmptyElim v

end SimpleGraph


