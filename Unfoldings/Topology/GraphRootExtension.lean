module

public import Schoenflies.Graph.Tree
public import Unfoldings.Topology.GraphReachability
public import Unfoldings.Topology.GraphForestMap

/-!
# Root extensions of multigraphs

Adjoin an outside vertex and a separately named edge to every marked root.
All original edges retain their names: loops and parallel edges are preserved.
Isolated marked vertices are included, so an empty cut still has its outside
star. This interface is independent of geometric unfoldings.
-/

@[expose] public section

noncomputable section

namespace Graph

variable {V E : Type*} (G : Graph V E) (roots : Set V)

/-- A forest whose every vertex component contains exactly one marked root. -/
def IsRootedForest : Prop :=
  G.IsAcyclic ∧ ∀ v ∈ G.vertexSet, ∃! r, r ∈ roots ∧ G.Reaches v r

def rootExtension : Graph (Option V) (E ⊕ roots) where
  vertexSet := {v | match v with
    | none => True
    | some v => v ∈ G.vertexSet ∨ v ∈ roots}
  edgeSet := {e | match e with
    | .inl e => e ∈ G.edgeSet
    | .inr _ => True}
  IsLink e a b := match e with
    | .inl e => ∃ u v, G.IsLink e u v ∧ a = some u ∧ b = some v
    | .inr r => (a = none ∧ b = some r.val) ∨ (a = some r.val ∧ b = none)
  isLink_symm := by
    intro e _
    constructor
    intro a b link
    cases e with
    | inl e =>
      obtain ⟨u, v, link, rfl, rfl⟩ := link
      exact ⟨v, u, link.symm, rfl, rfl⟩
    | inr r =>
      exact link.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  eq_or_eq_of_isLink_of_isLink := by
    intro e a b c d first second
    cases e with
    | inl e =>
      obtain ⟨u, v, link, rfl, rfl⟩ := first
      obtain ⟨w, z, other, rfl, rfl⟩ := second
      exact (link.left_eq_or_eq other).imp (congrArg some) (congrArg some)
    | inr r =>
      rcases first with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals rcases second with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals simp
  edge_mem_iff_exists_isLink := by
    intro e
    cases e with
    | inl e =>
      constructor
      · intro member
        obtain ⟨u, v, link⟩ := (G.edge_mem_iff_exists_isLink e).mp member
        exact ⟨some u, some v, u, v, link, rfl, rfl⟩
      · rintro ⟨_, _, u, v, link, _, _⟩
        exact link.edge_mem
    | inr r => exact ⟨fun _ => ⟨none, some r.val, Or.inl ⟨rfl, rfl⟩⟩,
        fun _ => True.intro⟩
  left_mem_of_isLink := by
    intro e a b link
    cases e with
    | inl e =>
      obtain ⟨u, v, link, rfl, rfl⟩ := link
      exact Or.inl link.left_mem
    | inr r =>
      rcases link with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · trivial
      · exact Or.inr r.property

theorem IsLink.rootExtension {G : Graph V E} {e : E} {u v : V} (link : G.IsLink e u v) :
    (G.rootExtension roots).IsLink (.inl e) (some u) (some v) :=
  ⟨u, v, link, rfl, rfl⟩

theorem rootExtension_spoke (r : roots) :
    (G.rootExtension roots).IsLink (.inr r) none (some r.val) := Or.inl ⟨rfl, rfl⟩

theorem Reaches.rootExtension {G : Graph V E} {u v : V} (reach : G.Reaches u v) :
    (G.rootExtension roots).Reaches (some u) (some v) := by
  obtain ⟨edges, walk⟩ := reach
  exact ⟨edges.map Sum.inl, walk.mapAlong (H := G.rootExtension roots) some Sum.inl
    (fun _ member => Or.inl member) (fun {_ _ _} link => link.rootExtension roots)⟩

theorem rootExtension_connected_iff (root_mem : roots ⊆ G.vertexSet) :
    (G.rootExtension roots).Connected ↔ ∀ v ∈ G.vertexSet, ∃ r ∈ roots, G.Reaches v r := by
  constructor
  · intro connected v member
    let P : Option V → Prop
      | none => True
      | some w => ∃ r ∈ roots, G.Reaches w r
    have step {e : E ⊕ roots} {a b : Option V}
        (link : (G.rootExtension roots).IsLink e a b) (initial : P a) : P b := by
      cases e with
      | inl e =>
        obtain ⟨u, w, link, rfl, rfl⟩ := link
        obtain ⟨r, root, reach⟩ := initial
        exact ⟨r, root, (Reaches.of_isLink link.symm).trans reach⟩
      | inr r =>
        rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨r.val, r.property, Reaches.refl (root_mem r.property)⟩
        · trivial
    obtain ⟨edges, walk⟩ := connected.reaches (show none ∈ (G.rootExtension roots).vertexSet by
      trivial) (show some v ∈ (G.rootExtension roots).vertexSet from Or.inl member)
    exact walk.propagate P @step True.intro
  · intro covered
    have reach (v : Option V) (member : v ∈ (G.rootExtension roots).vertexSet) :
        (G.rootExtension roots).Reaches none v := by
      cases v with
      | none => exact Reaches.refl (by trivial)
      | some v =>
        rcases member with original | root
        · obtain ⟨r, root, path⟩ := covered v original
          exact (Reaches.of_isLink (G.rootExtension_spoke roots ⟨r, root⟩)).trans
            (path.symm.rootExtension roots)
        · exact Reaches.of_isLink (G.rootExtension_spoke roots ⟨v, root⟩)
    exact ⟨⟨none, by trivial⟩, fun a ha b hb => (reach a ha).symm.trans (reach b hb)⟩

/-- Original walks survive deletion of every outside spoke. -/
theorem Reaches.rootExtension_delete_spoke {G : Graph V E} {u v : V}
    (reach : G.Reaches u v) (r : roots) :
    ((G.rootExtension roots).deleteEdges {Sum.inr r}).Reaches (some u) (some v) := by
  obtain ⟨edges, walk⟩ := reach
  apply (walk.mapAlong (H := G.rootExtension roots) some Sum.inl (fun _ member => Or.inl member)
    (fun {_ _ _} link => link.rootExtension roots)).reaches_deleteEdges
  intro f member equal
  obtain ⟨e, _member, rfl⟩ := List.mem_map.mp member
  change (Sum.inl e : E ⊕ roots) = Sum.inr r at equal
  cases equal

theorem rootExtension_roots_separated (forest : (G.rootExtension roots).IsAcyclic)
    {r s : V} (hr : r ∈ roots) (hs : s ∈ roots) (reach : G.Reaches r s) : r = s := by
  by_contra different
  let first : roots := ⟨r, hr⟩
  let last : roots := ⟨s, hs⟩
  have other : ((G.rootExtension roots).deleteEdges {Sum.inr first}).IsLink
      (Sum.inr last) (some s) none := by
    rw [Graph.deleteEdges_isLink]
    exact ⟨(G.rootExtension_spoke roots last).symm, by
      intro equal
      exact different (congrArg Subtype.val (Sum.inr.inj equal)).symm⟩
  have alt := (reach.rootExtension_delete_spoke roots first).trans (Reaches.of_isLink other)
  exact (forest.isBridge (G.rootExtension_spoke roots first).edge_mem).not_reaches
    (G.rootExtension_spoke roots first).symm alt

theorem rootExtension_acyclic_of_roots_separated (root_mem : roots ⊆ G.vertexSet)
    (forest : G.IsAcyclic)
    (separated : ∀ r ∈ roots, ∀ s ∈ roots, G.Reaches r s → r = s) :
    (G.rootExtension roots).IsAcyclic := by
  classical
  let H := G.rootExtension roots
  have original_bridge {e : E} {u v : V} (link : G.IsLink e u v) :
      H.IsBridge (Sum.inl e) := by
    let D := G.deleteEdges {e}
    let outside : Prop := ∃ r ∈ roots, D.Reaches u r
    let color : Option V → Prop
      | none => outside
      | some w => if G.Reaches u w then D.Reaches u w else outside
    have old_step {f : E} {a b : V} (step : D.IsLink f a b) :
        color (some a) = color (some b) := by
      have original : G.Reaches u a ↔ G.Reaches u b :=
        ⟨fun path => path.trans (Reaches.of_isLink step.1),
          fun path => path.trans (Reaches.of_isLink step.1.symm)⟩
      have deleted : D.Reaches u a ↔ D.Reaches u b :=
        ⟨fun path => path.trans (Reaches.of_isLink step),
          fun path => path.trans (Reaches.of_isLink step.symm)⟩
      simp only [color, original]
      split_ifs <;> first | exact propext deleted | rfl
    have root_color (r : roots) : color (some r.val) = color none := by
      change (if G.Reaches u r.val then D.Reaches u r.val else outside) = outside
      split_ifs with connected
      · apply propext
        constructor
        · exact fun reach => ⟨r.val, r.property, reach⟩
        · rintro ⟨s, hs, reach⟩
          have same := separated r.val r.property s hs
            (connected.symm.trans reach.of_deleteEdges)
          exact same.symm ▸ reach
      · rfl
    have step {f : E ⊕ roots} {a b : Option V}
        (actual : (H.deleteEdges {Sum.inl e}).IsLink f a b) : color a = color b := by
      obtain ⟨actual, omitted⟩ := actual
      cases f with
      | inl f =>
        obtain ⟨a, b, old, rfl, rfl⟩ := actual
        apply old_step
        rw [Graph.deleteEdges_isLink]
        exact ⟨old, fun same => omitted (congrArg Sum.inl same)⟩
      | inr r =>
        rcases actual with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (root_color r).symm
        · exact root_color r
    apply Graph.isBridge_of_not_reaches (link.rootExtension roots)
    rintro ⟨edges, walk⟩
    have equal := walk.eq_of_link_invariant color @step
    have at_u : color (some u) := by
      change if G.Reaches u u then D.Reaches u u else outside
      rw [ite_eq_left (Reaches.refl link.left_mem)]
      exact Reaches.refl link.left_mem
    have at_v : ¬ color (some v) := by
      change ¬ (if G.Reaches u v then D.Reaches u v else outside)
      rw [ite_eq_left (Reaches.of_isLink link)]
      exact (forest.isBridge link.edge_mem).not_reaches link
    exact at_v (equal ▸ at_u)
  have spoke_bridge (r : roots) : H.IsBridge (Sum.inr r) := by
    let color : Option V → Prop
      | none => False
      | some w => G.Reaches r.val w
    have step {f : E ⊕ roots} {a b : Option V}
        (actual : (H.deleteEdges {Sum.inr r}).IsLink f a b) : color a = color b := by
      obtain ⟨actual, omitted⟩ := actual
      cases f with
      | inl f =>
        obtain ⟨a, b, link, rfl, rfl⟩ := actual
        exact propext ⟨fun reach => reach.trans (Reaches.of_isLink link),
          fun reach => reach.trans (Reaches.of_isLink link.symm)⟩
      | inr s =>
        have absent : ¬ G.Reaches r.val s.val := by
          intro reach
          have equal := separated r.val r.property s.val s.property reach
          exact omitted (congrArg Sum.inr (Subtype.ext equal).symm)
        rcases actual with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact propext ⟨False.elim, absent⟩
        · exact propext ⟨absent, False.elim⟩
    apply Graph.isBridge_of_not_reaches (G.rootExtension_spoke roots r)
    rintro ⟨edges, walk⟩
    have equal := walk.eq_of_link_invariant color @step
    have yes : color (some r.val) := Reaches.refl (root_mem r.property)
    exact Eq.mpr equal yes
  intro e member
  cases e with
  | inl e =>
    obtain ⟨u, v, link⟩ := (G.edge_mem_iff_exists_isLink e).mp member
    exact (original_bridge link).not_liesOnCycle
  | inr r => exact (spoke_bridge r).not_liesOnCycle

theorem rootExtension_isTree_iff (root_mem : roots ⊆ G.vertexSet) :
    (G.rootExtension roots).IsTree ↔ G.IsRootedForest roots := by
  constructor
  · rintro ⟨connected, forest⟩
    have original : G.IsAcyclic := forest.of_mapAlong
      (G := G) (H := G.rootExtension roots) some Sum.inl
      (fun _ member => Or.inl member)
      (fun {_ _ _} link => link.rootExtension roots) Sum.inl_injective
    refine ⟨original, ?_⟩
    intro v member
    obtain ⟨r, hr, reach⟩ := (G.rootExtension_connected_iff roots root_mem).mp connected v member
    exact ⟨r, ⟨hr, reach⟩, fun s hs =>
      G.rootExtension_roots_separated roots forest hs.1 hr (hs.2.symm.trans reach)⟩
  · rintro ⟨forest, rooted⟩
    have separated : ∀ r ∈ roots, ∀ s ∈ roots, G.Reaches r s → r = s := by
      intro r hr s hs reach
      obtain ⟨root, _present, unique⟩ := rooted r (root_mem hr)
      exact (unique r ⟨hr, Reaches.refl (root_mem hr)⟩).trans (unique s ⟨hs, reach⟩).symm
    exact ⟨(G.rootExtension_connected_iff roots root_mem).mpr
      (fun v member => (rooted v member).exists),
      G.rootExtension_acyclic_of_roots_separated roots root_mem forest separated⟩

end Graph
