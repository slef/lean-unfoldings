module

public import Unfoldings.Topology.GraphRootExtension
public import Unfoldings.Topology.GraphVertexMap

/-!
# Recover rooted forests from a quotient identifying exactly the roots

Edge names survive quotienting, including loops and parallel edges. A tree
quotient therefore excludes cycles and paths joining distinct marked roots.
Connectedness forces every component to meet a root.
-/

@[expose] public section

namespace Graph

variable {V W E : Type*} (G : Graph V E) (roots : Set V) (f : V → W)

theorem isRootedForest_of_map_tree (root_mem : roots ⊆ G.vertexSet) (nonempty : roots.Nonempty)
    (fibers : ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet,
      f u = f v ↔ u = v ∨ (u ∈ roots ∧ v ∈ roots))
    (tree : (G.map f).IsTree) : G.IsRootedForest roots := by
  have forest : G.IsAcyclic := tree.isAcyclic.of_mapAlong
    (G := G) (H := G.map f) f id (fun _ member => Set.mem_image_of_mem f member)
    (fun {_ _ _} link => link.map f) Function.injective_id
  have separated {r s : V} (hr : r ∈ roots) (hs : s ∈ roots)
      (reach : G.Reaches r s) : r = s := by
    exact reach.eq_of_map_eq f id (fun _ member => Set.mem_image_of_mem f member)
      (fun {_ _ _} link => link.map f) tree.isAcyclic Function.injective_id
      ((fibers r (root_mem hr) s (root_mem hs)).mpr (Or.inr ⟨hr, hs⟩))
  have fiber_reaches {u v : V} (hu : u ∈ G.vertexSet) (hv : v ∈ G.vertexSet)
      (equal : f u = f v) : (G.rootExtension roots).Reaches (some u) (some v) := by
    rcases (fibers u hu v hv).mp equal with rfl | ⟨ur, vr⟩
    · exact Reaches.refl (Or.inl hu)
    · exact (Reaches.of_isLink (G.rootExtension_spoke roots ⟨u, ur⟩).symm).trans
        (Reaches.of_isLink (G.rootExtension_spoke roots ⟨v, vr⟩))
  have lift {a b : W} {walk : List E} (actual : (G.map f).IsWalk a walk b) :
      ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, f u = a → f v = b →
        (G.rootExtension roots).Reaches (some u) (some v) := by
    induction actual with
    | nil member =>
      intro u hu v hv first last
      exact fiber_reaches hu hv (first.trans last.symm)
    | cons link _ ih =>
      intro u hu v hv first last
      obtain ⟨x, y, old, fx, fy⟩ := link
      have start : f u = f x := first.trans fx.symm
      exact (fiber_reaches hu old.left_mem start).trans
        ((Reaches.of_isLink (old.rootExtension roots)).trans
          (ih y old.right_mem v hv fy last))
  obtain ⟨root, root_member⟩ := nonempty
  have connected : (G.rootExtension roots).Connected := by
    have to_outside (v : Option V) (member : v ∈ (G.rootExtension roots).vertexSet) :
        (G.rootExtension roots).Reaches v none := by
      cases v with
      | none => exact Reaches.refl (by trivial)
      | some v =>
        have present : v ∈ G.vertexSet := member.elim id (fun h => root_mem h)
        obtain ⟨edges, walk⟩ := tree.connected.reaches
          (Set.mem_image_of_mem f present) (Set.mem_image_of_mem f (root_mem root_member))
        exact (lift walk v present root (root_mem root_member) rfl rfl).trans
          (Reaches.of_isLink (G.rootExtension_spoke roots ⟨root, root_member⟩).symm)
    exact ⟨⟨none, by trivial⟩,
      fun u hu v hv => (to_outside u hu).trans (to_outside v hv).symm⟩
  refine ⟨forest, ?_⟩
  intro v member
  obtain ⟨r, hr, reach⟩ := (G.rootExtension_connected_iff roots root_mem).mp connected v member
  exact ⟨r, ⟨hr, reach⟩, fun s hs => separated hs.1 hr (hs.2.symm.trans reach)⟩

end Graph
