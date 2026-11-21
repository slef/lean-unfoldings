module

public import Unfoldings.FewestNets.IcosahedronLabeledStars

/-! Every actual mesh site has one of the canonical face, seam, or pentagon stars. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar

/-- The canonical orbit representatives cover all actual cyclic Voronoi stars. -/
theorem meshSite_has_realizedModel {q : ℕ} (hq : 0 < q) (a : meshSites q) :
    (∃ i j, (i, j) ∈ faceMeshKeys q ∧ Nonempty (MeshStarRealization a (face q i j))) ∨
      (∃ i, i ∈ seamMeshKeys q ∧ Nonempty (MeshStarRealization a (seam q i))) ∨
      Nonempty (MeshStarRealization a (pentagon q)) := by
  obtain ⟨label, _, realized⟩ := exists_perimeterIndex_realizing hq a
  rcases label with f | e | v
  · let key := (faceMeshKeys q).get f.2.1
    exact .inl ⟨key.1, key.2, List.get_mem _ _, realized⟩
  · let key := (seamMeshKeys q).get e.2.1
    exact .inr (.inl ⟨key, List.get_mem _ _, realized⟩)
  · exact .inr (.inr realized)

end Unfoldings.FewestNets.Icosahedron
