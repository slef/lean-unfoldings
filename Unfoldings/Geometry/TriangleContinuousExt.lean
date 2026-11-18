module

public import Unfoldings.Geometry.Triangle

/-! Continuous triangle maps are determined by the genuine two-dimensional interior. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem dense_interior_cells (T : Triangle) : Dense {x : T.Cell | x.val ∈ interior T.carrier} := by
  rw [dense_iff_closure_eq]
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have image : Subtype.val '' {x : T.Cell | x.val ∈ interior T.carrier} =
      interior T.carrier := by
    ext p
    constructor
    · rintro ⟨x, member, rfl⟩
      exact member
    · intro member
      exact ⟨⟨p, interior_subset member⟩, member, rfl⟩
  rw [image, T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
    T.compact_carrier.isClosed.closure_eq]
  exact Set.eq_univ_of_forall (fun x => x.property)

theorem continuous_ext_on_interior (T : Triangle) {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f g : T.Cell → Y) (first : Continuous f) (last : Continuous g)
    (same : ∀ x : T.Cell, x.val ∈ interior T.carrier → f x = g x) : f = g := by
  have all := closure_minimal (show {x : T.Cell | x.val ∈ interior T.carrier} ⊆
    {x | f x = g x} from same) (isClosed_eq first last)
  rw [T.dense_interior_cells.closure_eq] at all
  exact funext (fun x => all (Set.mem_univ x))

end Unfoldings.Triangle
