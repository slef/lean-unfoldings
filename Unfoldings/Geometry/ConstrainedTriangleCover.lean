module

public import Unfoldings.Geometry.AffineArrangement
public import Unfoldings.Geometry.Barycentric

/-! Line-aligned cells cover a whole coarse triangle using cells contained in that triangle. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem covered_by_contained_cells {I : Type*} [Finite I] (T : Triangle) (cells : I → Triangle)
    (cover : T.carrier ⊆ ⋃ i, (cells i).carrier)
    (signs : I → Fin 3 → Bool)
    (side : ∀ i p, p ∈ (cells i).carrier → ∀ k,
      0 ≤ AffineArrangement.signed (T.coord k) (signs i k) p) :
    ∀ p ∈ T.carrier, ∃ i, (cells i).carrier ⊆ T.carrier ∧ p ∈ (cells i).carrier := by
  let good := {i : I // (cells i).carrier ⊆ T.carrier}
  have closed : IsClosed (⋃ i : good, (cells i.val).carrier) :=
    isClosed_iUnion_of_finite (fun i => (cells i.val).compact_carrier.isClosed)
  have inside : interior T.carrier ⊆ ⋃ i : good, (cells i.val).carrier := by
    intro p interior_point
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp (cover (interior_subset interior_point))
    have contained : (cells i).carrier ⊆ T.carrier := by
      intro q q_member
      rw [T.carrier_eq_nonneg_coord]
      intro k
      cases value : signs i k
      · have positive := T.interior_eq_pos_coord.le interior_point k
        have bound := side i p member k
        simp only [AffineArrangement.signed_apply, value, Bool.false_eq_true, ↓reduceIte] at bound
        linarith
      · have bound := side i q q_member k
        simpa only [AffineArrangement.signed_apply, value, ↓reduceIte] using bound
    exact Set.mem_iUnion.mpr ⟨⟨i, contained⟩, member⟩
  have all := closure_minimal inside closed
  rw [T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
    T.compact_carrier.isClosed.closure_eq] at all
  intro p member
  obtain ⟨i, covered⟩ := Set.mem_iUnion.mp (all member)
  exact ⟨i.val, i.property, covered⟩

end Unfoldings.Triangle
