module

public import Unfoldings.Topology.ParentFrontierNeighbor

/-! A first-contact branch of length at most one adds only its original source. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.ParentFrontier

variable {V : Type*} [Finite V] {P : AscendingParents V} (S : P.ParentFrontier)

/-- Includes a repeated source: a zero-length step leaves the processed set unchanged. -/
theorem process_processed_eq_insert_of_le_one {vertex : V}
    (single : S.contactTime vertex ≤ 1) :
    (S.process vertex).processed = insert vertex S.processed := by
  ext w
  constructor
  · rintro (old | ⟨i, same⟩)
    · exact Or.inr old
    · have zero : i.val = 0 := by omega
      exact Or.inl (by simpa only [zero, Function.iterate_zero_apply] using same.symm)
  · rintro (same | old)
    · rw [same]
      exact (S.mem_process_iff vertex vertex).mpr (Or.inr (P.ancestor_refl vertex))
    · exact Or.inl old

end Unfoldings.AscendingParents.ParentFrontier
