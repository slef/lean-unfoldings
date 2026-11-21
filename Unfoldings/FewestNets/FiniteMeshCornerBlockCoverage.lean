module

public import Unfoldings.FewestNets.FiniteMeshPerimeterBlockSum

/-! Membership in some block of a covered finite key list. -/

@[expose] public section

namespace Unfoldings.FewestNets

theorem exists_mem_keyBlock {ι : Type*} {keys : List ι} {size n : ℕ} {a : ι}
    (covers : keys.length ≤ size * n) (mem : a ∈ keys) :
    ∃ i : Fin n, a ∈ (keys.drop (size * i.val)).take size := by
  rw [← flatten_keyBlocks_eq_of_length_le keys size n covers] at mem
  obtain ⟨block, blocks, content⟩ := List.mem_flatten.mp mem
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp blocks
  exact ⟨i, content⟩

end Unfoldings.FewestNets
