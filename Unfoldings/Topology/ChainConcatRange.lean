module

public import Unfoldings.Topology.ChainConcatenation

/-! Exact oriented interval coverage of concatenated actual chains. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n m : ℕ} (c : P.Chain n) (d : P.Chain m)
  (separated : ∀ i j, c.point i ≠ d.point j ∧ c.point i ≠ P.turn (d.point j))
  (joined : P.mate (P.turn c.last) = d.first)

/-- Concatenation preserves exactly the original directed labels, without adding reversals. -/
theorem concat_point_range_iff (x : X) :
    (∃ i, (c.concat d separated joined).point i = x) ↔
      (∃ i, c.point i = x) ∨ (∃ j, d.point j = x) := by
  constructor
  · rintro ⟨i, equal⟩
    change concatenatedPoint c d i = x at equal
    by_cases before : i.val < n + 1
    · rw [concatenatedPoint, dite_eq_left before] at equal
      exact Or.inl ⟨_, equal⟩
    · rw [concatenatedPoint, dite_eq_right before] at equal
      exact Or.inr ⟨_, equal⟩
  · rintro (⟨i, equal⟩ | ⟨j, equal⟩)
    · exact ⟨⟨i.val, by have bound := i.isLt; omega⟩,
        (c.concat_point_left d separated joined i).trans equal⟩
    · exact ⟨⟨n + 1 + j.val, by have bound := j.isLt; omega⟩,
        (c.concat_point_right d separated joined j).trans equal⟩

end PairedInvolutions.System.Chain
