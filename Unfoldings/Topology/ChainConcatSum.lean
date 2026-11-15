module

public import Unfoldings.Topology.ChainConcatRange
public import Mathlib.Algebra.BigOperators.Fin

/-! Exact additive weights of concatenated original interval chains. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n m : ℕ} (c : P.Chain n) (d : P.Chain m)
  (separated : ∀ i j, c.point i ≠ d.point j ∧ c.point i ≠ P.turn (d.point j))
  (joined : P.mate (P.turn c.last) = d.first)

/-- Every original interval weight is counted once, in the actual concatenation. -/
theorem sum_concat {M : Type*} [AddCommMonoid M] (weight : X → M) :
    (∑ k, weight ((c.concat d separated joined).point k)) =
      (∑ i, weight (c.point i)) + ∑ j, weight (d.point j) := by
  let indices : Fin ((n + 1) + (m + 1)) ≃ Fin (n + m + 1 + 1) := finCongr (by omega)
  have sum := Equiv.sum_comp indices (fun k => weight ((c.concat d separated joined).point k))
  rw [Fin.sum_univ_add] at sum
  have left (i : Fin (n + 1)) :
      weight ((c.concat d separated joined).point (indices (Fin.castAdd (m + 1) i))) =
        weight (c.point i) := by
    change weight ((c.concat d separated joined).point ⟨i.val, by omega⟩) = _
    rw [c.concat_point_left]
  have right (j : Fin (m + 1)) :
      weight ((c.concat d separated joined).point (indices (Fin.natAdd (n + 1) j))) =
        weight (d.point j) := by
    change weight ((c.concat d separated joined).point ⟨n + 1 + j.val, by omega⟩) = _
    rw [c.concat_point_right]
  simpa only [left, right] using sum.symm

/-- Concatenation visits precisely the two original bank families in either orientation. -/
theorem concat_visited_iff (x : X) :
    (c.concat d separated joined).Visited x ↔ c.Visited x ∨ d.Visited x := by
  constructor
  · rintro ⟨k, same | same⟩
    all_goals
      obtain (⟨i, at_i⟩ | ⟨j, at_j⟩) :=
        (c.concat_point_range_iff d separated joined _).mp ⟨k, rfl⟩
    · exact Or.inl ⟨i, Or.inl (same.trans at_i.symm)⟩
    · exact Or.inr ⟨j, Or.inl (same.trans at_j.symm)⟩
    · exact Or.inl ⟨i, Or.inr (same.trans (congrArg P.turn at_i.symm))⟩
    · exact Or.inr ⟨j, Or.inr (same.trans (congrArg P.turn at_j.symm))⟩
  · rintro (⟨i, same | same⟩ | ⟨j, same | same⟩)
    · exact ⟨⟨i.val, by omega⟩,
        Or.inl (same.trans (c.concat_point_left d separated joined i).symm)⟩
    · exact ⟨⟨i.val, by omega⟩,
        Or.inr (same.trans (congrArg P.turn (c.concat_point_left d separated joined i).symm))⟩
    · exact ⟨⟨n + 1 + j.val, by have bound := j.isLt; omega⟩,
        Or.inl (same.trans (c.concat_point_right d separated joined j).symm)⟩
    · exact ⟨⟨n + 1 + j.val, by have bound := j.isLt; omega⟩,
        Or.inr (same.trans (congrArg P.turn (c.concat_point_right d separated joined j).symm))⟩

end PairedInvolutions.System.Chain
