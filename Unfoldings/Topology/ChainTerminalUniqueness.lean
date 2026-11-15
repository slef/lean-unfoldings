module

public import Unfoldings.Topology.PairedInvolutions
public import Mathlib.Logic.Function.Iterate

/-! In a paired-interval system, actual initial and terminal germs determine the entire chain. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

variable {X : Type*} {P : PairedInvolutions.System X} {n m : ℕ} (c : P.Chain n) (d : P.Chain m)

/-- Every point of the ordered chain follows the actual deterministic endpoint pairings. -/
theorem point_eq_iterate (i : Fin (n + 1)) :
    c.point i = (P.mate ∘ P.turn)^[i.val] c.first := by
  induction i using Fin.induction with
  | zero => rfl
  | succ k ih =>
    rw [← c.next k]
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    rw [Function.iterate_succ_apply']
    exact congrArg (P.mate ∘ P.turn) ih

/-- Equal named terminal germs determine both the number of original intervals and every
ordered interval point. The chains need not have been supplied with the same length. -/
theorem eq_length_and_points_of_terminals (initial : c.first = d.first)
    (terminal : P.turn c.last = P.turn d.last) :
    n = m ∧ ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), i.val = j.val → c.point i = d.point j := by
  have points (i : Fin (n + 1)) (j : Fin (m + 1)) (same : i.val = j.val) :
      c.point i = d.point j := by
    rw [c.point_eq_iterate, d.point_eq_iterate, same, initial]
  have last : c.last = d.last := P.turn_involutive.injective terminal
  have length : n = m := by
    rcases le_total n m with before | after
    · have at_n := points (Fin.last n) ⟨n, by omega⟩ rfl
      have indices := d.injective (at_n.symm.trans last)
      exact congrArg Fin.val indices
    · have at_m := points ⟨m, by omega⟩ (Fin.last m) rfl
      have indices := c.injective (at_m.trans last.symm)
      exact (congrArg Fin.val indices).symm
  exact ⟨length, points⟩

/-- The two descriptions visit exactly the same original endpoints, in the same orientation. -/
theorem visited_iff_of_terminals (initial : c.first = d.first)
    (terminal : P.turn c.last = P.turn d.last) (x : X) : c.Visited x ↔ d.Visited x := by
  obtain ⟨length, points⟩ := c.eq_length_and_points_of_terminals d initial terminal
  constructor
  · rintro ⟨i, same | same⟩
    all_goals
      let j : Fin (m + 1) := ⟨i.val, by rw [← length]; exact i.isLt⟩
      have at_point := points i j rfl
    · exact ⟨j, Or.inl (same.trans at_point)⟩
    · exact ⟨j, Or.inr (same.trans (congrArg P.turn at_point))⟩
  · rintro ⟨j, same | same⟩
    all_goals
      let i : Fin (n + 1) := ⟨j.val, by rw [length]; exact j.isLt⟩
      have at_point := points i j rfl
    · exact ⟨i, Or.inl (same.trans at_point.symm)⟩
    · exact ⟨i, Or.inr (same.trans (congrArg P.turn at_point.symm))⟩

end PairedInvolutions.System.Chain
