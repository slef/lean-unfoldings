module

public import Unfoldings.Topology.PairedInvolutions

/-! Concatenate actual paired-involution chains while retaining every original interval label. -/

@[expose] public section

noncomputable section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n m : ℕ} (c : P.Chain n) (d : P.Chain m)

/-- The point sequence in the original order of two successive labeled blocks. -/
def concatenatedPoint (i : Fin (n + m + 2)) : X :=
  if before : i.val < n + 1 then c.point ⟨i.val, before⟩
  else d.point ⟨i.val - (n + 1), by have bound := i.isLt; omega⟩

/-- Join disjoint labeled interval chains at their actual next endpoint. The separation
condition excludes repeating a bank in either orientation. -/
def concat (separated : ∀ i j, c.point i ≠ d.point j ∧ c.point i ≠ P.turn (d.point j))
    (joined : P.mate (P.turn c.last) = d.first) : P.Chain (n + m + 1) where
  point := concatenatedPoint c d
  injective := by
    intro x y same
    dsimp only [concatenatedPoint] at same
    by_cases hx : x.val < n + 1
    · by_cases hy : y.val < n + 1
      · rw [dite_eq_left hx, dite_eq_left hy] at same
        exact Fin.ext (congrArg (fun i : Fin (n + 1) => i.val) (c.injective same))
      · rw [dite_eq_left hx, dite_eq_right hy] at same
        exact ((separated _ _).1 same).elim
    · by_cases hy : y.val < n + 1
      · rw [dite_eq_right hx, dite_eq_left hy] at same
        exact ((separated _ _).1 same.symm).elim
      · rw [dite_eq_right hx, dite_eq_right hy] at same
        have values := congrArg Fin.val (d.injective same)
        apply Fin.ext
        dsimp only at values
        omega
  disjoint := by
    intro x y same
    dsimp only [concatenatedPoint] at same
    by_cases hx : x.val < n + 1
    · by_cases hy : y.val < n + 1
      · rw [dite_eq_left hx, dite_eq_left hy] at same
        exact c.disjoint _ _ same
      · rw [dite_eq_left hx, dite_eq_right hy] at same
        exact (separated _ _).2 same
    · by_cases hy : y.val < n + 1
      · rw [dite_eq_right hx, dite_eq_left hy] at same
        have reversed := congrArg P.turn same
        rw [P.turn_involutive] at reversed
        exact (separated _ _).2 reversed.symm
      · rw [dite_eq_right hx, dite_eq_right hy] at same
        exact d.disjoint _ _ same
  next := by
    intro k
    dsimp only [concatenatedPoint]
    by_cases before : k.val < n
    · rw [dite_eq_left (by change k.val < n + 1; omega),
        dite_eq_left (by change k.val + 1 < n + 1; omega)]
      exact c.next ⟨k.val, before⟩
    · by_cases at_join : k.val = n
      · rw [dite_eq_left (by change k.val < n + 1; omega),
          dite_eq_right (by change ¬ k.val + 1 < n + 1; omega)]
        simpa only [first, last, at_join, Fin.val_castSucc, Fin.val_succ, Nat.sub_self]
          using! joined
      · rw [dite_eq_right (by change ¬ k.val < n + 1; omega),
          dite_eq_right (by change ¬ k.val + 1 < n + 1; omega)]
        let j : Fin m := ⟨k.val - (n + 1), by have bound := k.isLt; omega⟩
        exact (d.next j).trans (congrArg d.point (Fin.ext (by
          dsimp [j]
          omega)))

variable (separated : ∀ i j, c.point i ≠ d.point j ∧ c.point i ≠ P.turn (d.point j))
  (joined : P.mate (P.turn c.last) = d.first)

@[simp] theorem concat_first : (c.concat d separated joined).first = c.first := by
  change concatenatedPoint c d 0 = c.first
  rw [concatenatedPoint, dite_eq_left (by change 0 < n + 1; omega)]
  rfl

@[simp] theorem concat_last : (c.concat d separated joined).last = d.last := by
  change concatenatedPoint c d (Fin.last (n + m + 1)) = d.last
  rw [concatenatedPoint, dite_eq_right (by change ¬ n + m + 1 < n + 1; omega)]
  apply congrArg d.point
  apply Fin.ext
  dsimp only [last, Fin.val_last]
  omega

/-- Every original interval in the first chain keeps its actual label. -/
theorem concat_point_left (i : Fin (n + 1)) :
    (c.concat d separated joined).point ⟨i.val, by have bound := i.isLt; omega⟩ = c.point i := by
  change concatenatedPoint c d _ = _
  rw [concatenatedPoint, dite_eq_left i.isLt]

/-- Every original interval in the second chain occurs immediately after the first block. -/
theorem concat_point_right (j : Fin (m + 1)) :
    (c.concat d separated joined).point
        ⟨n + 1 + j.val, by have bound := j.isLt; omega⟩ = d.point j := by
  change concatenatedPoint c d _ = _
  rw [concatenatedPoint, dite_eq_right (by change ¬ n + 1 + j.val < n + 1; omega)]
  apply congrArg d.point
  apply Fin.ext
  dsimp only
  omega

end PairedInvolutions.System.Chain
