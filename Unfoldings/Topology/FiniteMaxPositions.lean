module

public import Unfoldings.Topology.FiniteRecordProgress
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Fin

/-! Finite maxima and threshold crossings have strict bounds outside their extreme indices. -/

@[expose] public section

namespace Unfoldings

theorem exists_first_ge_position {α : Type*} [LinearOrder α] {n : ℕ}
    (height : Fin (n + 1) → α) (level : α) (pivot : Fin (n + 1))
    (reaches : level ≤ height pivot) :
    ∃ j : Fin (n + 1), j ≤ pivot ∧ level ≤ height j ∧
      ∀ k : Fin (n + 1), k < j → height k < level := by
  classical
  have candidates : ∃ j : ℕ, ∃ hj : j < n + 1,
      j ≤ pivot.val ∧ level ≤ height ⟨j, hj⟩ := ⟨pivot.val, pivot.isLt, le_rfl, reaches⟩
  let j := Nat.find candidates
  obtain ⟨hj, before, above⟩ := Nat.find_spec candidates
  refine ⟨⟨j, hj⟩, before, above, ?_⟩
  intro k earlier
  by_contra not_below
  have candidate : ∃ hk : k.val < n + 1,
      k.val ≤ pivot.val ∧ level ≤ height ⟨k.val, hk⟩ :=
    ⟨k.isLt, (show k.val < j from earlier).le.trans before, not_lt.mp not_below⟩
  have minimal := Nat.find_min' candidates candidate
  change j ≤ k.val at minimal
  have before_j : k.val < j := earlier
  omega

theorem exists_last_ge_position {α : Type*} [LinearOrder α] {n : ℕ}
    (height : Fin (n + 1) → α) (level : α) (pivot : Fin (n + 1))
    (reaches : level ≤ height pivot) :
    ∃ j : Fin (n + 1), pivot ≤ j ∧ level ≤ height j ∧
      ∀ k : Fin (n + 1), j < k → height k < level := by
  obtain ⟨j, before, above, earlier⟩ := exists_first_ge_position (fun k => height k.rev)
    level pivot.rev (by simpa only [Fin.rev_rev] using reaches)
  refine ⟨j.rev, ?_, above, ?_⟩
  · simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr before
  · intro k later
    have before_j : k.rev < j := by
      simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr later
    simpa only [Fin.rev_rev] using earlier k.rev before_j

theorem exists_first_max_position {α : Type*} [LinearOrder α] {n : ℕ}
    (height : Fin (n + 1) → α) :
    ∃ first : Fin (n + 1), (∀ k, height k ≤ height first) ∧
      ∀ k : Fin (n + 1), k < first → height k < height first := by
  obtain ⟨pivot, maximum⟩ := Finite.exists_max height
  obtain ⟨first, _, above, earlier⟩ := exists_first_ge_position height (height pivot) pivot le_rfl
  have same : height first = height pivot := le_antisymm (maximum first) above
  refine ⟨first, fun k => (maximum k).trans_eq same.symm, ?_⟩
  intro k before
  exact (earlier k before).trans_eq same.symm

theorem exists_first_last_max_positions {α : Type*} [LinearOrder α] {n : ℕ}
    (height : Fin (n + 1) → α) :
    ∃ first last : Fin (n + 1), first ≤ last ∧ height first = height last ∧
      (∀ k, height k ≤ height first) ∧
      (∀ k : Fin (n + 1), k < first → height k < height first) ∧
      ∀ k : Fin (n + 1), last < k → height k < height last := by
  obtain ⟨first, first_maximum, first_strict⟩ := exists_first_max_position height
  obtain ⟨backward, last_maximum, last_strict⟩ :=
    exists_first_max_position (fun k => height k.rev)
  let last := backward.rev
  have maximum_last (k : Fin (n + 1)) : height k ≤ height last := by
    simpa only [Fin.rev_rev] using last_maximum k.rev
  have ordered : first ≤ last := by
    by_contra reversed
    exact (first_strict last (lt_of_not_ge reversed)).not_ge (maximum_last first)
  have same := le_antisymm (maximum_last first) (first_maximum last)
  refine ⟨first, last, ordered, same, first_maximum, first_strict, ?_⟩
  intro k after
  have before : k.rev < backward := by
    simpa only [last, Fin.rev_rev] using Fin.rev_lt_rev.mpr after
  simpa only [Fin.rev_rev] using last_strict k.rev before

end Unfoldings
