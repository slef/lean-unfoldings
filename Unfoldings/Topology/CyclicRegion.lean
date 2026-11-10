module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Tactic.NormNum

/-! Exactly two changes of membership in a finite cyclic permutation give one entry and one exit. -/

@[expose] public section

namespace Unfoldings

variable {X : Type*} [Finite X]

/-- Orient two unordered region exits by conservation of the membership indicator. -/
theorem exists_oriented_two_exits (next : Equiv.Perm X) (inside : X → Prop)
    (a b : X) (different : a ≠ b)
    (changes : ∀ i, ((inside i ∧ ¬ inside (next i)) ∨
      (inside (next i) ∧ ¬ inside i)) ↔ i = a ∨ i = b) :
    ∃ enter leave : X, enter ≠ leave ∧ (¬ inside enter ∧ inside (next enter)) ∧
      (inside leave ∧ ¬ inside (next leave)) ∧
      ∀ i, i ≠ enter → i ≠ leave → (inside (next i) ↔ inside i) := by
  classical
  let := Fintype.ofFinite X
  let delta (i : X) : ℤ := (if inside (next i) then 1 else 0) - (if inside i then 1 else 0)
  have unchanged (i : X) (first : i ≠ a) (last : i ≠ b) :
      inside (next i) ↔ inside i := by
    have no_change : ¬ ((inside i ∧ ¬ inside (next i)) ∨
        (inside (next i) ∧ ¬ inside i)) := by
      rw [changes]
      exact fun alternatives => alternatives.elim first last
    constructor
    · intro future
      by_contra current
      exact no_change (Or.inr ⟨future, current⟩)
    · intro current
      by_contra future
      exact no_change (Or.inl ⟨current, future⟩)
  have zero : (∑ i, delta i) = 0 := by
    simp only [delta, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp next (fun i => if inside i then (1 : ℤ) else 0), sub_self]
  have point (i : X) : delta i =
      (if i = a then delta a else 0) + (if i = b then delta b else 0) := by
    by_cases first : i = a
    · subst i
      simp only [ite_true, ite_eq_right different, add_zero]
    · by_cases last : i = b
      · subst i
        simp only [ite_true, ite_eq_right different.symm, zero_add]
      · simp only [ite_eq_right first, ite_eq_right last, add_zero, delta, unchanged i first last,
          sub_self]
  have balance : delta a + delta b = 0 := by
    have total : (∑ i, delta i) = delta a + delta b := by
      calc
        _ = ∑ i : X, ((if i = a then delta a else 0) +
            (if i = b then delta b else 0)) := Finset.sum_congr rfl (fun i _ => point i)
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact total.symm.trans zero
  have at_a := (changes a).mpr (Or.inl rfl)
  have at_b := (changes b).mpr (Or.inr rfl)
  rcases at_a with leaves_a | enters_a <;> rcases at_b with leaves_b | enters_b
  · simp only [delta, ite_eq_left leaves_a.1, ite_eq_right leaves_a.2,
      ite_eq_left leaves_b.1, ite_eq_right leaves_b.2] at balance
    norm_num at balance
  · exact ⟨b, a, different.symm, ⟨enters_b.2, enters_b.1⟩, leaves_a,
      fun i first last => unchanged i last first⟩
  · exact ⟨a, b, different, ⟨enters_a.2, enters_a.1⟩, leaves_b, unchanged⟩
  · simp only [delta, ite_eq_left enters_a.1, ite_eq_right enters_a.2,
      ite_eq_left enters_b.1, ite_eq_right enters_b.2] at balance
    norm_num at balance

end Unfoldings
