module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Nat.Find

/-! Local progress to the next strict record propagates to a first maximum. -/

@[expose] public section

namespace Unfoldings

theorem finite_record_increases_to_first_maximum {α β : Type*}
    [LinearOrder α] [Preorder β] {n : ℕ}
    (height : Fin n → α) (value : Fin n → β)
    (step : ∀ a b : Fin n, a < b → height a < height b →
      (∀ c : Fin n, a < c → c < b → height c ≤ height a) → value a ≤ value b)
    (i j : Fin n) (ordered : i ≤ j)
    (highest : ∀ c : Fin n, i ≤ c → c < j → height c < height j) : value i ≤ value j := by
  classical
  have core : ∀ gap : ℕ, ∀ a b : Fin n, b.val - a.val = gap → a ≤ b →
      (∀ c : Fin n, a ≤ c → c < b → height c < height b) → value a ≤ value b := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | h gap ih =>
      intro a b equation ordered highest
      by_cases same : a = b
      · rw [same]
      have before : a < b := lt_of_le_of_ne ordered same
      have candidates : ∃ k : ℕ, ∃ hk : k < n,
          a.val < k ∧ k ≤ b.val ∧ height a < height ⟨k, hk⟩ :=
        ⟨b.val, b.isLt, before, le_rfl, highest a le_rfl before⟩
      let k := Nat.find candidates
      obtain ⟨hk, after, before_end, rises⟩ := Nat.find_spec candidates
      let next : Fin n := ⟨k, hk⟩
      change a.val < k at after
      change k ≤ b.val at before_end
      have after_fin : a < next := after
      have before_end_fin : next ≤ b := before_end
      have prior : ∀ c : Fin n, a < c → c < next → height c ≤ height a := by
        intro c after_a before_next
        by_contra higher
        have candidate : ∃ hc : c.val < n,
            a.val < c.val ∧ c.val ≤ b.val ∧ height a < height ⟨c.val, hc⟩ :=
          ⟨c.isLt, after_a, before_next.le.trans before_end_fin, lt_of_not_ge higher⟩
        have minimal := Nat.find_min' candidates candidate
        change k ≤ c.val at minimal
        have strictly_before : c.val < k := before_next
        omega
      have advance := step a next after_fin rises prior
      have smaller : b.val - next.val < gap := by
        change b.val - k < gap
        omega
      have finish := ih (b.val - next.val) smaller next b rfl before_end_fin
        (fun c after_next before_b => highest c (after_fin.le.trans after_next) before_b)
      exact advance.trans finish
  exact core (j.val - i.val) i j rfl ordered highest

/-- The same record argument, with indices processed from right to left. -/
theorem finite_record_increases_to_last_maximum {α β : Type*}
    [LinearOrder α] [Preorder β] {n : ℕ}
    (height : Fin n → α) (value : Fin n → β)
    (step : ∀ a b : Fin n, b < a → height a < height b →
      (∀ c : Fin n, b < c → c < a → height c ≤ height a) → value a ≤ value b)
    (i j : Fin n) (ordered : j ≤ i)
    (highest : ∀ c : Fin n, j < c → c ≤ i → height c < height j) : value i ≤ value j := by
  have reversed_step : ∀ a b : Fin n, a < b → height a.rev < height b.rev →
      (∀ c : Fin n, a < c → c < b → height c.rev ≤ height a.rev) →
        value a.rev ≤ value b.rev := by
    intro a b before rises between
    apply step a.rev b.rev (Fin.rev_lt_rev.mpr before) rises
    intro c after_b before_a
    have first : a < c.rev := by
      simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr before_a
    have last : c.rev < b := by
      simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr after_b
    simpa only [Fin.rev_rev] using between c.rev first last
  have result := finite_record_increases_to_first_maximum
    (fun k => height k.rev) (fun k => value k.rev) reversed_step i.rev j.rev
    (Fin.rev_le_rev.mpr ordered) (fun c after_i before_j => by
      rw [Fin.rev_rev]
      apply highest c.rev
      · simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr before_j
      · simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr after_i)
  simpa only [Fin.rev_rev] using result

end Unfoldings
