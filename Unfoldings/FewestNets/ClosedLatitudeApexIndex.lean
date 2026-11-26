module

public import Unfoldings.FewestNets.CheckedLatitudeSweep

/-! Compute an opposing index in constant time using the exact tie rule. -/

@[expose] public section

namespace Unfoldings.FewestNets.LatitudeRings

def midpointPredecessors (m n i : ℕ) (includeTie : Bool) : ℕ :=
  ((2 * i + 1) * n + if includeTie then m else m - 1) / (2 * m)

private theorem midpointPredecessors_le {m n : ℕ} (i : Fin m) (includeTie : Bool) :
    midpointPredecessors m n i includeTie ≤ n := by
  have mp := Nat.zero_lt_of_lt i.isLt
  have u : 2 * i.val + 1 ≤ 2 * m := by omega
  have h := Nat.mul_le_mul_right n u
  have b : (if includeTie then m else m - 1) < 2 * m := by split <;> omega
  unfold midpointPredecessors
  apply Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr ?_)
  rw [show n.succ * (2 * m) = (2 * m) * n + 2 * m by rw [Nat.succ_mul, mul_comm n]]
  omega

private theorem lt_midpointPredecessors {m n : ℕ} (i : Fin m) (j : Fin n) (includeTie : Bool) :
    j.val < midpointPredecessors m n i includeTie ↔
      (if includeTie then (2 * j.val + 1) * m ≤ (2 * i.val + 1) * n
        else (2 * j.val + 1) * m < (2 * i.val + 1) * n) := by
  have mp := Nat.zero_lt_of_lt i.isLt
  unfold midpointPredecessors
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le (by omega : 0 < 2 * m)]
  rw [show (j.val + 1) * (2 * m) = (2 * j.val + 1) * m + m by ring]
  cases includeTie <;> simp <;> omega

private theorem card_lt_fin {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter fun j : Fin n => j.val < k).card = k := by
  refine Eq.trans ?_ (Finset.card_range k)
  refine Finset.card_bij (fun i _ => i.val) ?_ (fun i _ j _ eq => Fin.ext eq) ?_
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro j hj
    have jt := Finset.mem_range.mp hj
    exact ⟨⟨j, jt.trans_le hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, jt⟩, rfl⟩

private theorem rationalMidpointKey_inr_lt_inl {m n : ℕ} (i : Fin m) (j : Fin n) :
    rationalMidpointKey (.inr j : Fin m ⊕ Fin n) < rationalMidpointKey (.inl i : Fin m ⊕ Fin n) ↔
      (2 * j.val + 1) * m ≤ (2 * i.val + 1) * n := by
  have mp : (0 : ℚ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have np : (0 : ℚ) < n := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  rw [Prod.Lex.lt_iff]
  change (((2 * j.val + 1 : ℕ) : ℚ) / n < ((2 * i.val + 1 : ℕ) : ℚ) / m ∨
    ((2 * j.val + 1 : ℕ) : ℚ) / n = ((2 * i.val + 1 : ℕ) : ℚ) / m ∧ 0 < (1 : ℕ)) ↔ _
  rw [and_iff_left Nat.zero_lt_one, ← le_iff_lt_or_eq, div_le_div_iff₀ np mp]
  exact_mod_cast Iff.rfl

private theorem rationalMidpointKey_inl_lt_inr {m n : ℕ} (i : Fin m) (j : Fin n) :
    rationalMidpointKey (.inl i : Fin m ⊕ Fin n) < rationalMidpointKey (.inr j : Fin m ⊕ Fin n) ↔
      (2 * i.val + 1) * n < (2 * j.val + 1) * m := by
  have mp : (0 : ℚ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have np : (0 : ℚ) < n := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  rw [Prod.Lex.lt_iff]
  change (((2 * i.val + 1 : ℕ) : ℚ) / m < ((2 * j.val + 1 : ℕ) : ℚ) / n ∨
    ((2 * i.val + 1 : ℕ) : ℚ) / m = ((2 * j.val + 1 : ℕ) : ℚ) / n ∧ (1 : ℕ) < 0) ↔ _
  simp only [Nat.not_lt_zero, and_false, or_false, div_lt_div_iff₀ mp np]
  exact_mod_cast Iff.rfl

/-- Index of the opposing point at a lower-row midpoint. -/
theorem oppositeIndex_inl_formula {m n : ℕ} (i : Fin m) :
    oppositeIndex (.inl i : Fin m ⊕ Fin n) = midpointPredecessors m n i true := by
  rw [oppositeIndex, ← card_lt_fin (midpointPredecessors_le (n := n) i true)]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rationalMidpointKey_inr_lt_inl,
    lt_midpointPredecessors, ite_true]

/-- Index of the opposing point at an upper-row midpoint. -/
theorem oppositeIndex_inr_formula {m n : ℕ} (j : Fin n) :
    oppositeIndex (.inr j : Fin m ⊕ Fin n) = midpointPredecessors n m j false := by
  rw [oppositeIndex, ← card_lt_fin (midpointPredecessors_le (n := m) j false)]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rationalMidpointKey_inl_lt_inr,
    lt_midpointPredecessors, Bool.false_eq_true, ite_false]

end Unfoldings.FewestNets.LatitudeRings
