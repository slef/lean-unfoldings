module

public import Unfoldings.Geometry.StraightGapJoinBank

/-! Closed finite and infinite bank parameters embed in their single signed join domain. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings

/-- Transport a finite edge parameter to the signed join domain. -/
def bankJoinFiniteTime (t : unitInterval) : BankJoinTime :=
  ⟨t.val - 1, by have := t.property.1; change -1 ≤ t.val - 1; linarith⟩

/-- Transport an original tail parameter to the signed join domain. -/
def bankJoinTailTime (t : ℝ≥0) : BankJoinTime :=
  ⟨t.val, by change -1 ≤ t.val; linarith [t.property]⟩

/-- Every actual finite point is still named by its original parameter before the join. -/
theorem joinedBank_finite {X : Type*} (finite : unitInterval → X) (tail : ℝ≥0 → X)
    (at_join : finite 1 = tail 0) (t : unitInterval) :
    joinedBank finite tail (bankJoinFiniteTime t) = finite t := by
  by_cases eq : t = 1
  · subst t
    have zero : bankJoinFiniteTime 1 = ⟨0, by norm_num⟩ := by
      apply Subtype.ext
      change (1 : ℝ) - 1 = 0
      exact sub_self _
    rw [zero, joinedBank_zero, ← at_join]
  · have near : (bankJoinFiniteTime t).val < 0 := sub_neg.mpr
      (lt_of_le_of_ne (show t.val ≤ (1 : ℝ) from t.property.2)
        (fun eq' => eq (Subtype.ext eq')))
    rw [joinedBank, dite_eq_left near]
    apply congrArg finite
    apply Subtype.ext
    change 1 + (t.val - 1) = t.val
    ring

/-- Every actual tail point is still named by its original unbounded parameter. -/
theorem joinedBank_tail {X : Type*} (finite : unitInterval → X) (tail : ℝ≥0 → X)
    (t : ℝ≥0) :
    joinedBank finite tail (bankJoinTailTime t) = tail t := by
  rw [joinedBank, dite_eq_right (show ¬ (bankJoinTailTime t).val < 0 from not_lt_of_ge t.property)]
  rfl

/-- Joining the two original closed banks keeps precisely the union of their ranges. -/
theorem joinedBank_range {X : Type*} (finite : unitInterval → X) (tail : ℝ≥0 → X)
    (at_join : finite 1 = tail 0) :
    Set.range (joinedBank finite tail) = Set.range finite ∪ Set.range tail := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    unfold joinedBank
    split
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact ⟨bankJoinFiniteTime s, joinedBank_finite finite tail at_join s⟩
    · exact ⟨bankJoinTailTime s, joinedBank_tail finite tail s⟩

end Unfoldings
