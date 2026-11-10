module

public import Unfoldings.Geometry.AngularCrofton
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Elementary counts of strict sign changes around finite cycles. -/

@[expose] public section

namespace Unfoldings

open scoped ENNReal

variable {I : Type*} [Fintype I]

/-- The strict crossing sum is the cardinality of the actual sign-changing edges. -/
theorem angularCrossings_eq_card (ray : I → Space) (next : I → I) (n : Space) :
    angularCrossings ray next n =
      (Fintype.card {i : I // inner ℝ n (ray i) * inner ℝ n (ray (next i)) < 0} : ℝ≥0∞) := by
  classical
  simp only [angularCrossings, Set.indicator_apply, spatialSignChange, Set.mem_ofPred_eq]
  rw [Finset.sum_boole]
  simp only [Fintype.card_subtype]

/-- A permutation has equally many transitions in either direction across a sign partition. -/
theorem card_sign_changes_even (value : I → ℝ) (next : Equiv.Perm I)
    (nonzero : ∀ i, value i ≠ 0) :
    ∃ k : ℕ, Fintype.card {i : I // value i * value (next i) < 0} = 2 * k := by
  classical
  let A := Finset.univ.filter (fun i => 0 < value i)
  let B := Finset.univ.filter (fun i => 0 < value (next i))
  have cardinality : A.card = B.card := by
    dsimp [A, B]
    simpa only [Finset.sum_boole, Nat.cast_id] using
      (Equiv.sum_comp next (fun i => if 0 < value i then (1 : ℕ) else 0)).symm
  have changes : Finset.univ.filter (fun i => value i * value (next i) < 0) =
      (A \ B) ∪ (B \ A) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff, A, B]
    rcases lt_or_gt_of_ne (nonzero i) with hi | hi <;>
      rcases lt_or_gt_of_ne (nonzero (next i)) with hj | hj <;>
      simp [hi, hj, hi.not_gt, hj.not_gt, mul_neg_iff]
  refine ⟨(A \ B).card, ?_⟩
  rw [Fintype.card_subtype, changes, Finset.card_union_of_disjoint disjoint_sdiff_sdiff,
    ← Finset.card_sdiff_comm cardinality]
  omega

/-- With a bound of two, every nonconstant genuine cyclic sign sequence crosses exactly twice. -/
theorem card_cyclic_sign_changes_eq_two {m : ℕ} (value : Fin (m + 1) → ℝ)
    (nonzero : ∀ i, value i ≠ 0)
    (positive : ∃ i, 0 < value i) (negative : ∃ i, value i < 0)
    (bound : Fintype.card {i : Fin (m + 1) // value i * value (finRotate (m + 1) i) < 0} ≤ 2) :
    Fintype.card {i : Fin (m + 1) // value i * value (finRotate (m + 1) i) < 0} = 2 := by
  have exists_change : ∃ i, value i * value (finRotate (m + 1) i) < 0 := by
    by_contra none
    push Not at none
    have adjacent (i : Fin (m + 1)) : (0 < value i) ↔ 0 < value (finRotate (m + 1) i) := by
      rcases lt_or_gt_of_ne (nonzero i) with hi | hi <;>
        rcases lt_or_gt_of_ne (nonzero (finRotate (m + 1) i)) with hj | hj
      · exact iff_of_false hi.not_gt hj.not_gt
      · exact (not_lt_of_ge (none i) (mul_neg_of_neg_of_pos hi hj)).elim
      · exact (not_lt_of_ge (none i) (mul_neg_of_pos_of_neg hi hj)).elim
      · exact iff_of_true hi hj
    have constant (i : Fin (m + 1)) : (0 < value i) ↔ 0 < value 0 := by
      refine Fin.induction Iff.rfl (fun k previous => ?_) i
      have step := adjacent k.castSucc
      rw [show finRotate (m + 1) k.castSucc = k.succ from finRotate_of_lt k.isLt] at step
      exact step.symm.trans previous
    obtain ⟨i, hi⟩ := positive
    obtain ⟨j, hj⟩ := negative
    exact hj.not_gt ((constant j).mpr ((constant i).mp hi))
  have count_positive : 0 < Fintype.card
      {i : Fin (m + 1) // value i * value (finRotate (m + 1) i) < 0} := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i, hi⟩ := exists_change
    exact ⟨⟨i, hi⟩⟩
  obtain ⟨k, hk⟩ := card_sign_changes_even value (finRotate (m + 1)) nonzero
  omega

end Unfoldings
