module

public import Unfoldings.Geometry.WeightedHeadingBudget
public import Mathlib.Data.Finset.Max

/-! Chain local polar-window comparisons without assuming a uniform global heading cone. -/

@[expose] public section

namespace Unfoldings

variable {n : ℕ}

/-- Polar variation strictly between the two compared links; both terminal links may be trimmed. -/
def interiorVariation (variation : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => i < k ∧ k < j), variation k

/-- Charge a completed window through its final link, leaving the next window disjoint. -/
def throughVariation (variation : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => i < k ∧ k ≤ j), variation k

/-- Completed windows consume exactly their difference of future-variation budgets. -/
theorem throughVariation_eq_future_sub (variation : Fin n → ℝ) {i j : Fin n} (ordered : i ≤ j) :
    throughVariation variation i j = futureVariation variation i - futureVariation variation j := by
  classical
  simp only [throughVariation, futureVariation, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases first : i < k <;> by_cases last : j < k
  · simp only [first, last, not_le_of_gt last, and_false, ite_false, ite_true, sub_self]
  · simp only [first, last, le_of_not_gt last, and_self, ite_true, ite_false, sub_zero]
  · exact (first (ordered.trans_lt last)).elim
  · simp only [first, last, false_and, ite_false, sub_zero]

/-- Every incomplete window uses at most the whole future variation. -/
theorem interiorVariation_le_future (variation : Fin n → ℝ) (nonnegative : ∀ k, 0 ≤ variation k)
    (i j : Fin n) : interiorVariation variation i j ≤ futureVariation variation i := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun k member => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp member).2.1⟩)
    (fun k _ _ => nonnegative k)

/-- Completing a window only adds its nonnegative final-link variation. -/
theorem interiorVariation_le_through (variation : Fin n → ℝ) (nonnegative : ∀ k, 0 ≤ variation k)
    (i j : Fin n) : interiorVariation variation i j ≤ throughVariation variation i j := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun k member => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp member).2.1, (Finset.mem_filter.mp member).2.2.le⟩)
    (fun k _ _ => nonnegative k)

/-- The predecessor window includes exactly the intermediate links, also at adjacent indices. -/
theorem interiorVariation_eq_through_pred (variation : Fin n → ℝ) (i j : Fin n)
    (positive : 0 < j.val) :
    interiorVariation variation i j = throughVariation variation i ⟨j.val - 1, by omega⟩ := by
  classical
  unfold interiorVariation throughVariation
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (i.val < k.val ∧ k.val < j.val) ↔ (i.val < k.val ∧ k.val ≤ j.val - 1)
  omega

/-- Local window bounds imply a variation-weighted global bound, allowing arbitrarily many turns. -/
theorem abs_heading_sub_le_weighted_local_budget (heading variation : Fin n → ℝ)
    {B δ : ℝ} (budget : 0 ≤ B) (width : 0 < δ) (nonnegative : ∀ k, 0 ≤ variation k)
    (window : ∀ i j, i ≤ j → interiorVariation variation i j < δ → |heading i - heading j| ≤ B)
    (anchor i : Fin n) (ordered : i ≤ anchor) :
    |heading i - heading anchor| ≤ B * (1 + futureVariation variation i / δ) := by
  classical
  have future_nonnegative (i : Fin n) : 0 ≤ futureVariation variation i :=
    Finset.sum_nonneg (fun k _ => nonnegative k)
  suffices ∀ d (i : Fin n), anchor.val - i.val = d → i ≤ anchor →
      |heading i - heading anchor| ≤ B * (1 + futureVariation variation i / δ) from
    this _ i rfl ordered
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i distance ordered
    by_cases short : interiorVariation variation i anchor < δ
    · exact (window i anchor ordered short).trans (by
        nlinarith [mul_nonneg budget (div_nonneg (future_nonnegative i) width.le)])
    · let candidates := Finset.univ.filter (fun j : Fin n =>
        j ≤ anchor ∧ δ ≤ throughVariation variation i j)
      have nonempty : candidates.Nonempty := ⟨anchor, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, le_rfl, (le_of_not_gt short).trans
          (interiorVariation_le_through variation nonnegative i anchor)⟩⟩
      let j := candidates.min' nonempty
      have member : j ∈ candidates := candidates.min'_mem nonempty
      obtain ⟨before_anchor, charged⟩ := (Finset.mem_filter.mp member).2
      have later : i < j := by
        by_contra not_later
        have before : j ≤ i := le_of_not_gt not_later
        have zero : throughVariation variation i j = 0 := by
          apply Finset.sum_eq_zero
          intro k member
          have both := (Finset.mem_filter.mp member).2
          exact (not_lt_of_ge (both.2.trans before) both.1).elim
        rw [zero] at charged
        exact not_le_of_gt width charged
      have jp : 0 < j.val := by change i.val < j.val at later; omega
      let pred : Fin n := ⟨j.val - 1, by omega⟩
      have pred_lt : pred < j := by change j.val - 1 < j.val; omega
      have before : interiorVariation variation i j < δ := by
        rw [interiorVariation_eq_through_pred variation i j jp]
        change throughVariation variation i pred < δ
        by_contra not_short
        have present : pred ∈ candidates := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, pred_lt.le.trans before_anchor, le_of_not_gt not_short⟩
        have minimal : j ≤ pred := candidates.min'_le pred present
        exact not_lt_of_ge minimal pred_lt
      have smaller : anchor.val - j.val < d := by
        change j.val ≤ anchor.val at before_anchor
        change i.val < j.val at later
        omega
      have remainder := ih (anchor.val - j.val) smaller j rfl before_anchor
      have step := window i j later.le before
      have triangle : |heading i - heading anchor| ≤ |heading i - heading j| +
          |heading j - heading anchor| := abs_sub_le _ _ _
      rw [throughVariation_eq_future_sub variation later.le] at charged
      have divide : 1 ≤ (futureVariation variation i - futureVariation variation j) / δ :=
        (le_div_iff₀ width).mpr (by simpa using charged)
      have numeric := mul_le_mul_of_nonneg_left divide budget
      have identity : (futureVariation variation i - futureVariation variation j) / δ =
          futureVariation variation i / δ - futureVariation variation j / δ := sub_div _ _ _
      rw [identity] at numeric
      nlinarith

end Unfoldings
