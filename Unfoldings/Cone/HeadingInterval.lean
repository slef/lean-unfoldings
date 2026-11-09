module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith

/-!
# Pointed heading intervals containing nearby directions

Two directions in a positive finite heading range that differ by less than
pi fit into a positive-width interval shorter than pi in that same range.
Coincident directions, including the two range endpoints, are allowed.
-/

@[expose] public section

namespace Unfoldings

theorem exists_pointed_heading_interval (L : ℝ) (positive : 0 < L)
    (θ φ : ℝ) (left : θ ∈ Set.Icc 0 L) (right : φ ∈ Set.Icc 0 L)
    (close : |θ - φ| < Real.pi) :
    ∃ a b : ℝ, 0 < b - a ∧ b - a < Real.pi ∧ 0 ≤ a ∧ b ≤ L ∧
      θ ∈ Set.Icc a b ∧ φ ∈ Set.Icc a b := by
  let lo := min θ φ
  let hi := max θ φ
  have lower : 0 ≤ lo := le_min left.1 right.1
  have upper : hi ≤ L := max_le left.2 right.2
  have ordered : lo ≤ hi := (min_le_left _ _).trans (le_max_left _ _)
  have width : hi - lo < Real.pi := by
    simpa only [hi, lo, max_sub_min_eq_abs, abs_sub_comm φ θ] using close
  have interval : ∃ a b : ℝ, 0 < b - a ∧ b - a < Real.pi ∧ 0 ≤ a ∧ b ≤ L ∧
      lo ∈ Set.Icc a b ∧ hi ∈ Set.Icc a b := by
    rcases lt_or_eq_of_le ordered with strict | same
    · exact ⟨lo, hi, sub_pos.mpr strict, width, lower, upper,
        ⟨le_rfl, strict.le⟩, ⟨strict.le, le_rfl⟩⟩
    · by_cases room : hi < L
      · let δ := min ((L - hi) / 2) (Real.pi / 2)
        have δpos : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
        have δbound₁ : δ ≤ (L - hi) / 2 := min_le_left _ _
        have δbound₂ : δ ≤ Real.pi / 2 := min_le_right _ _
        refine ⟨hi, hi + δ, by linarith, by linarith [Real.pi_pos], by linarith,
          by linarith, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
      · have endpoint : hi = L := le_antisymm upper (le_of_not_gt room)
        let δ := min (L / 2) (Real.pi / 2)
        have δpos : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
        have δbound₁ : δ ≤ L / 2 := min_le_left _ _
        have δbound₂ : δ ≤ Real.pi / 2 := min_le_right _ _
        refine ⟨L - δ, L, by linarith, by linarith [Real.pi_pos], by linarith,
          le_rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  obtain ⟨a, b, gap, small, first, last, lo_mem, hi_mem⟩ := interval
  exact ⟨a, b, gap, small, first, last,
    ⟨lo_mem.1.trans (min_le_left _ _), (le_max_left _ _).trans hi_mem.2⟩,
    ⟨lo_mem.1.trans (min_le_right _ _), (le_max_right _ _).trans hi_mem.2⟩⟩

end Unfoldings
