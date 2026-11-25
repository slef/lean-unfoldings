module

public import Unfoldings.FewestNets.LatitudeSweepCounts

/-! A sorted midpoint sweep keeps the opposite-row vertex within half a step. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- Longitude of a row site, including the repeated site at the end of the strip. -/
def rowLongitude (n i : ℕ) : ℝ := 2 * π * i / n

theorem rowLongitude_mono (n : ℕ) : Monotone (rowLongitude n) := by
  intro i j ordered
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr ordered) (by positivity)) (Nat.cast_nonneg _)

/-- After all earlier midpoints have been advanced, the actual remaining
site is a closest site on this row, with either tied site allowed. -/
theorem rowProgress_closest {n total : ℕ} (positive : 0 < n) (rank : Fin n → Fin total)
    (monotone : StrictMono rank) (stage : ℕ) {longitude : ℝ} (in_strip : longitude ∈ Set.Icc 0 (2 * π))
    (before : ∀ i, (rank i).val < stage → rowMidpoint n i ≤ longitude)
    (after : ∀ i, stage ≤ (rank i).val → longitude ≤ rowMidpoint n i) :
    |longitude - rowLongitude n (rowProgress rank stage)| ≤ π / n := by
  let current := rowProgress rank stage
  let half := π / (n : ℝ)
  have n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr positive
  have half_nonneg : 0 ≤ half := div_nonneg pi_pos.le n_pos.le
  have count : current ≤ n := rowProgress_le rank stage
  have first : rowLongitude n current - half ≤ longitude := by
    by_cases start : current = 0
    · rw [start]
      have zero : rowLongitude n 0 = 0 := by simp [rowLongitude]
      rw [zero]
      linarith only [half_nonneg, in_strip.1]
    · let j : Fin n := ⟨current - 1, by omega⟩
      have prior : (rank j).val < stage :=
        (earlier_iff_lt_rowProgress rank monotone stage j).mpr (by change current - 1 < current; omega)
      have actual := before j prior
      have index : (j.val : ℝ) = (current : ℝ) - 1 := by
        have add : j.val + 1 = current := by change current - 1 + 1 = current; omega
        have real : (j.val : ℝ) + 1 = current := by exact_mod_cast add
        linarith only [real]
      unfold rowLongitude
      unfold rowMidpoint at actual
      rw [index] at actual
      dsimp only [half]
      convert actual using 1
      ring
  have last : longitude ≤ rowLongitude n current + half := by
    by_cases finish : current = n
    · rw [finish]
      have period : rowLongitude n n = 2 * π := by
        unfold rowLongitude
        exact mul_div_cancel_right₀ _ n_pos.ne'
      rw [period]
      linarith only [half_nonneg, in_strip.2]
    · let j : Fin n := ⟨current, by omega⟩
      have next : stage ≤ (rank j).val := Nat.le_of_not_gt (fun earlier => by
        have impossible := (earlier_iff_lt_rowProgress rank monotone stage j).mp earlier
        exact (Nat.lt_irrefl current) impossible)
      have actual := after j next
      unfold rowLongitude
      unfold rowMidpoint at actual
      dsimp only [half]
      change longitude ≤ 2 * π * ((current : ℝ) + 1 / 2) / n at actual
      convert actual using 1
      ring
  exact abs_le.mpr ⟨by linarith only [first], by linarith only [last]⟩

end Unfoldings.FewestNets
