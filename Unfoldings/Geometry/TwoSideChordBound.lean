module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Two omitted directions bound the remaining chords by the vertical width. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped BigOperators

private theorem sin_abs_lower_between_horizontal_windows {a ρ : ℝ}
    (nonneg : 0 ≤ ρ) (first : ρ ≤ a) (last : a ≤ 2 * Real.pi - ρ)
    (away : a ≤ Real.pi - ρ ∨ Real.pi + ρ ≤ a) :
    Real.sin ρ ≤ |Real.sin a| := by
  have compare {b : ℝ} (order : ρ ≤ b) (small : b ≤ Real.pi / 2) :
      Real.sin ρ ≤ Real.sin b :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) small order
  rcases away with lower | upper
  · by_cases h : a ≤ Real.pi / 2
    · exact (compare first h).trans (le_abs_self _)
    · have h' := compare (b := Real.pi - a) (by linarith) (by linarith)
      rw [Real.sin_pi_sub] at h'
      exact h'.trans (le_abs_self _)
  · by_cases h : a ≤ Real.pi + Real.pi / 2
    · have h' := compare (b := a - Real.pi) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at h'
      exact h'.trans (neg_le_abs _)
    · have h' := compare (b := 2 * Real.pi - a) (by linarith) (by linarith)
      rw [Real.sin_two_pi_sub] at h'
      exact h'.trans (neg_le_abs _)

private theorem sum_absolute_vertical_increments (n : ℕ) (y : ℕ → ℝ) {m : ℕ} (hm : m ≤ n)
    (up : ∀ i < m, y i ≤ y (i + 1))
    (down : ∀ i, m ≤ i → i < n → y (i + 1) ≤ y i)
    (cycle : y n = y 0) :
    (∑ i ∈ Finset.range n, |y (i + 1) - y i|) = 2 * (y m - y 0) := by
  have telescoping (start k : ℕ) :
      (∑ i ∈ Finset.range k, (y (start + i + 1) - y (start + i))) = y (start + k) - y start := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring
  have split : m + (n - m) = n := Nat.add_sub_of_le hm
  have rising : (∑ i ∈ Finset.range m, |y (i + 1) - y i|) = y m - y 0 := by
    have initial : (∑ i ∈ Finset.range m, (y (i + 1) - y i)) = y m - y 0 := by
      simpa only [Nat.zero_add] using telescoping 0 m
    rw [← initial]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonneg (sub_nonneg.mpr (up i (Finset.mem_range.mp hi)))]
  have falling : (∑ i ∈ Finset.range (n - m), |y (m + i + 1) - y (m + i)|) = y m - y n := by
    calc
      _ = -(∑ i ∈ Finset.range (n - m), (y (m + i + 1) - y (m + i))) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i hi =>
          abs_of_nonpos (sub_nonpos.mpr (down (m + i) (by omega)
            (by have := Finset.mem_range.mp hi; omega))))
      _ = _ := by rw [telescoping, split]; ring
  calc
    _ = (∑ i ∈ Finset.range m, |y (i + 1) - y i|) +
        ∑ i ∈ Finset.range (n - m), |y (m + i + 1) - y (m + i)| := by
      rw [← Finset.sum_range_add, split]
    _ = _ := by rw [rising, falling, cycle]; ring

/-- For a closed planar chord chain whose headings run once around the circle
in sorted order, a lower bound on successive heading gaps bounds length after
omitting two sides. The angular spacing also includes the gap across zero. -/
theorem exists_omit_two_chords (n : ℕ) (heading length y : ℕ → ℝ)
    {η lo hi : ℝ} (positive : 0 < η) (_small : η ≤ Real.pi)
    (head_in : ∀ i < n, 0 ≤ heading i ∧ heading i ≤ 2 * Real.pi)
    (separated : ∀ i j, i < j → j < n →
      η ≤ heading j - heading i ∧ heading j - heading i ≤ 2 * Real.pi - η)
    (length_nonneg : ∀ i < n, 0 ≤ length i)
    (vertical : ∀ i < n, y (i + 1) - y i = length i * Real.sin (heading i))
    (cycle : y n = y 0) (width : ∀ i ≤ n, lo ≤ y i ∧ y i ≤ hi) :
    ∃ omitted : Finset ℕ, omitted ⊆ Finset.range n ∧ omitted.card ≤ 2 ∧
      (∑ i ∈ Finset.range n \ omitted, length i) * Real.sin (η / 2) ≤ 2 * (hi - lo) := by
  classical
  let L := (Finset.range n).filter fun i => heading i < η / 2 ∨ 2 * Real.pi - η / 2 < heading i
  let R := (Finset.range n).filter fun i => |heading i - Real.pi| < η / 2
  have left_one : L.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro i j hi' hj'
    by_cases equal : i = j
    · exact equal
    exfalso
    have pair (a b : ℕ) (ab : a < b) (ha : a ∈ L) (hb : b ∈ L) : False := by
      obtain ⟨han, hleft⟩ : a < n ∧
          (heading a < η / 2 ∨ 2 * Real.pi - η / 2 < heading a) := by simpa [L] using ha
      obtain ⟨hbn, hright⟩ : b < n ∧
          (heading b < η / 2 ∨ 2 * Real.pi - η / 2 < heading b) := by simpa [L] using hb
      have a_bounds := head_in a han
      have b_bounds := head_in b hbn
      have gaps := separated a b ab hbn
      rcases hleft with l | l <;> rcases hright with r | r <;> linarith [a_bounds.1, b_bounds.2,
        gaps.1, gaps.2]
    rcases lt_or_gt_of_ne equal with less | more
    · exact pair i j less hi' hj'
    · exact pair j i more hj' hi'
  have right_one : R.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro i j hi' hj'
    by_cases equal : i = j
    · exact equal
    exfalso
    have pair (a b : ℕ) (ab : a < b) (ha : a ∈ R) (hb : b ∈ R) : False := by
      obtain ⟨_, hleft⟩ : a < n ∧ |heading a - Real.pi| < η / 2 := by simpa [R] using ha
      obtain ⟨hbn, hright⟩ : b < n ∧ |heading b - Real.pi| < η / 2 := by simpa [R] using hb
      linarith [(abs_lt.mp hleft).1, (abs_lt.mp hright).2, (separated a b ab hbn).1]
    rcases lt_or_gt_of_ne equal with less | more
    · exact pair i j less hi' hj'
    · exact pair j i more hj' hi'
  let omitted := L ∪ R
  have omitted_subset : omitted ⊆ Finset.range n :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have omitted_size : omitted.card ≤ 2 := by
    exact (Finset.card_union_le L R).trans (by omega)
  have exists_step : ∃ k : ℕ, k = n ∨ Real.pi < heading k := ⟨n, Or.inl rfl⟩
  let m := Nat.find exists_step
  have hm : m ≤ n := Nat.find_min' exists_step (Or.inl rfl)
  have strip := sum_absolute_vertical_increments n y hm
    (fun i hi' => by
      have hin : i < n := by omega
      have early := Nat.find_min exists_step hi'
      have heading_le : heading i ≤ Real.pi := le_of_not_gt (fun h => early (Or.inr h))
      have sin_nonneg := Real.sin_nonneg_of_nonneg_of_le_pi (head_in i hin).1 heading_le
      rw [← sub_nonneg, vertical i hin]
      exact mul_nonneg (length_nonneg i hin) sin_nonneg)
    (fun i hi' hin => by
      have positive_heading : Real.pi < heading m := by
        rcases Nat.find_spec exists_step with equal | h
        · change m = n at equal
          omega
        · exact h
      have ordered : heading m ≤ heading i := by
        rcases eq_or_lt_of_le hi' with equal | less
        · rw [equal]
        · have gap := (separated m i less hin).1
          linarith
      have sin_nonpos : Real.sin (heading i) ≤ 0 := by
        have h := Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0 ≤ heading i - Real.pi by linarith)
          (show heading i - Real.pi ≤ Real.pi by linarith [(head_in i hin).2])
        rw [Real.sin_sub_pi] at h
        linarith
      rw [← sub_nonpos, vertical i hin]
      exact mul_nonpos_of_nonneg_of_nonpos (length_nonneg i hin) sin_nonpos)
    cycle
  refine ⟨omitted, omitted_subset, omitted_size, ?_⟩
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i ∈ Finset.range n \ omitted, |y (i + 1) - y i| := by
      apply Finset.sum_le_sum
      intro i hi'
      obtain ⟨range, not_omitted⟩ := Finset.mem_sdiff.mp hi'
      have hin := Finset.mem_range.mp range
      have not_L : i ∉ L := by
        intro present
        exact not_omitted (Finset.mem_union_left R present)
      have not_R : i ∉ R := by
        intro present
        exact not_omitted (Finset.mem_union_right L present)
      have first : η / 2 ≤ heading i := le_of_not_gt fun h =>
        not_L (Finset.mem_filter.mpr ⟨range, Or.inl h⟩)
      have last : heading i ≤ 2 * Real.pi - η / 2 := le_of_not_gt fun h =>
        not_L (Finset.mem_filter.mpr ⟨range, Or.inr h⟩)
      have away : heading i ≤ Real.pi - η / 2 ∨ Real.pi + η / 2 ≤ heading i := by
        have h : η / 2 ≤ |heading i - Real.pi| := le_of_not_gt fun h =>
          not_R (Finset.mem_filter.mpr ⟨range, h⟩)
        rcases le_abs.mp h with h | h
        · right
          linarith
        · left
          linarith
      rw [vertical i hin, abs_mul, abs_of_nonneg (length_nonneg i hin)]
      exact mul_le_mul_of_nonneg_left
        (sin_abs_lower_between_horizontal_windows (by positivity) first last away)
        (length_nonneg i hin)
    _ ≤ ∑ i ∈ Finset.range n, |y (i + 1) - y i| :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => abs_nonneg _)
    _ = 2 * (y m - y 0) := strip
    _ ≤ 2 * (hi - lo) := by linarith [(width m hm).2, (width 0 (Nat.zero_le n)).1]

end Unfoldings
