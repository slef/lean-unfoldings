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

private theorem vertical_variation_le_width (n : ℕ) (heading length y : ℕ → ℝ)
    {η lo hi : ℝ} (positive : 0 < η)
    (head_in : ∀ i < n, 0 ≤ heading i ∧ heading i ≤ 2 * Real.pi)
    (separated : ∀ i j, i < j → j < n →
      η ≤ heading j - heading i ∧ heading j - heading i ≤ 2 * Real.pi - η)
    (length_nonneg : ∀ i < n, 0 ≤ length i)
    (vertical : ∀ i < n, y (i + 1) - y i = length i * Real.sin (heading i))
    (cycle : y n = y 0) (width : ∀ i ≤ n, lo ≤ y i ∧ y i ≤ hi) :
    (∑ i ∈ Finset.range n, |y (i + 1) - y i|) ≤ 2 * (hi - lo) := by
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
          linarith only [gap, positive]
      have sin_nonpos : Real.sin (heading i) ≤ 0 := by
        have h := Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0 ≤ heading i - Real.pi by linarith)
          (show heading i - Real.pi ≤ Real.pi by linarith [(head_in i hin).2])
        rw [Real.sin_sub_pi] at h
        linarith
      rw [← sub_nonpos, vertical i hin]
      exact mul_nonpos_of_nonneg_of_nonpos (length_nonneg i hin) sin_nonpos)
    cycle
  rw [strip]
  linarith only [(width m hm).2, (width 0 (Nat.zero_le n)).1]

private theorem sine_le_sum_of_sines {ρ u v : ℝ} (small : ρ ≤ Real.pi / 2)
    (u_le : u ≤ ρ) (v_nonneg : 0 ≤ v) (v_le : v ≤ ρ)
    (separated : ρ ≤ u + v) : Real.sin ρ ≤ Real.sin u + Real.sin v := by
  have cut_nonneg : 0 ≤ ρ - v := sub_nonneg.mpr v_le
  have cut_le : ρ - v ≤ u := by linarith only [separated]
  have sine_cut := Real.sin_nonneg_of_nonneg_of_le_pi cut_nonneg
    (by linarith only [small, v_nonneg, Real.pi_pos])
  have sine_v := Real.sin_nonneg_of_nonneg_of_le_pi v_nonneg
    (by linarith only [v_le, small, Real.pi_pos])
  calc
    Real.sin ρ = Real.sin (ρ - v) * Real.cos v + Real.cos (ρ - v) * Real.sin v := by
      rw [← Real.sin_add, sub_add_cancel]
    _ ≤ Real.sin (ρ - v) + Real.sin v := by
      exact add_le_add
        (mul_le_of_le_one_right sine_cut (Real.cos_le_one _))
        (mul_le_of_le_one_left sine_v (Real.cos_le_one _))
    _ ≤ _ := add_le_add
      (Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith only [cut_nonneg, Real.pi_pos]) (u_le.trans small) cut_le) le_rfl

private theorem omit_one_of_two {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (length factor : ι → ℝ) (ν : ℝ) (size : S.card ≤ 2)
    (nonneg : ∀ i ∈ S, 0 ≤ length i) (factor_nonneg : ∀ i ∈ S, 0 ≤ factor i)
    (pair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ν ≤ factor i + factor j) :
    ∃ O : Finset ι, O ⊆ S ∧ O.card ≤ 1 ∧
      (∑ i ∈ S \ O, length i * ν) ≤ ∑ i ∈ S, length i * factor i := by
  by_cases present : S.Nonempty
  · obtain ⟨k, hk, longest⟩ := Finset.exists_max_image S length present
    refine ⟨{k}, Finset.singleton_subset_iff.mpr hk, by simp, ?_⟩
    rw [Finset.sdiff_singleton_eq_erase]
    have small : (S.erase k).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hk]
      omega
    by_cases remains : (S.erase k).Nonempty
    · obtain ⟨j, hj⟩ := remains
      have equal : S.erase k = {j} := Finset.Subset.antisymm
        (fun i hi => Finset.mem_singleton.mpr (Finset.card_le_one_iff.mp small hi hj))
        (Finset.singleton_subset_iff.mpr hj)
      have hjs := Finset.mem_of_mem_erase hj
      have distinct := (Finset.mem_erase.mp hj).1
      rw [← Finset.sum_erase_add S (fun i => length i * factor i) hk, equal]
      simp only [Finset.sum_singleton]
      calc
        length j * ν ≤ length j * (factor j + factor k) :=
          mul_le_mul_of_nonneg_left (pair j hjs k hk distinct) (nonneg j hjs)
        _ = length j * factor j + length j * factor k := mul_add _ _ _
        _ ≤ _ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (longest j hjs) (factor_nonneg k hk))
    · rw [Finset.not_nonempty_iff_eq_empty.mp remains, Finset.sum_empty]
      exact Finset.sum_nonneg fun i hi => mul_nonneg (nonneg i hi) (factor_nonneg i hi)
  · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp present]
    simp

/-- For a closed planar chord chain in cyclic heading order, omit at most two
sides and bound the remaining length using the sine of any cutoff no greater
than the heading separation and a right angle. If two chords are close to
one horizontal direction, their combined vertical variation pays for the
shorter chord. -/
theorem exists_omit_two_chords_with_cutoff (n : ℕ) (heading length y : ℕ → ℝ)
    {η ρ lo hi : ℝ} (positive : 0 < ρ) (small : ρ ≤ Real.pi / 2) (cutoff : ρ ≤ η)
    (head_in : ∀ i < n, 0 ≤ heading i ∧ heading i ≤ 2 * Real.pi)
    (separated : ∀ i j, i < j → j < n →
      η ≤ heading j - heading i ∧ heading j - heading i ≤ 2 * Real.pi - η)
    (length_nonneg : ∀ i < n, 0 ≤ length i)
    (vertical : ∀ i < n, y (i + 1) - y i = length i * Real.sin (heading i))
    (cycle : y n = y 0) (width : ∀ i ≤ n, lo ≤ y i ∧ y i ≤ hi) :
    ∃ omitted : Finset ℕ, omitted ⊆ Finset.range n ∧ omitted.card ≤ 2 ∧
      (∑ i ∈ Finset.range n \ omitted, length i) * Real.sin ρ ≤ 2 * (hi - lo) := by
  classical
  let U := Finset.range n
  let L := U.filter fun i => heading i < ρ ∨ 2 * Real.pi - ρ < heading i
  let R := U.filter fun i => |heading i - Real.pi| < ρ
  let B := U \ (L ∪ R)
  let factor (i : ℕ) := |Real.sin (heading i)|
  let cost (i : ℕ) := length i * factor i
  have Lsub : L ⊆ U := Finset.filter_subset _ _
  have Rsub : R ⊆ U := Finset.filter_subset _ _
  have L_disjoint_R : Disjoint L R := Finset.disjoint_left.mpr fun i hi hj => by
    have bounds := abs_lt.mp (Finset.mem_filter.mp hj).2
    rcases (Finset.mem_filter.mp hi).2 with low | high
    · linarith only [small, low, bounds.1]
    · linarith only [small, high, bounds.2]
  have L_order {i j : ℕ} (hi : i ∈ L) (hj : j ∈ L) (ij : i < j) :
      heading i < ρ ∧ 2 * Real.pi - ρ < heading j := by
    have near_i := (Finset.mem_filter.mp hi).2
    have near_j := (Finset.mem_filter.mp hj).2
    have in_i := head_in i (Finset.mem_range.mp (Lsub hi))
    have in_j := head_in j (Finset.mem_range.mp (Lsub hj))
    have gap := (separated i j ij (Finset.mem_range.mp (Lsub hj))).1
    rcases near_i with low_i | high_i <;> rcases near_j with low_j | high_j
    · exfalso; linarith only [gap, cutoff, in_i.1, low_j]
    · exact ⟨low_i, high_j⟩
    · exfalso; linarith only [gap, cutoff, high_i, low_j, small, Real.pi_pos]
    · exfalso; linarith only [gap, cutoff, high_i, in_j.2]
  have R_order {i j : ℕ} (hi : i ∈ R) (hj : j ∈ R) (ij : i < j) :
      heading i < Real.pi ∧ Real.pi < heading j := by
    have near_i := abs_lt.mp (Finset.mem_filter.mp hi).2
    have near_j := abs_lt.mp (Finset.mem_filter.mp hj).2
    have gap := (separated i j ij (Finset.mem_range.mp (Rsub hj))).1
    constructor <;> linarith only [near_i.1, near_j.2, gap, cutoff]
  have size_of_two_windows (S : Finset ℕ) (split : ℝ)
      (order : ∀ i ∈ S, ∀ j ∈ S, i < j → heading i < split ∧ split ≤ heading j) :
      S.card ≤ 2 := by
    have size := Finset.card_le_card_of_injOn (s := S) (t := (Finset.univ : Finset Bool))
      (fun i => decide (heading i < split)) (fun _ _ => Finset.mem_univ _)
      (by
        intro i hi j hj equal
        have unequal (k l : ℕ) (hk : k ∈ S) (hl : l ∈ S) (kl : k < l) :
            decide (heading k < split) ≠ decide (heading l < split) := by
          obtain ⟨first, last⟩ := order k hk l hl kl
          simp [first, not_lt.mpr last]
        rcases lt_trichotomy i j with less | same | more
        · exact False.elim (unequal i j hi hj less equal)
        · exact same
        · exact False.elim (unequal j i hj hi more equal.symm))
    simpa using size
  have L_size := size_of_two_windows L ρ fun i hi j hj ij => by
    obtain ⟨first, last⟩ := L_order hi hj ij
    exact ⟨first, by linarith only [last, small, Real.pi_pos]⟩
  have R_size := size_of_two_windows R Real.pi fun i hi j hj ij =>
    ⟨(R_order hi hj ij).1, (R_order hi hj ij).2.le⟩
  have L_pair {i j : ℕ} (hi : i ∈ L) (hj : j ∈ L) (ij : i < j) :
      Real.sin ρ ≤ factor i + factor j := by
    obtain ⟨first, last⟩ := L_order hi hj ij
    have ini := head_in i (Finset.mem_range.mp (Lsub hi))
    have jn := Finset.mem_range.mp (Lsub hj)
    have inj := head_in j jn
    have gap := (separated i j ij jn).2
    let v := 2 * Real.pi - heading j
    have v_nonneg : 0 ≤ v := sub_nonneg.mpr inj.2
    have v_le : v ≤ ρ := by dsimp [v]; linarith only [last]
    have vlo : 0 ≤ Real.sin v :=
      Real.sin_nonneg_of_nonneg_of_le_pi v_nonneg (by linarith only [v_le, small, Real.pi_pos])
    have ilo : 0 ≤ Real.sin (heading i) :=
      Real.sin_nonneg_of_nonneg_of_le_pi ini.1 (by linarith only [first, small, Real.pi_pos])
    have ordered := sine_le_sum_of_sines small first.le v_nonneg v_le
      (show ρ ≤ heading i + v by dsimp [v]; linarith only [gap, cutoff])
    change Real.sin ρ ≤ |Real.sin (heading i)| + |Real.sin (heading j)|
    rw [abs_of_nonneg ilo, ← abs_neg (Real.sin (heading j)),
      ← Real.sin_two_pi_sub (heading j), abs_of_nonneg vlo]
    exact ordered
  have R_pair {i j : ℕ} (hi : i ∈ R) (hj : j ∈ R) (ij : i < j) :
      Real.sin ρ ≤ factor i + factor j := by
    obtain ⟨first, last⟩ := R_order hi hj ij
    let u := Real.pi - heading i
    let v := heading j - Real.pi
    have u_nonneg : 0 ≤ u := sub_nonneg.mpr first.le
    have v_nonneg : 0 ≤ v := sub_nonneg.mpr last.le
    have u_le : u ≤ ρ := by
      dsimp [u]; linarith only [(abs_lt.mp (Finset.mem_filter.mp hi).2).1]
    have v_le : v ≤ ρ := (abs_lt.mp (Finset.mem_filter.mp hj).2).2.le
    have separation := (separated i j ij (Finset.mem_range.mp (Rsub hj))).1
    have ordered := sine_le_sum_of_sines small u_le v_nonneg v_le
      (show ρ ≤ u + v by dsimp [u, v]; linarith only [separation, cutoff])
    have lo_u := Real.sin_nonneg_of_nonneg_of_le_pi u_nonneg
      (by linarith only [u_le, small, Real.pi_pos])
    have lo_v := Real.sin_nonneg_of_nonneg_of_le_pi v_nonneg
      (by linarith only [v_le, small, Real.pi_pos])
    change Real.sin ρ ≤ |Real.sin (heading i)| + |Real.sin (heading j)|
    rw [← Real.sin_pi_sub (heading i), ← abs_neg (Real.sin (heading j)),
      ← Real.sin_sub_pi (heading j), abs_of_nonneg lo_u, abs_of_nonneg lo_v]
    exact ordered
  have choose (S : Finset ℕ) (sub : S ⊆ U) (size : S.card ≤ 2)
      (ordered : ∀ {i j : ℕ}, i ∈ S → j ∈ S → i < j → Real.sin ρ ≤ factor i + factor j) :
      ∃ O : Finset ℕ, O ⊆ S ∧ O.card ≤ 1 ∧
        (∑ i ∈ S \ O, length i * Real.sin ρ) ≤ ∑ i ∈ S, cost i := by
    apply omit_one_of_two S length factor (Real.sin ρ) size
      (fun i hi => length_nonneg i (Finset.mem_range.mp (sub hi))) (fun _ _ => abs_nonneg _)
    intro i hi j hj distinct
    rcases lt_or_gt_of_ne distinct with less | more
    · exact ordered hi hj less
    · simpa only [add_comm] using ordered hj hi more
  obtain ⟨OL, OLsub, OLsize, Lcost⟩ := choose L Lsub L_size L_pair
  obtain ⟨OR, ORsub, ORsize, Rcost⟩ := choose R Rsub R_size R_pair
  have Bcost : (∑ i ∈ B, length i * Real.sin ρ) ≤ ∑ i ∈ B, cost i := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨range, exterior⟩ := Finset.mem_sdiff.mp hi
    have not_L : ¬ (heading i < ρ ∨ 2 * Real.pi - ρ < heading i) :=
      fun h => exterior (Finset.mem_union_left R (Finset.mem_filter.mpr ⟨range, h⟩))
    have not_R : ¬ |heading i - Real.pi| < ρ :=
      fun h => exterior (Finset.mem_union_right L (Finset.mem_filter.mpr ⟨range, h⟩))
    have away : heading i ≤ Real.pi - ρ ∨ Real.pi + ρ ≤ heading i := by
      rcases le_abs.mp (le_of_not_gt not_R) with h | h
      · right; linarith only [h]
      · left; linarith only [h]
    exact mul_le_mul_of_nonneg_left
      (sin_abs_lower_between_horizontal_windows positive.le
        (le_of_not_gt fun h => not_L (Or.inl h))
        (le_of_not_gt fun h => not_L (Or.inr h)) away)
      (length_nonneg i (Finset.mem_range.mp range))
  have cover : B ∪ (L ∪ R) = U :=
    Finset.sdiff_union_of_subset (Finset.union_subset Lsub Rsub)
  have disjoint : Disjoint B (L ∪ R) := Finset.sdiff_disjoint
  have residual : B ∪ ((L \ OL) ∪ (R \ OR)) = U \ (OL ∪ OR) := by
    ext i
    have left_inside : i ∈ L → i ∈ U := fun h => Lsub h
    have right_inside : i ∈ R → i ∈ U := fun h => Rsub h
    have left_removed : i ∈ OL → i ∈ L := fun h => OLsub h
    have right_removed : i ∈ OR → i ∈ R := fun h => ORsub h
    have different : i ∈ L → i ∈ R → False := fun h => Finset.disjoint_left.mp L_disjoint_R h
    simp only [B, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have residual_disjoint : Disjoint (L \ OL) (R \ OR) :=
    L_disjoint_R.mono Finset.sdiff_subset Finset.sdiff_subset
  have residual_with_B : Disjoint B ((L \ OL) ∪ (R \ OR)) :=
    disjoint.mono_right (Finset.union_subset_union Finset.sdiff_subset Finset.sdiff_subset)
  have variation (i : ℕ) (hi : i ∈ U) : cost i = |y (i + 1) - y i| := by
    have hin := Finset.mem_range.mp hi
    rw [vertical i hin, abs_mul, abs_of_nonneg (length_nonneg i hin)]
  refine ⟨OL ∪ OR, Finset.union_subset (OLsub.trans Lsub) (ORsub.trans Rsub),
    (Finset.card_union_le OL OR).trans (by omega), ?_⟩
  change (∑ i ∈ U \ (OL ∪ OR), length i) * Real.sin ρ ≤ _
  rw [Finset.sum_mul]
  calc
    _ = (∑ i ∈ B, length i * Real.sin ρ) + (∑ i ∈ L \ OL, length i * Real.sin ρ) +
        ∑ i ∈ R \ OR, length i * Real.sin ρ := by
      rw [← residual, Finset.sum_union residual_with_B, Finset.sum_union residual_disjoint, add_assoc]
    _ ≤ (∑ i ∈ B, cost i) + (∑ i ∈ L, cost i) + ∑ i ∈ R, cost i :=
      add_le_add (add_le_add Bcost Lcost) Rcost
    _ = ∑ i ∈ U, cost i := by
      rw [← cover, Finset.sum_union disjoint, Finset.sum_union L_disjoint_R, add_assoc]
    _ = ∑ i ∈ U, |y (i + 1) - y i| := Finset.sum_congr rfl variation
    _ ≤ _ := vertical_variation_le_width n heading length y (positive.trans_le cutoff)
      head_in separated length_nonneg vertical cycle width

/-- The half-angle version of the two-side bound, valid for every positive
heading separation up to a straight angle. -/
theorem exists_omit_two_chords (n : ℕ) (heading length y : ℕ → ℝ)
    {η lo hi : ℝ} (positive : 0 < η) (small : η ≤ Real.pi)
    (head_in : ∀ i < n, 0 ≤ heading i ∧ heading i ≤ 2 * Real.pi)
    (separated : ∀ i j, i < j → j < n →
      η ≤ heading j - heading i ∧ heading j - heading i ≤ 2 * Real.pi - η)
    (length_nonneg : ∀ i < n, 0 ≤ length i)
    (vertical : ∀ i < n, y (i + 1) - y i = length i * Real.sin (heading i))
    (cycle : y n = y 0) (width : ∀ i ≤ n, lo ≤ y i ∧ y i ≤ hi) :
    ∃ omitted : Finset ℕ, omitted ⊆ Finset.range n ∧ omitted.card ≤ 2 ∧
      (∑ i ∈ Finset.range n \ omitted, length i) * Real.sin (η / 2) ≤ 2 * (hi - lo) :=
  exists_omit_two_chords_with_cutoff n heading length y
    (by linarith only [positive]) (by linarith only [small]) (by linarith only [positive])
    head_in separated length_nonneg vertical cycle width

end Unfoldings
