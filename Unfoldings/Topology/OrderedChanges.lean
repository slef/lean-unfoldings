module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Selecting an ordered tail of changes

For a bounded signal, selecting a tail of its nonzero increments telescopes.
The criterion ignores zero increments, so it applies to ordered geometric
crossings with arbitrary subdivisions between them.
-/

@[expose] public section

namespace Unfoldings

/-- All successive increments telescope, including a zero-edge chain. -/
theorem sum_fin_succ_sub {n : ℕ} (signal : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (signal i.succ - signal i.castSucc)) =
      signal (Fin.last n) - signal 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have previous := ih (fun i => signal i.castSucc)
    change (∑ i : Fin n, (signal i.succ.castSucc - signal i.castSucc.castSucc)) +
      (signal (Fin.last (n + 1)) - signal (Fin.last n).castSucc) = _
    rw [previous]
    simp only [Fin.castSucc_zero]
    ring

/-- An upper set of nonzero increments sums to the final signal minus one bounded value. -/
theorem sum_ordered_changes_representation {n : ℕ} (signal : Fin (n + 1) → ℝ)
    (bounded : ∀ i, signal i ∈ Set.Icc (0 : ℝ) 1)
    (selected : Fin n → Prop) [DecidablePred selected]
    (ordered : ∀ i j : Fin n, i ≤ j → signal i.succ ≠ signal i.castSucc →
      signal j.succ ≠ signal j.castSucc → selected i → selected j) :
    ∃ initial ∈ Set.Icc (0 : ℝ) 1,
      (∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0) =
        signal (Fin.last n) - initial := by
  classical
  induction n with
  | zero => exact ⟨signal 0, bounded 0, by simp⟩
  | succ n ih =>
    let small_signal (i : Fin (n + 1)) := signal i.castSucc
    let small_selected (i : Fin n) := selected i.castSucc
    have small_ordered (i j : Fin n) (le : i ≤ j)
        (first : small_signal i.succ ≠ small_signal i.castSucc)
        (last : small_signal j.succ ≠ small_signal j.castSucc)
        (inside : small_selected i) : small_selected j := by
      exact ordered i.castSucc j.castSucc (by exact le) first last inside
    obtain ⟨initial, initial_bounds, prefix_sum⟩ := ih small_signal
      (fun i => bounded i.castSucc) small_selected small_ordered
    change (∑ i : Fin n, if selected i.castSucc then
      signal i.succ.castSucc - signal i.castSucc.castSucc else 0) =
        signal (Fin.last n).castSucc - initial at prefix_sum
    have split_sum : (∑ i : Fin (n + 1),
        if selected i then signal i.succ - signal i.castSucc else 0) =
      (∑ i : Fin n, if selected i.castSucc then
        signal i.succ.castSucc - signal i.castSucc.castSucc else 0) +
      (if selected (Fin.last n) then
        signal (Fin.last (n + 1)) - signal (Fin.last n).castSucc else 0) := by
      rw [Fin.sum_univ_castSucc]
      rfl
    by_cases last_selected : selected (Fin.last n)
    · refine ⟨initial, initial_bounds, ?_⟩
      rw [split_sum, ite_eq_left last_selected, prefix_sum]
      ring
    · by_cases unchanged : signal (Fin.last (n + 1)) = signal (Fin.last n).castSucc
      · refine ⟨initial, initial_bounds, ?_⟩
        rw [split_sum, ite_eq_right last_selected, add_zero, prefix_sum, unchanged]
      · have zero (i : Fin n) :
          (if selected i.castSucc then signal i.succ.castSucc - signal i.castSucc.castSucc
            else 0) = 0 := by
          by_cases inside : selected i.castSucc
          · have same : signal i.succ.castSucc = signal i.castSucc.castSucc := by
              by_contra different
              exact last_selected (ordered i.castSucc (Fin.last n) (Fin.le_last _)
                different unchanged inside)
            simp only [ite_eq_left inside, same, sub_self]
          · exact ite_eq_right inside
        refine ⟨signal (Fin.last (n + 1)), bounded _, ?_⟩
        rw [split_sum, Finset.sum_eq_zero (fun i _ => zero i), ite_eq_right last_selected, add_zero,
          sub_self]

/-- Ordered signed changes have a uniform bound, independent of the number of crossings. -/
theorem abs_sum_ordered_changes_le_one {n : ℕ} (signal : Fin (n + 1) → ℝ)
    (bounded : ∀ i, signal i ∈ Set.Icc (0 : ℝ) 1)
    (selected : Fin n → Prop) [DecidablePred selected]
    (ordered : ∀ i j : Fin n, i ≤ j → signal i.succ ≠ signal i.castSucc →
      signal j.succ ≠ signal j.castSucc → selected i → selected j) :
    |∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0| ≤ 1 := by
  obtain ⟨initial, initial_bounds, total⟩ :=
    sum_ordered_changes_representation signal bounded selected ordered
  rw [total]
  apply abs_le.mpr
  have endpoint := bounded (Fin.last n)
  constructor <;> linarith [initial_bounds.1, initial_bounds.2, endpoint.1, endpoint.2]

/-- A lower set of nonzero signed changes has the same mesh-independent bound. -/
theorem abs_sum_reverse_ordered_changes_le_one {n : ℕ} (signal : Fin (n + 1) → ℝ)
    (bounded : ∀ i, signal i ∈ Set.Icc (0 : ℝ) 1)
    (selected : Fin n → Prop) [DecidablePred selected]
    (ordered : ∀ i j : Fin n, i ≤ j → signal i.succ ≠ signal i.castSucc →
      signal j.succ ≠ signal j.castSucc → selected j → selected i) :
    |∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0| ≤ 1 := by
  classical
  have complement_ordered (i j : Fin n) (le : i ≤ j)
      (first : signal i.succ ≠ signal i.castSucc) (last : signal j.succ ≠ signal j.castSucc)
      (outside : ¬ selected i) : ¬ selected j := fun inside =>
    outside (ordered i j le first last inside)
  obtain ⟨initial, initial_bounds, complement_sum⟩ :=
    sum_ordered_changes_representation signal bounded (fun i => ¬ selected i) complement_ordered
  have total : (∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0) +
      (∑ i : Fin n, if ¬ selected i then signal i.succ - signal i.castSucc else 0) =
        signal (Fin.last n) - signal 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin n, (signal i.succ - signal i.castSucc) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := sum_fin_succ_sub signal
  rw [complement_sum] at total
  have selected_sum : (∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0) =
      initial - signal 0 := by linarith
  rw [selected_sum]
  apply abs_le.mpr
  have first := bounded 0
  constructor <;> linarith [initial_bounds.1, initial_bounds.2, first.1, first.2]

/-- For a monotone bounded signal, every selection of its increments is bounded. -/
theorem abs_sum_selected_changes_of_monotone {n : ℕ} (signal : Fin (n + 1) → ℝ)
    (bounded : ∀ i, signal i ∈ Set.Icc (0 : ℝ) 1) (monotone : Monotone signal)
    (selected : Fin n → Prop) [DecidablePred selected] :
    |∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0| ≤ 1 := by
  have increments (i : Fin n) : 0 ≤ signal i.succ - signal i.castSucc :=
    sub_nonneg.mpr (monotone (Fin.castSucc_le_succ i))
  have lower : 0 ≤ ∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0 :=
    Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact increments i
      · exact le_rfl)
  rw [abs_of_nonneg lower]
  calc
    _ ≤ ∑ i : Fin n, (signal i.succ - signal i.castSucc) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact le_rfl
      · exact increments i
    _ = signal (Fin.last n) - signal 0 := sum_fin_succ_sub signal
    _ ≤ 1 := by linarith [(bounded (Fin.last n)).2, (bounded 0).1]

/-- For an antitone bounded signal, every selection of its increments is also bounded. -/
theorem abs_sum_selected_changes_of_antitone {n : ℕ} (signal : Fin (n + 1) → ℝ)
    (bounded : ∀ i, signal i ∈ Set.Icc (0 : ℝ) 1) (antitone : Antitone signal)
    (selected : Fin n → Prop) [DecidablePred selected] :
    |∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0| ≤ 1 := by
  have reverse_bounds (i) : 1 - signal i ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [(bounded i).1, (bounded i).2]
  have reverse : Monotone (fun i => 1 - signal i) :=
    fun i j le => sub_le_sub_left (antitone le) 1
  have result := abs_sum_selected_changes_of_monotone (fun i => 1 - signal i)
    reverse_bounds reverse selected
  have negated : (∑ i : Fin n, if selected i then
      (1 - signal i.succ) - (1 - signal i.castSucc) else 0) =
        -(∑ i : Fin n, if selected i then signal i.succ - signal i.castSucc else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [negated, abs_neg] at result
  exact result

end Unfoldings
