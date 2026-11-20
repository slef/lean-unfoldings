module

public import Unfoldings.Basic
public import Unfoldings.Combinatorics.LabelChanges
public import Mathlib.Tactic.Linarith

/-! Algebraic Euler accounting and the two-side omission bound for Gaussian polygons. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Unfoldings

variable {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E]
  (sides : F → Finset E) (changed : E → Prop) [DecidablePred changed]

/-- The Euler contribution of a polygon with the given number of changed sides. -/
def componentCharge (k : ℕ) : ℝ :=
  (k : ℝ) / 2 - if k = 0 then 0 else 1

/-- Omitting at most two boundary sides still bounds the contribution of the
polygon by half the number of changed sides that remain. -/
theorem componentCharge_le_half_card_filtered_sdiff (s deleted : Finset E)
    (few : deleted.card ≤ 2) (not_one : (s.filter changed).card ≠ 1) :
    0 ≤ componentCharge (s.filter changed).card ∧
      componentCharge (s.filter changed).card ≤ ((s \ deleted).filter changed).card / (2 : ℝ) := by
  by_cases zero : (s.filter changed).card = 0
  · simp [zero, componentCharge, div_nonneg]
  have split : ((s \ deleted).filter changed).card +
      ((s.filter changed) ∩ deleted).card = (s.filter changed).card := by
    have eq : (s \ deleted).filter changed = (s.filter changed) \ deleted := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    rw [eq, Finset.card_sdiff_add_card_inter]
  have omitted : ((s.filter changed) ∩ deleted).card ≤ 2 :=
    (Finset.card_le_card Finset.inter_subset_right).trans few
  have two : 2 ≤ (s.filter changed).card := by omega
  have rem : (s.filter changed).card ≤ ((s \ deleted).filter changed).card + 2 := by omega
  have rem_real : ((s.filter changed).card : ℝ) ≤ ((s \ deleted).filter changed).card + 2 := by
    exact_mod_cast rem
  have two_real : (2 : ℝ) ≤ (s.filter changed).card := by exact_mod_cast two
  simp only [componentCharge, ite_eq_right zero]
  constructor <;> linarith

/-- Each changed edge contributes one incidence to each of its two polygons. -/
theorem sum_card_filtered_sides (twice : ∀ e, (Finset.univ.filter fun f => e ∈ sides f).card = 2) :
    (∑ f, (sides f |>.filter changed).card) = 2 * (Finset.univ.filter changed).card := by
  classical
  have indic (f : F) : (sides f |>.filter changed).card =
      ∑ e : E, if e ∈ sides f ∧ changed e then (1 : ℕ) else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext e
    simp
  simp only [indic]
  rw [Finset.sum_comm]
  have column (e : E) :
      (∑ f : F, if e ∈ sides f ∧ changed e then (1 : ℕ) else 0) =
        2 * (if changed e then 1 else 0) := by
    by_cases h : changed e
    · simp only [h, and_true, ite_true, mul_one, Finset.sum_boole, Nat.cast_id]
      exact twice e
    · simp [h]
  simp only [column, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]

/-- Once the two Euler identities are known, the exact component count is the
constant two plus the sum of polygon contributions. The mixed polygons are
identified by their changed sides and the incidence count is derived here. -/
theorem component_count_eq_two_add_sum_charges
    (vertices components : ℕ)
    (sphere_euler : (vertices : ℤ) - Fintype.card E + Fintype.card F = 2)
    (label_euler : (components : ℤ) = (vertices : ℤ) -
        (Finset.univ.filter fun e : E => ¬ changed e).card +
        (Finset.univ.filter fun f : F => (sides f |>.filter changed).card = 0).card)
    (twice : ∀ e, (Finset.univ.filter fun f => e ∈ sides f).card = 2) :
    (components : ℝ) = 2 + ∑ f, componentCharge (sides f |>.filter changed).card := by
  classical
  have count_E := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset E)) changed
  have count_F := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
    (fun f => (sides f |>.filter changed).card = 0)
  rw [Finset.card_univ] at count_E count_F
  have mono_mixed :
      (Finset.univ.filter fun f : F => (sides f |>.filter changed).card = 0).card +
        (Finset.univ.filter fun f : F => (sides f |>.filter changed).card ≠ 0).card =
        Fintype.card F := count_F
  have euler : (components : ℤ) = 2 + (Finset.univ.filter changed).card -
      (Finset.univ.filter fun f : F => (sides f |>.filter changed).card ≠ 0).card := by
    omega
  have euler_real : (components : ℝ) = 2 + (Finset.univ.filter changed).card -
      (Finset.univ.filter fun f : F => (sides f |>.filter changed).card ≠ 0).card := by
    exact_mod_cast euler
  have twice_real : (∑ f, ((sides f |>.filter changed).card : ℝ)) =
      2 * (Finset.univ.filter changed).card := by
    exact_mod_cast sum_card_filtered_sides sides changed twice
  have mixed : (∑ f, if (sides f |>.filter changed).card = 0 then (0 : ℝ) else 1) =
      (Finset.univ.filter fun f : F => (sides f |>.filter changed).card ≠ 0).card := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro f _
    by_cases h : (sides f |>.filter changed).card = 0 <;> simp [h]
  simp only [componentCharge, Finset.sum_sub_distrib, ← Finset.sum_div, mixed, twice_real]
  linarith

end Unfoldings
