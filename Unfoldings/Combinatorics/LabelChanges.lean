module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.NormNum

/-! Counting color changes around cyclically ordered boundary sides. -/

@[expose] public section

namespace Unfoldings

open scoped BigOperators

variable {I L : Type*} [Fintype I]

open Classical in
/-- A finite permutation of boundary positions cannot change the label at exactly one position. -/
theorem card_label_changes_ne_one (next : Equiv.Perm I) (label : I → L) :
    (Finset.univ.filter fun i => label i ≠ label (next i)).card ≠ 1 := by
  classical
  intro only_one
  obtain ⟨i, lone⟩ := Finset.card_eq_one.mp only_one
  have change_i : label i ≠ label (next i) := by
    have h : i ∈ Finset.univ.filter (fun j => label j ≠ label (next j)) := by
      rw [lone]
      exact Finset.mem_singleton_self i
    exact (Finset.mem_filter.mp h).2
  have fixed (j : I) (distinct : j ≠ i) : label j = label (next j) := by
    by_contra changed
    have h : j ∈ Finset.univ.filter (fun k => label k ≠ label (next k)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, changed⟩
    rw [lone] at h
    exact distinct (Finset.mem_singleton.mp h)
  let weight (j : I) : ℤ := if label j = label i then 1 else 0
  have sum_weight : (∑ j, (weight j - weight (next j))) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp next weight, sub_self]
  have equal (j : I) : weight j - weight (next j) = if j = i then 1 else 0 := by
    by_cases h : j = i
    · subst j
      simp [weight, Ne.symm change_i]
    · simp [weight, ← fixed j h, h]
  simp only [equal, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at sum_weight
  norm_num at sum_weight

end Unfoldings
