module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin

/-!
# Labels and changes around a finite cycle

Every proper nonempty label class has an entry where the predecessor has a
different label. Consequently a nonconstant cyclic list has no more distinct
labels than changes. This combinatorial statement is independent of geometry.
-/

@[expose] public section

namespace Unfoldings

theorem finRotate_symm_succ {n : ℕ} (i : Fin n) :
    (finRotate (n + 1)).symm i.succ = i.castSucc := by
  apply (finRotate (n + 1)).injective
  rw [Equiv.apply_symm_apply]
  exact (finRotate_of_lt i.isLt).symm

theorem finRotate_symm_zero (n : ℕ) :
    (finRotate (n + 1)).symm 0 = Fin.last n := by
  apply (finRotate (n + 1)).injective
  rw [Equiv.apply_symm_apply, finRotate_last]

theorem exists_cyclic_label_entry {α : Type*} {n : ℕ} (label : Fin (n + 1) → α) (a : α)
    (visited : ∃ i, label i = a) (outside : ∃ i, label i ≠ a) :
    ∃ i, label i = a ∧ label ((finRotate (n + 1)).symm i) ≠ a := by
  classical
  by_cases at_zero : label 0 = a
  · let other := Finset.univ.filter (fun i => label i ≠ a)
    have nonempty : other.Nonempty := by
      obtain ⟨i, hi⟩ := outside
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨j, hj, maximal⟩ := Finset.exists_max_image other id nonempty
    have different : label j ≠ a := (Finset.mem_filter.mp hj).2
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have next_label : label k.succ = a := by
        by_contra not_label
        have bound := maximal k.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_label⟩)
        exact (not_le_of_gt k.castSucc_lt_succ) bound
      exact ⟨k.succ, next_label, by rwa [finRotate_symm_succ]⟩
    · exact ⟨0, at_zero, by rwa [finRotate_symm_zero]⟩
  · let same := Finset.univ.filter (fun i => label i = a)
    have nonempty : same.Nonempty := by
      obtain ⟨i, hi⟩ := visited
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨j, hj, minimal⟩ := Finset.exists_min_image same id nonempty
    have at_j : label j = a := (Finset.mem_filter.mp hj).2
    have nonzero : j ≠ 0 := fun equal => at_zero (equal ▸ at_j)
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero nonzero
    have previous_other : label k.castSucc ≠ a := by
      intro previous_label
      have bound := minimal k.castSucc
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, previous_label⟩)
      exact (not_le_of_gt k.castSucc_lt_succ) bound
    exact ⟨k.succ, at_j, by rwa [finRotate_symm_succ]⟩

theorem cyclic_label_card_le_changes {α : Type*} [DecidableEq α] {n : ℕ}
    (label : Fin (n + 1) → α) (nonconstant : ∃ i j, label i ≠ label j) :
    (Finset.univ.image label).card ≤
      (Finset.univ.filter (fun i => label ((finRotate (n + 1)).symm i) ≠ label i)).card := by
  classical
  let changes := Finset.univ.filter
    (fun i => label ((finRotate (n + 1)).symm i) ≠ label i)
  have included : Finset.univ.image label ⊆ changes.image label := by
    intro a ha
    obtain ⟨i, _member, at_i⟩ := Finset.mem_image.mp ha
    obtain ⟨j, k, different⟩ := nonconstant
    have outside : ∃ l, label l ≠ a := by
      by_cases hj : label j = a
      · exact ⟨k, fun hk => different (hj.trans hk.symm)⟩
      · exact ⟨j, hj⟩
    obtain ⟨l, at_l, previous⟩ := exists_cyclic_label_entry label a ⟨i, at_i⟩ outside
    exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by rwa [at_l]⟩, at_l⟩
  exact (Finset.card_le_card included).trans Finset.card_image_le

theorem exists_pair_mem_cover_of_card_le_two {α : Type*} (s : Finset α)
    (nonempty : s.Nonempty) (small : s.card ≤ 2) :
    ∃ a ∈ s, ∃ b ∈ s, ∀ x ∈ s, x = a ∨ x = b := by
  classical
  obtain ⟨a, ha⟩ := nonempty
  have erased_small : (s.erase a).card ≤ 1 := by
    rw [Finset.card_erase_of_mem ha]
    omega
  by_cases remains : (s.erase a).Nonempty
  · obtain ⟨b, hb⟩ := remains
    refine ⟨a, ha, b, (Finset.mem_erase.mp hb).2, ?_⟩
    intro x hx
    by_cases same : x = a
    · exact Or.inl same
    · exact Or.inr (Finset.card_le_one.mp erased_small x (Finset.mem_erase.mpr ⟨same, hx⟩) b hb)
  · refine ⟨a, ha, a, ha, ?_⟩
    intro x hx
    by_cases same : x = a
    · exact Or.inl same
    · exact (remains ⟨x, Finset.mem_erase.mpr ⟨same, hx⟩⟩).elim

end Unfoldings
