module

public import Unfoldings.Combinatorics.CyclicAdjacentRemoval
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic

/-! Move the start of a cyclically ordered list of directions to a chosen period. -/

@[expose] public section

namespace Unfoldings

theorem add_finRotate_comm {n : ℕ} (i start : Fin (n + 1)) :
    finRotate (n + 1) i + start = finRotate (n + 1) (i + start) := by
  simp only [finRotate_apply]
  ac_rfl

/-- An increasing lift of cyclic directions can be rotated so that the
entire ordered list lies in the first period, with the same separation. -/
theorem exists_cyclic_heading_reindex {n : ℕ} (H : Fin (n + 1) → ℝ) {eta period : ℝ}
    (positive : 0 < eta)
    (range : ∀ i, 0 ≤ H i ∧ H i < 2 * period)
    (gap : ∀ i j, i < j → eta ≤ H j - H i ∧ H j - H i ≤ period - eta) :
    ∃ (start : Fin (n + 1)) (h : Fin (n + 1) → ℝ),
      (∀ i, 0 ≤ h i ∧ h i < period) ∧
      (∀ i j, i < j → eta ≤ h j - h i ∧ h j - h i ≤ period - eta) ∧
      (∀ i, h i = H (i + start) ∨ h i + period = H (i + start)) := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun i => period ≤ H i
  by_cases any : S.Nonempty
  · let start := S.min' any
    have at_start : period ≤ H start :=
      (Finset.mem_filter.mp (S.min'_mem any)).2
    have bottom (i : Fin (n + 1)) (before : i < start) : H i < period := by
      by_contra not_low
      have member : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt not_low⟩
      exact (not_lt_of_ge (S.min'_le _ member)) before
    have top (i : Fin (n + 1)) (after : start ≤ i) : period ≤ H i := by
      rcases lt_or_eq_of_le after with before | rfl
      · linarith only [at_start, positive, (gap _ _ before).1]
      · exact at_start
    let shift (i : Fin (n + 1)) := i + start
    let h (i : Fin (n + 1)) :=
      if n + 1 ≤ i.val + start.val then H (shift i) else H (shift i) - period
    have index (i : Fin (n + 1)) :
        (shift i).val =
          if n + 1 ≤ i.val + start.val then i.val + start.val - (n + 1)
          else i.val + start.val := Fin.val_add_eq_ite _ _
    have too_large (i : Fin (n + 1)) (wrap : n + 1 ≤ i.val + start.val) :
        shift i < start := by
      have ix := index i
      rw [ite_eq_left wrap] at ix
      omega
    have small (i : Fin (n + 1)) (wrap : ¬ n + 1 ≤ i.val + start.val) :
        start ≤ shift i := by
      have ix := index i
      rw [ite_eq_right wrap] at ix
      omega
    refine ⟨start, h, ?_, ?_, ?_⟩
    · intro i
      by_cases wrap : n + 1 ≤ i.val + start.val
      · rw [show h i = H (shift i) from ite_eq_left wrap]
        exact ⟨(range _).1, bottom _ (too_large i wrap)⟩
      · rw [show h i = H (shift i) - period from ite_eq_right wrap]
        exact ⟨sub_nonneg.mpr (top _ (small i wrap)), by linarith [(range (shift i)).2]⟩
    · intro i j ij
      have ix := index i
      have jx := index j
      by_cases iwrap : n + 1 ≤ i.val + start.val
      · have jwrap : n + 1 ≤ j.val + start.val := by omega
        rw [ite_eq_left iwrap] at ix
        rw [ite_eq_left jwrap] at jx
        rw [show h i = H (shift i) from ite_eq_left iwrap,
          show h j = H (shift j) from ite_eq_left jwrap]
        exact gap _ _ (by omega)
      · rw [ite_eq_right iwrap] at ix
        rw [show h i = H (shift i) - period from ite_eq_right iwrap]
        by_cases jwrap : n + 1 ≤ j.val + start.val
        · rw [show h j = H (shift j) from ite_eq_left jwrap]
          have reverse : shift j < shift i := (too_large j jwrap).trans_le (small i iwrap)
          have bound := gap _ _ reverse
          constructor <;> linarith [bound.1, bound.2]
        · rw [ite_eq_right jwrap] at jx
          rw [show h j = H (shift j) - period from ite_eq_right jwrap]
          have bound := gap (shift i) (shift j) (by omega)
          constructor <;> linarith [bound.1, bound.2]
    · intro i
      by_cases wrap : n + 1 ≤ i.val + start.val
      · exact Or.inl (ite_eq_left wrap)
      · right
        rw [show h i = H (shift i) - period from ite_eq_right wrap, sub_add_cancel]
  · refine ⟨0, H, fun i => ⟨(range i).1, ?_⟩, gap, ?_⟩
    · by_contra not_low
      exact any ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt not_low⟩⟩
    · intro i
      simp

end Unfoldings
