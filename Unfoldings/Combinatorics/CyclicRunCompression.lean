module

public import Unfoldings.Topology.CyclicLabels
public import Mathlib.Data.Finset.Sort

/-! Compress a cyclic list at the entries where its label changes. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {A : Type*} {n : ℕ} (label : Fin (n + 1) → A)

open Classical in
/-- A run begins exactly where the preceding label differs. -/
def cyclicRunStarts : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => label ((finRotate (n + 1)).symm i) ≠ label i

@[simp] theorem mem_cyclicRunStarts (i : Fin (n + 1)) :
    i ∈ cyclicRunStarts label ↔ label ((finRotate (n + 1)).symm i) ≠ label i := by
  classical
  simp [cyclicRunStarts]

private theorem cyclic_predecessor_val {i : Fin (n + 1)} (nonzero : i ≠ 0) :
    ((finRotate (n + 1)).symm i).val + 1 = i.val := by
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero nonzero
  rw [finRotate_symm_succ]
  rfl

theorem eq_of_no_cyclicRunStarts_between {a b : Fin (n + 1)} (ab : a ≤ b)
    (same : ∀ i, a < i → i ≤ b → i ∉ cyclicRunStarts label) : label b = label a := by
  classical
  by_contra different
  let bad := Finset.univ.filter fun i : Fin (n + 1) => a ≤ i ∧ i ≤ b ∧ label i ≠ label a
  have nonempty : bad.Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ab, le_rfl, different⟩⟩
  let j := bad.min' nonempty
  obtain ⟨aj, jb, not_label⟩ := (Finset.mem_filter.mp (bad.min'_mem nonempty)).2
  have first : a < j := lt_of_le_of_ne aj (fun h => not_label (congrArg label h.symm))
  have nonzero : j ≠ 0 := by
    intro h
    rw [h] at first
    exact (not_lt_of_ge (Fin.zero_le _)) first
  let k := (finRotate (n + 1)).symm j
  have prev := cyclic_predecessor_val nonzero
  change k.val + 1 = j.val at prev
  have kj : k < j := by omega
  have ak : a ≤ k := by omega
  have at_prev : label k = label a := by
    by_contra wrong
    have member : k ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ak, kj.le.trans jb, wrong⟩
    exact (not_lt_of_ge (bad.min'_le k member)) kj
  exact same j first jb ((mem_cyclicRunStarts label j).mpr (at_prev ▸ Ne.symm not_label))

variable {m : ℕ} (count : (cyclicRunStarts label).card = m + 1)

/-- The start indices in increasing cyclic order, starting from the least change. -/
def cyclicRunStart : Fin (m + 1) ↪o Fin (n + 1) :=
  (cyclicRunStarts label).orderEmbOfFin count

theorem cyclicRunStart_mem (i : Fin (m + 1)) :
    cyclicRunStart label count i ∈ cyclicRunStarts label :=
  Finset.orderEmbOfFin_mem _ _ _

theorem exists_cyclicRunStart_of_mem {i : Fin (n + 1)} (hi : i ∈ cyclicRunStarts label) :
    ∃ j, cyclicRunStart label count j = i := by
  change i ∈ Set.range ((cyclicRunStarts label).orderEmbOfFin count)
  rwa [Finset.range_orderEmbOfFin]

/-- Every original label is present at some run start. -/
theorem exists_cyclicRunStart_label (i : Fin (n + 1)) :
    ∃ j, label (cyclicRunStart label count j) = label i := by
  let a := label i
  let t := cyclicRunStart label count 0
  have changes := (mem_cyclicRunStarts label t).mp (cyclicRunStart_mem label count 0)
  have outside : ∃ j, label j ≠ a := by
    by_cases equal : label t = a
    · exact ⟨(finRotate (n + 1)).symm t, fun h => changes (h.trans equal.symm)⟩
    · exact ⟨t, equal⟩
  obtain ⟨k, equal, previous⟩ := exists_cyclic_label_entry label a ⟨i, rfl⟩ outside
  obtain ⟨j, rfl⟩ := exists_cyclicRunStart_of_mem label count
    ((mem_cyclicRunStarts label k).mpr (fun h => previous (h.trans equal)))
  exact ⟨j, equal⟩

/-- The label immediately before the next start is the current run's label,
including the run that crosses the end of the index list. -/
theorem label_predecessor_cyclicRunStart (i : Fin (m + 1)) :
    label ((finRotate (n + 1)).symm (cyclicRunStart label count (finRotate (m + 1) i))) =
      label (cyclicRunStart label count i) := by
  let start := cyclicRunStart label count
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [finRotate_last]
    let head := start 0
    let tail := start (Fin.last m)
    let last := Fin.last n
    have no_after {j : Fin (n + 1)} (later : tail < j) : j ∉ cyclicRunStarts label := by
      intro member
      obtain ⟨k, rfl⟩ := exists_cyclicRunStart_of_mem label count member
      exact (not_lt_of_ge (start.monotone (Fin.le_last k))) later
    have no_before {j : Fin (n + 1)} (earlier : j < head) : j ∉ cyclicRunStarts label := by
      intro member
      obtain ⟨k, rfl⟩ := exists_cyclicRunStart_of_mem label count member
      exact (not_lt_of_ge (start.monotone (Fin.zero_le k))) earlier
    have finish : label last = label tail :=
      eq_of_no_cyclicRunStarts_between label (Fin.le_last tail) (fun _ hj _ => no_after hj)
    change label ((finRotate (n + 1)).symm head) = label tail
    by_cases zero : head = 0
    · rw [zero, finRotate_symm_zero]
      exact finish
    · let before := (finRotate (n + 1)).symm head
      have prev := cyclic_predecessor_val zero
      change before.val + 1 = head.val at prev
      have first : (0 : Fin (n + 1)) < head := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm zero)
      have begin : label last = label 0 := by
        have same := not_not.mp (fun h => no_before first ((mem_cyclicRunStarts label 0).mpr h))
        rwa [finRotate_symm_zero] at same
      have across : label before = label 0 :=
        eq_of_no_cyclicRunStarts_between label (Fin.zero_le before)
          (fun j _ bound => no_before (by omega))
      exact across.trans (begin.symm.trans finish)
  · rw [show finRotate (m + 1) k.castSucc = k.succ from finRotate_of_lt k.isLt]
    let a := start k.castSucc
    let b := start k.succ
    have ab : a < b := start.strictMono k.castSucc_lt_succ
    have bne : b ≠ 0 := fun h => (not_lt_of_ge (Fin.zero_le a)) (h ▸ ab)
    let before := (finRotate (n + 1)).symm b
    have prev := cyclic_predecessor_val bne
    change before.val + 1 = b.val at prev
    have a_before : a ≤ before := by omega
    have before_b : before < b := by omega
    change label before = label a
    apply eq_of_no_cyclicRunStarts_between label a_before
    intro j aj jb member
    obtain ⟨l, rfl⟩ := exists_cyclicRunStart_of_mem label count member
    have kl : k.castSucc < l := start.lt_iff_lt.mp aj
    have lk : l < k.succ := start.lt_iff_lt.mp (jb.trans_lt before_b)
    change k.val < l.val at kl
    change l.val < k.val + 1 at lk
    omega

end Unfoldings
