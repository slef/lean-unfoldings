module

public import Unfoldings.Combinatorics.LabelChanges
public import Unfoldings.Topology.CyclicLabels

/-! Removing adjacent positions from a cycle leaves one ordered path. -/

@[expose] public section

namespace Unfoldings

theorem eq_of_finRotate_invariant {A : Type*} {n : ℕ} (label : Fin (n + 1) → A)
    (invariant : ∀ i, label i = label (finRotate (n + 1) i)) (i j : Fin (n + 1)) :
    label i = label j := by
  by_contra different
  obtain ⟨k, here, prior⟩ := exists_cyclic_label_entry label (label i)
    ⟨i, rfl⟩ ⟨j, Ne.symm different⟩
  have consistent := invariant ((finRotate (n + 1)).symm k)
  rw [Equiv.apply_symm_apply] at consistent
  exact prior (consistent.trans here)

theorem finRotate_ne_of_three_le {n : ℕ} (large : 3 ≤ n + 1) (i : Fin (n + 1)) :
    finRotate (n + 1) i ≠ i := by
  intro equal
  rw [finRotate_apply] at equal
  have zero : (1 : Fin (n + 1)) = 0 := add_left_cancel (equal.trans (add_zero i).symm)
  have val := congrArg Fin.val zero
  simp only [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega), Fin.val_zero] at val
  omega

theorem finRotate_twice_ne_of_three_le {n : ℕ} (large : 3 ≤ n + 1) (i : Fin (n + 1)) :
    finRotate (n + 1) (finRotate (n + 1) i) ≠ i := by
  intro equal
  simp only [finRotate_apply, add_assoc] at equal
  have zero : (1 : Fin (n + 1)) + 1 = 0 := add_left_cancel (equal.trans (add_zero i).symm)
  have val := congrArg Fin.val zero
  simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
    Nat.mod_eq_of_lt (show 1 + 1 < n + 1 by omega), Fin.val_zero] at val
  omega

/-- A label that is constant along every surviving edge after removing two
consecutive cyclic positions is constant on the surviving path. -/
theorem eq_of_finRotate_invariant_away_from_pair {A : Type*} {n : ℕ} (large : 3 ≤ n + 1)
    (label : Fin (n + 1) → A) (a : Fin (n + 1))
    (invariant : ∀ i, i ≠ a → i ≠ finRotate (n + 1) a →
      finRotate (n + 1) i ≠ a → finRotate (n + 1) i ≠ finRotate (n + 1) a →
      label i = label (finRotate (n + 1) i))
    {i j : Fin (n + 1)} (ia : i ≠ a) (ib : i ≠ finRotate (n + 1) a)
    (ja : j ≠ a) (jb : j ≠ finRotate (n + 1) a) :
    label i = label j := by
  classical
  let next := finRotate (n + 1)
  let b := next a
  let before := next.symm a
  let after := next b
  have ba : b ≠ a := finRotate_ne_of_three_le large a
  have after_a : after ≠ a := finRotate_twice_ne_of_three_le large a
  have after_b : after ≠ b := finRotate_ne_of_three_le large b
  have before_a : before ≠ a := fun h => ba (by
    have eq := congrArg next h
    rw [next.apply_symm_apply] at eq
    exact eq.symm)
  have before_b : before ≠ b := fun h => after_a (by
    have eq := congrArg next h
    rw [next.apply_symm_apply] at eq
    exact eq.symm)
  let fill (i : Fin (n + 1)) :=
    if i = a then label before else if i = b then label after else label i
  have step (k : Fin (n + 1)) (ka : k ≠ a) : fill k = fill (next k) := by
    by_cases kb : k = b
    · subst k
      change fill b = fill after
      simp only [fill, ite_eq_right ba, ite_eq_right after_a, ite_eq_right after_b, ite_true]
    · by_cases nk : next k = a
      · have eq : k = before := next.injective (nk.trans (next.apply_symm_apply a).symm)
        rw [nk, eq]
        simp only [fill, ite_eq_left rfl, ite_eq_right before_a, ite_eq_right before_b]
      · have nb : next k ≠ b := fun h => ka (next.injective h)
        simp only [fill, ite_eq_right ka, ite_eq_right kb, ite_eq_right nk, ite_eq_right nb]
        exact invariant k ka kb nk nb
  have full (k : Fin (n + 1)) : fill k = fill (next k) := by
    by_cases at_a : fill a = fill b
    · by_cases ka : k = a
      · exact ka.symm ▸ at_a
      · exact step k ka
    · have changes : (Finset.univ.filter fun k => fill k ≠ fill (next k)) = {a} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun d => Classical.byContradiction (fun neq => d (step k neq)),
          fun eq => eq.symm ▸ at_a⟩
      exact (card_label_changes_ne_one next fill (by rw [changes, Finset.card_singleton])).elim
  change i ≠ b at ib
  change j ≠ b at jb
  have same := eq_of_finRotate_invariant fill full i j
  simpa only [fill, ite_eq_right ia, ite_eq_right ib, ite_eq_right ja, ite_eq_right jb] using same

end Unfoldings
