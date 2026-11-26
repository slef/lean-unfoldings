module

public import Unfoldings.FewestNets.LatitudeRingsSweep
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.FinRange

/-! Execute the exact formal latitude sweep using rational midpoint order. -/

@[expose] public section

namespace Unfoldings.FewestNets.LatitudeRings

open Real

/-- The scaled longitude and the upper-first tie rule are both executable. -/
def rationalMidpointKey {m n : ℕ} : Fin m ⊕ Fin n → ℚ ×ₗ ℕ
  | .inl i => toLex (((2 * i.val + 1 : ℕ) : ℚ) / m, 1)
  | .inr j => toLex (((2 * j.val + 1 : ℕ) : ℚ) / n, 0)

private theorem midpointKey_form {m n : ℕ} (s : Fin m ⊕ Fin n) :
    ofLex (midpointKey s) =
      (π * ((ofLex (rationalMidpointKey s)).1 : ℝ), (ofLex (rationalMidpointKey s)).2) := by
  cases s with
  | inl i =>
    change (rowMidpoint m i, 1) = (π * (((2 * i.val + 1 : ℕ) : ℚ) / m : ℚ), 1)
    congr 1
    unfold rowMidpoint
    push_cast
    ring
  | inr j =>
    change (rowMidpoint n j, 0) = (π * (((2 * j.val + 1 : ℕ) : ℚ) / n : ℚ), 0)
    congr 1
    unfold rowMidpoint
    push_cast
    ring

theorem rationalMidpointKey_le_iff {m n : ℕ} {s t : Fin m ⊕ Fin n} :
    rationalMidpointKey s ≤ rationalMidpointKey t ↔ midpointKey s ≤ midpointKey t := by
  let x := (ofLex (rationalMidpointKey s)).1
  let y := (ofLex (rationalMidpointKey t)).1
  have lt : π * (x : ℝ) < π * (y : ℝ) ↔ x < y := by
    constructor
    · intro h
      exact_mod_cast (lt_of_mul_lt_mul_left h pi_pos.le)
    · intro h
      exact mul_lt_mul_of_pos_left (by exact_mod_cast h) pi_pos
  rw [Prod.Lex.le_iff, Prod.Lex.le_iff, midpointKey_form s, midpointKey_form t]
  have less :
      π * ((ofLex (rationalMidpointKey s)).1 : ℝ) < π * ((ofLex (rationalMidpointKey t)).1 : ℝ) ↔
        (ofLex (rationalMidpointKey s)).1 < (ofLex (rationalMidpointKey t)).1 := lt
  simp only [mul_right_inj' pi_ne_zero, Rat.cast_inj, less]

theorem rationalMidpointKey_lt_iff {m n : ℕ} {s t : Fin m ⊕ Fin n} :
    rationalMidpointKey s < rationalMidpointKey t ↔ midpointKey s < midpointKey t := by
  rw [lt_iff_not_ge, lt_iff_not_ge, rationalMidpointKey_le_iff]

/-- The apex index can be computed directly by counting opposing midpoints
strictly earlier than this advance. -/
def oppositeIndex {m n : ℕ} : Fin m ⊕ Fin n → ℕ
  | .inl i => (Finset.univ.filter fun j : Fin n =>
      rationalMidpointKey (.inr j : Fin m ⊕ Fin n) < rationalMidpointKey (.inl i : Fin m ⊕ Fin n)).card
  | .inr j => (Finset.univ.filter fun i : Fin m =>
      rationalMidpointKey (.inl i : Fin m ⊕ Fin n) < rationalMidpointKey (.inr j : Fin m ⊕ Fin n)).card

theorem oppositeIndex_inl_eq {m n : ℕ} (step : Fin (m + n) ≃ Fin m ⊕ Fin n)
    (sorted : StrictMono (midpointKey ∘ step)) (index : Fin (m + n))
    (i : Fin m) (at_i : step index = .inl i) :
    oppositeIndex (.inl i : Fin m ⊕ Fin n) = rowProgress (upperRank step) index.val := by
  rw [oppositeIndex, rowProgress]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rationalMidpointKey_lt_iff]
  have h := sorted.lt_iff_lt (a := upperRank step j) (b := index)
  simpa only [Function.comp_apply, upperRank, Equiv.apply_symm_apply, at_i, Fin.lt_def] using h

theorem oppositeIndex_inr_eq {m n : ℕ} (step : Fin (m + n) ≃ Fin m ⊕ Fin n)
    (sorted : StrictMono (midpointKey ∘ step)) (index : Fin (m + n))
    (j : Fin n) (at_j : step index = .inr j) :
    oppositeIndex (.inr j : Fin m ⊕ Fin n) = rowProgress (lowerRank step) index.val := by
  rw [oppositeIndex, rowProgress]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rationalMidpointKey_lt_iff]
  have h := sorted.lt_iff_lt (a := lowerRank step i) (b := index)
  simpa only [Function.comp_apply, lowerRank, Equiv.apply_symm_apply, at_j, Fin.lt_def] using h

/-- The computable list uses the same tie convention as the geometric sweep. -/
def checkedSweep (m n : ℕ) : List (Fin m ⊕ Fin n) :=
  (((List.finRange m).map (Sum.inl : Fin m → Fin m ⊕ Fin n)) ++
    (List.finRange n).map Sum.inr).mergeSort
      (fun x y => decide (rationalMidpointKey x ≤ rationalMidpointKey y))

private theorem checkedSweep_sorted (m n : ℕ) :
    (checkedSweep m n).Pairwise (fun x y => midpointKey x ≤ midpointKey y) := by
  have hs := List.pairwise_mergeSort
    (le := fun (x y : Fin m ⊕ Fin n) => decide (rationalMidpointKey x ≤ rationalMidpointKey y))
    (fun x y z h₁ h₂ => by simpa using (decide_eq_true_eq.mp h₁).trans (decide_eq_true_eq.mp h₂))
    (fun x y => by simpa using (le_total (rationalMidpointKey x) (rationalMidpointKey y)))
    (((List.finRange m).map (Sum.inl : Fin m → Fin m ⊕ Fin n)) ++ (List.finRange n).map Sum.inr)
  unfold checkedSweep
  exact hs.imp (fun (h : decide (rationalMidpointKey _ ≤ rationalMidpointKey _) = true) =>
    rationalMidpointKey_le_iff.mp (decide_eq_true_eq.mp h))

/-- The executable list is exactly the actual geometric order, including
when two advances have the same longitude. -/
theorem checkedSweep_eq (m n : ℕ) : checkedSweep m n = List.ofFn (sweepOrder m n) := by
  let before (x y : Fin m ⊕ Fin n) := midpointKey x ≤ midpointKey y
  have perm : List.Perm (checkedSweep m n) (List.ofFn (sweepOrder m n)) := by
    apply (List.mergeSort_perm _ _).trans
    apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
    · intro x
      constructor
      · intro _
        exact List.mem_ofFn.mpr ⟨(sweepOrder m n).symm x, (sweepOrder m n).apply_symm_apply x⟩
      · intro _
        cases x <;> simp
    · apply List.nodup_append.mpr
      exact ⟨(List.nodup_finRange m).map Sum.inl_injective, (List.nodup_finRange n).map Sum.inr_injective,
        by simp [List.disjoint_left]⟩
    · exact List.nodup_ofFn.mpr (sweepOrder m n).injective
  have ordered : (List.ofFn (sweepOrder m n)).Pairwise before := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj lt
    simpa only [List.getElem_ofFn, before, Function.comp_apply] using ((sweepOrder_sorted m n)
      (show (⟨i, by simpa using hi⟩ : Fin (m + n)) < ⟨j, by simpa using hj⟩ from lt)).le
  exact perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => midpointKey_injective (le_antisymm h₁ h₂))
    (checkedSweep_sorted m n) ordered

end Unfoldings.FewestNets.LatitudeRings
