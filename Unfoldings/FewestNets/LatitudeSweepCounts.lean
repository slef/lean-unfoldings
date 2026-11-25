module

public import Unfoldings.FewestNets.LatitudeMidpointMerge
public import Mathlib.Order.Interval.Finset.Fin

/-! At each midpoint advance, each row's current index counts its earlier edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

variable {n total : ℕ} (rank : Fin n → Fin total)

/-- How many of this row's edges have been advanced before a given step. -/
def rowProgress (stage : ℕ) : ℕ :=
  (Finset.univ.filter fun k => (rank k).val < stage).card

theorem rowProgress_mono : Monotone (rowProgress rank) := by
  intro a b ordered
  apply Finset.card_le_card
  intro k member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
  exact member.trans_le ordered

theorem rowProgress_le (stage : ℕ) : rowProgress rank stage ≤ n := by
  simpa only [rowProgress, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le Finset.univ (fun k => (rank k).val < stage)

theorem rowProgress_zero : rowProgress rank 0 = 0 := by
  simp [rowProgress]

theorem rowProgress_end : rowProgress rank total = n := by
  have all : (Finset.univ.filter fun k : Fin n => (rank k).val < total) = Finset.univ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, (rank k).isLt]
  rw [rowProgress, all, Finset.card_univ, Fintype.card_fin]

/-- Earlier edges form exactly a prefix, even when the other row was advanced
several times since the previous edge. -/
theorem earlier_iff_lt_rowProgress (mono : StrictMono rank) (stage : ℕ) (k : Fin n) :
    (rank k).val < stage ↔ k.val < rowProgress rank stage := by
  constructor
  · intro before
    have contained : Finset.Iic k ⊆ Finset.univ.filter (fun j => (rank j).val < stage) := by
      intro j member
      rw [Finset.mem_Iic] at member
      have earlier : (rank j).val ≤ (rank k).val := mono.monotone member
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, earlier.trans_lt before⟩
    have count := Finset.card_le_card contained
    rw [Fin.card_Iic] at count
    unfold rowProgress
    omega
  · intro before
    by_contra! later
    have contained : Finset.univ.filter (fun j => (rank j).val < stage) ⊆ Finset.Iio k := by
      intro j member
      apply Finset.mem_Iio.mpr
      exact mono.lt_iff_lt.mp ((Finset.mem_filter.mp member).2.trans_le later)
    have count := Finset.card_le_card contained
    rw [Fin.card_Iio] at count
    unfold rowProgress at before
    omega

/-- One step leaves a row's index fixed when its ordered edge belongs to the other row. -/
theorem rowProgress_succ_eq_of_no_edge (stage : ℕ) (next : ∀ k, (rank k).val ≠ stage) :
    rowProgress rank (stage + 1) = rowProgress rank stage := by
  unfold rowProgress
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have different := next k
  omega

/-- A row index increments by one precisely at its actual next edge. -/
theorem rowProgress_succ_eq_of_edge (injective : Function.Injective rank) (k : Fin n) :
    rowProgress rank ((rank k).val + 1) = rowProgress rank (rank k).val + 1 := by
  classical
  have insert_edge :
      (Finset.univ.filter fun j : Fin n => (rank j).val < (rank k).val + 1) =
        insert k (Finset.univ.filter fun j : Fin n => (rank j).val < (rank k).val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    have equal : (rank j).val = (rank k).val ↔ j = k :=
      ⟨fun h => injective (Fin.ext h), fun h => congrArg (fun i => (rank i).val) h⟩
    rw [← equal]
    omega
  rw [rowProgress, insert_edge, Finset.card_insert_of_notMem]
  · rfl
  · simp

end Unfoldings.FewestNets
