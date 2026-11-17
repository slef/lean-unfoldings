module

public import Unfoldings.Topology.FiniteIntervalPartition
public import Mathlib.Analysis.Convex.Topology

/-! Order finite partitions of a positive closed interval without changing original parameters. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Normalize a genuine nonnegative interval by an order equivalence. -/
def positiveIccOrderIso {T : ℝ} (positive : 0 < T) : Set.Icc (0 : ℝ) T ≃o unitInterval where
  toFun t := ⟨t.val / T, div_nonneg t.property.1 positive.le,
    (div_le_one positive).mpr t.property.2⟩
  invFun u := ⟨u.val * T, mul_nonneg u.property.1 positive.le,
    mul_le_of_le_one_left positive.le u.property.2⟩
  left_inv t := Subtype.ext (div_mul_cancel₀ t.val positive.ne')
  right_inv u := Subtype.ext (mul_div_cancel_right₀ u.val positive.ne')
  map_rel_iff' := div_le_div_iff_of_pos_right positive

/-- Exact ordering of all original pieces of a positive closed interval, including both
endpoints and every join. Original interval parameters are retained in the conclusion. -/
theorem exists_ordered_positive_Icc_partition {ι : Type*} [Finite ι] {T : ℝ}
    (positive : 0 < T) (lower upper : ι → Set.Icc (0 : ℝ) T)
    (genuine : ∀ i, lower i < upper i)
    (separated : Pairwise (fun i j => Disjoint (Set.Ioo (lower i) (upper i))
      (Set.Ioo (lower j) (upper j))))
    (cover : ∀ t, ∃ i, lower i ≤ t ∧ t ≤ upper i) :
    ∃ n : ℕ, ∃ index : Fin (n + 1) ≃ ι,
      StrictMono (fun i => lower (index i)) ∧
        (lower (index 0)).val = 0 ∧ (upper (index (Fin.last n))).val = T ∧
          ∀ i : Fin n, upper (index i.castSucc) = lower (index i.succ) := by
  let e := positiveIccOrderIso positive
  have apart : Pairwise (fun i j => Disjoint (Set.Ioo (e (lower i)) (e (upper i)))
      (Set.Ioo (e (lower j)) (e (upper j)))) := by
    intro i j different
    apply Set.disjoint_left.mpr
    intro u first last
    exact Set.disjoint_left.mp (separated different)
      (show e.symm u ∈ Set.Ioo (lower i) (upper i) from
        ⟨(e.lt_iff_lt).mp (by simpa only [e.apply_symm_apply] using first.1),
          (e.lt_iff_lt).mp (by simpa only [e.apply_symm_apply] using first.2)⟩)
      (show e.symm u ∈ Set.Ioo (lower j) (upper j) from
        ⟨(e.lt_iff_lt).mp (by simpa only [e.apply_symm_apply] using last.1),
          (e.lt_iff_lt).mp (by simpa only [e.apply_symm_apply] using last.2)⟩)
  have covered (u : unitInterval) : ∃ i, e (lower i) ≤ u ∧ u ≤ e (upper i) := by
    obtain ⟨i, first, last⟩ := cover (e.symm u)
    exact ⟨i, by simpa only [e.apply_symm_apply] using e.monotone first,
      by simpa only [e.apply_symm_apply] using e.monotone last⟩
  obtain ⟨n, index, strict, first, last, joins⟩ := exists_ordered_interval_partition
    (fun i => e (lower i)) (fun i => e (upper i)) (fun i => e.strictMono (genuine i)) apart covered
  have zero : e ⟨0, le_rfl, positive.le⟩ = 0 := Subtype.ext (zero_div T)
  have one : e ⟨T, positive.le, le_rfl⟩ = 1 := Subtype.ext (div_self positive.ne')
  refine ⟨n, index, fun i j before => (e.lt_iff_lt).mp (strict before), ?_, ?_, ?_⟩
  · exact congrArg Subtype.val (e.injective (first.trans zero.symm))
  · exact congrArg Subtype.val (e.injective (last.trans one.symm))
  · exact fun i => e.injective (joins i)

end Unfoldings
