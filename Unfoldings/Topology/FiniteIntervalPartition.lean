module

public import Unfoldings.Topology.FiniteIntervalCover
public import Mathlib.Order.Interval.Set.Disjoint

/-! Nondegenerate finite closed interval partitions have a unique increasing order with no gaps. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {ι : Type*} (lower upper : ι → unitInterval)
  (positive : ∀ i, lower i < upper i)
  (separated : Pairwise (fun i j => Disjoint (Set.Ioo (lower i) (upper i))
    (Set.Ioo (lower j) (upper j))))

include positive separated in
/-- Distinct closed partition intervals meet in at most their ordered common endpoint. -/
theorem interval_partition_order {i j : ι} (before : lower i < lower j) :
    upper i ≤ lower j := by
  by_contra wrong
  have different : i ≠ j := fun same => before.ne (congrArg lower same)
  obtain ⟨x, first, last⟩ := exists_between (lt_min (lt_of_not_ge wrong) (positive j))
  exact Set.disjoint_left.mp (separated different)
    ⟨before.trans first, last.trans_le (min_le_left _ _)⟩
    ⟨first, last.trans_le (min_le_right _ _)⟩

include positive separated in
/-- Lower endpoints cannot repeat in a nondegenerate partition. -/
theorem interval_partition_lower_injective : Function.Injective lower := by
  intro i j equal
  by_contra different
  have bound : lower i < min (upper i) (upper j) :=
    lt_min (positive i) (equal ▸ positive j)
  obtain ⟨x, first, last⟩ := exists_between bound
  exact Set.disjoint_left.mp (separated different)
    ⟨first, last.trans_le (min_le_left _ _)⟩
    ⟨equal ▸ first, last.trans_le (min_le_right _ _)⟩

include positive separated in
/-- Increasing lower endpoints also order the upper endpoints. -/
theorem interval_partition_upper_order {i j : ι} (before : lower i ≤ lower j) :
    upper i ≤ upper j := by
  rcases lt_or_eq_of_le before with strict | equal
  · exact (interval_partition_order lower upper positive separated strict).trans (positive j).le
  · exact le_of_eq (congrArg upper
      (interval_partition_lower_injective lower upper positive separated equal))

variable [Finite ι]

include positive separated in
/-- All original intervals occur once, in increasing order, with exact shared endpoints. -/
theorem exists_ordered_interval_partition
    (cover : ∀ t : unitInterval, ∃ i, lower i ≤ t ∧ t ≤ upper i) :
    ∃ n : ℕ, ∃ index : Fin (n + 1) ≃ ι,
      StrictMono (fun i => lower (index i)) ∧ lower (index 0) = 0 ∧
        upper (index (Fin.last n)) = 1 ∧
          ∀ i : Fin n, upper (index i.castSucc) = lower (index i.succ) := by
  classical
  let := Fintype.ofFinite ι
  let s := Finset.univ.image lower
  have injective := interval_partition_lower_injective lower upper positive separated
  let chosen : ι ≃ s := Equiv.ofBijective
    (fun i => ⟨lower i, Finset.mem_image_of_mem lower (Finset.mem_univ i)⟩) ⟨by
      intro i j same
      exact injective (congrArg Subtype.val same), by
      rintro ⟨x, member⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
      exact ⟨i, rfl⟩⟩
  obtain ⟨k, _at_zero⟩ := cover 0
  have present : s.Nonempty := ⟨lower k, Finset.mem_image_of_mem lower (Finset.mem_univ k)⟩
  let n := s.card - 1
  have cardinality : s.card = n + 1 := by have := present.card_pos; omega
  let index : Fin (n + 1) ≃ ι := (s.orderIsoOfFin cardinality).toEquiv.trans chosen.symm
  have position (i : Fin (n + 1)) : lower (index i) = s.orderEmbOfFin cardinality i :=
    congrArg Subtype.val (chosen.apply_symm_apply (s.orderIsoOfFin cardinality i))
  have strict : StrictMono (fun i => lower (index i)) := by
    intro i j before
    change lower (index i) < lower (index j)
    rw [position, position]
    exact (s.orderEmbOfFin cardinality).strictMono before
  have start : lower (index 0) = 0 := by
    obtain ⟨i, lo, _hi⟩ := cover 0
    apply le_antisymm
    · exact (strict.monotone (Fin.zero_le (index.symm i))).trans (by
        simpa only [Equiv.apply_symm_apply] using lo)
    · exact (lower (index 0)).property.1
  have finish : upper (index (Fin.last n)) = 1 := by
    obtain ⟨i, _lo, hi⟩ := cover 1
    have ordered := interval_partition_upper_order lower upper positive separated
      (strict.monotone (Fin.le_last (index.symm i)))
    rw [Equiv.apply_symm_apply] at ordered
    exact le_antisymm (upper (index (Fin.last n))).property.2 (hi.trans ordered)
  refine ⟨n, index, strict, start, finish, fun i => ?_⟩
  have ordered := interval_partition_order lower upper positive separated
    (strict (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
  apply le_antisymm ordered
  by_contra wrong
  obtain ⟨t, after, before⟩ := exists_between (lt_of_not_ge wrong)
  obtain ⟨k, lo, hi⟩ := cover t
  let j := index.symm k
  by_cases earlier : j ≤ i.castSucc
  · have bounded := interval_partition_upper_order lower upper positive separated
      (strict.monotone earlier)
    rw [Equiv.apply_symm_apply] at bounded
    exact (after.trans_le (hi.trans bounded)).false
  · have later : i.succ ≤ j := by
      change i.val + 1 ≤ j.val
      have : i.val < j.val := lt_of_not_ge earlier
      omega
    have bounded := strict.monotone later
    rw [Equiv.apply_symm_apply] at bounded
    exact (before.trans_le (bounded.trans lo)).false

end Unfoldings
