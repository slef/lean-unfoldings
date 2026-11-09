module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.UnitInterval
public meta import Lean.Elab.Tactic.Omega

/-!
# Subdividing a finite closed interval cover

Sort all covering interval endpoints, together with zero and one. No covering
endpoint lies strictly between consecutive subdivision points. Any interval
containing their midpoint therefore contains the whole subdivision interval.
The number of pieces is at most twice the size of the cover plus one.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem orderEmbOfFin_no_between {α : Type*} [LinearOrder α] (s : Finset α)
    {n : ℕ} (cardinality : s.card = n + 1) (i : Fin n) {x : α} (member : x ∈ s) :
    ¬ (s.orderEmbOfFin cardinality i.castSucc < x ∧
      x < s.orderEmbOfFin cardinality i.succ) := by
  obtain ⟨j, equal⟩ := (s.range_orderEmbOfFin cardinality).ge member
  rw [← equal]
  intro between
  have first : i.castSucc < j := (s.orderEmbOfFin cardinality).lt_iff_lt.mp between.1
  have last : j < i.succ := (s.orderEmbOfFin cardinality).lt_iff_lt.mp between.2
  have first' : i.val < j.val := first
  have last' : j.val < i.val + 1 := last
  omega

theorem exists_finite_interval_subdivision {ι : Type*} [Fintype ι]
    (lower upper : ι → unitInterval)
    (cover : ∀ t : unitInterval, ∃ i, lower i ≤ t ∧ t ≤ upper i) :
    ∃ n : ℕ, n ≤ 2 * Fintype.card ι + 1 ∧
      ∃ time : Fin (n + 1) → unitInterval, StrictMono time ∧ time 0 = 0 ∧
        time (Fin.last n) = 1 ∧ ∃ piece : Fin n → ι,
          ∀ i, Set.Icc (time i.castSucc) (time i.succ) ⊆
            Set.Icc (lower (piece i)) (upper (piece i)) := by
  classical
  let s : Finset unitInterval := insert 0 (insert 1
    (Finset.univ.image lower ∪ Finset.univ.image upper))
  have zero_mem : (0 : unitInterval) ∈ s := Finset.mem_insert_self _ _
  have one_mem : (1 : unitInterval) ∈ s := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have lo_mem (i : ι) : lower i ∈ s :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem lower (Finset.mem_univ i))))
  have hi_mem (i : ι) : upper i ∈ s :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image_of_mem upper (Finset.mem_univ i))))
  have two : 2 ≤ s.card := by
    have included : ({0, 1} : Finset unitInterval) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with equal | member
      · exact equal ▸ zero_mem
      · exact (Finset.mem_singleton.mp member) ▸ one_mem
    simpa using Finset.card_le_card included
  let n := s.card - 1
  have cardinality : s.card = n + 1 := by omega
  let time := s.orderEmbOfFin cardinality
  have start : time 0 = 0 := by
    obtain ⟨j, equal⟩ := (s.range_orderEmbOfFin cardinality).ge zero_mem
    apply le_antisymm
    · exact (time.monotone (Fin.zero_le j)).trans_eq equal
    · exact (time 0).property.1
  have finish : time (Fin.last n) = 1 := by
    obtain ⟨j, equal⟩ := (s.range_orderEmbOfFin cardinality).ge one_mem
    apply le_antisymm
    · exact (time (Fin.last n)).property.2
    · exact equal.symm.trans_le (time.monotone (Fin.le_last j))
  have pieces (i : Fin n) : ∃ k : ι,
      Set.Icc (time i.castSucc) (time i.succ) ⊆ Set.Icc (lower k) (upper k) := by
    have ordered : time i.castSucc < time i.succ := time.strictMono Fin.castSucc_lt_succ
    obtain ⟨middle, first, last⟩ := exists_between ordered
    obtain ⟨k, low, high⟩ := cover middle
    have left : lower k ≤ time i.castSucc := by
      by_contra wrong
      exact orderEmbOfFin_no_between s cardinality i (lo_mem k)
        ⟨lt_of_not_ge wrong, low.trans_lt last⟩
    have right : time i.succ ≤ upper k := by
      by_contra wrong
      exact orderEmbOfFin_no_between s cardinality i (hi_mem k)
        ⟨first.trans_le high, lt_of_not_ge wrong⟩
    exact ⟨k, fun _ h => ⟨left.trans h.1, h.2.trans right⟩⟩
  choose piece inside using pieces
  have bound : s.card ≤ 2 * Fintype.card ι + 2 := by
    have inserts := (Finset.card_insert_le 0 (insert 1
      (Finset.univ.image lower ∪ Finset.univ.image upper))).trans
      (Nat.add_le_add_right (Finset.card_insert_le 1 _) 1)
    have union := Finset.card_union_le (Finset.univ.image lower) (Finset.univ.image upper)
    have low := Finset.card_image_le (s := Finset.univ) (f := lower)
    have high := Finset.card_image_le (s := Finset.univ) (f := upper)
    rw [Finset.card_univ] at low high
    change s.card ≤ _ at inserts
    omega
  exact ⟨n, by omega, time, time.strictMono, start, finish, piece, inside⟩

end Unfoldings
