module

public import Unfoldings.Topology.ChainSuffix
public import Unfoldings.Topology.PairedInvolutionExtension
public import Unfoldings.Topology.ChainTerminalUniqueness

/-! A proper interval in a connected finite pairing cycle has an exact complementary interval. -/

@[expose] public section

namespace PairedInvolutions.System

variable {X : Type*} [Finite X] (P : PairedInvolutions.System X)

/-- Complete a proper actual interval with the remaining original labeled intervals.
All joins, separation and coverage are derived from the original pairing cycle. -/
theorem exists_complementary_chain (connected : P.Connected) (free : ∀ x, P.mate x ≠ x)
    {n : ℕ} (c : P.Chain n) (not_closed : P.mate (P.turn c.last) ≠ c.first) :
    ∃ m : ℕ, ∃ d : P.Chain m,
      (∀ i j, c.point i ≠ d.point j ∧ c.point i ≠ P.turn (d.point j)) ∧
      P.mate (P.turn c.last) = d.first ∧ P.mate (P.turn d.last) = c.first ∧
      ∀ x, c.Visited x ∨ d.Visited x := by
  obtain ⟨N, whole, longer, kept, closes, covers⟩ := P.exists_cycle_extension connected free c
  have first : whole.first = c.first := kept 0
  have last : whole.point ⟨n, by omega⟩ = c.last := kept (Fin.last n)
  have proper : n < N := by
    by_contra absent
    have equal : n = N := by omega
    have endpoint : whole.last = c.last := by
      exact (congrArg whole.point (Fin.ext equal.symm)).trans last
    apply not_closed
    rw [← endpoint, closes, first]
  let d := whole.suffix (n + 1) (by omega)
  have apart : ∀ i j, c.point i ≠ d.point j ∧ c.point i ≠ P.turn (d.point j) := by
    intro i j
    have before : whole.point ⟨i.val, by omega⟩ = c.point i := kept i
    have after : d.point j = whole.point ⟨n + 1 + j.val, by have bound := j.isLt; omega⟩ := rfl
    constructor
    · intro same
      rw [← before, after] at same
      have values := congrArg Fin.val (whole.injective same)
      have bound := i.isLt
      dsimp only at values
      omega
    · rw [← before, after]
      exact whole.disjoint _ _
  have joined : P.mate (P.turn c.last) = d.first := by
    have next := whole.next ⟨n, proper⟩
    change P.mate (P.turn (whole.point ⟨n, by omega⟩)) = whole.point ⟨n + 1, by omega⟩ at next
    rw [last] at next
    change _ = (whole.suffix (n + 1) (by omega)).first
    rw [whole.suffix_first]
    exact next
  have closing : P.mate (P.turn d.last) = c.first := by
    change P.mate (P.turn (whole.suffix (n + 1) (by omega)).last) = _
    rw [whole.suffix_last, closes, first]
  have each (j : Fin (N + 1)) :
      (∃ i, whole.point j = c.point i) ∨ (∃ k, whole.point j = d.point k) := by
    by_cases before : j.val ≤ n
    · let i : Fin (n + 1) := ⟨j.val, by omega⟩
      exact Or.inl ⟨i, (congrArg whole.point (Fin.ext rfl)).trans (kept i)⟩
    · let k : Fin (N - (n + 1) + 1) := ⟨j.val - (n + 1), by have bound := j.isLt; omega⟩
      refine Or.inr ⟨k, ?_⟩
      apply congrArg whole.point
      apply Fin.ext
      dsimp [k]
      omega
  refine ⟨N - (n + 1), d, apart, joined, closing, ?_⟩
  intro x
  obtain ⟨j, same | same⟩ := covers x
  · rcases each j with ⟨i, at_i⟩ | ⟨k, at_k⟩
    · exact Or.inl ⟨i, Or.inl (same.trans at_i)⟩
    · exact Or.inr ⟨k, Or.inl (same.trans at_k)⟩
  · rcases each j with ⟨i, at_i⟩ | ⟨k, at_k⟩
    · exact Or.inl ⟨i, Or.inr (same.trans (congrArg P.turn at_i))⟩
    · exact Or.inr ⟨k, Or.inr (same.trans (congrArg P.turn at_k))⟩


/-- Two actual intervals with complementary endpoint joins partition the original cycle.
No separate coverage or separation certificate is needed. -/
theorem complementary_chains_partition (connected : P.Connected) (free : ∀ x, P.mate x ≠ x)
    {n m : ℕ} (c : P.Chain n) (d : P.Chain m)
    (joined : P.mate (P.turn c.last) = d.first)
    (closes : P.mate (P.turn d.last) = c.first) (different : d.first ≠ c.first) :
    (∀ i j, c.point i ≠ d.point j ∧ c.point i ≠ P.turn (d.point j)) ∧
      ∀ x, c.Visited x ∨ d.Visited x := by
  have not_closed : P.mate (P.turn c.last) ≠ c.first := by rwa [joined]
  obtain ⟨l, remaining, apart, first, last, covers⟩ :=
    P.exists_complementary_chain connected free c not_closed
  have initial : remaining.first = d.first := first.symm.trans joined
  have terminal : P.turn remaining.last = P.turn d.last :=
    P.mate_involutive.injective (last.trans closes.symm)
  obtain ⟨length, points⟩ := remaining.eq_length_and_points_of_terminals d initial terminal
  constructor
  · intro i j
    let k : Fin (l + 1) := ⟨j.val, by rw [length]; exact j.isLt⟩
    simpa only [points k j rfl] using apart i k
  · intro x
    rcases covers x with first | last
    · exact Or.inl first
    · exact Or.inr ((remaining.visited_iff_of_terminals d initial terminal x).mp last)

end PairedInvolutions.System
