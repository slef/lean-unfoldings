module

public import Unfoldings.Topology.PairedInvolutions

/-! Extend any actual interval chain to a complete cycle without changing its original prefix. -/

@[expose] public section

namespace PairedInvolutions.System

variable {X : Type*} [Finite X] (P : PairedInvolutions.System X)

/-- Extend every prescribed chain in its original orientation to the full finite pairing cycle. -/
theorem exists_cycle_extension (connected : P.Connected) (free : ∀ x, P.mate x ≠ x)
    {n : ℕ} (c : P.Chain n) :
    ∃ m : ℕ, ∃ d : P.Chain m, ∃ longer : n ≤ m,
      (∀ i : Fin (n + 1), d.point ⟨i.val, by omega⟩ = c.point i) ∧
      P.mate (P.turn d.last) = d.first ∧ ∀ x, d.Visited x := by
  classical
  let _ := Fintype.ofFinite X
  let extensionExists (m : ℕ) := ∃ d : P.Chain m, ∃ longer : n ≤ m,
    ∀ i : Fin (n + 1), d.point ⟨i.val, by omega⟩ = c.point i
  have initial : extensionExists n := ⟨c, le_rfl, fun i => by congr⟩
  let N := Nat.findGreatest extensionExists (Fintype.card X)
  have bound_n : n ≤ Fintype.card X := by have := c.length_le_card; omega
  obtain ⟨d, longer, kept⟩ := Nat.findGreatest_spec bound_n initial
  change n ≤ N at longer
  have inside : d.Visited (P.mate (P.turn d.last)) := by
    by_contra fresh
    let q := P.mate (P.turn d.last)
    let extended := d.append q fresh rfl
    have bounded : N + 1 ≤ Fintype.card X := by have := extended.length_le_card; omega
    have larger : extensionExists (N + 1) := by
      refine ⟨extended, by omega, ?_⟩
      intro i
      change Fin.snoc (α := fun _ : Fin (N + 2) => X) d.point q
        (⟨i.val, by omega⟩ : Fin (N + 2)) = c.point i
      let j : Fin (N + 1) := ⟨i.val, by omega⟩
      rw [show (⟨i.val, by omega⟩ : Fin (N + 2)) = j.castSucc from Fin.ext rfl]
      exact (Fin.snoc_castSucc (α := fun _ : Fin (N + 2) => X) q d.point j).trans (kept i)
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self N) bounded larger
  have closed : P.mate (P.turn d.last) = d.first := by
    rcases d.closes_or_boundary inside with closes | boundary
    · exact closes
    · exact (free _ boundary).elim
  have start : P.mate d.first = P.turn d.last := by rw [← closed, P.mate_involutive]
  exact ⟨N, d, longer, kept, closed, d.covers connected (Or.inl start) (Or.inl closed)⟩

end PairedInvolutions.System
