module

public import Unfoldings.Topology.PairedInvolutions

/-!
# The actual pairings in an ordered link chain

A nonfixed endpoint pairing in a spanning ordered chain is either between
consecutive intervals or between the two outer ends of a cyclic chain.
The interval case excludes the latter alternatives by its fixed endpoints.
-/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n : ℕ} (c : P.Chain n)

theorem pairing_cases
    (start : P.mate c.first = P.turn c.last ∨ P.mate c.first = c.first)
    (finish : P.mate (P.turn c.last) = c.first ∨ P.mate (P.turn c.last) = P.turn c.last)
    {x y : X} (visited : c.Visited x) (paired : P.mate x = y) (different : x ≠ y) :
    (∃ k : Fin n, x = P.turn (c.point k.castSucc) ∧ y = c.point k.succ) ∨
    (∃ k : Fin n, x = c.point k.succ ∧ y = P.turn (c.point k.castSucc)) ∨
    (x = P.turn c.last ∧ y = c.first) ∨ (x = c.first ∧ y = P.turn c.last) := by
  obtain ⟨i, rfl | rfl⟩ := visited
  · revert paired different
    refine Fin.cases ?_ (fun k => ?_) i
    · intro paired different
      rcases start with closes | fixed
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, paired.symm.trans closes⟩))
      · exact (different (fixed.symm.trans paired)).elim
    · intro paired _
      exact Or.inr (Or.inl ⟨k, rfl, paired.symm.trans (c.mate_succ k)⟩)
  · revert paired different
    refine Fin.lastCases ?_ (fun k => ?_) i
    · intro paired different
      rcases finish with closes | fixed
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, paired.symm.trans closes⟩))
      · exact (different (fixed.symm.trans paired)).elim
    · intro paired _
      exact Or.inl ⟨k, rfl, paired.symm.trans (c.next k)⟩

/-- In an interval chain, every nonfixed pairing is between consecutive intervals. -/
theorem interval_pairing_cases
    (start : P.mate c.first = c.first)
    (finish : P.mate (P.turn c.last) = P.turn c.last)
    {x y : X} (visited : c.Visited x) (paired : P.mate x = y) (different : x ≠ y) :
    (∃ k : Fin n, x = P.turn (c.point k.castSucc) ∧ y = c.point k.succ) ∨
    (∃ k : Fin n, x = c.point k.succ ∧ y = P.turn (c.point k.castSucc)) := by
  rcases c.pairing_cases (Or.inr start) (Or.inr finish) visited paired different with
    forward | backward | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl forward
  · exact Or.inr backward
  · exact (different (finish.symm.trans paired)).elim
  · exact (different (start.symm.trans paired)).elim

end PairedInvolutions.System.Chain
