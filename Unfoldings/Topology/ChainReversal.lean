module

public import Unfoldings.Topology.PairedInvolutions
public import Mathlib.Data.Fin.Rev

/-! Reverse an actual paired-interval chain, including each bank's endpoint orientation. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n : ℕ} (c : P.Chain n)

/-- Reverse both interval order and the two ends of every original interval. -/
def reverse : P.Chain n where
  point i := P.turn (c.point i.rev)
  injective := P.turn_involutive.injective.comp (c.injective.comp Fin.rev_injective)
  disjoint i j same := by
    rw [P.turn_involutive] at same
    exact c.disjoint j.rev i.rev same.symm
  next i := by
    rw [P.turn_involutive, Fin.rev_castSucc, Fin.rev_succ]
    exact c.mate_succ i.rev

@[simp] theorem reverse_first : c.reverse.first = P.turn c.last := by
  simp only [reverse, first, last, Fin.rev_zero]

@[simp] theorem reverse_last : c.reverse.last = P.turn c.first := by
  simp only [reverse, first, last, Fin.rev_last]

@[simp] theorem reverse_reverse : c.reverse.reverse = c := by
  cases c
  dsimp only [reverse]
  congr 1
  funext i
  simp only [Fin.rev_rev]
  exact P.turn_involutive _

end PairedInvolutions.System.Chain
