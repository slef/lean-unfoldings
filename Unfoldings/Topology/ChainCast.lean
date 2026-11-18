module

public import Unfoldings.Topology.PairedInvolutions

/-! Changing a chain's length index preserves its actual bank labels and endpoints. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n m : ℕ} (c : P.Chain n) (equal : n = m)

/-- Transport a chain across an equality of its finite length indices. -/
def cast : P.Chain m := equal ▸ c

@[simp] theorem cast_first : (c.cast equal).first = c.first := by
  subst m
  rfl

@[simp] theorem cast_last : (c.cast equal).last = c.last := by
  subst m
  rfl

/-- Each bank keeps its original label at the same natural-number index. -/
theorem cast_point (i : Fin (m + 1)) :
    (c.cast equal).point i = c.point ⟨i.val, by omega⟩ := by
  subst m
  rfl

end PairedInvolutions.System.Chain
