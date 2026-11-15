module

public import Unfoldings.Topology.PairedInvolutions

/-! Exact terminal intervals of actual paired-involution chains. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n : ℕ} (c : P.Chain n)

/-- Drop an initial block without changing any subsequent original label or successor. -/
def suffix (start : ℕ) (fits : start ≤ n) : P.Chain (n - start) where
  point i := c.point ⟨start + i.val, by have bound := i.isLt; omega⟩
  injective := by
    intro i j same
    have values := congrArg Fin.val (c.injective same)
    apply Fin.ext
    dsimp only at values
    omega
  disjoint i j := c.disjoint _ _
  next k := by
    let old : Fin n := ⟨start + k.val, by have bound := k.isLt; omega⟩
    exact (c.next old).trans (congrArg c.point (Fin.ext (by dsimp [old]; omega)))

@[simp] theorem suffix_first (start : ℕ) (fits : start ≤ n) :
    (c.suffix start fits).first = c.point ⟨start, by omega⟩ :=
  congrArg c.point (Fin.ext (Nat.add_zero _))

@[simp] theorem suffix_last (start : ℕ) (fits : start ≤ n) :
    (c.suffix start fits).last = c.last :=
  congrArg c.point (Fin.ext (Nat.add_sub_of_le fits))

/-- Each suffix index is its exact original offset, with no reparametrization. -/
theorem suffix_point (start : ℕ) (fits : start ≤ n) (i : Fin (n - start + 1)) :
    (c.suffix start fits).point i = c.point ⟨start + i.val, by have bound := i.isLt; omega⟩ := rfl

end PairedInvolutions.System.Chain
