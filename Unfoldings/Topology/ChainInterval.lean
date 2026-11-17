module

public import Unfoldings.Topology.PairedInvolutions

/-! Exact consecutive intervals of actual paired-involution chains. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n : ℕ} (c : P.Chain n)

/-- Include each consecutive bank index with its exact original offset. -/
def intervalIndex (_chain : P.Chain n) (first length : ℕ) (fits : first + length ≤ n) :
    Fin (length + 1) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨first + i.val, by have bound := i.isLt; omega⟩)
    (fun _ _ before => Nat.add_lt_add_left before first)

/-- Keep exactly a consecutive block of banks, retaining their actual successors. -/
def interval (first length : ℕ) (fits : first + length ≤ n) : P.Chain length where
  point i := c.point (c.intervalIndex first length fits i)
  injective := c.injective.comp (c.intervalIndex first length fits).injective
  disjoint i j := c.disjoint _ _
  next k := by
    let old : Fin n := ⟨first + k.val, by have bound := k.isLt; omega⟩
    have equal : c.intervalIndex first length fits k.succ = old.succ := by
      apply Fin.ext
      change first + (k.val + 1) = (first + k.val) + 1
      omega
    exact (c.next old).trans (congrArg c.point equal.symm)

@[simp] theorem interval_point (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin (length + 1)) :
    (c.interval first length fits).point i = c.point (c.intervalIndex first length fits i) := rfl

@[simp] theorem interval_first (first length : ℕ) (fits : first + length ≤ n) :
    (c.interval first length fits).first = c.point ⟨first, by omega⟩ :=
  congrArg c.point (Fin.ext (Nat.add_zero _))

@[simp] theorem interval_last (first length : ℕ) (fits : first + length ≤ n) :
    (c.interval first length fits).last = c.point ⟨first + length, by omega⟩ := rfl

end PairedInvolutions.System.Chain
