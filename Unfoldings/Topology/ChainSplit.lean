module

public import Unfoldings.Topology.ChainSuffix
public import Mathlib.Algebra.BigOperators.Fin

/-! Splitting an ordered paired chain at one genuine join preserves its weights. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u v

variable {X : Type u} {P : System X} {n : ℕ} (c : P.Chain n)

/-- Keep the interval through a chosen corner of the chain. -/
def initial (finish : ℕ) (fits : finish ≤ n) : P.Chain finish where
  point i := c.point ⟨i.val, by have bound := i.isLt; omega⟩
  injective := by
    intro i j same
    exact Fin.ext (congrArg (fun k : Fin (n + 1) => k.val) (c.injective same))
  disjoint i j := c.disjoint _ _
  next k := c.next ⟨k.val, by have bound := k.isLt; omega⟩

@[simp] theorem initial_first (finish : ℕ) (fits : finish ≤ n) :
    (c.initial finish fits).first = c.first := rfl

@[simp] theorem initial_last (finish : ℕ) (fits : finish ≤ n) :
    (c.initial finish fits).last = c.point ⟨finish, by omega⟩ := rfl

@[simp] theorem initial_point (finish : ℕ) (fits : finish ≤ n) (i : Fin (finish + 1)) :
    (c.initial finish fits).point i = c.point ⟨i.val, by have bound := i.isLt; omega⟩ := rfl

theorem sum_initial_suffix {M : Type v} [AddCommMonoid M] (k : Fin n) (weight : X → M) :
    let a := c.initial k.val k.isLt.le
    let b := c.suffix (k.val + 1) k.isLt
    (∑ i : Fin (n + 1), weight (c.point i)) =
      (∑ i : Fin (k.val + 1), weight (a.point i)) +
        ∑ i : Fin (n - (k.val + 1) + 1), weight (b.point i) := by
  dsimp only
  let e : Fin ((k.val + 1) + (n - (k.val + 1) + 1)) ≃ Fin (n + 1) :=
    finCongr (by have h := k.isLt; omega)
  have h := Equiv.sum_comp e (fun i => weight (c.point i))
  rw [Fin.sum_univ_add] at h
  exact h.symm

end PairedInvolutions.System.Chain
