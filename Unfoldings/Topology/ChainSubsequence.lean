module

public import Unfoldings.Topology.PairedInvolutions
public import Mathlib.Order.Fin.Basic

/-! A directed subchain has contiguous indices unless it crosses the chosen first end. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u

variable {X : Type u} {P : System X} {n m : ℕ} (c : P.Chain n) (d : P.Chain m)

/-- An actual successor appearing after the first end has the next numerical index. -/
theorem successor_index {a b : Fin (m + 1)}
    (next : P.mate (P.turn (d.point a)) = d.point b) (nonzero : b ≠ 0) :
    b.val = a.val + 1 := by
  have positive : 0 < b.val := by
    by_contra absent
    exact nonzero (Fin.ext (by change b.val = 0; omega))
  let k : Fin m := ⟨b.val - 1, by have bound := b.isLt; omega⟩
  have at_b : k.succ = b := Fin.ext (by dsimp [k]; omega)
  have equal : P.mate (P.turn (d.point k.castSucc)) =
      P.mate (P.turn (d.point a)) := by
    rw [d.next, at_b, next]
  have previous := d.injective
    (P.turn_involutive.injective (P.mate_involutive.injective equal))
  have values := congrArg Fin.val previous
  dsimp [k] at values
  omega

open Classical in
/-- Directed coverage and avoidance of the first end inside a block derive its exact
contiguous placement. No proposed numerical ordering is an input. -/
theorem exists_contiguous_embedding
    (covered : ∀ i, ∃ j, d.point j = c.point i)
    (not_first : ∀ k : Fin n, c.point k.succ ≠ d.first) :
    ∃ index : Fin (n + 1) ↪o Fin (m + 1),
      (∀ i, d.point (index i) = c.point i) ∧
      ∀ i, (index i).val = (index 0).val + i.val := by
  let locate (i : Fin (n + 1)) : Fin (m + 1) := (covered i).choose
  have named (i) : d.point (locate i) = c.point i := (covered i).choose_spec
  have step (k : Fin n) : (locate k.succ).val = (locate k.castSucc).val + 1 := by
    apply d.successor_index
    · rw [named, named, c.next]
    · intro equal
      apply not_first k
      rw [← named k.succ, equal]
      rfl
  have offset (i : Fin (n + 1)) : (locate i).val = (locate 0).val + i.val := by
    induction i using Fin.induction with
    | zero => simp
    | succ k previous =>
      rw [step, previous]
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
  have monotone : StrictMono locate := by
    intro i j less
    change (locate i).val < (locate j).val
    rw [offset i, offset j]
    exact Nat.add_lt_add_left less _
  exact ⟨OrderEmbedding.ofStrictMono locate monotone, named, offset⟩

end PairedInvolutions.System.Chain
