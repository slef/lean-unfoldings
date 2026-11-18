module

public import Unfoldings.Topology.ChainBlockAssembly
public import Mathlib.Data.Fintype.BigOperators

/-! Exact additive weights for any complete disjoint family of actual chain blocks. -/

@[expose] public section

namespace PairedInvolutions.System.Chain

universe u v w

variable {X : Type u} {P : System X} {n : ℕ} (chain : P.Chain n)

/-- Complete block coverage counts each actual directed interval exactly once. -/
theorem sum_of_finite_block_cover {A : Type v} [Fintype A] (block : A → P.ChainBlock)
    (apart : ∀ a b, a ≠ b → ∀ i j, (block a).2.point i ≠ (block b).2.point j)
    (covered : ∀ x, (∃ i, chain.point i = x) ↔ ∃ a j, (block a).2.point j = x)
    {M : Type w} [AddCommMonoid M] (weight : X → M) :
    (∑ i, weight (chain.point i)) = ∑ a, ∑ j, weight ((block a).2.point j) := by
  classical
  let B := (a : A) × Fin ((block a).1 + 1)
  let point (b : B) : X := (block b.1).2.point b.2
  have point_injective : Function.Injective point := by
    rintro ⟨a, i⟩ ⟨b, j⟩ same
    have equal : a = b := by
      by_contra different
      exact apart a b different i j same
    subst b
    exact congrArg (Sigma.mk a) ((block a).2.injective same)
  have indices (i : Fin (n + 1)) : ∃ b : B, point b = chain.point i := by
    obtain ⟨a, j, same⟩ := (covered (chain.point i)).mp ⟨i, rfl⟩
    exact ⟨⟨a, j⟩, same⟩
  choose index matching using indices
  have injective : Function.Injective index := by
    intro i j same
    apply chain.injective
    exact (matching i).symm.trans ((congrArg point same).trans (matching j))
  have surjective : Function.Surjective index := by
    intro b
    obtain ⟨i, same⟩ := (covered (point b)).mpr ⟨b.1, b.2, rfl⟩
    exact ⟨i, point_injective ((matching i).trans same)⟩
  let e : Fin (n + 1) ≃ B := Equiv.ofBijective index ⟨injective, surjective⟩
  calc
    _ = ∑ i, weight (point (e i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg weight (matching i).symm
    _ = ∑ b : B, weight (point b) := Equiv.sum_comp e (fun b => weight (point b))
    _ = _ := Fintype.sum_sigma _

end PairedInvolutions.System.Chain
