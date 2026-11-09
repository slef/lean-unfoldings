module

public import Mathlib.Data.Set.Finite.Lattice

/-! Finitely many choices made a bounded number of times give finitely many reachable states. -/

@[expose] public section

namespace Unfoldings

variable {A I : Type*} (step : A → I → A) (initial : A)

def finiteReach : ℕ → Set A
  | 0 => {initial}
  | n + 1 => finiteReach n ∪ (⋃ a ∈ finiteReach n, Set.range (step a))

theorem finite_finiteReach [Finite I] (n : ℕ) : (finiteReach step initial n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton initial
  | succ n ih => exact ih.union (ih.biUnion (fun a _ => Set.finite_range (step a)))

theorem finiteReach_mono : Monotone (finiteReach step initial) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

theorem finiteReach_step {n : ℕ} {a : A} (member : a ∈ finiteReach step initial n) (i : I) :
    step a i ∈ finiteReach step initial (n + 1) := by
  apply Or.inr
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨member, ⟨i, rfl⟩⟩⟩

theorem initial_mem_finiteReach (n : ℕ) : initial ∈ finiteReach step initial n :=
  finiteReach_mono step initial (Nat.zero_le n) (Set.mem_singleton initial)

end Unfoldings
