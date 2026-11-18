module

public import Unfoldings.Topology.ParentPaths

/-! Removing a genuine first parent edge reduces the root distance by exactly one. -/

@[expose] public section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V)

/-- A nonroot's first parent edge is counted exactly once in its rootward path. -/
theorem distanceToRoot_parent_step (v : V) (nonroot : v ∉ P.roots) :
    P.distanceToRoot v = P.distanceToRoot (P.parent v) + 1 := by
  classical
  have positive : 0 < P.distanceToRoot v :=
    Nat.pos_of_ne_zero (fun zero => nonroot ((P.distanceToRoot_eq_zero_iff v).mp zero))
  apply le_antisymm
  · apply Nat.find_min' (P.exists_iterate_root v)
    simpa only [Function.iterate_succ_apply] using P.iterate_distanceToRoot_mem (P.parent v)
  · by_contra later
    have before : P.distanceToRoot v - 1 < P.distanceToRoot (P.parent v) := by omega
    apply P.iterate_lt_distanceToRoot_not_mem (P.parent v) before
    have reaches := P.iterate_distanceToRoot_mem v
    have count : P.distanceToRoot v = (P.distanceToRoot v - 1) + 1 := by omega
    rw [count, Function.iterate_succ_apply] at reaches
    exact reaches

end Unfoldings.AscendingParents
