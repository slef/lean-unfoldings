module

public import Unfoldings.Topology.AscendingForest

/-! The first boundary root along each finite increasing parent orbit. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V)

theorem exists_iterate_root (v : V) : ∃ n : ℕ, P.parent^[n] v ∈ P.roots := by
  obtain ⟨r, root, n, equal⟩ := P.exists_ancestor_root v
  exact ⟨n, equal.symm ▸ root⟩

open scoped Classical in
/-- The first root is included, and iteration stops before a constant root step is added. -/
def distanceToRoot (v : V) : ℕ := Nat.find (P.exists_iterate_root v)

theorem iterate_distanceToRoot_mem (v : V) : P.parent^[P.distanceToRoot v] v ∈ P.roots := by
  classical
  exact Nat.find_spec (P.exists_iterate_root v)

theorem iterate_lt_distanceToRoot_not_mem (v : V) {k : ℕ} (before : k < P.distanceToRoot v) :
    P.parent^[k] v ∉ P.roots := by
  classical
  exact Nat.find_min (P.exists_iterate_root v) before

theorem iterate_distanceToRoot_eq_root (v : V) : P.parent^[P.distanceToRoot v] v = P.root v :=
  P.ancestor_root_unique ⟨P.distanceToRoot v, rfl⟩ (P.ancestor_root v)
    (P.iterate_distanceToRoot_mem v) (P.root_mem v)

theorem distanceToRoot_eq_zero_iff (v : V) : P.distanceToRoot v = 0 ↔ v ∈ P.roots := by
  classical
  constructor
  · intro zero
    have root := P.iterate_distanceToRoot_mem v
    simpa only [zero, Function.iterate_zero_apply] using root
  · intro root
    exact Nat.eq_zero_of_le_zero (Nat.find_min' (P.exists_iterate_root v)
      (show P.parent^[0] v ∈ P.roots from root))

/-- No vertex repeats before the first root, by strict ascent of the actual potential. -/
theorem strictMono_height_rootOrbit (v : V) :
    StrictMono (fun i : Fin (P.distanceToRoot v + 1) => P.height (P.parent^[i.val] v)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  change P.height (P.parent^[i.val] v) < P.height (P.parent^[i.val + 1] v)
  rw [Function.iterate_succ_apply']
  exact P.ascending _ (P.iterate_lt_distanceToRoot_not_mem v i.isLt)

end Unfoldings.AscendingParents
