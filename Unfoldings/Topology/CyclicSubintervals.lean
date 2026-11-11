module

public import Unfoldings.Topology.CyclicIntervals
public import Unfoldings.Topology.CyclicRegionPairing

/-! Prefixes and suffixes inside a cyclic region with exactly two exits. -/

@[expose] public section

namespace Unfoldings

/-- Two inside endpoints determine a forward subinterval lying entirely inside the parent
region if the first is its first inside point, or the second is its last inside point. -/
theorem exists_finRotate_subinterval {n : ℕ} (parent : Fin (n + 1) → Prop)
    (enter leave : Fin (n + 1)) (different : enter ≠ leave)
    (enters : ¬ parent enter ∧ parent (finRotate (n + 1) enter))
    (leaves : parent leave ∧ ¬ parent (finRotate (n + 1) leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave →
      (parent (finRotate (n + 1) i) ↔ parent i))
    (start finish : Fin (n + 1)) (distinct : start ≠ finish)
    (start_inside : parent start) (finish_inside : parent finish)
    (anchored : start = finRotate (n + 1) enter ∨ finish = leave) :
    ∃ (region : Fin (n + 1) → Prop) (a b : Fin (n + 1)),
      a ≠ b ∧ finRotate (n + 1) a = start ∧ finRotate (n + 1) b = finish ∧
      (¬ region a ∧ region (finRotate (n + 1) a)) ∧
      (region b ∧ ¬ region (finRotate (n + 1) b)) ∧
      (∀ i, i ≠ a → i ≠ b → (region (finRotate (n + 1) i) ↔ region i)) ∧
      ∀ i, region i → parent i := by
  obtain ⟨region, a, b, ne, first, last, first_change, last_change, unchanged, prefixes⟩ :=
    exists_finRotate_interval start finish distinct
  have paired : region enter ↔ region leave :=
    cyclic_region_crossings_paired (finRotate (n + 1)) region parent a b enter leave ne different
      first_change last_change unchanged enters leaves stable (by
        rw [first, last]
        exact iff_of_true start_inside finish_inside)
  have avoid_enter : ¬ region enter := by
    rcases anchored with beginning | ending
    · have same : a = enter := (finRotate (n + 1)).injective (first.trans beginning)
      exact same ▸ first_change.1
    · have avoid_leave : ¬ region leave := by
        rw [last, ending] at last_change
        exact last_change.2
      exact fun member => avoid_leave (paired.mp member)
  have avoid_leave : ¬ region leave := fun member => avoid_enter (paired.mpr member)
  refine ⟨region, a, b, ne, first, last, first_change, last_change, unchanged, ?_⟩
  intro i member
  obtain ⟨m, at_i, path⟩ := prefixes i member
  have along : ∀ j : ℕ, j ≤ m → parent ((finRotate (n + 1))^[j] start) := by
    intro j
    induction j with
    | zero => exact fun _ => start_inside
    | succ j ih =>
      intro before
      have past : j ≤ m := Nat.le_trans (Nat.le_succ j) before
      have here := path j past
      have not_enter : (finRotate (n + 1))^[j] start ≠ enter :=
        fun equal => avoid_enter (equal ▸ here)
      have not_leave : (finRotate (n + 1))^[j] start ≠ leave :=
        fun equal => avoid_leave (equal ▸ here)
      rw [Function.iterate_succ_apply']
      exact (stable _ not_enter not_leave).mpr (ih past)
  exact at_i ▸ along m le_rfl

end Unfoldings
