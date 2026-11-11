module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Abel

/-!
# Displacement around a selected part of a finite cycle

Summing the actual edge vectors whose initial vertices lie inside a region
cancels all internal positions. Only its entrance and exit positions remain.
No simplicity or non-overlap of the drawing is assumed.
-/

@[expose] public section

namespace Unfoldings

variable {X V : Type*} [Fintype X] [AddCommGroup V]

/-- Additive cancellation with exactly one entering and one leaving edge. -/
theorem displacement_of_two_region_exits (next : Equiv.Perm X) (inside : X → Prop)
    [DecidablePred inside] (position : X → V) (enter leave : X)
    (different : enter ≠ leave) (enters : ¬ inside enter ∧ inside (next enter))
    (leaves : inside leave ∧ ¬ inside (next leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave → (inside (next i) ↔ inside i)) :
    (∑ i, if inside i then position (next i) - position i else 0) =
      position (next leave) - position (next enter) := by
  classical
  let selected (i : X) := if inside i then position i else 0
  have local_step (i : X) :
      (if inside i then position (next i) - position i else 0) =
        selected (next i) - selected i +
          (if i = leave then position (next leave) else 0) -
          (if i = enter then position (next enter) else 0) := by
    by_cases first : i = enter
    · subst i
      simp [selected, enters.1, enters.2, different]
    · by_cases last : i = leave
      · subst i
        simp only [selected, leaves.1, leaves.2, ite_true, ite_false,
          different.symm, sub_zero, zero_sub]
        abel
      · simp only [ite_eq_right first, ite_eq_right last, add_zero, sub_zero,
          selected, stable i first last]
        split_ifs <;> simp
  calc
    _ = ∑ i, (selected (next i) - selected i +
        (if i = leave then position (next leave) else 0) -
        (if i = enter then position (next enter) else 0)) :=
      Finset.sum_congr rfl (fun i _ => local_step i)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Equiv.sum_comp next selected, sub_self, zero_add,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Including the entrance edge gives the gap between the two copies of its far vertex. -/
theorem displacement_gap_of_two_region_exits (next : Equiv.Perm X) (inside : X → Prop)
    [DecidablePred inside] (position : X → V) (enter leave : X)
    (different : enter ≠ leave) (enters : ¬ inside enter ∧ inside (next enter))
    (leaves : inside leave ∧ ¬ inside (next leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave → (inside (next i) ↔ inside i)) :
    position (next leave) - position enter =
      (position (next enter) - position enter) +
        ∑ i, if inside i then position (next i) - position i else 0 := by
  rw [displacement_of_two_region_exits next inside position enter leave
    different enters leaves stable]
  abel

end Unfoldings
