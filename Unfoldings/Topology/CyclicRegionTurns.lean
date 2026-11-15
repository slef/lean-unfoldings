module

public import Unfoldings.Topology.CyclicRegion

/-! Exact real turn cancellation around a finite selected region, without angle reduction. -/

@[expose] public section

namespace Unfoldings

variable {X A : Type*} [Fintype X] [AddCommGroup A]

open Classical in
/-- Real headings telescope across a selected region with one entering and one leaving edge.
Only steps whose terminal vertex is selected need obey the heading relation. -/
theorem sum_turn_of_two_region_exits (next : Equiv.Perm X) (inside : X → Prop)
    (heading turn : X → A)
    (step : ∀ i, inside (next i) → heading (next i) - heading i = turn (next i))
    (enter leave : X) (different : enter ≠ leave)
    (enters : ¬ inside enter ∧ inside (next enter))
    (leaves : inside leave ∧ ¬ inside (next leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave → (inside (next i) ↔ inside i)) :
    (∑ i, if inside i then turn i else 0) = heading leave - heading enter := by
  classical
  have at_step (i : X) : (if inside (next i) then turn (next i) else 0) =
      (if inside (next i) then heading (next i) else 0) -
        (if inside (next i) then heading i else 0) := by
    by_cases selected : inside (next i)
    · simp only [selected, ite_true, step i selected]
    · simp only [selected, ite_false, sub_self]
  have boundary (i : X) :
      (if inside i then heading i else 0) - (if inside (next i) then heading i else 0) =
        (if i = leave then heading i else 0) - (if i = enter then heading i else 0) := by
    by_cases initial : i = enter
    · subst i
      simp only [enters.1, enters.2, different, ite_true, ite_false, zero_sub]
    · by_cases terminal : i = leave
      · subst i
        simp only [leaves.1, leaves.2, initial, ite_true, ite_false, sub_zero]
      · simp only [stable i initial terminal, initial, terminal, ite_false, sub_self]
  calc
    _ = ∑ i, if inside (next i) then turn (next i) else 0 :=
      (Equiv.sum_comp next (fun i => if inside i then turn i else 0)).symm
    _ = (∑ i, if inside i then heading i else 0) -
        ∑ i, if inside (next i) then heading i else 0 := by
      simp only [at_step, Finset.sum_sub_distrib]
      rw [Equiv.sum_comp next (fun i => if inside i then heading i else 0)]
    _ = ∑ i, ((if i = leave then heading i else 0) -
        (if i = enter then heading i else 0)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => boundary i)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Unfoldings
