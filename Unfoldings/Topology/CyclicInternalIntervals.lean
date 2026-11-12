module

public import Unfoldings.Topology.CyclicSubintervals

/-! Any two points of a proper cyclic interval have an oriented subinterval inside it. -/

@[expose] public section

namespace Unfoldings

/-- A predicate invariant under the cyclic successor is constant. -/
theorem finRotate_invariant {n : ℕ} (p : Fin (n + 1) → Prop)
    (stable : ∀ i, p (finRotate (n + 1) i) ↔ p i)
    (start : Fin (n + 1)) (initial : p start) : ∀ i, p i := by
  intro i
  let k : Fin (n + 1) := i - start
  have orbit : (finRotate (n + 1))^[k.val] start = i := by
    rw [← finCycle_eq_finRotate_iterate]
    simpa only [finCycle_apply, k, add_comm] using sub_add_cancel i start
  have along : ∀ m : ℕ, p ((finRotate (n + 1))^[m] start) := by
    intro m
    induction m with
    | zero => exact initial
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact (stable _).mpr ih
  exact orbit ▸ along k.val

/-- Reversing the two transitions selects precisely the complementary arc. -/
theorem finRotate_opposite_regions {n : ℕ} (p q : Fin (n + 1) → Prop)
    (a b : Fin (n + 1))
    (p_enters : ¬ p a ∧ p (finRotate (n + 1) a))
    (p_leaves : p b ∧ ¬ p (finRotate (n + 1) b))
    (p_stable : ∀ i, i ≠ a → i ≠ b → (p (finRotate (n + 1) i) ↔ p i))
    (q_enters : ¬ q b ∧ q (finRotate (n + 1) b))
    (q_leaves : q a ∧ ¬ q (finRotate (n + 1) a))
    (q_stable : ∀ i, i ≠ b → i ≠ a → (q (finRotate (n + 1) i) ↔ q i)) :
    ∀ i, p i ↔ ¬ q i := by
  refine finRotate_invariant (fun i => p i ↔ ¬ q i) ?_ a ?_
  · intro i
    by_cases first : i = a
    · subst i
      simp only [p_enters.1, p_enters.2, q_leaves.1, q_leaves.2,
        not_false_eq_true, not_true_eq_false, iff_self]
    · by_cases last : i = b
      · subst i
        simp only [p_leaves.1, p_leaves.2, q_enters.1, q_enters.2,
          not_false_eq_true, not_true_eq_false, iff_self]
      · rw [p_stable i first last, q_stable i last first]
  · exact iff_of_false p_enters.1 (not_not.mpr q_leaves.1)

/-- One of the two arcs between distinct inside points stays in the parent interval.
The orientation is chosen by the proof and both actual endpoints are retained. -/
theorem exists_finRotate_internal_interval {n : ℕ} (parent : Fin (n + 1) → Prop)
    (enter leave : Fin (n + 1)) (different : enter ≠ leave)
    (enters : ¬ parent enter ∧ parent (finRotate (n + 1) enter))
    (leaves : parent leave ∧ ¬ parent (finRotate (n + 1) leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave →
      (parent (finRotate (n + 1) i) ↔ parent i))
    (start finish : Fin (n + 1)) (distinct : start ≠ finish)
    (start_inside : parent start) (finish_inside : parent finish) :
    ∃ (region : Fin (n + 1) → Prop) (a b : Fin (n + 1)),
      a ≠ b ∧
      ((finRotate (n + 1) a = start ∧ finRotate (n + 1) b = finish) ∨
        (finRotate (n + 1) a = finish ∧ finRotate (n + 1) b = start)) ∧
      (¬ region a ∧ region (finRotate (n + 1) a)) ∧
      (region b ∧ ¬ region (finRotate (n + 1) b)) ∧
      (∀ i, i ≠ a → i ≠ b → (region (finRotate (n + 1) i) ↔ region i)) ∧
      ∀ i, region i → parent i := by
  classical
  have inside_arc (x y : Fin (n + 1)) (x_in : parent x) (y_in : parent y)
      (region : Fin (n + 1) → Prop) (a b : Fin (n + 1)) (ne : a ≠ b)
      (first : finRotate (n + 1) a = x) (last : finRotate (n + 1) b = y)
      (first_change : ¬ region a ∧ region (finRotate (n + 1) a))
      (last_change : region b ∧ ¬ region (finRotate (n + 1) b))
      (unchanged : ∀ i, i ≠ a → i ≠ b → (region (finRotate (n + 1) i) ↔ region i))
      (prefixes : ∀ i, region i → ∃ m : ℕ, (finRotate (n + 1))^[m] x = i ∧
        ∀ j ≤ m, region ((finRotate (n + 1))^[j] x))
      (avoid : ¬ region enter) : ∀ i, region i → parent i := by
    have paired : region enter ↔ region leave :=
      cyclic_region_crossings_paired (finRotate (n + 1)) region parent a b enter leave
        ne different first_change last_change unchanged enters leaves stable (by
          rw [first, last]; exact iff_of_true x_in y_in)
    have avoid_leave : ¬ region leave := fun member => avoid (paired.mpr member)
    intro i member
    obtain ⟨m, at_i, path⟩ := prefixes i member
    have along : ∀ j : ℕ, j ≤ m → parent ((finRotate (n + 1))^[j] x) := by
      intro j
      induction j with
      | zero => exact fun _ => x_in
      | succ j ih =>
        intro before
        have past : j ≤ m := Nat.le_trans (Nat.le_succ j) before
        have here := path j past
        rw [Function.iterate_succ_apply']
        exact (stable _ (fun equal => avoid (equal ▸ here))
          (fun equal => avoid_leave (equal ▸ here))).mpr (ih past)
    exact at_i ▸ along m le_rfl
  obtain ⟨p, a, b, ne, first, last, pe, pl, ps, pp⟩ :=
    exists_finRotate_interval start finish distinct
  by_cases avoids : ¬ p enter
  · exact ⟨p, a, b, ne, Or.inl ⟨first, last⟩, pe, pl, ps,
      inside_arc start finish start_inside finish_inside p a b ne first last pe pl ps pp avoids⟩
  · obtain ⟨q, c, d, qne, qfirst, qlast, qe, ql, qs, qp⟩ :=
      exists_finRotate_interval finish start distinct.symm
    have cb : c = b := (finRotate (n + 1)).injective (qfirst.trans last.symm)
    have da : d = a := (finRotate (n + 1)).injective (qlast.trans first.symm)
    subst c
    subst d
    have opposite := finRotate_opposite_regions p q a b pe pl ps qe ql qs
    have avoid_q : ¬ q enter := (opposite enter).mp (Classical.not_not.mp avoids)
    exact ⟨q, b, a, qne, Or.inr ⟨qfirst, qlast⟩, qe, ql, qs,
      inside_arc finish start finish_inside start_inside q b a qne qfirst qlast qe ql qs qp
        avoid_q⟩

end Unfoldings
