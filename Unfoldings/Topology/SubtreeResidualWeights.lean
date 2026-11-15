module

public import Unfoldings.Topology.ChildSubtrees

/-! Subtracting all immediate-child subtree weights leaves exactly the junction's own weight. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Fintype V] (P : AscendingParents V)

open scoped Classical in
/-- Immediate-child subtrees account for all proper descendants, with arbitrary vertex weights. -/
theorem sum_child_descendant_weights (e : V) (nonroot : e ∉ P.roots) (weight : V → ℝ) :
    (∑ c : {c : V // c ∉ P.roots}, if P.parent c.val = e then
      ∑ v ∈ P.descendants c.val, weight v else 0) =
      ∑ v : V, if P.Ancestor v e ∧ v ≠ e then weight v else 0 := by
  classical
  simp only [descendants, Finset.sum_filter]
  have expand (c : {c : V // c ∉ P.roots}) :
      (if P.parent c.val = e then
        ∑ v : V, if P.Ancestor v c.val then weight v else 0 else 0) =
      ∑ v : V, if P.parent c.val = e ∧ P.Ancestor v c.val then weight v else 0 := by
    by_cases parent : P.parent c.val = e
    · simp only [parent, ite_true, true_and]
    · simp only [parent, ite_false, false_and, Finset.sum_const_zero]
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases proper : P.Ancestor v e ∧ v ≠ e
  · rw [ite_eq_left proper]
    obtain ⟨c, candidate, unique⟩ := P.exists_unique_child_ancestor nonroot proper.1 proper.2
    rw [Finset.sum_eq_single c]
    · exact ite_eq_left candidate
    · intro other _ different
      exact ite_eq_right (fun hypotheses => different (unique other hypotheses))
    · intro absent
      exact (absent (Finset.mem_univ c)).elim
  · rw [ite_eq_right proper]
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right (fun candidate =>
      proper (P.proper_descendant_of_child c.property candidate.1 candidate.2))

open scoped Classical in
/-- The junction residual is its original vertex weight, independent of the number of branches. -/
theorem descendant_weight_sub_children (e : V) (nonroot : e ∉ P.roots) (weight : V → ℝ) :
    (∑ v ∈ P.descendants e, weight v) -
      (∑ c : {c : V // c ∉ P.roots}, if P.parent c.val = e then
        ∑ v ∈ P.descendants c.val, weight v else 0) = weight e := by
  classical
  rw [P.sum_child_descendant_weights e nonroot weight]
  have split (v : V) : (if P.Ancestor v e then weight v else 0) =
      (if v = e then weight e else 0) +
        (if P.Ancestor v e ∧ v ≠ e then weight v else 0) := by
    by_cases same : v = e
    · subst v
      simp only [P.ancestor_refl, ite_true, ne_eq, not_true_eq_false, and_false, ite_false,
        add_zero]
    · by_cases reaches : P.Ancestor v e <;> simp [same, reaches]
  simp only [descendants, Finset.sum_filter]
  conv_lhs =>
    enter [1]
    simp only [split, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_sub_cancel_right]

end Unfoldings.AscendingParents
