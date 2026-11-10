module

public import Unfoldings.Topology.ParentOrbitEnumeration

/-!
# Summing signed corrections over nested subtrees

A descendant weight occurs in every ancestor subtree. Interchanging the finite
sums counts it through its own root path once, allowing signed crossings to
cancel before a curvature bound is applied.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Fintype V] (P : AscendingParents V)

open scoped Classical in
/-- Nested subtree weights regroup as signed corrections along each original vertex's root path. -/
theorem sum_subtree_weights_eq_rootPaths (curvature crossing : V → ℝ) :
    (∑ e : V, if e ∉ P.roots then crossing e * (∑ v ∈ P.descendants e, curvature v) else 0) =
      ∑ v : V, curvature v *
        (∑ i : Fin (P.distanceToRoot v), crossing (P.parent^[i.val] v)) := by
  classical
  conv_rhs =>
    enter [2, v]
    rw [← P.sum_nonroot_ancestors v crossing]
  simp only [descendants, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  have expand (e : V) :
      (if e ∉ P.roots then
        ∑ v : V, if P.Ancestor v e then crossing e * curvature v else 0 else 0) =
      ∑ v : V, if e ∉ P.roots ∧ P.Ancestor v e then curvature v * crossing e else 0 := by
    by_cases root : e ∈ P.roots
    · simp only [root, not_true_eq_false, ite_false, false_and, Finset.sum_const_zero]
    · simp only [root, not_false_eq_true, ite_true, true_and]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> ring
  simp_rw [expand]
  rw [Finset.sum_comm]

open scoped Classical in
/-- Signed path corrections are bounded once per original vertex, despite nested ancestor cuts. -/
theorem abs_sum_subtree_weights_le (curvature crossing : V → ℝ)
    (nonnegative : ∀ v, 0 ≤ curvature v)
    (path_bound : ∀ v, |∑ i : Fin (P.distanceToRoot v), crossing (P.parent^[i.val] v)| ≤ 1) :
    |∑ e : V, if e ∉ P.roots then crossing e * (∑ v ∈ P.descendants e, curvature v) else 0| ≤
      ∑ v : V, curvature v := by
  classical
  rw [P.sum_subtree_weights_eq_rootPaths]
  calc
    _ ≤ ∑ v : V, |curvature v *
        (∑ i : Fin (P.distanceToRoot v), crossing (P.parent^[i.val] v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      rw [abs_mul, abs_of_nonneg (nonnegative v)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (path_bound v) (nonnegative v)

end Unfoldings.AscendingParents
