module

public import Unfoldings.Topology.SubtreeWeights
public import Unfoldings.Topology.OrderedChanges

/-! Parent differences telescope before nested subtree weights are charged to original vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V)

theorem sum_parent_difference_rootPath (value : V → ℝ) (v : V) :
    (∑ i : Fin (P.distanceToRoot v),
      (value (P.parent^[i.val] v) - value (P.parent (P.parent^[i.val] v)))) =
        value v - value (P.root v) := by
  let f (i : Fin (P.distanceToRoot v + 1)) := value (P.parent^[i.val] v)
  have step (i : Fin (P.distanceToRoot v)) :
      value (P.parent^[i.val] v) - value (P.parent (P.parent^[i.val] v)) =
        -(f i.succ - f i.castSucc) := by
    simp only [f, Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']
    ring
  simp only [step, Finset.sum_neg_distrib, sum_fin_succ_sub]
  change -(value (P.parent^[P.distanceToRoot v] v) - value v) = _
  rw [P.iterate_distanceToRoot_eq_root]
  ring

variable [Fintype V]

open Classical in
/-- Every nested ancestor weight occurs exactly once after parent differences telescope. -/
theorem sum_subtree_parent_differences (weight value : V → ℝ) :
    (∑ e : V, if e ∉ P.roots then
      (value e - value (P.parent e)) * (∑ v ∈ P.descendants e, weight v) else 0) =
        ∑ v : V, weight v * (value v - value (P.root v)) := by
  rw [P.sum_subtree_weights_eq_rootPaths]
  exact Finset.sum_congr rfl (fun v _ => by rw [P.sum_parent_difference_rootPath])

open Classical in
/-- No crossing-count premise is needed for membership changes along actual parent edges. -/
theorem abs_sum_subtree_membership_changes_le (weight : V → ℝ)
    (nonnegative : ∀ v, 0 ≤ weight v) (selected : Set V) :
    |∑ e : V, if e ∉ P.roots then
      ((if e ∈ selected then (1 : ℝ) else 0) -
        (if P.parent e ∈ selected then 1 else 0)) *
          (∑ v ∈ P.descendants e, weight v) else 0| ≤ ∑ v : V, weight v := by
  classical
  apply P.abs_sum_subtree_weights_le weight _ nonnegative
  intro v
  have cancel := P.sum_parent_difference_rootPath
    (fun v => if v ∈ selected then (1 : ℝ) else 0) v
  rw [cancel]
  by_cases first : v ∈ selected <;> by_cases last : P.root v ∈ selected <;>
    simp only [first, last, ite_true, ite_false, sub_zero, sub_self, zero_sub, abs_zero, abs_one,
      abs_neg, zero_le_one, le_refl]

end Unfoldings.AscendingParents
