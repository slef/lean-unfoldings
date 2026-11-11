module

public import Unfoldings.Cap.CompletedMatchedBankPoints
public import Unfoldings.Topology.ChildSubtrees

/-! Completed-parent child gaps equal the sum of all immediate child-parent gaps. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

open scoped Classical in
/-- Actual child-end displacement is conserved across the immediate attached branches. -/
theorem child_gap_eq_sum_child_parent_gaps
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
    N.parentExitPoint D e 1 - N.parentEntrancePoint D e 1 =
      ∑ c : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
        if N.spanningCompletion.parents.parent c.val = e.val then N.parentPositionGap D c else 0
          := by
  classical
  let weight (v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :=
    N.parentExitVector D v - N.parentEntryVector D v
  have partition := N.spanningCompletion.parents.sum_child_subtree_weights e weight
  have rewrite_gaps : (∑ c : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
      if N.spanningCompletion.parents.parent c.val = e.val then N.parentPositionGap D c else 0) =
      ∑ v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
        if N.spanningCompletion.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else 0
          := by
    simpa only [N.parent_position_gap_eq_descendant_sum D, weight] using partition
  have erased : (∑ v ∈ Finset.univ.erase e,
      if N.spanningCompletion.parents.Ancestor v.val e.val then weight v else 0) =
      ∑ v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
        if N.spanningCompletion.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else 0
          := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ e)]
    have top : (if N.spanningCompletion.parents.Ancestor e.val e.val then weight e else 0) =
      weight e :=
      ite_eq_left (N.spanningCompletion.parents.ancestor_refl e.val)
    rw [top]
    have remove_top : (∑ v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
        if N.spanningCompletion.parents.Ancestor v.val e.val then weight v else 0) =
        (∑ v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
          if N.spanningCompletion.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else
            0) + weight e := by
      have each (v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
          (if N.spanningCompletion.parents.Ancestor v.val e.val then weight v else 0) =
          (if N.spanningCompletion.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else
            0) +
          (if v = e then weight e else 0) := by
        by_cases same : v = e
        · subst v
          simp only [N.spanningCompletion.parents.ancestor_refl, ite_true, ne_eq, not_true_eq_false,
            and_false, ite_false, zero_add]
        · have unequal : v.val ≠ e.val := fun equal => same (Subtype.ext equal)
          by_cases reaches : N.spanningCompletion.parents.Ancestor v.val e.val
          · rw [ite_eq_left reaches, ite_eq_left (show
              N.spanningCompletion.parents.Ancestor v.val e.val ∧ v.val ≠ e.val from ⟨reaches,
                unequal⟩),
              ite_eq_right same, add_zero]
          · have improper : ¬ (N.spanningCompletion.parents.Ancestor v.val e.val ∧ v.val ≠ e.val) :=
              fun h => reaches h.1
            rw [ite_eq_right reaches, ite_eq_right improper, ite_eq_right same, add_zero]
      simp_rw [each, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [remove_top, add_sub_cancel_right]
  rw [N.matched_bank_gap_eq D e 1, sub_self, zero_smul, add_zero, rewrite_gaps]
  exact erased

end Unfoldings.ConvexCap.RadialCutForest
