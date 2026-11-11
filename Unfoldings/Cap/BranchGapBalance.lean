module

public import Unfoldings.Cap.MatchedBankPoints
public import Unfoldings.Topology.ChildSubtrees

/-!
# Exact positional balance at every branching vertex

The child-end gap of a parent seam is exactly the sum of the parent-end gaps
of its immediate child seams. This accounts for the translations caused by
all attached branches and allows zero-width gaps without extra assumptions.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (D : FacewiseDevelopment C M.retain)

open scoped Classical in
/-- Actual child-end displacement is conserved across the immediate attached branches. -/
theorem child_gap_eq_sum_child_parent_gaps
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    M.parentExitPoint D e 1 - M.parentEntrancePoint D e 1 =
      ∑ c : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        if M.parents.parent c.val = e.val then M.parentPositionGap D c else 0 := by
  classical
  let weight (v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :=
    M.parentExitVector D v - M.parentEntryVector D v
  have partition := M.parents.sum_child_subtree_weights e weight
  have rewrite_gaps : (∑ c : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
      if M.parents.parent c.val = e.val then M.parentPositionGap D c else 0) =
      ∑ v : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        if M.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else 0 := by
    simpa only [M.parent_position_gap_eq_descendant_sum D, weight] using partition
  have erased : (∑ v ∈ Finset.univ.erase e,
      if M.parents.Ancestor v.val e.val then weight v else 0) =
      ∑ v : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        if M.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else 0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ e)]
    have top : (if M.parents.Ancestor e.val e.val then weight e else 0) = weight e :=
      ite_eq_left (M.parents.ancestor_refl e.val)
    rw [top]
    have remove_top : (∑ v : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        if M.parents.Ancestor v.val e.val then weight v else 0) =
        (∑ v : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
          if M.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else 0) + weight e := by
      have each (v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
          (if M.parents.Ancestor v.val e.val then weight v else 0) =
          (if M.parents.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else 0) +
          (if v = e then weight e else 0) := by
        by_cases same : v = e
        · subst v
          simp only [M.parents.ancestor_refl, ite_true, ne_eq, not_true_eq_false,
            and_false, ite_false, zero_add]
        · have unequal : v.val ≠ e.val := fun equal => same (Subtype.ext equal)
          by_cases reaches : M.parents.Ancestor v.val e.val
          · rw [ite_eq_left reaches, ite_eq_left (show
              M.parents.Ancestor v.val e.val ∧ v.val ≠ e.val from ⟨reaches, unequal⟩),
              ite_eq_right same, add_zero]
          · have improper : ¬ (M.parents.Ancestor v.val e.val ∧ v.val ≠ e.val) :=
              fun h => reaches h.1
            rw [ite_eq_right reaches, ite_eq_right improper, ite_eq_right same, add_zero]
      simp_rw [each, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [remove_top, add_sub_cancel_right]
  rw [M.matched_bank_gap_eq D e 1, sub_self, zero_smul, add_zero, rewrite_gaps]
  exact erased

end Unfoldings.ConvexCap.SectorForest
