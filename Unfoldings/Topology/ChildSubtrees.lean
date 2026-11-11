module

public import Unfoldings.Topology.SelectedSubtree

/-!
# Immediate-child subtrees partition the proper descendants

These finite rooted-forest identities use only ascending parents. They apply
to arbitrary additive weights, independently of embeddings and developments.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V)

/-- Two ancestors of the same vertex are comparable along its one parent orbit. -/
theorem ancestors_comparable {v a b : V} (first : P.Ancestor v a) (last : P.Ancestor v b) :
    P.Ancestor a b ∨ P.Ancestor b a := by
  obtain ⟨n, first⟩ := first
  obtain ⟨m, last⟩ := last
  rcases le_total n m with before | after
  · left
    exact ⟨m - n, by rw [← first, ← Function.iterate_add_apply, Nat.sub_add_cancel before, last]⟩
  · right
    exact ⟨n - m, by rw [← last, ← Function.iterate_add_apply, Nat.sub_add_cancel after, first]⟩

theorem child_ancestor_unique {e v a b : V}
    (a_nonroot : a ∉ P.roots) (b_nonroot : b ∉ P.roots)
    (a_parent : P.parent a = e) (b_parent : P.parent b = e)
    (first : P.Ancestor v a) (last : P.Ancestor v b) : a = b := by
  by_contra different
  rcases P.ancestors_comparable first last with forward | backward
  · have reaches := (P.ancestor_parent_iff different).mp forward
    rw [a_parent, ← b_parent] at reaches
    exact P.not_ancestor_parent_self b_nonroot reaches
  · have reaches := (P.ancestor_parent_iff (fun same => different same.symm)).mp backward
    rw [b_parent, ← a_parent] at reaches
    exact P.not_ancestor_parent_self a_nonroot reaches

/-- Every proper descendant lies in exactly one immediate-child subtree. -/
theorem exists_unique_child_ancestor {e v : V} (nonroot : e ∉ P.roots)
    (reaches : P.Ancestor v e) (different : v ≠ e) :
    ∃! c : {c : V // c ∉ P.roots}, P.parent c.val = e ∧ P.Ancestor v c.val := by
  obtain ⟨n, reaches⟩ := reaches
  cases n with
  | zero => exact (different reaches).elim
  | succ n =>
    let c := P.parent^[n] v
    have parent : P.parent c = e := by
      simpa only [c, Function.iterate_succ_apply'] using reaches
    have c_nonroot : c ∉ P.roots := P.descendant_nonroot nonroot ⟨1, parent⟩
    refine ⟨⟨c, c_nonroot⟩, ⟨parent, n, rfl⟩, ?_⟩
    intro other hypotheses
    exact Subtype.ext (P.child_ancestor_unique other.property c_nonroot
      hypotheses.1 parent hypotheses.2 ⟨n, rfl⟩)

theorem proper_descendant_of_child {e v c : V} (nonroot : c ∉ P.roots)
    (parent : P.parent c = e) (reaches : P.Ancestor v c) : P.Ancestor v e ∧ v ≠ e := by
  refine ⟨reaches.trans P ⟨1, parent⟩, ?_⟩
  intro same
  rw [same, ← parent] at reaches
  exact P.not_ancestor_parent_self nonroot reaches

variable [Fintype V]

open scoped Classical in
/-- Additive weights of all proper descendants are the sum of immediate-child subtree weights. -/
theorem sum_child_subtree_weights {W : Type*} [AddCommMonoid W]
    (e : {v : V // v ∉ P.roots}) (weight : {v : V // v ∉ P.roots} → W) :
    (∑ c : {v : V // v ∉ P.roots}, if P.parent c.val = e.val then
      ∑ v : {v : V // v ∉ P.roots}, if P.Ancestor v.val c.val then weight v else 0 else 0) =
    ∑ v : {v : V // v ∉ P.roots},
      if P.Ancestor v.val e.val ∧ v.val ≠ e.val then weight v else 0 := by
  classical
  have expand (c : {v : V // v ∉ P.roots}) :
      (if P.parent c.val = e.val then
        ∑ v : {v : V // v ∉ P.roots}, if P.Ancestor v.val c.val then weight v else 0 else 0) =
      ∑ v : {v : V // v ∉ P.roots},
        if P.parent c.val = e.val ∧ P.Ancestor v.val c.val then weight v else 0 := by
    by_cases parent : P.parent c.val = e.val
    · simp only [parent, ite_true, true_and]
    · simp only [parent, ite_false, false_and, Finset.sum_const_zero]
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases proper : P.Ancestor v.val e.val ∧ v.val ≠ e.val
  · rw [ite_eq_left proper]
    obtain ⟨c, candidate, unique⟩ := P.exists_unique_child_ancestor e.property proper.1 proper.2
    rw [Finset.sum_eq_single c]
    · exact ite_eq_left candidate
    · intro other _ different
      apply ite_eq_right
      intro hypotheses
      exact different (unique other hypotheses)
    · intro absent
      exact (absent (Finset.mem_univ c)).elim
  · rw [ite_eq_right proper]
    apply Finset.sum_eq_zero
    intro c _
    apply ite_eq_right
    intro candidate
    exact proper (P.proper_descendant_of_child c.property candidate.1 candidate.2)

end Unfoldings.AscendingParents
