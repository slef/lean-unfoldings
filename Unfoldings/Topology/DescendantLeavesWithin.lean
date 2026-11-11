module

public import Unfoldings.Topology.DescendantLeaves

/-! A sweep coordinate need only ascend on the descendant subtree under consideration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V)

theorem exists_descendant_leaf_within (height : V → ℝ) (e : V) (nonroot : e ∉ P.roots)
    (ascending : ∀ v, P.Ancestor v e → v ∉ P.roots → height v < height (P.parent v)) :
    ∃ leaf : V, P.Ancestor leaf e ∧ leaf ∉ P.roots ∧ height leaf ≤ height e ∧
      ∀ child ∉ P.roots, P.parent child ≠ leaf := by
  let := Fintype.ofFinite V
  have present : (P.descendants e).Nonempty :=
    ⟨e, (P.mem_descendants e e).mpr (P.ancestor_refl e)⟩
  obtain ⟨leaf, member, minimal⟩ := (P.descendants e).exists_min_image height present
  have reaches := (P.mem_descendants leaf e).mp member
  refine ⟨leaf, reaches, P.descendant_nonroot nonroot reaches,
    minimal e ((P.mem_descendants e e).mpr (P.ancestor_refl e)), ?_⟩
  intro child child_nonroot parent
  have child_reaches : P.Ancestor child e := (show P.Ancestor child leaf from ⟨1, parent⟩).trans
    P reaches
  have lower := minimal child ((P.mem_descendants child e).mpr child_reaches)
  have greater := ascending child child_reaches child_nonroot
  rw [parent] at greater
  exact not_lt_of_ge lower greater

end Unfoldings.AscendingParents
