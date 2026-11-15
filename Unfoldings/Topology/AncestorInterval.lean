module

public import Unfoldings.Topology.AscendingForest

/-! An increasing parent orbit has antisymmetric ancestry and no vertex between parent neighbors. -/

@[expose] public section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V)

/-- Strict increase away from roots makes original ancestry antisymmetric. -/
theorem ancestor_antisymm {a b : V} (forward : P.Ancestor a b) (backward : P.Ancestor b a) :
    a = b := by
  by_contra different
  have nonroot : a ∉ P.roots := by
    intro root
    obtain ⟨n, at_b⟩ := forward
    exact different ((Function.iterate_fixed (P.fixed_root a root) n).symm.trans at_b)
  exact P.not_ancestor_parent_self nonroot
    (((P.ancestor_parent_iff different).mp forward).trans P backward)

/-- The closed original ancestor interval from a vertex to its parent has no other vertex. -/
theorem ancestor_between_parent {child middle : V} (first : P.Ancestor child middle)
    (last : P.Ancestor middle (P.parent child)) : middle = child ∨ middle = P.parent child := by
  by_cases same : middle = child
  · exact Or.inl same
  · exact Or.inr (P.ancestor_antisymm last
      ((P.ancestor_parent_iff (Ne.symm same)).mp first))

end Unfoldings.AscendingParents
