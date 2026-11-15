module

public import Unfoldings.Complex.RootwardBankEnumeration
public import Unfoldings.Topology.ChildSubtrees

/-! Upcoming surviving original banks have the strict order of the rootward parent path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include roots starts in
/-- Strict original ancestry forces the strict order of the actual surviving bank indices. -/
theorem rootward_bank_index_lt_of_ancestor (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i)
    (ancestor : P.Ancestor (C.contourOriginalVertex S Q j.val)
      (C.contourOriginalVertex S Q k.val))
    (different : C.contourOriginalVertex S Q j.val ≠ C.contourOriginalVertex S Q k.val) :
    j.val.val < k.val.val := by
  have data := C.future_current_bank_rootward S roots Q starts i k.val
    k.property.1 k.property.2.1 k.property.2.2
  obtain ⟨enter, leave, side, _ordered, interval, first, last⟩ :=
    C.exists_named_linear_subtree_interval S roots Q starts
      (C.contourOriginalVertex S Q k.val) data.1
  obtain ⟨_, other, named⟩ := C.future_current_bank_named S roots Q starts i k.val
    k.property.1 k.property.2.1 k.property.2.2
  have at_leave : k.val = leave := by
    rcases C.named_parent_bank_index_eq S Q (C.contourOriginalVertex S Q k.val) data.1
        enter leave k.val side other first last named with at_entry | at_leave
    · have bounds := (interval i).mp data.2.2.1
      have future := k.property.1
      have values := congrArg Fin.val at_entry
      omega
    · exact at_leave
  have bounds := (interval j.val).mp ancestor
  have le_index : j.val.val ≤ k.val.val := by simpa only [at_leave] using bounds.2
  have ne_index : j.val.val ≠ k.val.val := by
    intro same
    exact different (congrArg (C.contourOriginalVertex S Q) (Fin.ext same))
  omega

include roots starts in
/-- The bank order strictly increases the original potential. The stored edges are therefore
in their original rootward order and cannot repeat or reverse an original ancestor segment. -/
theorem rootward_bank_order_of_parent (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) : j.val.val < k.val.val := by
  have data := C.future_current_bank_rootward S roots Q starts i j.val
    j.property.1 j.property.2.1 j.property.2.2
  apply C.rootward_bank_index_lt_of_ancestor S roots Q starts i j k
  · exact parent ▸ P.ancestor_parent (C.contourOriginalVertex S Q j.val)
  · intro same
    have fixed := parent.trans same.symm
    exact (P.ascending _ data.1).ne (congrArg P.height fixed).symm

include roots starts in
/-- The ordinary bank-index order is exactly the strict original ancestor order. -/
theorem rootward_bank_index_lt_iff (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i) :
    j.val.val < k.val.val ↔
      P.Ancestor (C.contourOriginalVertex S Q j.val) (C.contourOriginalVertex S Q k.val) ∧
        C.contourOriginalVertex S Q j.val ≠ C.contourOriginalVertex S Q k.val := by
  constructor
  · intro before
    have different : C.contourOriginalVertex S Q j.val ≠ C.contourOriginalVertex S Q k.val := by
      intro same
      have bank_eq : j = k := (C.rootwardBankEquiv S roots Q starts i).injective
        (Subtype.ext same)
      exact before.ne (congrArg (fun b : C.RootwardBank S Q i => b.val.val) bank_eq)
    have first := C.future_current_bank_rootward S roots Q starts i j.val
      j.property.1 j.property.2.1 j.property.2.2
    have last := C.future_current_bank_rootward S roots Q starts i k.val
      k.property.1 k.property.2.1 k.property.2.2
    rcases P.ancestors_comparable first.2.2.1 last.2.2.1 with forward | backward
    · exact ⟨forward, different⟩
    · have reverse := C.rootward_bank_index_lt_of_ancestor S roots Q starts i k j
        backward different.symm
      omega
  · exact fun both => C.rootward_bank_index_lt_of_ancestor S roots Q starts i j k both.1 both.2

end Unfoldings.TriangleComplex
