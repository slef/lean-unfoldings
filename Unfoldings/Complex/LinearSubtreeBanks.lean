module

public import Unfoldings.Complex.LinearSubtreeContour
public import Unfoldings.Complex.OrientedParentBanks

/-! The ordinary subtree interval has the two named original parent banks as its endpoints. -/

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
/-- Linear order, original vertex region and original seam-side names are constructed together. -/
theorem exists_named_linear_subtree_interval (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) :
    ∃ enter leave : Fin (Q.length + 1), ∃ side : Bool,
      enter.val < leave.val ∧
      (∀ i, P.Ancestor (C.contourOriginalVertex S Q i) vertex ↔
        enter.val < i.val ∧ i.val ≤ leave.val) ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point enter)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) (!side) := by
  obtain ⟨enter, leave, different, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits S roots Q.cycle Q.closes Q.covers vertex nonroot
  obtain ⟨side, first, last⟩ :=
    C.opposite_parent_banks_of_exits S roots Q vertex nonroot enter leave different enters leaves
  have outside : ¬ C.SubtreeBoundaryInside S Q.cycle vertex 0 :=
    fun member => P.descendant_nonroot nonroot member starts
  obtain ⟨ordered, interval⟩ := finRotate_two_exits_linear_interval
    (C.SubtreeBoundaryInside S Q.cycle vertex) enter leave enters leaves stable outside
  exact ⟨enter, leave, side, ordered, interval, first, last⟩

/-- Any named bank of this original parent seam is one of the interval's two ends. -/
theorem named_parent_bank_index_eq (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (enter leave j : Fin (Q.length + 1)) (side other : Bool)
    (first : (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point enter)).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S vertex nonroot) side)
    (last : (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point leave)).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S vertex nonroot) (!side))
    (named : (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point j)).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S vertex nonroot) other) : j = enter ∨ j = leave := by
  have either : other = side ∨ other = !side := by
    cases other <;> cases side <;> simp
  rcases either with same | same
  · exact Or.inl (C.boundaryChain_banks_injective (C.selectedRetain S) Q.cycle
      (by dsimp only; rw [named, first, same]))
  · exact Or.inr (C.boundaryChain_banks_injective (C.selectedRetain S) Q.cycle
      (by dsimp only; rw [named, last, same]))

end Unfoldings.TriangleComplex
