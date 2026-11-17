module

public import Unfoldings.Geometry.SpatialEnvelopeCutBankParameters
public import Unfoldings.Polyhedron.DirectedBankSubinterval

/-! Either original cut-bank orientation spans precisely the original projected seam edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance cutBankSegmentIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (retain : Set T.pairedComplex.Seam)

/-- The literal starting and ending spatial positions of either bank span the
same original projected edge, in either chosen starting orientation. -/
theorem horizontal_cutBank_directed_segment (s : T.pairedComplex.CutSeam retain)
    (side flag : Bool) :
    segment ℝ
      (Cap.horizontal (T.pairedFolding.boundaryPosition
        ((T.pairedComplex.boundaryEndEquiv retain).symm
          (T.pairedComplex.cutBank retain s side, flag))))
      (Cap.horizontal (T.pairedFolding.boundaryPosition
        (T.pairedComplex.boundaryTurn retain ((T.pairedComplex.boundaryEndEquiv retain).symm
          (T.pairedComplex.cutBank retain s side, flag))))) =
      (T.projectedTriangle (T.pairedComplex.left s.val).face).edge
        (T.pairedComplex.left s.val).edge := by
  let bank := T.pairedComplex.cutBank retain s side
  let p := (T.pairedComplex.boundaryEndEquiv retain).symm (bank, flag)
  have ends (u : unitInterval) (endpoint : u.val = 0 ∨ u.val = 1) :
      Cap.horizontal (T.pairedFolding.toSpace retain (T.pairedComplex.directedBoundaryPath p u)) =
          (T.projectedTriangle (T.pairedComplex.left s.val).face).vertex
            (T.pairedComplex.left s.val).edge ∨
      Cap.horizontal (T.pairedFolding.toSpace retain (T.pairedComplex.directedBoundaryPath p u)) =
          (T.projectedTriangle (T.pairedComplex.left s.val).face).vertex
            (Triangle.next (T.pairedComplex.left s.val).edge) := by
    have position := congrArg (fun z => Cap.horizontal (T.pairedFolding.toSpace retain z))
      (T.pairedComplex.directedBoundaryPath_from_bank bank flag u)
    have original := T.horizontal_cutBank_endpoint retain s side
      (T.pairedComplex.bankParameterFromEnd bank flag u)
      (T.pairedComplex.bankParameterFromEnd_isVertex_of_endpoint bank flag u endpoint)
    exact original.imp (position.trans ·) (position.trans ·)
  have initial := ends 0 (Or.inl rfl)
  have final := ends 1 (Or.inr rfl)
  simp only [T.pairedFolding.directedBoundaryPath_lineMap,
    show (0 : unitInterval).val = (0 : ℝ) from rfl,
    AffineMap.lineMap_apply_zero] at initial
  simp only [T.pairedFolding.directedBoundaryPath_lineMap,
    show (1 : unitInterval).val = (1 : ℝ) from rfl,
    AffineMap.lineMap_apply_one] at final
  have different := T.horizontal_boundaryPosition_ne p
  rcases initial with first | first
  · rcases final with last | last
    · exact (different (first.trans last.symm)).elim
    · rw [first, last]
      rfl
  · rcases final with last | last
    · rw [first, last, segment_symm]
      rfl
    · exact (different (first.trans last.symm)).elim

end Unfoldings.SpatialEnvelope.Triangulation
