module

public import Unfoldings.Cap.CompletedBranchDisplacements

/-! Matched actual completed-bank points and their exact descendant gap identity. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

/-- The actual entrance bank, parametrized from its parent copy toward its child. -/
def parentEntrancePoint (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) (s
  : ℝ) : Plane :=
  D.boundaryPosition (N.completedContour.cycle.point (N.parentBankOpening D e).enter) -
    s • N.parentEntryVector D e

/-- The actual exit bank, parametrized from its parent copy toward its child. -/
def parentExitPoint (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) (s :
  ℝ) : Plane :=
  D.boundaryPosition (C.boundaryTurn N.completedRetain
      (N.completedContour.cycle.point (N.parentBankOpening D e).leave)) -
    s • N.parentExitVector D e

open scoped Classical in
/-- Every branch contributes its complete gap; the top edge contributes its remaining fraction. -/
theorem matched_bank_gap_eq (e : {v : C.Vertex Set.univ // v ∉
  N.spanningCompletion.parents.roots}) (s : ℝ) :
    N.parentExitPoint D e s - N.parentEntrancePoint D e s =
      (∑ v ∈ Finset.univ.erase e, if N.spanningCompletion.parents.Ancestor v.val e.val then
        N.parentExitVector D v - N.parentEntryVector D v else 0) +
      (1 - s) • (N.parentExitVector D e - N.parentEntryVector D e) := by
  classical
  let term (v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :=
    if N.spanningCompletion.parents.Ancestor v.val e.val then
      N.parentExitVector D v - N.parentEntryVector D v else 0
  have split_sum := Finset.sum_erase_add Finset.univ term (Finset.mem_univ e)
  have top : term e = N.parentExitVector D e - N.parentEntryVector D e := by
    simp only [term, N.spanningCompletion.parents.ancestor_refl, ite_true]
  rw [top] at split_sum
  have positions : N.parentExitPoint D e s - N.parentEntrancePoint D e s =
      N.parentPositionGap D e - s •
        (N.parentExitVector D e - N.parentEntryVector D e) := by
    dsimp only [parentExitPoint, parentEntrancePoint, parentPositionGap]
    rw [smul_sub]
    abel
  rw [positions, N.parent_position_gap_eq_descendant_sum D e, ← split_sum]
  change (∑ v ∈ Finset.univ.erase e, term v) + _ - _ =
    (∑ v ∈ Finset.univ.erase e, term v) + _
  rw [sub_smul, one_smul]
  abel

end Unfoldings.ConvexCap.RadialCutForest
