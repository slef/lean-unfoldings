module

public import Unfoldings.Cap.CompletedBankPositionOrder
public import Unfoldings.Geometry.StrictQuadrantRotation

/-! Completed-parent bank noncrossing, with arbitrary additional flat branches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} {R : K.RadialCutForest q cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1}
  {D : FacewiseDevelopment C R.completedRetain}
  (B : R.FiveSectorFrameData positive small D)

/-- A positive whole-subtree curvature gives a strict actual paired-vector opening. -/
theorem parent_vector_strict_order
    (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (curved : 0 < R.completedSubtreeCurvature e.val) :
    (B.sectorFrame i
      (R.parentExitVector D e - R.parentEntryVector D e)).re < 0 ∧
    0 < (B.sectorFrame i
      (R.parentExitVector D e - R.parentEntryVector D e)).im := by
  let O := R.parentBankOpening D e
  have first := B.quadrants i O.entranceFace _ inside
    (R.completed_parent_direction_ne_zero e.val e.property)
  have last := B.quadrants i O.exitFace _ inside
    (R.completed_parent_direction_ne_zero e.val e.property)
  have strict := quadrant_rotation_coordinate_strict curved
    ((R.completedSubtreeCurvature_le_total e.val).trans_lt budget) (B.parent_rotation i O)
    first.1 first.2 last.1 last.2
  simpa only [framedDirection_eq, map_sub, Complex.sub_re, Complex.sub_im,
    sub_neg, sub_pos, parentExitVector, parentEntryVector] using strict

include B in
/-- A common point on the two actual bank segments must have matched parameters. -/
theorem bank_intersection_parameter_eq
    (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sectors : R.CurvedSubtreeInSector (t := t) i e)
    {s r : ℝ} (_s_le : s ≤ 1) (r_le : r ≤ 1)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (same : R.parentEntrancePoint D e s = R.parentExitPoint D e r) : s = r := by
  let frame := B.sectorFrame i
  have direction := B.quadrants i (R.parentBankOpening D e).entranceFace _ inside
    (R.completed_parent_direction_ne_zero e.val e.property)
  change 0 < (frame (R.parentEntryVector D e)).re ∧
    0 < (frame (R.parentEntryVector D e)).im at direction
  have ordered := B.matched_bank_points_order i e sectors r r_le budget
  change (frame _).re ≤ (frame _).re ∧ (frame _).im ≤ (frame _).im at ordered
  have coordinates (a : ℝ) : frame (R.parentEntrancePoint D e a) =
      frame (D.boundaryPosition
        (R.completedContour.cycle.point (R.parentBankOpening D e).enter)) -
      a • frame (R.parentEntryVector D e) := by
    rw [parentEntrancePoint, map_sub, map_smul]
  have h := congrArg frame same
  rcases lt_trichotomy s r with before | equal | after
  · have strict := mul_lt_mul_of_pos_right before direction.1
    have first := congrArg Complex.re (coordinates s)
    have last := congrArg Complex.re (coordinates r)
    have equal := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul] at first last
    linarith [ordered.1]
  · exact equal
  · have strict := mul_lt_mul_of_pos_right after direction.2
    have first := congrArg Complex.im (coordinates s)
    have last := congrArg Complex.im (coordinates r)
    have equal := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.smul_im, smul_eq_mul] at first last
    linarith [ordered.2]

/-- Positive descendant curvature strictly separates matched points before the child endpoint. -/
theorem matched_bank_strict_horizontal
    (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sectors : R.CurvedSubtreeInSector (t := t) i e) {s : ℝ} (before_child : s < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (curved : 0 < R.completedSubtreeCurvature e.val) :
    (B.sectorFrame i (R.parentExitPoint D e s)).re <
      (B.sectorFrame i (R.parentEntrancePoint D e s)).re := by
  classical
  let frame := B.sectorFrame i
  have proper :
      (frame (∑ v ∈ Finset.univ.erase e, if R.spanningCompletion.parents.Ancestor v.val e.val then
        R.parentExitVector D v - R.parentEntryVector D v else 0)).re ≤ 0 := by
    simp only [map_sum, Complex.re_sum]
    apply Finset.sum_nonpos
    intro v _
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order i e sectors budget.le v reaches).1
    · simp only [map_zero, Complex.zero_re, le_refl]
  have top := (B.parent_vector_strict_order i e inside budget curved).1
  have negative := add_neg_of_nonpos_of_neg proper
    (mul_neg_of_pos_of_neg (sub_pos.mpr before_child) top)
  have gap : frame (R.parentExitPoint D e s) - frame (R.parentEntrancePoint D e s) =
      frame (∑ v ∈ Finset.univ.erase e, if R.spanningCompletion.parents.Ancestor v.val e.val then
        R.parentExitVector D v - R.parentEntryVector D v else 0) +
      (1 - s) • frame (R.parentExitVector D e - R.parentEntryVector D e) := by
    rw [← map_sub, R.matched_bank_gap_eq D e s, map_add, map_smul]
  have re_gap := congrArg Complex.re gap
  simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] at re_gap
  change (frame _).re < (frame _).re
  linarith

include B in
/-- Positive subtree curvature makes the two actual parent-bank interiors disjoint. -/
theorem parent_bank_interiors_ne
    (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sectors : R.CurvedSubtreeInSector (t := t) i e)
    {s r : ℝ} (s_before : s < 1) (r_before : r < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (curved : 0 < R.completedSubtreeCurvature e.val) :
    R.parentEntrancePoint D e s ≠ R.parentExitPoint D e r := by
  intro same
  have parameters := B.bank_intersection_parameter_eq i e inside sectors
    s_before.le r_before.le budget.le same
  subst r
  have strict := B.matched_bank_strict_horizontal i e inside sectors s_before budget curved
  rw [same] at strict
  exact (lt_irrefl _ strict)

include B in
/-- Any contact before the child endpoint has zero whole-subtree curvature. -/
theorem parent_bank_contact_flat
    (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sectors : R.CurvedSubtreeInSector (t := t) i e)
    {s r : ℝ} (s_before : s < 1) (r_before : r < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (same : R.parentEntrancePoint D e s = R.parentExitPoint D e r) :
    R.completedSubtreeCurvature e.val = 0 := by
  apply le_antisymm _ (R.completedSubtreeCurvature_nonneg e.val)
  by_contra positive
  exact B.parent_bank_interiors_ne i e inside sectors s_before r_before budget
    (lt_of_not_ge positive) same

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
