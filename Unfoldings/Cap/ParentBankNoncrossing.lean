module

public import Unfoldings.Cap.MatchedBankPoints
public import Unfoldings.Geometry.StrictQuadrantRotation

/-!
# Noncrossing of the actual two banks of a branching parent seam

Any common point has the same physical parameter on both banks. If the entire
descendant subtree has positive curvature, their relative interiors are disjoint.
For zero subtree curvature, the two directed vectors agree, permitting contact.
This does not yet compare banks of different original seams or different trees.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

/-- A positive whole-subtree curvature gives a strict actual paired-vector opening. -/
theorem parent_vector_strict_order
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (curved : 0 < M.subtreeCurvature e.val) :
    (B.sectorFrame (K.sourceSectorLabel t origin e.val)
      (M.parentExitVector D e - M.parentEntryVector D e)).re < 0 ∧
    0 < (B.sectorFrame (K.sourceSectorLabel t origin e.val)
      (M.parentExitVector D e - M.parentEntryVector D e)).im := by
  let O := M.parentBankOpening D e
  have first := B.parent_quadrants O.entranceFace e.val e.property
  have last := B.parent_quadrants O.exitFace e.val e.property
  have strict := quadrant_rotation_coordinate_strict curved
    ((M.subtreeCurvature_le_total e.val).trans_lt budget) (B.parent_rotation O)
    first.1 first.2 last.1 last.2
  simpa only [framedDirection_eq, map_sub, Complex.sub_re, Complex.sub_im,
    sub_neg, sub_pos, parentExitVector, parentEntryVector] using strict

include B in
/-- A common point on the two actual bank segments must have matched parameters. -/
theorem bank_intersection_parameter_eq
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    {s r : ℝ} (_s_le : s ≤ 1) (r_le : r ≤ 1)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (same : M.parentEntrancePoint D e s = M.parentExitPoint D e r) : s = r := by
  let frame := B.sectorFrame (K.sourceSectorLabel t origin e.val)
  have direction := B.parent_quadrants (M.parentBankOpening D e).entranceFace e.val e.property
  change 0 < (frame (M.parentEntryVector D e)).re ∧
    0 < (frame (M.parentEntryVector D e)).im at direction
  have ordered := B.matched_bank_points_order e r r_le budget
  change (frame _).re ≤ (frame _).re ∧ (frame _).im ≤ (frame _).im at ordered
  have coordinates (a : ℝ) : frame (M.parentEntrancePoint D e a) =
      frame (D.boundaryPosition
        (M.projectionContour.cycle.point (M.parentBankOpening D e).enter)) -
      a • frame (M.parentEntryVector D e) := by
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
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) {s : ℝ} (before_child : s < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (curved : 0 < M.subtreeCurvature e.val) :
    (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentExitPoint D e s)).re <
      (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentEntrancePoint D e s)).re := by
  classical
  let frame := B.sectorFrame (K.sourceSectorLabel t origin e.val)
  have proper :
      (frame (∑ v ∈ Finset.univ.erase e, if M.parents.Ancestor v.val e.val then
        M.parentExitVector D v - M.parentEntryVector D v else 0)).re ≤ 0 := by
    simp only [map_sum, Complex.re_sum]
    apply Finset.sum_nonpos
    intro v _
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order budget.le reaches).1
    · simp only [map_zero, Complex.zero_re, le_refl]
  have top := (B.parent_vector_strict_order e budget curved).1
  have negative := add_neg_of_nonpos_of_neg proper
    (mul_neg_of_pos_of_neg (sub_pos.mpr before_child) top)
  have gap : frame (M.parentExitPoint D e s) - frame (M.parentEntrancePoint D e s) =
      frame (∑ v ∈ Finset.univ.erase e, if M.parents.Ancestor v.val e.val then
        M.parentExitVector D v - M.parentEntryVector D v else 0) +
      (1 - s) • frame (M.parentExitVector D e - M.parentEntryVector D e) := by
    rw [← map_sub, M.matched_bank_gap_eq D e s, map_add, map_smul]
  have re_gap := congrArg Complex.re gap
  simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] at re_gap
  change (frame _).re < (frame _).re
  linarith

include B in
/-- Positive subtree curvature makes the two actual parent-bank interiors disjoint. -/
theorem parent_bank_interiors_ne
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    {s r : ℝ} (s_before : s < 1) (r_before : r < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (curved : 0 < M.subtreeCurvature e.val) :
    M.parentEntrancePoint D e s ≠ M.parentExitPoint D e r := by
  intro same
  have parameters := B.bank_intersection_parameter_eq e s_before.le r_before.le budget.le same
  subst r
  have strict := B.matched_bank_strict_horizontal e s_before budget curved
  rw [same] at strict
  exact (lt_irrefl _ strict)

include B in
/-- Any contact before the child endpoint has zero whole-subtree curvature. -/
theorem parent_bank_contact_flat
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    {s r : ℝ} (s_before : s < 1) (r_before : r < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (same : M.parentEntrancePoint D e s = M.parentExitPoint D e r) :
    M.subtreeCurvature e.val = 0 := by
  apply le_antisymm _ (M.subtreeCurvature_nonneg e.val)
  by_contra positive
  exact B.parent_bank_interiors_ne e s_before r_before budget (lt_of_not_ge positive) same

/-- At zero whole-subtree curvature, the actual two outward bank vectors agree. -/
theorem parent_vectors_eq_of_flat
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (flat : M.subtreeCurvature e.val = 0) :
    M.parentExitVector D e = M.parentEntryVector D e := by
  have rotation := (M.parentBankOpening D e).rotation
  rw [flat, polarRay_zero, one_mul] at rotation
  exact (D.boundaryCycleFrame M.projectionContour.cycle).injective rotation

end Unfoldings.ConvexCap.SectorForest.SectorFrameData
