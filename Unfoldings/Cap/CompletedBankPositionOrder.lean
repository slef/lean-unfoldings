module

public import Unfoldings.Cap.CompletedMatchedBankPoints
public import Unfoldings.Cap.CompletedBankVectorOrder

/-! Branching bank gaps remain ordered when only the nonzero openings share a sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)
  {t : ℝ} {D : FacewiseDevelopment C R.completedRetain}

/-- Only descendants with positive opening need the common sector constraint. -/
def CurvedSubtreeInSector (i : FiveSector)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots}) : Prop :=
  ∀ v : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots},
    R.spanningCompletion.parents.Ancestor v.val e.val →
    0 < R.completedSubtreeCurvature v.val →
      K.projectedVertex (R.spanningCompletion.parents.parent v.val) - K.projectedVertex v.val ∈
        closedFiveSector t i

/-- A flat branch has no vector opening, regardless of its direction. -/
theorem completed_parent_vectors_eq_of_flat
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (flat : R.completedSubtreeCurvature e.val = 0) :
    R.parentExitVector D e = R.parentEntryVector D e := by
  have rotation := (R.parentBankOpening D e).rotation
  rw [flat, polarRay_zero, one_mul] at rotation
  exact (D.boundaryCycleFrame R.completedContour.cycle).injective rotation

namespace FiveSectorFrameData

variable {R} {positive : 0 < t} {small : t < 1}
  (B : R.FiveSectorFrameData positive small D)

/-- Fixed sector coordinates for all actual developed position differences. -/
def sectorFrame (i : FiveSector) : Plane ≃ₗᵢ[ℝ] ℂ :=
  (R.calibratedFrame D B.anchor B.reference).trans
    (Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place)

theorem framedDirection_eq (i : FiveSector) (f : Face) (direction : Plane) :
    B.framedDirection i f direction = B.sectorFrame i (D.developedDirection K f direction) := rfl

/-- Flat descendants contribute zero; every other paired-vector gap points left and up. -/
theorem descendant_vector_gap_order (i : FiveSector)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (sectors : R.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (v : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (reaches : R.spanningCompletion.parents.Ancestor v.val e.val) :
    (B.sectorFrame i (R.parentExitVector D v - R.parentEntryVector D v)).re ≤ 0 ∧
      0 ≤ (B.sectorFrame i (R.parentExitVector D v - R.parentEntryVector D v)).im := by
  by_cases curved : 0 < R.completedSubtreeCurvature v.val
  · have ordered := B.parent_vector_order i (R.parentBankOpening D v)
      (sectors v reaches curved) budget
    simpa only [framedDirection_eq, map_sub, Complex.sub_re, Complex.sub_im,
      sub_nonpos, sub_nonneg, parentExitVector, parentEntryVector] using ordered
  · have flat : R.completedSubtreeCurvature v.val = 0 :=
      le_antisymm (le_of_not_gt curved) (R.completedSubtreeCurvature_nonneg v.val)
    rw [R.completed_parent_vectors_eq_of_flat v flat, sub_self, map_zero]
    exact ⟨le_rfl, le_rfl⟩

/-- The actual two parent copies have the same coordinate order, including all branches. -/
theorem parent_position_gap_order (i : FiveSector)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (sectors : R.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    (B.sectorFrame i (R.parentPositionGap D e)).re ≤ 0 ∧
      0 ≤ (B.sectorFrame i (R.parentPositionGap D e)).im := by
  classical
  rw [R.parent_position_gap_eq_descendant_sum D e, map_sum]
  simp only [Complex.re_sum, Complex.im_sum]
  constructor
  · apply Finset.sum_nonpos
    intro v _
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order i e sectors budget v reaches).1
    · simp only [map_zero, Complex.zero_re, le_refl]
  · apply Finset.sum_nonneg
    intro v _
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order i e sectors budget v reaches).2
    · simp only [map_zero, Complex.zero_im, le_refl]

/-- Both actual endpoint copies and all matched bank points have the proved left/up order. -/
theorem matched_bank_points_order (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (sectors : R.CurvedSubtreeInSector (t := t) i e)
    (s : ℝ) (at_most_one : s ≤ 1)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    (B.sectorFrame i (R.parentExitPoint D e s)).re ≤
      (B.sectorFrame i (R.parentEntrancePoint D e s)).re ∧
    (B.sectorFrame i (R.parentEntrancePoint D e s)).im ≤
      (B.sectorFrame i (R.parentExitPoint D e s)).im := by
  classical
  let frame := B.sectorFrame i
  have proper :
      (frame (∑ v ∈ Finset.univ.erase e, if R.spanningCompletion.parents.Ancestor v.val e.val then
        R.parentExitVector D v - R.parentEntryVector D v else 0)).re ≤ 0 ∧
      0 ≤ (frame (∑ v ∈ Finset.univ.erase e, if R.spanningCompletion.parents.Ancestor v.val e.val
        then
        R.parentExitVector D v - R.parentEntryVector D v else 0)).im := by
    simp only [map_sum, Complex.re_sum, Complex.im_sum]
    constructor
    · apply Finset.sum_nonpos
      intro v _
      split_ifs with reaches
      · exact (B.descendant_vector_gap_order i e sectors budget v reaches).1
      · simp only [map_zero, Complex.zero_re, le_refl]
    · apply Finset.sum_nonneg
      intro v _
      split_ifs with reaches
      · exact (B.descendant_vector_gap_order i e sectors budget v reaches).2
      · simp only [map_zero, Complex.zero_im, le_refl]
  have top := B.descendant_vector_gap_order i e sectors budget e
    (R.spanningCompletion.parents.ancestor_refl e.val)
  have remaining : 0 ≤ 1 - s := sub_nonneg.mpr at_most_one
  have horizontal := add_nonpos proper.1 (mul_nonpos_of_nonneg_of_nonpos remaining top.1)
  have vertical := add_nonneg proper.2 (mul_nonneg remaining top.2)
  have gap : frame (R.parentExitPoint D e s) - frame (R.parentEntrancePoint D e s) =
      frame (∑ v ∈ Finset.univ.erase e, if R.spanningCompletion.parents.Ancestor v.val e.val then
        R.parentExitVector D v - R.parentEntryVector D v else 0) +
      (1 - s) • frame (R.parentExitVector D e - R.parentEntryVector D e) := by
    rw [← map_sub, R.matched_bank_gap_eq D e s, map_add, map_smul]
  have re_gap := congrArg Complex.re gap
  have im_gap := congrArg Complex.im gap
  simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] at re_gap
  simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul] at im_gap
  change (frame _).re ≤ (frame _).re ∧ (frame _).im ≤ (frame _).im
  constructor <;> linarith


end FiveSectorFrameData
end Unfoldings.ConvexCap.RadialCutForest
