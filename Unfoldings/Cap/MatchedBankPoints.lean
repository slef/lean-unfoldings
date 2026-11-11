module

public import Unfoldings.Cap.BankPositionOrder

/-!
# Matched points on actual branching parent banks

Move by the same fraction from each actual parent copy toward its child.
The gap is a sum of proper-descendant paired-vector differences plus the
remaining fraction of the top edge's paired-vector difference. Thus all
matched points, including both endpoints and flat contacts, are ordered.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (D : FacewiseDevelopment C M.retain)

/-- The actual entrance bank, parametrized from its parent copy toward its child. -/
def parentEntrancePoint (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s : ℝ) : Plane :=
  D.boundaryPosition (M.projectionContour.cycle.point (M.parentBankOpening D e).enter) -
    s • M.parentEntryVector D e

/-- The actual exit bank, parametrized from its parent copy toward its child. -/
def parentExitPoint (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s : ℝ) : Plane :=
  D.boundaryPosition (C.boundaryTurn M.retain
      (M.projectionContour.cycle.point (M.parentBankOpening D e).leave)) -
    s • M.parentExitVector D e

open scoped Classical in
/-- Every branch contributes its complete gap; the top edge contributes its remaining fraction. -/
theorem matched_bank_gap_eq (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s : ℝ) :
    M.parentExitPoint D e s - M.parentEntrancePoint D e s =
      (∑ v ∈ Finset.univ.erase e, if M.parents.Ancestor v.val e.val then
        M.parentExitVector D v - M.parentEntryVector D v else 0) +
      (1 - s) • (M.parentExitVector D e - M.parentEntryVector D e) := by
  classical
  let term (v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :=
    if M.parents.Ancestor v.val e.val then
      M.parentExitVector D v - M.parentEntryVector D v else 0
  have split_sum := Finset.sum_erase_add Finset.univ term (Finset.mem_univ e)
  have top : term e = M.parentExitVector D e - M.parentEntryVector D e := by
    simp only [term, M.parents.ancestor_refl, ite_true]
  rw [top] at split_sum
  have positions : M.parentExitPoint D e s - M.parentEntrancePoint D e s =
      M.parentPositionGap D e - s •
        (M.parentExitVector D e - M.parentEntryVector D e) := by
    dsimp only [parentExitPoint, parentEntrancePoint, parentPositionGap]
    rw [smul_sub]
    abel
  rw [positions, M.parent_position_gap_eq_descendant_sum D e, ← split_sum]
  change (∑ v ∈ Finset.univ.erase e, term v) + _ - _ =
    (∑ v ∈ Finset.univ.erase e, term v) + _
  rw [sub_smul, one_smul]
  abel

namespace SectorFrameData

variable {M D} {positive : 0 < t} {small : t < 1}
  (B : M.SectorFrameData positive small D)

/-- Both actual endpoint copies and all matched bank points have the proved left/up order. -/
theorem matched_bank_points_order (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (s : ℝ) (at_most_one : s ≤ 1)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentExitPoint D e s)).re ≤
      (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentEntrancePoint D e s)).re ∧
    (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentEntrancePoint D e s)).im ≤
      (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentExitPoint D e s)).im := by
  classical
  let frame := B.sectorFrame (K.sourceSectorLabel t origin e.val)
  have proper :
      (frame (∑ v ∈ Finset.univ.erase e, if M.parents.Ancestor v.val e.val then
        M.parentExitVector D v - M.parentEntryVector D v else 0)).re ≤ 0 ∧
      0 ≤ (frame (∑ v ∈ Finset.univ.erase e, if M.parents.Ancestor v.val e.val then
        M.parentExitVector D v - M.parentEntryVector D v else 0)).im := by
    simp only [map_sum, Complex.re_sum, Complex.im_sum]
    constructor
    · apply Finset.sum_nonpos
      intro v _
      split_ifs with reaches
      · exact (B.descendant_vector_gap_order budget reaches).1
      · simp only [map_zero, Complex.zero_re, le_refl]
    · apply Finset.sum_nonneg
      intro v _
      split_ifs with reaches
      · exact (B.descendant_vector_gap_order budget reaches).2
      · simp only [map_zero, Complex.zero_im, le_refl]
  have top := B.descendant_vector_gap_order budget (M.parents.ancestor_refl e.val)
  have remaining : 0 ≤ 1 - s := sub_nonneg.mpr at_most_one
  have horizontal := add_nonpos proper.1 (mul_nonpos_of_nonneg_of_nonpos remaining top.1)
  have vertical := add_nonneg proper.2 (mul_nonneg remaining top.2)
  have gap : frame (M.parentExitPoint D e s) - frame (M.parentEntrancePoint D e s) =
      frame (∑ v ∈ Finset.univ.erase e, if M.parents.Ancestor v.val e.val then
        M.parentExitVector D v - M.parentEntryVector D v else 0) +
      (1 - s) • frame (M.parentExitVector D e - M.parentEntryVector D e) := by
    rw [← map_sub, M.matched_bank_gap_eq D e s, map_add, map_smul]
  have re_gap := congrArg Complex.re gap
  have im_gap := congrArg Complex.im gap
  simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] at re_gap
  simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul] at im_gap
  change (frame _).re ≤ (frame _).re ∧ (frame _).im ≤ (frame _).im
  constructor <;> linarith

end SectorFrameData
end Unfoldings.ConvexCap.SectorForest
