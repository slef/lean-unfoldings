module

public import Unfoldings.Cap.CompletedBranchJumpOrder
public import Unfoldings.Cap.CompletedParentBankNoncrossing
public import Unfoldings.Geometry.StrictQuadrantSums

/-! An actual branch excursion is zero whenever either controlling coordinate is zero. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem excursion_gap_coordinate_zero_iff (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) (E : N.ContourExcursion e) :
    let gap := D.boundaryPosition (N.completedContour.cycle.point
      (finRotate (N.completedContour.length + 1) E.last)) -
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.first))
    ((B.sectorFrame i gap).re = 0 ↔ gap = 0) ∧
      ((B.sectorFrame i gap).im = 0 ↔ gap = 0) := by
  classical
  let gap := D.boundaryPosition (N.completedContour.cycle.point
      (finRotate (N.completedContour.length + 1) E.last)) -
    D.boundaryPosition (N.completedContour.cycle.point
      (finRotate (N.completedContour.length + 1) E.first))
  let term := fun v : {w : C.Vertex Set.univ // w ∉ N.spanningCompletion.parents.roots} =>
    if E.region (N.parentBankOpening D v).enter then
      B.sectorFrame i (N.parentExitVector D v - N.parentEntryVector D v) else 0
  have displacement : B.sectorFrame i gap = ∑ v, term v := by
    dsimp only [gap]
    rw [E.displacement D, map_sum]
    simp only [term, apply_ite, map_zero]
  have strict (v : {w : C.Vertex Set.univ // w ∉ N.spanningCompletion.parents.roots}) :
      term v = 0 ∨ (term v).re < 0 ∧ 0 < (term v).im := by
    dsimp only [term]
    split_ifs with selected
    · by_cases curved : 0 < N.completedSubtreeCurvature v.val
      · right
        exact B.parent_vector_strict_order i v
          (sectors v (E.selected_descendant D v selected) curved) budget curved
      · left
        have flat : N.completedSubtreeCurvature v.val = 0 :=
          le_antisymm (le_of_not_gt curved) (N.completedSubtreeCurvature_nonneg v.val)
        rw [N.completed_parent_vectors_eq_of_flat v flat, sub_self, map_zero]
    · exact Or.inl rfl
  have horizontal := sum_re_zero_iff_of_strict_quadrant term strict
  have vertical := sum_im_zero_iff_of_strict_quadrant term strict
  rw [← displacement] at horizontal vertical
  have zero : B.sectorFrame i gap = 0 ↔ gap = 0 := by
    constructor
    · intro same
      exact (B.sectorFrame i).injective (same.trans (B.sectorFrame i).map_zero.symm)
    · intro same
      rw [same, map_zero]
  exact ⟨horizontal.trans zero, vertical.trans zero⟩

theorem vertex_entrance_horizontal_eq_iff (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (target : Fin (N.completedContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val) :
    (B.sectorFrame i (D.boundaryPosition (N.completedContour.cycle.point target) -
      N.parentEntrancePoint D e 1)).re = 0 ↔
      D.boundaryPosition (N.completedContour.cycle.point target) = N.parentEntrancePoint D e 1 := by
  rw [N.parentEntrancePoint_child_index D]
  by_cases same : finRotate (N.completedContour.length + 1)
      (N.parentBankOpening D e).enter = target
  · rw [same, sub_self, map_zero]
    simp only [Complex.zero_re]
  · obtain ⟨E, first, last⟩ :=
      (N.parentBankOpening D e).exists_entrance_excursion target vertex same
    have zero := (B.excursion_gap_coordinate_zero_iff i e sectors budget E).1
    rw [first, last] at zero
    simpa only [sub_eq_zero] using zero

theorem vertex_exit_vertical_eq_iff (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (target : Fin (N.completedContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val) :
    (B.sectorFrame i (N.parentExitPoint D e 1 -
      D.boundaryPosition (N.completedContour.cycle.point target))).im = 0 ↔
      D.boundaryPosition (N.completedContour.cycle.point target) = N.parentExitPoint D e 1 := by
  rw [N.parentExitPoint_child_index D]
  by_cases same : target = (N.parentBankOpening D e).leave
  · rw [same, sub_self, map_zero]
    simp only [Complex.zero_im]
  · obtain ⟨E, first, last⟩ :=
      (N.parentBankOpening D e).exists_exit_excursion target vertex same
    have zero := (B.excursion_gap_coordinate_zero_iff i e sectors budget E).2
    rw [first, last, sub_eq_zero] at zero
    exact zero.trans eq_comm

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
