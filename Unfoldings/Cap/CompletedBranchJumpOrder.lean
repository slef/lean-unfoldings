module

public import Unfoldings.Cap.CompletedVertexExcursions
public import Unfoldings.Cap.CompletedBankPositionOrder

/-! Derived signs of actual branching-bank jumps, including all intermediate sibling openings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

theorem boundaryPosition_turn_eq_next (j : Fin (N.completedContour.length + 1)) :
    D.boundaryPosition (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point j)) =
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) j)) := by
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex N.completedRetain
    N.completedContour.cycle N.completedContour.closes j)
  change C.boundaryEndVertex N.completedRetain
    (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point j)) =
      C.boundaryEndVertex N.completedRetain
        (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) j)) at next
  exact congrArg (fun v => D.toPlane (C.vertexPoint N.completedRetain v)) next

theorem parentEntrancePoint_parent_index
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
    N.parentEntrancePoint D e 0 =
      D.boundaryPosition (N.completedContour.cycle.point (N.parentBankOpening D e).enter) := by
  simp only [parentEntrancePoint, zero_smul, sub_zero]

theorem parentEntrancePoint_child_index
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
    N.parentEntrancePoint D e 1 = D.boundaryPosition (N.completedContour.cycle.point
      (finRotate (N.completedContour.length + 1) (N.parentBankOpening D e).enter)) := by
  let O := N.parentBankOpening D e
  have ray : -N.parentEntryVector D e =
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) O.enter)) -
      D.boundaryPosition (N.completedContour.cycle.point O.enter) :=
    O.entrance_ray.symm.trans (D.boundaryRay_eq_cycle_displacement N.completedContour.cycle
      N.completedContour.closes O.enter)
  calc
    _ = D.boundaryPosition (N.completedContour.cycle.point O.enter) +
        (-N.parentEntryVector D e) := by rw [parentEntrancePoint, one_smul, sub_eq_add_neg]
    _ = _ := by rw [ray]; abel

theorem parentExitPoint_child_index
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
    N.parentExitPoint D e 1 =
      D.boundaryPosition (N.completedContour.cycle.point (N.parentBankOpening D e).leave) := by
  let O := N.parentBankOpening D e
  have ray : N.parentExitVector D e =
      D.boundaryPosition (C.boundaryTurn N.completedRetain
        (N.completedContour.cycle.point O.leave)) -
        D.boundaryPosition (N.completedContour.cycle.point O.leave) :=
    O.exit_ray.symm.trans (D.boundaryRay_eq_positions _)
  change D.boundaryPosition (C.boundaryTurn N.completedRetain
    (N.completedContour.cycle.point O.leave)) - (1 : ℝ) • N.parentExitVector D e = _
  rw [one_smul, ray]
  abel

theorem parentExitPoint_parent_index
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
    N.parentExitPoint D e 0 = D.boundaryPosition (N.completedContour.cycle.point
      (finRotate (N.completedContour.length + 1) (N.parentBankOpening D e).leave)) := by
  simp only [parentExitPoint, zero_smul, sub_zero]
  exact N.boundaryPosition_turn_eq_next D _

namespace FiveSectorFrameData

variable {N D} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- Every selected sibling opening contributes up-left; arbitrary flat branches contribute zero. -/
theorem excursion_gap_order (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) (E : N.ContourExcursion e) :
    (B.sectorFrame i (D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.last)) -
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.first)))).re ≤ 0 ∧
    0 ≤ (B.sectorFrame i (D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.last)) -
      D.boundaryPosition (N.completedContour.cycle.point
        (finRotate (N.completedContour.length + 1) E.first)))).im := by
  classical
  rw [E.displacement D, map_sum]
  simp only [Complex.re_sum, Complex.im_sum]
  constructor
  · apply Finset.sum_nonpos
    intro v _
    split_ifs with selected
    · exact (B.descendant_vector_gap_order i e sectors budget v
        (E.selected_descendant D v selected)).1
    · simp only [map_zero, Complex.zero_re, le_refl]
  · apply Finset.sum_nonneg
    intro v _
    split_ifs with selected
    · exact (B.descendant_vector_gap_order i e sectors budget v
        (E.selected_descendant D v selected)).2
    · simp only [map_zero, Complex.zero_im, le_refl]

/-- Every actual copy of the child vertex lies up-left of the entrance child copy. -/
theorem vertex_entrance_gap_order (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (target : Fin (N.completedContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val) :
    (B.sectorFrame i (D.boundaryPosition (N.completedContour.cycle.point target) -
      N.parentEntrancePoint D e 1)).re ≤ 0 ∧
    0 ≤ (B.sectorFrame i (D.boundaryPosition (N.completedContour.cycle.point target) -
      N.parentEntrancePoint D e 1)).im := by
  rw [N.parentEntrancePoint_child_index D]
  by_cases same : finRotate (N.completedContour.length + 1)
      (N.parentBankOpening D e).enter = target
  · rw [same, sub_self, map_zero]
    exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨E, first, last⟩ :=
      (N.parentBankOpening D e).exists_entrance_excursion target vertex same
    have order := B.excursion_gap_order i e sectors budget E
    rw [first, last] at order
    exact order

/-- Every actual copy lies down-right of the exit child copy. -/
theorem vertex_exit_gap_order (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (target : Fin (N.completedContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val) :
    (B.sectorFrame i (N.parentExitPoint D e 1 -
      D.boundaryPosition (N.completedContour.cycle.point target))).re ≤ 0 ∧
    0 ≤ (B.sectorFrame i (N.parentExitPoint D e 1 -
      D.boundaryPosition (N.completedContour.cycle.point target))).im := by
  rw [N.parentExitPoint_child_index D]
  by_cases same : target = (N.parentBankOpening D e).leave
  · rw [same, sub_self, map_zero]
    exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨E, first, last⟩ := (N.parentBankOpening D e).exists_exit_excursion target vertex same
    have order := B.excursion_gap_order i e sectors budget E
    rw [first, last] at order
    exact order

/-- The actual right bank jumps right/down and the actual left bank jumps left/up at a branch. -/
theorem parent_child_bank_jump_order (i : FiveSector)
    (e c : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parent : N.spanningCompletion.parents.parent c.val = e.val)
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    ((B.sectorFrame i (N.parentEntrancePoint D c 0)).re ≤
        (B.sectorFrame i (N.parentEntrancePoint D e 1)).re ∧
      (B.sectorFrame i (N.parentEntrancePoint D e 1)).im ≤
        (B.sectorFrame i (N.parentEntrancePoint D c 0)).im) ∧
    ((B.sectorFrame i (N.parentExitPoint D e 1)).re ≤
        (B.sectorFrame i (N.parentExitPoint D c 0)).re ∧
      (B.sectorFrame i (N.parentExitPoint D c 0)).im ≤
        (B.sectorFrame i (N.parentExitPoint D e 1)).im) := by
  constructor
  · rw [N.parentEntrancePoint_parent_index D c]
    simpa only [map_sub, Complex.sub_re, Complex.sub_im, sub_nonpos, sub_nonneg] using
      B.vertex_entrance_gap_order i e sectors budget (N.parentBankOpening D c).enter
        ((N.parentBankOpening D c).entrance_vertex.trans parent)
  · rw [N.parentExitPoint_parent_index D c]
    simpa only [map_sub, Complex.sub_re, Complex.sub_im, sub_nonpos, sub_nonneg] using
      B.vertex_exit_gap_order i e sectors budget
        (finRotate (N.completedContour.length + 1) (N.parentBankOpening D c).leave)
        ((N.parentBankOpening D c).exit_next_vertex.trans parent)

end FiveSectorFrameData
end Unfoldings.ConvexCap.RadialCutForest
