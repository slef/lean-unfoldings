module

public import Unfoldings.Complex.ContourSavedParentFan
public import Unfoldings.Complex.AngleCutSums

/-! Sum the final contour wedges in the actual saved outgoing fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

local notation "Retain" => C.selectedRetain S
local notation "Visit[" j "]" => C.contourOriginalVertex S Q j
local notation "Copy[" j "]" => C.boundaryEndVertex Retain (Q.cycle.point j)
local notation "Interval[" v "," h "]" => C.contourParentInterval S Q roots starts v h
local notation "Stage[" i "]" => C.processedParentRetain S (C.contourFrontier S Q i)

open scoped Classical in
/-- A saved outgoing angle is the exact sum of the final roof angles in its contour suffix. -/
theorem contourSavedParentFan_angle_eq_sum
    (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots)
    (stage : Fin (Q.length + 1)) (cut : S.edge ⟨parent, nonroot⟩ ∉ Stage[stage]) :
    let exit := (Interval[parent,nonroot]).leave
    let inc := C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)
    C.totalAngle Stage[stage] (C.vertexForgetCuts inc Copy[exit]) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (Q.length + 1) =>
        Visit[j] = parent ∧ (j = exit ∨ stage.val ≤ j.val + 1)),
        C.totalAngle Retain Copy[j] := by
  classical
  let exit := (Interval[parent,nonroot]).leave
  let inc := C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)
  let copy (j : Fin (Q.length + 1)) := Copy[j]
  let saved := C.vertexForgetCuts inc (copy exit)
  let F := Finset.univ.filter (fun j : Fin (Q.length + 1) =>
    Visit[j] = parent ∧ (j = exit ∨ stage.val ≤ j.val + 1))
  let V := Finset.univ.filter (fun w : C.Vertex Retain => C.vertexForgetCuts inc w = saved)
  have category := C.contourSavedParentFan_forget_eq_iff S Q roots starts parent nonroot stage cut
  have image : F.image copy = V := by
    ext w
    constructor
    · intro member
      obtain ⟨j, inside, rfl⟩ := Finset.mem_image.mp member
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (category j).mpr
        (Finset.mem_filter.mp inside).2⟩
    · intro member
      have inside : C.vertexForgetCuts inc w = saved := (Finset.mem_filter.mp member).2
      let restore := C.vertexForgetCuts (Set.subset_univ (Stage[stage]))
      have original_of_copy (z : C.Vertex Retain) :
          restore (C.vertexForgetCuts inc z) = C.vertexForgetCuts (Set.subset_univ _) z := by
        obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective Retain z
        rfl
      have original : C.vertexForgetCuts (Set.subset_univ Retain) w = parent :=
        (original_of_copy w).symm.trans ((congrArg restore inside).trans
          ((original_of_copy (copy exit)).trans
            (C.contourParentInterval_exit_original S Q roots starts parent nonroot).1))
      let bound : C.IsBoundaryVertex Retain w :=
        C.selectedCut_nonroot_copy_boundary S w (original.symm ▸ nonroot)
      let E := C.boundaryCycleVertexEquiv Retain Q.cycle Q.closes Q.covers
      obtain ⟨j, label⟩ := E.surjective ⟨w, bound⟩
      have tagged : copy j = w := congrArg Subtype.val label
      exact Finset.mem_image.mpr ⟨j,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (category j).mp
          ((congrArg (C.vertexForgetCuts inc) tagged).trans inside)⟩, tagged⟩
  have total := C.sum_totalAngle_vertexForgetCuts inc saved
  rw [← Finset.sum_filter] at total
  have injective : Function.Injective copy := fun _ _ equal =>
    C.boundaryCycle_vertices_injective Retain Q.cycle Q.closes equal
  change C.totalAngle Stage[stage] saved = ∑ j ∈ F, C.totalAngle Retain (copy j)
  rw [← total]
  change (∑ w ∈ V, C.totalAngle Retain w) = _
  rw [← image]
  exact Finset.sum_image injective.injOn

open scoped Classical in
/-- Between two saved outgoing angles, exactly the roof wedges between the two
processing times are removed. The exit wedge belongs to both saved fans. -/
theorem contourSavedParentFan_angle_sub_eq_sum
    (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots)
    (earlier later : Fin (Q.length + 1)) (ordered : earlier.val ≤ later.val)
    (old_cut : S.edge ⟨parent, nonroot⟩ ∉ Stage[earlier])
    (new_cut : S.edge ⟨parent, nonroot⟩ ∉ Stage[later]) :
    let exit := (Interval[parent,nonroot]).leave
    let old_inc := C.selectedRetain_subset_processed S (C.contourFrontier S Q earlier)
    let new_inc := C.selectedRetain_subset_processed S (C.contourFrontier S Q later)
    C.totalAngle Stage[earlier] (C.vertexForgetCuts old_inc Copy[exit]) -
      C.totalAngle Stage[later] (C.vertexForgetCuts new_inc Copy[exit]) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (Q.length + 1) =>
        Visit[j] = parent ∧ j ≠ exit ∧ earlier.val ≤ j.val + 1 ∧ j.val + 1 < later.val),
        C.totalAngle Retain Copy[j] := by
  classical
  let exit := (Interval[parent,nonroot]).leave
  let keep (stage : Fin (Q.length + 1)) :=
    Finset.univ.filter (fun j : Fin (Q.length + 1) =>
      Visit[j] = parent ∧ (j = exit ∨ stage.val ≤ j.val + 1))
  let interval := Finset.univ.filter (fun j : Fin (Q.length + 1) =>
    Visit[j] = parent ∧ j ≠ exit ∧ earlier.val ≤ j.val + 1 ∧ j.val + 1 < later.val)
  let angle (j : Fin (Q.length + 1)) := C.totalAngle Retain Copy[j]
  have nested : keep later ⊆ keep earlier := by
    intro j hj
    simp only [keep, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, hj.2.imp_right (ordered.trans ·)⟩
  have difference : keep earlier \ keep later = interval := by
    ext j
    simp only [keep, interval, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨parent_label, old⟩, fresh⟩
      have exit_ne : j ≠ exit := fun h => fresh ⟨parent_label, Or.inl h⟩
      exact ⟨parent_label, exit_ne, old.resolve_left exit_ne,
        lt_of_not_ge (fun h => fresh ⟨parent_label, Or.inr h⟩)⟩
    · rintro ⟨parent_label, exit_ne, old, fresh⟩
      exact ⟨⟨parent_label, Or.inr old⟩, fun h =>
        (not_le_of_gt fresh) (h.2.resolve_left exit_ne)⟩
  have old_angle := C.contourSavedParentFan_angle_eq_sum S Q roots starts parent nonroot
    earlier old_cut
  have new_angle := C.contourSavedParentFan_angle_eq_sum S Q roots starts parent nonroot
    later new_cut
  dsimp only
  rw [old_angle, new_angle]
  change (∑ j ∈ keep earlier, angle j) - (∑ j ∈ keep later, angle j) = ∑ j ∈ interval, angle j
  have total : (∑ j ∈ interval, angle j) + (∑ j ∈ keep later, angle j) =
      ∑ j ∈ keep earlier, angle j := by
    rw [← difference]
    exact Finset.sum_sdiff nested
  linarith

end Unfoldings.TriangleComplex
