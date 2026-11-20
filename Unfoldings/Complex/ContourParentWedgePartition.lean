module

public import Unfoldings.Complex.ContourExtremeChildWedgeRun
public import Unfoldings.Complex.ContourSavedFanAngles

/-! A child excursion separates the original parent's roof wedges into exact prefix and suffix. -/

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
local notation "Interval[" v "," h "]" => C.contourParentInterval S Q roots starts v h
local notation "ParentBank[" v "," h "," side "]" => C.contourParentBank S Q roots starts v h side

local notation "Edge" => {v : C.Vertex Set.univ // v ∉ P.roots}



local notation "Copy[" j "]" => C.boundaryEndVertex Retain (Q.cycle.point j)
local notation "Forget" => C.vertexForgetCuts (Set.subset_univ Retain)

open scoped Classical in
/-- The contour visits enumerate all original copies of a nonroot vertex once. -/
theorem contour_sum_totalAngle_parent (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (Q.length + 1) => Visit[j] = parent),
      C.totalAngle Retain Copy[j]) = C.totalAngle Set.univ parent := by
  classical
  let visits := Finset.univ.filter (fun j : Fin (Q.length + 1) => Visit[j] = parent)
  let fiber := Finset.univ.filter (fun w : C.Vertex Retain => Forget w = parent)
  let copy (j : Fin (Q.length + 1)) := Copy[j]
  have same : visits.image copy = fiber := by
    ext w
    constructor
    · intro h
      obtain ⟨j, member, rfl⟩ := Finset.mem_image.mp h
      have original : Visit[j] = parent := (Finset.mem_filter.mp member).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, original⟩
    · intro h
      have original : Forget w = parent := (Finset.mem_filter.mp h).2
      have bound : C.IsBoundaryVertex Retain w :=
        C.selectedCut_nonroot_copy_boundary S w (original.symm ▸ nonroot)
      obtain ⟨j, label⟩ := (C.boundaryCycleVertexEquiv Retain Q.cycle Q.closes Q.covers).surjective
        ⟨w, bound⟩
      have located : copy j = w := congrArg Subtype.val label
      refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, located⟩
      exact (congrArg Forget located).trans original
  have injective : Function.Injective copy := fun _ _ equal =>
    C.boundaryCycle_vertices_injective Retain Q.cycle Q.closes equal
  have total := C.sum_totalAngle_vertexForgetCuts (Set.subset_univ Retain) parent
  rw [← Finset.sum_filter] at total
  change (∑ j ∈ visits, C.totalAngle Retain (copy j)) = _
  rw [← total]
  change _ = ∑ w ∈ fiber, C.totalAngle Retain w
  rw [← same, Finset.sum_image injective.injOn]

/-- Enumerate the entire original nonroot fan in its contour order. -/
def contourFullParentWedgeRun (parent : Edge) :
    C.ContourParentWedgeRun S Q roots starts parent.val
      (finRotate (Q.length + 1) (Interval[parent.val,parent.property]).enter)
      (Interval[parent.val,parent.property]).leave := by
  let data := Interval[parent.val,parent.property]
  let first := finRotate (Q.length + 1) data.enter
  have starts_at : Visit[first] = parent.val :=
    C.contourOriginalVertex_after_enter S Q roots starts parent.val parent.property
  have finishes_at : Visit[data.leave] = parent.val :=
    (C.contourParentInterval_exit_original S Q roots starts parent.val parent.property).1
  exact C.contourParentWedgeRun S Q roots starts parent.val parent.property first data.leave
    ((data.subtree first).mp (starts_at.symm ▸ P.ancestor_refl parent.val)).2 starts_at finishes_at

open scoped Classical in
/-- A full parent run accounts for every part of the vertex's original angle. -/
theorem contourFullParentWedgeRun_sum (parent : Edge) :
    let A := C.contourFullParentWedgeRun S Q roots starts parent
    (∑ i, C.totalAngle Retain Copy[A.visit i]) = C.totalAngle Set.univ parent.val := by
  classical
  let data := Interval[parent.val,parent.property]
  let first := finRotate (Q.length + 1) data.enter
  let A := C.contourFullParentWedgeRun S Q roots starts parent
  let angle (j : Fin (Q.length + 1)) := C.totalAngle Retain Copy[j]
  have offset : first.val = data.enter.val + 1 :=
    C.contourParentInterval_enter_succ_val S Q roots starts parent.val parent.property
  have covered : Finset.univ.map A.visit.toEmbedding =
      Finset.univ.filter (fun j : Fin (Q.length + 1) => Visit[j] = parent.val) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (A.visits j).trans ⟨fun h => h.1, fun h => by
      have bounds := (data.subtree j).mp (h.symm ▸ P.ancestor_refl parent.val)
      change data.enter.val < j.val ∧ j.val ≤ data.leave.val at bounds
      exact ⟨h, by change first.val ≤ j.val; omega, bounds.2⟩⟩
  change (∑ i, angle (A.visit i)) = _
  calc
    _ = ∑ j ∈ Finset.univ.map A.visit.toEmbedding, angle j := by
      rw [Finset.sum_map]
      rfl
    _ = _ := by
      rw [covered]
      exact C.contour_sum_totalAngle_parent S Q parent.val parent.property

/-- A child's excursion partitions its parent's visits into two closed ordered runs. -/
theorem contour_parent_visits_before_or_after_child
    (parent child : Edge) (at_parent : P.parent child.val = parent.val) (j : Fin (Q.length + 1)) :
    let p := Interval[parent.val,parent.property]
    let c := Interval[child.val,child.property]
    let first := finRotate (Q.length + 1) p.enter
    let returned := finRotate (Q.length + 1) c.leave
    Visit[j] = parent.val ↔
      (Visit[j] = parent.val ∧ first ≤ j ∧ j ≤ c.enter) ∨
      (Visit[j] = parent.val ∧ returned ≤ j ∧ j ≤ p.leave) := by
  let p := Interval[parent.val,parent.property]
  let c := Interval[child.val,child.property]
  let first := finRotate (Q.length + 1) p.enter
  let returned := finRotate (Q.length + 1) c.leave
  have start : first.val = p.enter.val + 1 :=
    C.contourParentInterval_enter_succ_val S Q roots starts parent.val parent.property
  have excluded := (C.contourChild_consecutive_parent_visits S Q roots starts child.val
    child.property (at_parent.symm ▸ parent.property)).2.2.2
  constructor
  · intro here
    have bounds := (p.subtree j).mp (here.symm ▸ P.ancestor_refl parent.val)
    change p.enter.val < j.val ∧ j.val ≤ p.leave.val at bounds
    by_cases earlier : j ≤ c.enter
    · exact Or.inl ⟨here, by change first.val ≤ j.val; omega, earlier⟩
    · have before : c.enter.val < j.val := lt_of_not_ge earlier
      have after : returned ≤ j := by
        by_contra! early
        exact excluded j before early (here.trans at_parent.symm)
      exact Or.inr ⟨here, after, bounds.2⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

/-- Sum the two ordered runs on the two sides of a child excursion. -/
theorem contourParentWedgeRun_sum_prefix_add_suffix (parent child : Edge)
    (at_parent : P.parent child.val = parent.val)
    (A : C.ContourParentWedgeRun S Q roots starts parent.val
      (finRotate (Q.length + 1) (Interval[parent.val,parent.property]).enter)
      (Interval[child.val,child.property]).enter)
    (B : C.ContourParentWedgeRun S Q roots starts parent.val
      (finRotate (Q.length + 1) (Interval[child.val,child.property]).leave)
      (Interval[parent.val,parent.property]).leave) :
    (∑ i : Fin (A.length + 1), C.totalAngle Retain Copy[A.visit i]) +
      (∑ i : Fin (B.length + 1), C.totalAngle Retain Copy[B.visit i]) =
        C.totalAngle Set.univ parent.val := by
  classical
  let X := Finset.univ.map A.visit.toEmbedding
  let Y := Finset.univ.map B.visit.toEmbedding
  let angle (j : Fin (Q.length + 1)) := C.totalAngle Retain Copy[j]
  have covered : X ∪ Y =
      Finset.univ.filter (fun j : Fin (Q.length + 1) => Visit[j] = parent.val) := by
    ext j
    simp only [X, Y, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
      Finset.mem_filter]
    exact ((C.contour_parent_visits_before_or_after_child S Q roots starts parent child at_parent
      j).trans (or_congr (A.visits j).symm (B.visits j).symm)).symm
  have disjoint : Disjoint X Y := by
    refine Finset.disjoint_left.mpr ?_
    intro j in_X in_Y
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp in_X
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp in_Y
    have before := (A.at_visit x).2.2
    have after := (B.at_visit y).2.1
    change A.visit x = j at hx
    change B.visit y = j at hy
    rw [hx] at before
    rw [hy] at after
    let c := Interval[child.val,child.property]
    have offset := (C.contourChild_consecutive_parent_visits S Q roots starts child.val
      child.property (at_parent.symm ▸ parent.property)).1
    have ordered := c.ordered
    change j.val ≤ c.enter.val at before
    change (finRotate (Q.length + 1) c.leave).val ≤ j.val at after
    change (finRotate (Q.length + 1) c.leave).val = c.leave.val + 1 at offset
    omega
  have sum_X : (∑ j ∈ X, angle j) = ∑ i : Fin (A.length + 1), angle (A.visit i) := by
    rw [Finset.sum_map]
    rfl
  have sum_Y : (∑ j ∈ Y, angle j) = ∑ i : Fin (B.length + 1), angle (B.visit i) := by
    rw [Finset.sum_map]
    rfl
  change (∑ i, angle (A.visit i)) + (∑ i, angle (B.visit i)) = _
  rw [← sum_X, ← sum_Y, ← Finset.sum_union disjoint, covered]
  exact C.contour_sum_totalAngle_parent S Q parent.val parent.property

end Unfoldings.TriangleComplex
