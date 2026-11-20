module

public import Unfoldings.Complex.ContourParentWedgeRun

/-! Classify the contour runs before the first and after the last child block. -/

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


local notation "Event" => C.PositiveContourSource S Q
local notation "Source[" e "]" => C.positiveContourVertex S Q e
local notation "Stack[" v "]" => C.contourSavedGapStack S Q v

/-- At the first parent visit one original germ is the entry-side outgoing bank. -/
theorem contourParent_firstVisit_germ
    (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots) :
    let first := finRotate (Q.length + 1) (Interval[parent,nonroot]).enter
    C.boundaryMate Retain (Q.cycle.point first) = ParentBank[parent,nonroot,true] := by
  have next := Q.next_cyclic C (Interval[parent,nonroot]).enter
  exact ((C.boundaryMate_involutive Retain _).symm.trans
    (congrArg (C.boundaryMate Retain) next)).symm

/-- At the last parent visit one original germ is the exit-side outgoing bank. -/
theorem contourParent_lastVisit_germ
    (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots) :
    Q.cycle.point (Interval[parent,nonroot]).leave = ParentBank[parent,nonroot,false] := rfl

private theorem mem_parent_stack_ne_source (parent : C.Vertex Set.univ)
    (child : Edge) (at_parent : P.parent child.val = parent) (e : Event)
    (member : e ∈ Stack[child.val]) :
    e ∈ Stack[parent] ∧ Source[e] ≠ parent := by
  have ancestor := (C.mem_contourSavedGapStack S Q child.val e).mp member
  exact ⟨(C.mem_contourSavedGapStack S Q parent e).mpr
    (ancestor.trans P (at_parent ▸ P.ancestor_parent child.val)),
    fun equal => P.not_ancestor_parent_self child.property
      (at_parent.symm ▸ (equal ▸ ancestor))⟩

/-- Before the oldest child event, the contiguous roof run starts at the parent's first
visit. All earlier child seams in this run have empty gap stacks. -/
theorem exists_contourFirstChildWedgeRun (parent : Edge) (child : Edge)
    (at_parent : P.parent child.val = parent.val) (e : Event)
    (in_child : P.Ancestor Source[e] child.val)
    (oldest : ∀ other ∈ Stack[parent.val], Source[other] ≠ parent.val →
      e.val.val ≤ other.val.val) :
    let first := finRotate (Q.length + 1) (Interval[parent.val,parent.property]).enter
    let last := (Interval[child.val,child.property]).enter
    ∃ A : C.ContourParentWedgeRun S Q roots starts parent.val first last,
      ∀ i, Stack[(A.child i).val] = [] := by
  let p := Interval[parent.val,parent.property]
  let c := Interval[child.val,child.property]
  let first := finRotate (Q.length + 1) p.enter
  have first_at : Visit[first] = parent.val :=
    C.contourOriginalVertex_after_enter S Q roots starts parent.val parent.property
  have last_at : Visit[c.enter] = parent.val :=
    (C.contourParentInterval_entry_original S Q roots starts child.val child.property).1.trans
      at_parent
  have offset : first.val = p.enter.val + 1 :=
    C.contourParentInterval_enter_succ_val S Q roots starts parent.val parent.property
  have later : p.enter.val < c.enter.val :=
    C.contourParentInterval_enter_lt_of_original S Q roots starts parent.val parent.property
      c.enter last_at
  let A := C.contourParentWedgeRun S Q roots starts parent.val parent.property first c.enter
    (by change first.val ≤ c.enter.val; omega) first_at last_at
  have rank : c.enter.val < e.val.val := ((c.subtree e.val.castSucc).mp in_child).1
  refine ⟨A, fun i => List.eq_nil_iff_forall_not_mem.mpr ?_⟩
  intro other member
  let j := A.child i
  let d := Interval[j.val,j.property]
  have at_j : P.parent j.val = parent.val := A.child_parent i
  obtain ⟨at_stack, distinct⟩ := mem_parent_stack_ne_source C S Q parent.val j at_j other member
  have other_rank : other.val.val ≤ d.leave.val :=
    ((d.subtree other.val.castSucc).mp ((C.mem_contourSavedGapStack S Q j.val other).mp member)).2
  have returned := (C.contourChild_consecutive_parent_visits S Q roots starts j.val
    j.property (at_j.symm ▸ parent.property)).1
  have upper := (A.returns i).trans_le (A.at_visit i.succ).2.2
  change (finRotate (Q.length + 1) d.leave).val = d.leave.val + 1 at returned
  change (finRotate (Q.length + 1) d.leave).val ≤ c.enter.val at upper
  exact (not_le_of_gt (show other.val.val < e.val.val by omega)) (oldest other at_stack distinct)

/-- After the newest child event, the contiguous roof run ends at the parent's last
visit. All later child seams in this run have empty gap stacks. -/
theorem exists_contourLastChildWedgeRun (parent : Edge) (child : Edge)
    (at_parent : P.parent child.val = parent.val) (e : Event)
    (in_child : P.Ancestor Source[e] child.val)
    (newest : ∀ other ∈ Stack[parent.val], other.val.val ≤ e.val.val) :
    let first := finRotate (Q.length + 1) (Interval[child.val,child.property]).leave
    let last := (Interval[parent.val,parent.property]).leave
    ∃ A : C.ContourParentWedgeRun S Q roots starts parent.val first last,
      ∀ i, Stack[(A.child i).val] = [] := by
  let c := Interval[child.val,child.property]
  let p := Interval[parent.val,parent.property]
  let first := finRotate (Q.length + 1) c.leave
  obtain ⟨offset, _, at_first, _⟩ := C.contourChild_consecutive_parent_visits S Q roots starts
    child.val child.property (at_parent.symm ▸ parent.property)
  have first_at : Visit[first] = parent.val := at_first.trans at_parent
  have last_at : Visit[p.leave] = parent.val :=
    (C.contourParentInterval_exit_original S Q roots starts parent.val parent.property).1
  have upper : first ≤ p.leave :=
    ((p.subtree first).mp (first_at.symm ▸ P.ancestor_refl parent.val)).2
  let A := C.contourParentWedgeRun S Q roots starts parent.val parent.property
    first p.leave upper first_at last_at
  have rank : e.val.val ≤ c.leave.val := ((c.subtree e.val.castSucc).mp in_child).2
  refine ⟨A, fun i => List.eq_nil_iff_forall_not_mem.mpr ?_⟩
  intro other member
  let j := A.child i
  let d := Interval[j.val,j.property]
  have at_j : P.parent j.val = parent.val := A.child_parent i
  have at_stack := (mem_parent_stack_ne_source C S Q parent.val j at_j other member).1
  have other_rank : d.enter.val < other.val.val :=
    ((d.subtree other.val.castSucc).mp ((C.mem_contourSavedGapStack S Q j.val other).mp member)).1
  have lower := (A.at_visit i.castSucc).2.1.trans_eq (A.enters i).symm
  change first.val = c.leave.val + 1 at offset
  change first.val ≤ d.enter.val at lower
  exact (not_le_of_gt (show e.val.val < other.val.val by omega)) (newest other at_stack)

end Unfoldings.TriangleComplex
