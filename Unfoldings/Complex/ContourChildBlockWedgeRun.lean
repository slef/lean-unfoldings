module

public import Unfoldings.Complex.ContourParentWedgeRun

/-! The exact chain of wedges and empty child attachments between two positive gap blocks. -/

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
local notation "ParentBank[" v "," h "," side "]" => C.contourParentBank S Q roots starts v h side

local notation "Edge" => {v : C.Vertex Set.univ // v ∉ P.roots}

local notation "Event" => C.PositiveContourSource S Q
local notation "Source[" e "]" => C.positiveContourVertex S Q e
local notation "Stack[" v "]" => C.contourSavedGapStack S Q v

open scoped Classical in
/-- Two adjacent gap events from different children leave exactly a chain of original
roof wedges joined along empty stacks. The events occur at the two outside stack ends. -/
theorem exists_contourChildBlockWedgeRun
    (parent : C.Vertex Set.univ) (parent_nonroot : parent ∉ P.roots)
    (old_child new_child : Edge)
    (old_parent : P.parent old_child.val = parent) (new_parent : P.parent new_child.val = parent)
    (different : old_child.val ≠ new_child.val) (old new : Event)
    (old_in : P.Ancestor Source[old] old_child.val) (new_in : P.Ancestor Source[new] new_child.val)
    (pre post : List Event) (adjacent : Stack[parent] = pre ++ new :: old :: post) :
    let first := finRotate (Q.length + 1) (Interval[old_child.val,old_child.property]).leave
    let last := (Interval[new_child.val,new_child.property]).enter
    ∃ A : C.ContourParentWedgeRun S Q roots starts parent first last,
      (∃ older, Stack[old_child.val] = old :: older) ∧
      (∃ newer, Stack[new_child.val] = newer ++ [new]) ∧
      (∀ i, Stack[(A.child i).val] = []) ∧
      (∀ j : Fin (Q.length + 1), (∃ i, A.visit i = j) ↔ Visit[j] = parent ∧
        j ≠ (Interval[parent,parent_nonroot]).leave ∧ old.val.val ≤ j.val ∧ j.val < new.val.val) := by
  let first := finRotate (Q.length + 1) (Interval[old_child.val,old_child.property]).leave
  let last := (Interval[new_child.val,new_child.property]).enter
  have order : old.val.val < new.val.val := by
    have sorted : Stack[parent].Pairwise (fun a b => b.val.val < a.val.val) :=
      (C.contourEdgeGapStack_ordered S Q parent).reverse
    rw [adjacent] at sorted
    exact (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 _ List.mem_cons_self
  obtain ⟨ordered, range⟩ := C.contour_parent_visits_between_child_events S Q roots starts parent
    old_child.val new_child.val parent_nonroot old_child.property new_child.property old_parent
    new_parent different old new old_in new_in order
  obtain ⟨older, newer⟩ := C.contourSavedGapStack_boundary_events S Q roots starts parent
    old_child.val new_child.val parent_nonroot old_child.property new_child.property old_parent
    new_parent different old new old_in new_in pre post adjacent
  have at_first : Visit[first] = parent :=
    (C.contourChild_consecutive_parent_visits S Q roots starts old_child.val old_child.property
      (old_parent.symm ▸ parent_nonroot)).2.2.1.trans old_parent
  have at_last : Visit[last] = parent :=
    (C.contourParentInterval_entry_original S Q roots starts new_child.val new_child.property).1.trans
      new_parent
  let A := C.contourParentWedgeRun S Q roots starts parent parent_nonroot first last ordered at_first at_last
  have in_range (j : Fin (Q.length + 1)) : (∃ i, A.visit i = j) ↔
      Visit[j] = parent ∧ j ≠ (Interval[parent,parent_nonroot]).leave ∧
        old.val.val ≤ j.val ∧ j.val < new.val.val := by
    rw [A.visits]
    constructor
    · rintro ⟨hv, hl, hr⟩
      exact ⟨hv, (range j hv).mpr ⟨hl, hr⟩⟩
    · rintro ⟨hv, hb⟩
      exact ⟨hv, (range j hv).mp hb⟩
  refine ⟨A, older, newer, ?_, in_range⟩
  intro i
  let c := A.child i
  have first_bound : old.val.val ≤ (A.visit i.castSucc).val :=
    ((in_range _).mp ⟨i.castSucc, rfl⟩).2.2.1
  have last_bound : (A.visit i.succ).val < new.val.val :=
    ((in_range _).mp ⟨i.succ, rfl⟩).2.2.2
  have advance := (C.contourChild_consecutive_parent_visits S Q roots starts c.val c.property
    ((A.child_parent i).symm ▸ parent_nonroot)).1
  change (finRotate (Q.length + 1) (Interval[c.val,c.property]).leave).val =
    (Interval[c.val,c.property]).leave.val + 1 at advance
  have enters : (Interval[c.val,c.property]).enter = A.visit i.castSucc := A.enters i
  have returns : finRotate (Q.length + 1) (Interval[c.val,c.property]).leave = A.visit i.succ :=
    A.returns i
  rw [returns] at advance
  exact C.contour_child_stack_eq_nil_between_adjacent_events S Q roots starts parent c.val
    c.property (A.child_parent i) old new pre post adjacent
    (enters.symm ▸ first_bound) (by omega)

end Unfoldings.TriangleComplex
