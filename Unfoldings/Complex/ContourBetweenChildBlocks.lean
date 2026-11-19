module

public import Unfoldings.Complex.ContourChildVisits
public import Unfoldings.Complex.ContourGapStacks

/-! The roof wedges and empty seams between consecutive positive child blocks. -/

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

local notation "Event" => C.PositiveContourSource S Q
local notation "Source[" e "]" => C.positiveContourVertex S Q e
local notation "Stack[" v "]" => C.contourSavedGapStack S Q v

private theorem contour_parent_visit_le_exit
    (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots)
    (j : Fin (Q.length + 1)) (here : Visit[j] = parent) :
    j.val ≤ (Interval[parent,nonroot]).leave.val :=
  (((Interval[parent,nonroot]).subtree j).mp (here.symm ▸ P.ancestor_refl parent)).2

/-- Between events from distinct children, the final parent visits start at the old
child's return and end at the new child's entrance, including both end copies. -/
theorem contour_parent_visits_between_child_events
    (parent old_child new_child : C.Vertex Set.univ) (parent_nonroot : parent ∉ P.roots)
    (old_nonroot : old_child ∉ P.roots) (new_nonroot : new_child ∉ P.roots)
    (old_parent : P.parent old_child = parent) (new_parent : P.parent new_child = parent)
    (different : old_child ≠ new_child) (old new : Event)
    (old_in : P.Ancestor Source[old] old_child) (new_in : P.Ancestor Source[new] new_child)
    (order : old.val.val < new.val.val) :
    let old_back := finRotate (Q.length + 1) (Interval[old_child,old_nonroot]).leave
    let new_enter := (Interval[new_child,new_nonroot]).enter
    old_back.val ≤ new_enter.val ∧
      ∀ j : Fin (Q.length + 1), Visit[j] = parent →
        (j ≠ (Interval[parent,parent_nonroot]).leave ∧ old.val.val ≤ j.val ∧ j.val < new.val.val ↔
          old_back.val ≤ j.val ∧ j.val ≤ new_enter.val) := by
  let A := Interval[old_child,old_nonroot]
  let B := Interval[new_child,new_nonroot]
  let back := finRotate (Q.length + 1) A.leave
  let new_back := finRotate (Q.length + 1) B.leave
  obtain ⟨return_a, entry_a, _, none_a⟩ := C.contourChild_consecutive_parent_visits S Q
    roots starts old_child old_nonroot (old_parent.symm ▸ parent_nonroot)
  obtain ⟨return_b, entry_b, last_b, none_b⟩ := C.contourChild_consecutive_parent_visits S Q
    roots starts new_child new_nonroot (new_parent.symm ▸ parent_nonroot)
  change back.val = A.leave.val + 1 at return_a
  change new_back.val = B.leave.val + 1 at return_b
  change ∀ k : Fin (Q.length + 1), A.enter.val < k.val → k.val < back.val →
    Visit[k] ≠ P.parent old_child at none_a
  change ∀ k : Fin (Q.length + 1), B.enter.val < k.val → k.val < new_back.val →
    Visit[k] ≠ P.parent new_child at none_b
  have a_rank : A.enter.val < old.val.val ∧ old.val.val < back.val := by
    have h := (A.subtree old.val.castSucc).mp old_in
    change A.enter.val < old.val.val ∧ old.val.val ≤ A.leave.val at h
    omega
  have b_rank : B.enter.val < new.val.val ∧ new.val.val < new_back.val := by
    have h := (B.subtree new.val.castSucc).mp new_in
    change B.enter.val < new.val.val ∧ new.val.val ≤ B.leave.val at h
    omega
  have distinct_enter : A.enter ≠ B.enter := by
    intro same
    apply different
    have a := C.contourOriginalVertex_after_enter S Q roots starts old_child old_nonroot
    have b := C.contourOriginalVertex_after_enter S Q roots starts new_child new_nonroot
    change Visit[finRotate (Q.length + 1) A.enter] = old_child at a
    change Visit[finRotate (Q.length + 1) B.enter] = new_child at b
    rw [same] at a
    exact a.symm.trans b
  have entry_order : A.enter.val < B.enter.val := by
    by_contra! h
    have strict := h.lt_of_ne (fun eq => distinct_enter (Fin.ext eq.symm))
    exact none_b A.enter strict (by omega) ((entry_a.trans old_parent).trans new_parent.symm)
  have before : back.val ≤ B.enter.val := by
    by_contra! h
    exact none_a B.enter entry_order h ((entry_b.trans new_parent).trans old_parent.symm)
  have end_before_exit : B.enter.val < (Interval[parent,parent_nonroot]).leave.val := by
    have h := contour_parent_visit_le_exit C S Q roots starts parent parent_nonroot new_back
      (last_b.trans new_parent)
    omega
  change back.val ≤ B.enter.val ∧
    ∀ j : Fin (Q.length + 1), Visit[j] = parent →
      (j ≠ (Interval[parent,parent_nonroot]).leave ∧ old.val.val ≤ j.val ∧ j.val < new.val.val ↔
        back.val ≤ j.val ∧ j.val ≤ B.enter.val)
  refine ⟨before, ?_⟩
  intro j here
  constructor
  · rintro ⟨_, old_bound, new_bound⟩
    constructor
    · by_contra! h
      exact none_a j (by omega) h (here.trans old_parent.symm)
    · by_contra! h
      exact none_b j h (by omega) (here.trans new_parent.symm)
  · rintro ⟨old_bound, new_bound⟩
    refine ⟨?_, by omega, by omega⟩
    intro h
    have val := congrArg Fin.val h
    omega

/-- There is no event whose rank lies strictly between consecutive parent-stack entries. -/
theorem contourSavedGapStack_not_between_adjacent
    (parent : C.Vertex Set.univ) (old new : Event) (pre post : List Event)
    (adjacent : Stack[parent] = pre ++ new :: old :: post)
    (e : Event) (parent_member : e ∈ Stack[parent]) :
    ¬ (old.val.val < e.val.val ∧ e.val.val < new.val.val) := by
  have ordered : Stack[parent].Pairwise (fun a b => b.val.val < a.val.val) :=
    (C.contourEdgeGapStack_ordered S Q parent).reverse
  rw [adjacent] at ordered
  obtain ⟨_, rest_ordered, cross⟩ := List.pairwise_append.mp ordered
  have tail_ordered := (List.pairwise_cons.mp rest_ordered).2
  have member : e ∈ pre ++ new :: old :: post := adjacent ▸ parent_member
  intro ⟨after, before⟩
  rw [List.mem_append] at member
  rcases member with earlier | later
  · exact (not_lt_of_ge before.le) (cross e earlier new (List.mem_cons_self ..))
  · simp only [List.mem_cons] at later
    rcases later with rfl | rfl | m
    · exact lt_irrefl _ before
    · exact lt_irrefl _ after
    · exact (not_lt_of_ge after.le) ((List.pairwise_cons.mp tail_ordered).1 e m)

/-- A child whose whole excursion lies strictly between two adjacent event ranks
in the parent stack carries no gaps. -/
theorem contour_child_stack_eq_nil_between_adjacent_events
    (parent child : C.Vertex Set.univ) (nonroot : child ∉ P.roots)
    (at_parent : P.parent child = parent) (old new : Event) (pre post : List Event)
    (adjacent : Stack[parent] = pre ++ new :: old :: post)
    (after_old : old.val.val ≤ (Interval[child,nonroot]).enter.val)
    (before_new : (Interval[child,nonroot]).leave.val < new.val.val) :
    Stack[child] = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e member
  have inside := (C.mem_contourSavedGapStack S Q child e).mp member
  have bounds := ((Interval[child,nonroot]).subtree e.val.castSucc).mp inside
  change (Interval[child,nonroot]).enter.val < e.val.val ∧
    e.val.val ≤ (Interval[child,nonroot]).leave.val at bounds
  have parent_member : e ∈ Stack[parent] :=
    (C.mem_contourSavedGapStack S Q parent e).mpr
      (inside.trans P (at_parent ▸ P.ancestor_parent child))
  exact C.contourSavedGapStack_not_between_adjacent S Q parent old new pre post adjacent e
    parent_member ⟨after_old.trans_lt bounds.1, bounds.2.trans_lt before_new⟩

private theorem list_cons_of_no_preceding {A : Type*} {r : A → A → Prop}
    {xs : List A} {x : A} (sorted : xs.Pairwise r) (member : x ∈ xs)
    (no_before : ∀ a ∈ xs, ¬ r a x) : ∃ tail, xs = x :: tail := by
  cases xs with
  | nil => cases member
  | cons a as =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨as, rfl⟩
    · exact (no_before a List.mem_cons_self ((List.pairwise_cons.mp sorted).1 _ later)).elim

include roots starts in
/-- Across adjacent positive child blocks, the older event is newest on its own
child edge, and the newer event is oldest on its own child edge. -/
theorem contourSavedGapStack_boundary_events
    (parent old_child new_child : C.Vertex Set.univ) (parent_nonroot : parent ∉ P.roots)
    (old_nonroot : old_child ∉ P.roots) (new_nonroot : new_child ∉ P.roots)
    (old_parent : P.parent old_child = parent) (new_parent : P.parent new_child = parent)
    (different : old_child ≠ new_child) (old new : Event)
    (old_in : P.Ancestor Source[old] old_child) (new_in : P.Ancestor Source[new] new_child)
    (pre post : List Event) (adjacent : Stack[parent] = pre ++ new :: old :: post) :
    (∃ tail, Stack[old_child] = old :: tail) ∧
    (∃ preceding, Stack[new_child] = preceding ++ [new]) := by
  let A := Interval[old_child,old_nonroot]
  let B := Interval[new_child,new_nonroot]
  have order : old.val.val < new.val.val := by
    have sorted : Stack[parent].Pairwise (fun a b => b.val.val < a.val.val) :=
      (C.contourEdgeGapStack_ordered S Q parent).reverse
    rw [adjacent] at sorted
    exact (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 _ List.mem_cons_self
  have bounds := (C.contour_parent_visits_between_child_events S Q roots starts
    parent old_child new_child parent_nonroot old_nonroot new_nonroot old_parent new_parent
    different old new old_in new_in order).1
  have back_eq := (C.contourChild_consecutive_parent_visits S Q roots starts old_child old_nonroot
    (old_parent.symm ▸ parent_nonroot)).1
  change (finRotate (Q.length + 1) A.leave).val ≤ B.enter.val at bounds
  change (finRotate (Q.length + 1) A.leave).val = A.leave.val + 1 at back_eq
  have old_bound := (A.subtree old.val.castSucc).mp old_in
  have new_bound := (B.subtree new.val.castSucc).mp new_in
  change A.enter.val < old.val.val ∧ old.val.val ≤ A.leave.val at old_bound
  change B.enter.val < new.val.val ∧ new.val.val ≤ B.leave.val at new_bound
  constructor
  · refine list_cons_of_no_preceding (C.contourEdgeGapStack_ordered S Q old_child).reverse
      ((C.mem_contourSavedGapStack S Q old_child old).mpr old_in) ?_
    intro e member after
    have inside := (C.mem_contourSavedGapStack S Q old_child e).mp member
    have position := (A.subtree e.val.castSucc).mp inside
    change A.enter.val < e.val.val ∧ e.val.val ≤ A.leave.val at position
    have at_parent := (C.mem_contourSavedGapStack S Q parent e).mpr
      (inside.trans P (old_parent ▸ P.ancestor_parent old_child))
    exact C.contourSavedGapStack_not_between_adjacent S Q parent old new pre post adjacent e
      at_parent ⟨after, by omega⟩
  · have ascending : (Stack[new_child]).reverse.Pairwise (fun a b => a.val.val < b.val.val) := by
      simpa only [contourSavedGapStack, List.reverse_reverse] using
        C.contourEdgeGapStack_ordered S Q new_child
    have member : new ∈ (Stack[new_child]).reverse := List.mem_reverse.mpr
      ((C.mem_contourSavedGapStack S Q new_child new).mpr new_in)
    obtain ⟨tail, eq⟩ := list_cons_of_no_preceding ascending member (by
      intro e member before
      have inside := (C.mem_contourSavedGapStack S Q new_child e).mp
        (List.mem_reverse.mp member)
      have position := (B.subtree e.val.castSucc).mp inside
      change B.enter.val < e.val.val ∧ e.val.val ≤ B.leave.val at position
      have at_parent := (C.mem_contourSavedGapStack S Q parent e).mpr
        (inside.trans P (new_parent ▸ P.ancestor_parent new_child))
      exact C.contourSavedGapStack_not_between_adjacent S Q parent old new pre post adjacent e
        at_parent ⟨by omega, before⟩)
    refine ⟨tail.reverse, ?_⟩
    simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse eq

/-- At a roof wedge between two child excursions, the two boundary germs are
the ends of those children’s specified bank copies. -/
theorem contour_parent_wedge_end_eq_iff
    (old_child new_child : {v : C.Vertex Set.univ // v ∉ P.roots})
    (j : Fin (Q.length + 1))
    (after_old : finRotate (Q.length + 1) (Interval[old_child.val,old_child.property]).leave = j)
    (before_new : (Interval[new_child.val,new_child.property]).enter = j)
    (p : C.BoundaryEnd Retain) :
    C.boundaryEndVertex Retain p = Copy[j] ↔
      p = C.boundaryTurn Retain ParentBank[old_child.val,old_child.property,false] ∨
      p = C.boundaryTurn Retain ParentBank[new_child.val,new_child.property,true] := by
  let A := Interval[old_child.val,old_child.property]
  let B := Interval[new_child.val,new_child.property]
  have old_end : C.boundaryTurn Retain ParentBank[old_child.val,old_child.property,false] =
      C.boundaryMate Retain (Q.cycle.point j) := by
    have next := (Q.next_cyclic C A.leave).trans (congrArg Q.cycle.point after_old)
    exact ((C.boundaryMate_involutive Retain _).symm.trans (congrArg
      (C.boundaryMate Retain) next))
  have new_end : C.boundaryTurn Retain ParentBank[new_child.val,new_child.property,true] =
      Q.cycle.point j := by
    change C.boundaryTurn Retain (C.boundaryTurn Retain (Q.cycle.point B.enter)) = _
    exact ((C.boundaryTurn_involutive Retain _).trans (congrArg Q.cycle.point before_new))
  rw [C.boundaryEnd_vertex_eq_iff, old_end, new_end, or_comm]

end Unfoldings.TriangleComplex
