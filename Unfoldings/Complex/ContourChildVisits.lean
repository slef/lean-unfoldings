module

public import Unfoldings.Complex.ContourFirstVisit
public import Unfoldings.Complex.BoundaryContourRotation

/-! The original roof copies at a nonroot vertex follow the excursions through its children. -/

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

/-- The two original child-bank endpoints name the parent copies just before the
child excursion and just after its return. -/
theorem contourParentBank_finish_copies (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots) :
    let q := Interval[child,nonroot]
    C.boundaryEndVertex Retain (C.boundaryTurn Retain ParentBank[child,nonroot,true]) =
      Copy[q.enter] ∧
    C.boundaryEndVertex Retain (C.boundaryTurn Retain ParentBank[child,nonroot,false]) =
      Copy[finRotate (Q.length + 1) q.leave] := by
  let q := Interval[child,nonroot]
  constructor
  · change C.boundaryEndVertex Retain
      (C.boundaryTurn Retain (C.boundaryTurn Retain (Q.cycle.point q.enter))) = _
    rw [C.boundaryTurn_involutive]
  · exact congrArg Subtype.val (C.boundaryCycle_next_vertex Retain Q.cycle Q.closes q.leave)

/-- Leaving a child of a nonroot parent returns before the contour wraps to its root. -/
theorem contourParentInterval_leave_lt (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots)
    (parent_nonroot : P.parent child ∉ P.roots) :
    (Interval[child,nonroot]).leave.val < Q.length := by
  let q := Interval[child,nonroot]
  have at_parent : Visit[finRotate (Q.length + 1) q.leave] = P.parent child :=
    (congrArg (C.vertexForgetCuts (Set.subset_univ Retain))
      (C.contourParentBank_finish_copies S Q roots starts child nonroot).2).symm.trans
        (C.contourParentBank_finish S Q roots starts child nonroot false)
  by_contra! not_before
  change Q.length ≤ q.leave.val at not_before
  have last : q.leave = Fin.last Q.length := Fin.ext (by
    rw [Fin.val_last]
    exact le_antisymm (Nat.le_of_lt_succ q.leave.isLt) not_before)
  have wrap : finRotate (Q.length + 1) q.leave = 0 := last.symm ▸ finRotate_last
  have root : Visit[finRotate (Q.length + 1) q.leave] ∈ P.roots :=
    (congrArg (C.contourOriginalVertex S Q) wrap).symm ▸ starts
  exact parent_nonroot (at_parent ▸ root)

/-- These are consecutive visits to the parent. All intervening original vertices
belong to the child's subtree. -/
theorem contourChild_consecutive_parent_visits (child : C.Vertex Set.univ)
    (nonroot : child ∉ P.roots) (parent_nonroot : P.parent child ∉ P.roots) :
    let q := Interval[child,nonroot]
    let back := finRotate (Q.length + 1) q.leave
    back.val = q.leave.val + 1 ∧
      Visit[q.enter] = P.parent child ∧ Visit[back] = P.parent child ∧
      ∀ k, q.enter.val < k.val → k.val < back.val → Visit[k] ≠ P.parent child := by
  let q := Interval[child,nonroot]
  let back := finRotate (Q.length + 1) q.leave
  have leave := C.contourParentInterval_leave_lt S Q roots starts child nonroot parent_nonroot
  have finish : back.val = q.leave.val + 1 := by
    let j : Fin Q.length := ⟨q.leave.val, leave⟩
    have index : q.leave = j.castSucc := Fin.ext rfl
    exact (congrArg (fun i => (finRotate (Q.length + 1) i).val) index).trans
      (congrArg Fin.val (finRotate_of_lt j.isLt))
  have enter_parent : Visit[q.enter] = P.parent child :=
    (C.contourParentInterval_entry_original S Q roots starts child nonroot).1
  have leave_parent : Visit[back] = P.parent child :=
    (congrArg (C.vertexForgetCuts (Set.subset_univ Retain))
      (C.contourParentBank_finish_copies S Q roots starts child nonroot).2).symm.trans
        (C.contourParentBank_finish S Q roots starts child nonroot false)
  refine ⟨finish, enter_parent, leave_parent, ?_⟩
  intro k after before parent
  change q.enter.val < k.val at after
  change k.val < back.val at before
  have subtree : P.Ancestor Visit[k] child :=
    (q.subtree k).mpr ⟨after, by omega⟩
  exact P.not_ancestor_parent_self nonroot (parent ▸ subtree)

/-- Every pair of consecutive contour visits to a nonroot original vertex is an excursion
through exactly one of its original children. -/
theorem exists_child_of_consecutive_contour_visits
    (parent : C.Vertex Set.univ) (parent_nonroot : parent ∉ P.roots)
    (i j : Fin (Q.length + 1)) (ordered : i.val < j.val)
    (first : Visit[i] = parent) (last : Visit[j] = parent)
    (consecutive : ∀ k : Fin (Q.length + 1), i.val < k.val → k.val < j.val → Visit[k] ≠ parent) :
    ∃ (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots),
      P.parent child = parent ∧
      (Interval[child,nonroot]).enter = i ∧
      finRotate (Q.length + 1) (Interval[child,nonroot]).leave = j := by
  let k : Fin Q.length := ⟨i.val, by have bound := j.isLt; omega⟩
  have i_eq : k.castSucc = i := Fin.ext rfl
  let child := Visit[k.succ]
  have endpoints := C.contourOriginalVertex_neighbors_of_boundary_roots S roots Q k
  have parent_child : P.parent child = parent := by
    rcases endpoints with down | up | rim
    · exact down.trans ((congrArg (C.contourOriginalVertex S Q) i_eq).trans first)
    · have next : C.vertexForgetCuts (Set.subset_univ Retain)
          (C.boundaryEndVertex Retain (C.boundaryTurn Retain (Q.cycle.point i))) = child := by
        have copy := C.boundaryCycle_next_vertex Retain Q.cycle Q.closes k.castSucc
        have eq := congrArg (C.relativeBoundaryVertex (Set.subset_univ Retain)) copy
        have advance : finRotate (Q.length + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
        exact i_eq ▸ (eq.trans (congrArg (C.contourOriginalVertex S Q) advance))
      have next_parent : child = P.parent parent :=
        up.symm.trans (congrArg P.parent ((congrArg (C.contourOriginalVertex S Q) i_eq).trans first))
      have exit := C.contourParentBank_eq_of_contour S Q roots starts parent parent_nonroot i
        first (next.trans next_parent)
      have i_leave : i = (Interval[parent,parent_nonroot]).leave :=
        Q.cycle.injective exit
      have inside : P.Ancestor Visit[j] parent := last.symm ▸ P.ancestor_refl parent
      have before := ((Interval[parent,parent_nonroot]).subtree j).mp inside
      exact (not_lt_of_ge before.2 (i_leave ▸ ordered)).elim
    · exact (parent_nonroot ((congrArg (C.contourOriginalVertex S Q) i_eq).trans first ▸
        rim.1)).elim
  have nonroot : child ∉ P.roots := fun root =>
    parent_nonroot (parent_child ▸ ((P.fixed_root child root).symm ▸ root))
  let q := Interval[child,nonroot]
  have down := (q.subtree k.succ).mp (P.ancestor_refl child)
  have not_inside : ¬ P.Ancestor Visit[i] child := fun h =>
    P.not_ancestor_parent_self nonroot (parent_child.symm ▸ (first ▸ h))
  have at_entry : q.enter = i := by
    apply Fin.ext
    have i_after : q.enter.val ≤ i.val := by
      have successor : k.succ.val = i.val + 1 := rfl
      omega
    by_contra! unequal
    apply not_inside
    apply (q.subtree i).mpr
    have successor : k.succ.val = i.val + 1 := rfl
    omega
  let back := finRotate (Q.length + 1) q.leave
  obtain ⟨returned, _, to_parent, none_between⟩ :=
    C.contourChild_consecutive_parent_visits S Q roots starts child nonroot
      (parent_child.symm ▸ parent_nonroot)
  change back.val = q.leave.val + 1 at returned
  have after : i.val < back.val := by
    have window := q.ordered
    have entry : q.enter.val = i.val := congrArg Fin.val at_entry
    omega
  have at_parent : Visit[back] = parent := to_parent.trans parent_child
  have back_eq : back = j := by
    apply Fin.ext
    apply le_antisymm
    · by_contra! later
      exact (none_between j (at_entry.symm ▸ ordered) later) (last.trans parent_child.symm)
    · by_contra! later
      exact (consecutive back after later) at_parent
  exact ⟨child, nonroot, parent_child, at_entry, back_eq⟩

end Unfoldings.TriangleComplex
