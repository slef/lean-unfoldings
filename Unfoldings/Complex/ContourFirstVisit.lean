module

public import Unfoldings.Complex.ContourParentBanks
public import Unfoldings.Complex.ContourGapBankIndex
public import Unfoldings.Complex.SupportedContourNeighbors

/-! The first actual visit of each original nonroot is just after its parent-bank entrance. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)

local notation "interval" => C.contourParentInterval S Q roots starts vertex nonroot

/-- The first contour visit is the very next vertex after the parent edge entrance. -/
theorem contourOriginalVertex_after_enter :
    C.contourOriginalVertex S Q (finRotate (Q.length + 1) (interval).enter) = vertex := by
  have next := C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes (interval).enter
  have same := congrArg (C.relativeBoundaryVertex (Set.subset_univ _)) next
  exact same.symm.trans (C.contourParentInterval_entry_original S Q roots starts vertex nonroot).2

theorem contourParentInterval_enter_succ_val :
    (finRotate (Q.length + 1) (interval).enter).val = (interval).enter.val + 1 := by
  have enough : (interval).enter.val < Q.length := by
    have ordered := (interval).ordered
    have bound := (interval).leave.isLt
    omega
  let j : Fin Q.length := ⟨(interval).enter.val, enough⟩
  have same : (interval).enter = j.castSucc := Fin.ext rfl
  exact (congrArg (fun k => (finRotate (Q.length + 1) k).val) same).trans
    (congrArg Fin.val (finRotate_of_lt j.isLt))

/-- All later occurrences of the original vertex follow the first visit. -/
theorem contourParentInterval_enter_lt_of_original (i : Fin (Q.length + 1))
    (same : C.contourOriginalVertex S Q i = vertex) : (interval).enter.val < i.val := by
  have in_subtree : P.Ancestor (C.contourOriginalVertex S Q i) vertex :=
    same.symm ▸ P.ancestor_refl vertex
  exact (((interval).subtree i).mp in_subtree).1

/-- The stage just after crossing the literal entrance spends this nonroot once. -/
theorem mem_contourFrontier_processed_iff_enter (i : Fin (Q.length + 1)) :
    vertex ∈ (C.contourFrontier S Q i).processed ↔ (interval).enter.val + 1 < i.val := by
  rw [C.rim_contour_processed_iff_of_boundary_roots S roots Q starts]
  constructor
  · rintro (root | ⟨j, before, visit⟩)
    · exact (nonroot root).elim
    · have entered := C.contourParentInterval_enter_lt_of_original S Q roots starts
        vertex nonroot j visit
      omega
  · intro after
    refine Or.inr ⟨finRotate (Q.length + 1) (interval).enter, ?_, ?_⟩
    · exact (C.contourParentInterval_enter_succ_val S Q roots starts vertex nonroot).trans_lt after
    · exact C.contourOriginalVertex_after_enter S Q roots starts vertex nonroot

/-- A positive event spends its defect at the first literal visit of its own source. -/
theorem positiveContourSource_val_eq_enter_add_one
    (source : C.PositiveContourSource S Q) :
    let vertex := C.positiveContourVertex S Q source
    let nonroot := C.positiveContourVertex_nonroot S Q source
    source.val.val = (C.contourParentInterval S Q roots starts vertex nonroot).enter.val + 1 := by
  let vertex := C.positiveContourVertex S Q source
  let nonroot := C.positiveContourVertex_nonroot S Q source
  let block := C.contourParentInterval S Q roots starts vertex nonroot
  have entered : block.enter.val < source.val.val :=
    C.contourParentInterval_enter_lt_of_original S Q roots starts vertex nonroot source.val.castSucc
      rfl
  have fresh : ¬ block.enter.val + 1 < source.val.val := fun h =>
    source.property.1 ((C.mem_contourFrontier_processed_iff_enter S Q roots starts
      vertex nonroot source.val.castSucc).mpr h)
  exact Nat.le_antisymm (Nat.le_of_not_gt fresh) (Nat.succ_le_of_lt entered)

include roots starts in
/-- For its own source, the gap is at the last end of the newest-first original stack. -/
theorem contourSavedGapStack_source_last (source : C.PositiveContourSource S Q) :
    let v := C.positiveContourVertex S Q source
    ∃ ds, C.contourSavedGapStack S Q v = ds ++ [source] := by
  let v := C.positiveContourVertex S Q source
  let h := C.positiveContourVertex_nonroot S Q source
  let block := C.contourParentInterval S Q roots starts v h
  let stack := C.contourSavedGapStack S Q v
  have member : source ∈ stack :=
    (C.mem_contourSavedGapStack S Q v source).mpr (P.ancestor_refl v)
  have rank : source.val.val = block.enter.val + 1 :=
    C.positiveContourSource_val_eq_enter_add_one S Q roots starts source
  have not_before (other : C.PositiveContourSource S Q) (hm : other ∈ stack) :
      source.val.val ≤ other.val.val := by
    have ancestor := (C.mem_contourSavedGapStack S Q v other).mp hm
    have entered : block.enter.val < other.val.val :=
      ((block.subtree other.val.castSucc).mp ancestor).1
    omega
  have ordered : stack.Pairwise (fun a b => b.val < a.val) :=
    (C.contourEdgeGapStack_ordered S Q v).reverse
  obtain ⟨before, after, name⟩ := List.append_of_mem member
  have no_after : after = [] := by
    by_contra! present
    obtain ⟨other, hm⟩ := List.exists_mem_of_ne_nil after present
    have pair := (List.pairwise_append.mp (name ▸ ordered)).2.1
    have backwards : other.val < source.val :=
      (List.pairwise_cons.mp pair).1 other hm
    have in_stack : other ∈ stack :=
      name.symm ▸ List.mem_append_right before (List.mem_cons_of_mem source hm)
    exact (not_lt_of_ge (not_before other in_stack)) backwards
  exact ⟨before, by simpa only [no_after] using name⟩

end Unfoldings.TriangleComplex
