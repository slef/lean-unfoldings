module

public import Unfoldings.Cap.CompletedParentBankDisplacements
public import Unfoldings.Complex.SelectedBankSum

/-! Actual completed-parent position gaps sum every descendant bank-vector difference. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain}
  {e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}} (O : N.ParentBankOpening
    D e)

theorem entrance_vertex : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point O.enter)) =
      N.spanningCompletion.parents.parent e.val :=
  (C.selected_parent_bank_enters N.spanningCompletion.selection e.val e.property
    (N.completedContour.cycle.point O.enter) O.side O.first_named O.outside).1

theorem exit_vertex : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point O.leave)) = e.val :=
  (C.selected_parent_bank_leaves N.spanningCompletion.selection e.val e.property
    (N.completedContour.cycle.point O.leave) (!O.side) O.last_named O.inside).1

theorem entrance_ray : D.boundaryRay (N.completedContour.cycle.point O.enter) =
    -D.developedDirection K O.entranceFace
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val) :=
        by
  rw [← D.developedDirection_boundaryRay K,
    K.projectedGermVector_parent_entrance N.spanningCompletion.selection e.val e.property
      _ O.side O.first_named O.outside, D.developedDirection_neg]
  rfl

theorem exit_ray : D.boundaryRay (N.completedContour.cycle.point O.leave) =
    D.developedDirection K O.exitFace
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val) :=
        by
  rw [← D.developedDirection_boundaryRay K,
    K.projectedGermVector_parent_exit N.spanningCompletion.selection e.val e.property
      _ (!O.side) O.last_named O.inside]
  rfl

end Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

def parentEntryVector (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
  Plane :=
  D.developedDirection K (N.parentBankOpening D e).entranceFace
    (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val)

def parentExitVector (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
  Plane :=
  D.developedDirection K (N.parentBankOpening D e).exitFace
    (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val)

/-- Actual displacement of the parent copies, in the exit-minus-entrance order. -/
def parentPositionGap (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
  Plane :=
  D.boundaryPosition (C.boundaryTurn N.completedRetain
      (N.completedContour.cycle.point (N.parentBankOpening D e).leave)) -
    D.boundaryPosition (N.completedContour.cycle.point (N.parentBankOpening D e).enter)

theorem original_bank_start_root (i : Fin (N.completedContour.length + 1))
    (old : C.IsBoundaryEdge Set.univ
      (C.boundaryEndEquiv N.completedRetain (N.completedContour.cycle.point i)).1.val) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point i)) ∈
        N.spanningCompletion.parents.roots := by
  let bank := (C.boundaryEndEquiv N.completedRetain (N.completedContour.cycle.point i)).1
  have left := C.relativeBoundaryVertex_old_left (Set.subset_univ N.completedRetain) bank old
  have right := C.relativeBoundaryVertex_old_right (Set.subset_univ N.completedRetain) bank old
  rcases C.boundaryGraph_bank_link N.completedRetain (N.completedContour.cycle.point i) with
    ⟨first, _⟩ | ⟨first, _⟩
  · change C.boundaryEndAsVertex N.completedRetain _ = (C.boundaryGraph N.completedRetain).left
        bank at first
    rw [← first] at left
    exact N.spanningCompletion.roots_eq.symm ▸ left
  · change C.boundaryEndAsVertex N.completedRetain _ = (C.boundaryGraph N.completedRetain).right
        bank at first
    rw [← first] at right
    exact N.spanningCompletion.roots_eq.symm ▸ right

open scoped Classical in
/-- The actual parent gap is the sum of all descendant paired-vector differences. -/
theorem parent_position_gap_eq_descendant_sum
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
    N.parentPositionGap D e =
      ∑ v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
        if N.spanningCompletion.parents.Ancestor v.val e.val then
          N.parentExitVector D v - N.parentEntryVector D v else 0 := by
  classical
  let O := N.parentBankOpening D e
  let weight (i : Fin (N.completedContour.length + 1)) : Plane :=
    if C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val i then
      D.boundaryRay (N.completedContour.cycle.point i) else 0
  have old_zero (i : Fin (N.completedContour.length + 1))
      (old : C.IsBoundaryEdge Set.univ
        (C.boundaryEndEquiv N.completedRetain (N.completedContour.cycle.point i)).1.val) :
      weight i = 0 := by
    apply ite_eq_right
    intro inside
    exact N.spanningCompletion.parents.descendant_nonroot e.property inside
      (N.original_bank_start_root i old)
  have first (v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
      weight (N.parentBankOpening D v).enter =
        if N.spanningCompletion.parents.Ancestor (N.spanningCompletion.parents.parent v.val) e.val
          then
          -N.parentEntryVector D v else 0 := by
    change (if N.spanningCompletion.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain
        (N.completedContour.cycle.point (N.parentBankOpening D v).enter))) e.val then
      D.boundaryRay (N.completedContour.cycle.point (N.parentBankOpening D v).enter) else 0) = _
    rw [(N.parentBankOpening D v).entrance_vertex, (N.parentBankOpening D v).entrance_ray]
    rfl
  have last (v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
      weight (N.parentBankOpening D v).leave =
        if N.spanningCompletion.parents.Ancestor v.val e.val then N.parentExitVector D v else 0 :=
          by
    change (if N.spanningCompletion.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain
        (N.completedContour.cycle.point (N.parentBankOpening D v).leave))) e.val then
      D.boundaryRay (N.completedContour.cycle.point (N.parentBankOpening D v).leave) else 0) = _
    rw [(N.parentBankOpening D v).exit_vertex, (N.parentBankOpening D v).exit_ray]
    rfl
  have pair (v : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}) :
      weight (N.parentBankOpening D v).enter + weight (N.parentBankOpening D v).leave =
        (if N.spanningCompletion.parents.Ancestor v.val e.val then
          N.parentExitVector D v - N.parentEntryVector D v else 0) +
        (if v = e then N.parentEntryVector D e else 0) := by
    rw [first, last]
    by_cases same : v = e
    · subst v
      simp only [ite_eq_right (N.spanningCompletion.parents.not_ancestor_parent_self e.property),
        N.spanningCompletion.parents.ancestor_refl, ite_true, zero_add]
      abel
    · have different : v.val ≠ e.val := fun equal => same (Subtype.ext equal)
      rw [N.spanningCompletion.parents.ancestor_parent_iff different]
      simp only [ite_eq_right same]
      split_ifs <;> abel
  have counted := C.sum_selected_bank_weights N.spanningCompletion.selection
    N.completedContour.cycle
    N.completedContour.covers weight old_zero
    (fun v => (N.parentBankOpening D v).enter) (fun v => (N.parentBankOpening D v).leave)
    (fun v => (N.parentBankOpening D v).side)
    (fun v => (N.parentBankOpening D v).first_named)
    (fun v => (N.parentBankOpening D v).last_named)
  simp only [pair, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at counted
  have gap := O.parent_position_gap
  change N.parentPositionGap D e = _ at gap
  rw [O.entrance_ray] at gap
  change _ = -N.parentEntryVector D e + ∑ i, weight i at gap
  rw [counted] at gap
  exact gap.trans (by abel)

end Unfoldings.ConvexCap.RadialCutForest
