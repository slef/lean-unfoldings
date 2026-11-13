module

public import Unfoldings.Roof.ParentBankDisplacements
public import Unfoldings.Complex.SelectedBankSum

/-!
# Position gaps include every attached branch

The displacement between the two actual parent copies is the sum of the
paired outward bank-vector differences for every descendant edge. This is
additive bookkeeping on the actual cut contour, with overlap permitted.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {D : FacewiseDevelopment C M.retain}
  {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}} (O : M.ParentBankOpening D e)

theorem entrance_vertex : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point O.enter)) =
      M.parents.parent e.val :=
  (C.selected_parent_bank_enters M.selection e.val e.property
    (M.projectionContour.cycle.point O.enter) O.side O.first_named O.outside).1

theorem exit_vertex : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point O.leave)) = e.val :=
  (C.selected_parent_bank_leaves M.selection e.val e.property
    (M.projectionContour.cycle.point O.leave) (!O.side) O.last_named O.inside).1

theorem entrance_ray : D.boundaryRay (M.projectionContour.cycle.point O.enter) =
    -D.roofDirection K O.entranceFace
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) := by
  rw [← D.roofDirection_boundaryRay K,
    K.projectedGermVector_parent_entrance M.selection e.val e.property
      _ O.side O.first_named O.outside, D.roofDirection_neg]
  rfl

theorem exit_ray : D.boundaryRay (M.projectionContour.cycle.point O.leave) =
    D.roofDirection K O.exitFace
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) := by
  rw [← D.roofDirection_boundaryRay K,
    K.projectedGermVector_parent_exit M.selection e.val e.property
      _ (!O.side) O.last_named O.inside]
  rfl

end Unfoldings.ConvexRoof.SectorForest.ParentBankOpening

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  (D : FacewiseDevelopment C M.retain)

def parentEntryVector (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) : Plane :=
  D.roofDirection K (M.parentBankOpening D e).entranceFace
    (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val)

def parentExitVector (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) : Plane :=
  D.roofDirection K (M.parentBankOpening D e).exitFace
    (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val)

/-- Actual displacement of the parent copies, in the exit-minus-entrance order. -/
def parentPositionGap (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) : Plane :=
  D.boundaryPosition (C.boundaryTurn M.retain
      (M.projectionContour.cycle.point (M.parentBankOpening D e).leave)) -
    D.boundaryPosition (M.projectionContour.cycle.point (M.parentBankOpening D e).enter)

theorem original_bank_start_root (i : Fin (M.projectionContour.length + 1))
    (old : C.IsBoundaryEdge Set.univ
      (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point i)).1.val) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point i)) ∈ M.parents.roots := by
  let bank := (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point i)).1
  have left := C.relativeBoundaryVertex_old_left (Set.subset_univ M.retain) bank old
  have right := C.relativeBoundaryVertex_old_right (Set.subset_univ M.retain) bank old
  rcases C.boundaryGraph_bank_link M.retain (M.projectionContour.cycle.point i) with
    ⟨first, _⟩ | ⟨first, _⟩
  · change C.boundaryEndAsVertex M.retain _ = (C.boundaryGraph M.retain).left bank at first
    rw [← first] at left
    exact M.roots_eq.symm ▸ left
  · change C.boundaryEndAsVertex M.retain _ = (C.boundaryGraph M.retain).right bank at first
    rw [← first] at right
    exact M.roots_eq.symm ▸ right

open scoped Classical in
/-- The actual parent gap is the sum of all descendant paired-vector differences. -/
theorem parent_position_gap_eq_descendant_sum
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    M.parentPositionGap D e =
      ∑ v : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        if M.parents.Ancestor v.val e.val then
          M.parentExitVector D v - M.parentEntryVector D v else 0 := by
  classical
  let O := M.parentBankOpening D e
  let weight (i : Fin (M.projectionContour.length + 1)) : Plane :=
    if C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e.val i then
      D.boundaryRay (M.projectionContour.cycle.point i) else 0
  have old_zero (i : Fin (M.projectionContour.length + 1))
      (old : C.IsBoundaryEdge Set.univ
        (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point i)).1.val) :
      weight i = 0 := by
    apply ite_eq_right
    intro inside
    exact M.parents.descendant_nonroot e.property inside (M.original_bank_start_root i old)
  have first (v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
      weight (M.parentBankOpening D v).enter =
        if M.parents.Ancestor (M.parents.parent v.val) e.val then
          -M.parentEntryVector D v else 0 := by
    change (if M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point (M.parentBankOpening D v).enter))) e.val then
      D.boundaryRay (M.projectionContour.cycle.point (M.parentBankOpening D v).enter) else 0) = _
    rw [(M.parentBankOpening D v).entrance_vertex, (M.parentBankOpening D v).entrance_ray]
    rfl
  have last (v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
      weight (M.parentBankOpening D v).leave =
        if M.parents.Ancestor v.val e.val then M.parentExitVector D v else 0 := by
    change (if M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point (M.parentBankOpening D v).leave))) e.val then
      D.boundaryRay (M.projectionContour.cycle.point (M.parentBankOpening D v).leave) else 0) = _
    rw [(M.parentBankOpening D v).exit_vertex, (M.parentBankOpening D v).exit_ray]
    rfl
  have pair (v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
      weight (M.parentBankOpening D v).enter + weight (M.parentBankOpening D v).leave =
        (if M.parents.Ancestor v.val e.val then
          M.parentExitVector D v - M.parentEntryVector D v else 0) +
        (if v = e then M.parentEntryVector D e else 0) := by
    rw [first, last]
    by_cases same : v = e
    · subst v
      simp only [ite_eq_right (M.parents.not_ancestor_parent_self e.property),
        M.parents.ancestor_refl, ite_true, zero_add]
      abel
    · have different : v.val ≠ e.val := fun equal => same (Subtype.ext equal)
      rw [M.parents.ancestor_parent_iff different]
      simp only [ite_eq_right same]
      split_ifs <;> abel
  have counted := C.sum_selected_bank_weights M.selection M.projectionContour.cycle
    M.projectionContour.covers weight old_zero
    (fun v => (M.parentBankOpening D v).enter) (fun v => (M.parentBankOpening D v).leave)
    (fun v => (M.parentBankOpening D v).side)
    (fun v => (M.parentBankOpening D v).first_named)
    (fun v => (M.parentBankOpening D v).last_named)
  simp only [pair, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at counted
  have gap := O.parent_position_gap
  change M.parentPositionGap D e = _ at gap
  rw [O.entrance_ray] at gap
  change _ = -M.parentEntryVector D e + ∑ i, weight i at gap
  rw [counted] at gap
  exact gap.trans (by abel)

end Unfoldings.ConvexRoof.SectorForest
