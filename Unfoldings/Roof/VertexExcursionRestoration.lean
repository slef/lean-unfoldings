module

public import Unfoldings.Roof.VertexExcursionFlatness
public import Unfoldings.Roof.RestoredParentBankEndpoints

/-! Closing contour excursions identify their endpoints after the actual flat seams are restored. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.VertexContourExcursion

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {D : FacewiseDevelopment C M.retain}
  {e : C.Vertex Set.univ}
  (E : M.VertexContourExcursion e)

/-- This is an intrinsic quotient equality, rather than equality in a planar placement.
The proof integrates arbitrary vertex labels along the selected contour banks. -/
theorem endpoints_eq_of_selected_subtrees_flat
    (flat : ∀ v : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
      E.region (M.parentBankOpening D v).enter → M.subtreeCurvature v.val = 0) :
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) E.last))) =
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) E.first))) := by
  classical
  let vertex (i : Fin (M.projectionContour.length + 1)) :=
    C.vertexForgetCuts M.retain_subset_curvedRetain
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point i))
  let position (i : Fin (M.projectionContour.length + 1)) : ℤ :=
    if vertex i = vertex (finRotate (M.projectionContour.length + 1) E.first) then 1 else 0
  let weight (i : Fin (M.projectionContour.length + 1)) : ℤ :=
    if E.region i then position (finRotate (M.projectionContour.length + 1) i) - position i else 0
  have old_zero (i : Fin (M.projectionContour.length + 1))
      (old : C.IsBoundaryEdge Set.univ
        (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point i)).1.val) :
      weight i = 0 := by
    apply ite_eq_right
    intro member
    exact E.no_original_bank i member old
  have paired (v : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) :
      weight (M.parentBankOpening D v).enter + weight (M.parentBankOpening D v).leave = 0 := by
    dsimp only [weight]
    rw [← E.selected_pair D v]
    by_cases selected : E.region (M.parentBankOpening D v).enter
    · simp only [selected, ite_true]
      have first := (M.parentBankOpening D v).restored_child_endpoints (flat v selected)
      have last := (M.parentBankOpening D v).restored_parent_endpoints (flat v selected)
      change vertex (finRotate (M.projectionContour.length + 1)
        (M.parentBankOpening D v).enter) = vertex (M.parentBankOpening D v).leave at first
      change vertex (finRotate (M.projectionContour.length + 1)
        (M.parentBankOpening D v).leave) = vertex (M.parentBankOpening D v).enter at last
      simp only [position, first, last]
      abel
    · simp only [selected, ite_false, add_zero]
  have sum := C.sum_selected_bank_weights M.selection M.projectionContour.cycle
    M.projectionContour.covers weight old_zero
    (fun v => (M.parentBankOpening D v).enter) (fun v => (M.parentBankOpening D v).leave)
    (fun v => (M.parentBankOpening D v).side)
    (fun v => (M.parentBankOpening D v).first_named)
    (fun v => (M.parentBankOpening D v).last_named)
  simp only [paired, Finset.sum_const_zero] at sum
  have cancellation := displacement_of_two_region_exits
    (finRotate (M.projectionContour.length + 1)) E.region position E.first E.last E.different
    E.enters E.leaves E.stable
  have equal : position (finRotate (M.projectionContour.length + 1) E.last) =
      position (finRotate (M.projectionContour.length + 1) E.first) :=
    sub_eq_zero.mp (cancellation.symm.trans sum)
  change vertex (finRotate (M.projectionContour.length + 1) E.last) =
    vertex (finRotate (M.projectionContour.length + 1) E.first)
  by_contra different
  simp only [position, different, ite_false, ite_true] at equal
  norm_num at equal

end Unfoldings.ConvexRoof.SectorForest.VertexContourExcursion

namespace Unfoldings.ConvexRoof.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

include B in
/-- Every closing actual subtree excursion becomes a single intrinsic endpoint after pruning. -/
theorem closing_vertex_excursion_endpoints_identified
    {e : C.Vertex Set.univ}
    (E : M.VertexContourExcursion e)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (same : D.boundaryPosition (M.projectionContour.cycle.point
      (finRotate (M.projectionContour.length + 1) E.last)) =
        D.boundaryPosition (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) E.first))) :
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) E.last))) =
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) E.first))) :=
  E.endpoints_eq_of_selected_subtrees_flat
    ((B.vertex_excursion_gap_eq_zero_iff_selected_subtrees_flat E budget).mp same)

end Unfoldings.ConvexRoof.SectorForest.SectorFrameData
