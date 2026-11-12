module

public import Unfoldings.Cap.CompletedBranchJumpOrder
public import Unfoldings.Cap.CenteredTraceValues

/-! Every actual branch copy, including a visible strip trace, lies between its named banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem vertex_copy_gap_order (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (a : C.Vertex N.completedRetain)
    (original : C.vertexForgetCuts (Set.subset_univ _) a = e.val) :
    ((B.sectorFrame i (D.toPlane (C.vertexPoint N.completedRetain a) -
      N.parentEntrancePoint D e 1)).re ≤ 0 ∧
      0 ≤ (B.sectorFrame i (D.toPlane (C.vertexPoint N.completedRetain a) -
        N.parentEntrancePoint D e 1)).im) ∧
    ((B.sectorFrame i (N.parentExitPoint D e 1 -
      D.toPlane (C.vertexPoint N.completedRetain a))).re ≤ 0 ∧
      0 ≤ (B.sectorFrame i (N.parentExitPoint D e 1 -
        D.toPlane (C.vertexPoint N.completedRetain a))).im) := by
  let Q := C.boundaryCycleVertexEquiv N.completedRetain N.completedContour.cycle
    N.completedContour.closes N.completedContour.covers
  let target := Q.symm ⟨a, N.completed_all_vertices_boundary a⟩
  have at_vertex : C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point target) = a :=
    congrArg Subtype.val (Q.apply_symm_apply ⟨a, N.completed_all_vertices_boundary a⟩)
  have at_original : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val := by
    rw [at_vertex]
    exact original
  have first := B.vertex_entrance_gap_order i e sectors budget target at_original
  have last := B.vertex_exit_gap_order i e sectors budget target at_original
  change (_ ∧ _) ∧ (_ ∧ _)
  simpa only [FacewiseDevelopment.boundaryPosition, at_vertex] using And.intro first last

theorem face_vertex_copy_gap_order (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (f : Face) (member : K.projectedVertex e.val ∈ (K.projectedTriangle f).carrier) :
    ((B.sectorFrame i (D.projectedPlacement K f (K.projectedVertex e.val) -
      N.parentEntrancePoint D e 1)).re ≤ 0 ∧
      0 ≤ (B.sectorFrame i (D.projectedPlacement K f (K.projectedVertex e.val) -
        N.parentEntrancePoint D e 1)).im) ∧
    ((B.sectorFrame i (N.parentExitPoint D e 1 -
      D.projectedPlacement K f (K.projectedVertex e.val))).re ≤ 0 ∧
      0 ≤ (B.sectorFrame i (N.parentExitPoint D e 1 -
        D.projectedPlacement K f (K.projectedVertex e.val))).im) := by
  obtain ⟨j, at_corner⟩ := K.projected_corner_of_vertex_mem e.val f member
  let a := C.vertexOfCorner N.completedRetain (f, j)
  have original : C.vertexForgetCuts (Set.subset_univ _) a = e.val := by
    apply K.projectedVertex_injective
    simpa only [a, C.vertexForgetCuts_vertexOfCorner, K.projectedVertex_ofCorner] using at_corner
  have placed : D.projectedPlacement K f (K.projectedVertex e.val) =
      D.toPlane (C.vertexPoint N.completedRetain a) := by
    rw [← at_corner, K.projectedTriangle_vertex, ← K.projectFace_apply, D.projectedPlacement_apply]
    exact D.linkGerm_apex (⟨((f, j), false), rfl⟩ : C.LinkGerm N.completedRetain a)
  rw [placed]
  exact B.vertex_copy_gap_order i e sectors budget a original

/-- A branch trace retains its own actual copy. All such copies have these ordered bounds;
there is no assumption that the copies agree. -/
theorem trace_vertex_between_banks (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K source (N.calibratedFrame D B.anchor B.reference)
      (fiveSectorFrame t positive small i).place G domain z)
    (vertex : source + (fiveSectorFrame t positive small i).place.symm z =
      K.projectedVertex e.val) :
    (B.sectorFrame i (N.parentExitPoint D e 1)).re ≤ (G z).re ∧
      (G z).re ≤ (B.sectorFrame i (N.parentEntrancePoint D e 1)).re ∧
      (B.sectorFrame i (N.parentEntrancePoint D e 1)).im ≤ (G z).im ∧
      (G z).im ≤ (B.sectorFrame i (N.parentExitPoint D e 1)).im := by
  obtain ⟨f, member, _, value⟩ := trace
  rw [vertex] at member
  have bounds := B.face_vertex_copy_gap_order i e sectors budget f member
  let frame := (fiveSectorFrame t positive small i).place
  change G z = B.sectorFrame i
    (D.projectedPlacement K f (frame.symm (frame source + z))) at value
  rw [frame.symm.map_add, frame.symm_apply_apply, vertex] at value
  rw [map_sub, map_sub, Complex.sub_re, Complex.sub_im] at bounds
  rw [← value] at bounds
  exact ⟨sub_nonpos.mp bounds.2.1, sub_nonpos.mp bounds.1.1,
    sub_nonneg.mp bounds.1.2, sub_nonneg.mp bounds.2.2⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
