module

public import Unfoldings.Cap.CompletedFaceCopyOrder

/-! A visible branch trace starts its comparison continuation at its own actual contour copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

/-- Every containing-face value at a physical vertex is represented by a genuine
contour copy of that vertex. Distinct face values are not identified. -/
theorem exists_boundary_copy_of_face_vertex (w : C.Vertex Set.univ) (f : Face)
    (member : K.projectedVertex w ∈ (K.projectedTriangle f).carrier) :
    ∃ target : Fin (N.completedContour.length + 1),
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w ∧
      D.projectedPlacement K f (K.projectedVertex w) =
        D.boundaryPosition (N.completedContour.cycle.point target) := by
  obtain ⟨j, at_corner⟩ := K.projected_corner_of_vertex_mem w f member
  let a := C.vertexOfCorner N.completedRetain (f, j)
  have original : C.vertexForgetCuts (Set.subset_univ _) a = w := by
    apply K.projectedVertex_injective
    simpa only [a, C.vertexForgetCuts_vertexOfCorner, K.projectedVertex_ofCorner] using at_corner
  have placed : D.projectedPlacement K f (K.projectedVertex w) =
      D.toPlane (C.vertexPoint N.completedRetain a) := by
    rw [← at_corner, K.projectedTriangle_vertex, ← K.projectFace_apply, D.projectedPlacement_apply]
    exact D.linkGerm_apex (⟨((f, j), false), rfl⟩ : C.LinkGerm N.completedRetain a)
  let Q := C.boundaryCycleVertexEquiv N.completedRetain N.completedContour.cycle
    N.completedContour.closes N.completedContour.covers
  let target := Q.symm ⟨a, N.completed_all_vertices_boundary a⟩
  have at_vertex : C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point target) = a :=
    congrArg Subtype.val (Q.apply_symm_apply ⟨a, N.completed_all_vertices_boundary a⟩)
  refine ⟨target, by rw [at_vertex]; exact original, ?_⟩
  change _ = D.toPlane (C.vertexPoint N.completedRetain _)
  rw [at_vertex, placed]

namespace FiveSectorFrameData

variable {N D} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- The start of a visible trace's comparison continuation is its actual developed
value, expressed by its own contour index. No choice of a different bank copy is needed. -/
theorem trace_vertex_is_boundary_copy (i : FiveSector) (w : C.Vertex Set.univ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K source (N.calibratedFrame D B.anchor B.reference)
      (fiveSectorFrame t positive small i).place G domain z)
    (vertex : source + (fiveSectorFrame t positive small i).place.symm z = K.projectedVertex w) :
    ∃ target : Fin (N.completedContour.length + 1),
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w ∧
      G z = B.sectorFrame i (D.boundaryPosition (N.completedContour.cycle.point target)) := by
  obtain ⟨f, member, _, value⟩ := trace
  rw [vertex] at member
  obtain ⟨target, original, placed⟩ := N.exists_boundary_copy_of_face_vertex D w f member
  refine ⟨target, original, ?_⟩
  let frame := (fiveSectorFrame t positive small i).place
  change G z = B.sectorFrame i
    (D.projectedPlacement K f (frame.symm (frame source + z))) at value
  rw [frame.symm.map_add, frame.symm_apply_apply, vertex, placed] at value
  exact value

end FiveSectorFrameData
end Unfoldings.ConvexCap.RadialCutForest
