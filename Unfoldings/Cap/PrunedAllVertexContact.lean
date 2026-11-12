module

public import Unfoldings.Cap.AllVertexContact
public import Unfoldings.Cap.PrunedVertexContactFibers

/-! Global injectivity of curvature-pruned cap developments under physical contact control. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D) (nonoverlap : D.Nonoverlapping)
  (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)

include B budget in
/-- All same-original-vertex contacts, including arbitrary branch and rim copies,
are genuine intrinsic equalities in the pruned cut disk. -/
theorem vertex_contacts_identified (a b : C.Vertex M.retain)
    (labels : C.vertexForgetCuts (Set.subset_univ _) a =
      C.vertexForgetCuts (Set.subset_univ _) b)
    (same : D.toPlane (C.vertexPoint M.retain a) = D.toPlane (C.vertexPoint M.retain b)) :
    C.vertexForgetCuts M.retain_subset_curvedRetain a =
      C.vertexForgetCuts M.retain_subset_curvedRetain b := by
  let Q := C.boundaryCycleAllVertexEquiv M.retain M.projectionContour.cycle
    M.projectionContour.closes M.projectionContour.covers
    (C.selectedCut_all_vertices_boundary M.selection M.roots_eq)
  let i := Q.symm a
  let j := Q.symm b
  have first : C.boundaryEndVertex M.retain (M.projectionContour.cycle.point i) =
      a := Q.apply_symm_apply _
  have last : C.boundaryEndVertex M.retain (M.projectionContour.cycle.point j) =
      b := Q.apply_symm_apply _
  have physical : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point i)) =
        C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point j)) := by
    rw [first, last]
    exact labels
  have images : D.boundaryPosition (M.projectionContour.cycle.point i) =
      D.boundaryPosition (M.projectionContour.cycle.point j) := by
    change D.toPlane (C.vertexPoint M.retain
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point i))) =
        D.toPlane (C.vertexPoint M.retain
          (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point j)))
    rw [first, last]
    exact same
  have identified := B.contour_vertex_contacts_identified budget i j physical images
  rw [first, last] at identified
  exact identified

include B budget in
/-- Contacts between any two pruned copies of one physical vertex are intrinsic equalities. -/
theorem curved_same_original_vertex_copies_unique (a b : C.Vertex M.curvedRetain)
    (labels : C.vertexForgetCuts (Set.subset_univ _) a =
      C.vertexForgetCuts (Set.subset_univ _) b)
    (same : (M.curvedDevelopment D nonoverlap).toPlane (C.vertexPoint M.curvedRetain a) =
      (M.curvedDevelopment D nonoverlap).toPlane (C.vertexPoint M.curvedRetain b)) : a = b := by
  obtain ⟨a, rfl⟩ := C.vertexForgetCuts_surjective M.retain_subset_curvedRetain a
  obtain ⟨b, rfl⟩ := C.vertexForgetCuts_surjective M.retain_subset_curvedRetain b
  have compose (v : C.Vertex M.retain) :
      C.vertexForgetCuts (Set.subset_univ M.curvedRetain)
          (C.vertexForgetCuts M.retain_subset_curvedRetain v) =
        C.vertexForgetCuts (Set.subset_univ M.retain) v := by
    obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective M.retain v
    rfl
  have physical : C.vertexForgetCuts (Set.subset_univ M.retain) a =
      C.vertexForgetCuts (Set.subset_univ M.retain) b := by
    simpa only [compose] using labels
  have images : D.toPlane (C.vertexPoint M.retain a) =
      D.toPlane (C.vertexPoint M.retain b) := by
    rw [C.vertexPoint_vertexForgetCuts, C.vertexPoint_vertexForgetCuts] at same
    have at_vertex (v : C.Vertex M.retain) :
        (M.curvedDevelopment D nonoverlap).toPlane
            (C.forgetCuts M.retain_subset_curvedRetain (C.vertexPoint M.retain v)) =
          D.toPlane (C.vertexPoint M.retain v) :=
      D.restoreSeams_toPlane K.folding nonoverlap M.curvedRetain
        (M.curvedRetain_subset_coherentSeams D) M.retain_subset_curvedRetain _
    rwa [at_vertex, at_vertex] at same
  exact B.vertex_contacts_identified budget a b physical images

include B budget in
/-- Physical identification of all closed-face contacts yields an embedding of the entire
closed intrinsic cut disk. There are no remaining exceptional vertices or radii. -/
theorem curvedDevelopment_injective
    (physical_contacts : ∀ f g (p q : Plane),
      p ∈ (K.projectedTriangle f).carrier → q ∈ (K.projectedTriangle g).carrier →
      D.projectedPlacement K f p = D.projectedPlacement K g q → p = q) :
    Function.Injective (M.curvedDevelopment D nonoverlap).toPlane :=
  (SectorForest.curved_injective_iff_same_original_vertex_copies_unique
    B nonoverlap budget physical_contacts).mpr
      (B.curved_same_original_vertex_copies_unique nonoverlap budget)

end Unfoldings.ConvexCap.SectorForest.SectorFrameData
