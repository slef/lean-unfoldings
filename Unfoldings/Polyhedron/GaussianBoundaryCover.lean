module

public import Unfoldings.Polyhedron.GaussianIncidentHull
public import Unfoldings.Roof.GermNormalSides
public import Unfoldings.Geometry.GnomonicMinorArc
public import Unfoldings.Geometry.EquatorialMinorArc

/-! The Gaussian polygon boundary is covered by the actual incident dual seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- In a gnomonic chart of an actual Gaussian cell, every frontier point lifts
to the minor arc of an original seam incident to the primal vertex. -/
theorem exists_gaussian_frontier_incident_seam_cover (v : C.Vertex Set.univ) :
    ∃ q : Space, ‖q‖ = 1 ∧
      (∀ n ∈ F.gaussianCell (F.gaussianSiteOfVertex v), 0 < inner ℝ q n) ∧
      ∀ p ∈ frontier (Cap.gnomonicRegion
        (Cap.northFrame q '' F.gaussianCell (F.gaussianSiteOfVertex v))),
        ∃ s : C.Seam, (v = C.seamVertex s false ∨ v = C.seamVertex s true) ∧
          (Cap.northFrame q).symm (Cap.gnomonicNormal p) ∈
            closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
  obtain ⟨q, w, unit, hemisphere, internal, site, _⟩ :=
    P.exists_upperRoof_with_full_vertex_star N v
  let L := Cap.northFrame q
  let M := N.rotate L
  let PR := P.rotate L
  let K := PR.upperRoof M
  let U : Set Face := {f | 0 < M.normal f 2}
  let D := C.restrictFaces U
  have image_cell : K.sphericalNormalPolygon w = L '' F.gaussianCell (F.gaussianSiteOfVertex v) :=
    P.sphericalNormalPolygon_eq_image_gaussianCell N v q w unit hemisphere internal site
  have chart : Cap.gnomonicRegion (L '' F.gaussianCell (F.gaussianSiteOfVertex v)) =
      K.normalPolygon w := by
    rw [← image_cell, Cap.gnomonicRegion, ConvexRoof.sphericalNormalPolygon,
      Set.preimage_image_eq _ Cap.gnomonicNormal_injective]
  have inside := (K.projectedVertex_mem_interior_iff w).mpr internal
  have coordinates (a : D.Vertex Set.univ) :
      M.upperFolding.toSpace Set.univ (D.vertexPoint Set.univ a) =
        L (F.toSpace Set.univ (C.vertexPoint Set.univ (C.includeRestrictedVertexUniv U a))) := by
    obtain ⟨⟨f, j⟩, rfl⟩ := D.vertexOfCorner_surjective Set.univ a
    rw [C.includeRestrictedVertex_ofCorner_univ, F.toSpace_vertexOfCorner]
    have h := M.upperFolding.toSpace_vertexOfCorner (f : M.UpperFace) j
    exact h.trans rfl
  have original_vertex : C.includeRestrictedVertexUniv U w = v := by
    have h := (coordinates w).symm.trans site
    exact C.vertexPoint_injective Set.univ (P.embedded (L.injective h))
  have original_end (s : D.Seam) (b : Bool) :
      C.includeRestrictedVertexUniv U (D.seamVertex s b) = C.seamVertex s.val b := by
    change C.includeRestrictedVertexUniv U
      (D.vertexOfCorner Set.univ (D.germOfEndpoint (D.left s) b).1) = _
    rw [C.includeRestrictedVertex_ofCorner_univ]
    cases b <;> rfl
  refine ⟨q, unit, hemisphere, ?_⟩
  intro p on_frontier
  rw [chart] at on_frontier
  obtain ⟨s, a, link, on_segment⟩ :=
    K.exists_seam_slope_segment_of_mem_normalPolygon_frontier inside on_frontier
  have original_incident : v = C.seamVertex s.val false ∨ v = C.seamVertex s.val true := by
    rcases link with ⟨first, _⟩ | ⟨first, _⟩
    · exact Or.inl (original_vertex.symm.trans
        ((congrArg (C.includeRestrictedVertexUniv U) first).trans (original_end s false)))
    · exact Or.inr (original_vertex.symm.trans
        ((congrArg (C.includeRestrictedVertexUniv U) first).trans (original_end s true)))
  refine ⟨s.val, original_incident, ?_⟩
  have lifted : Cap.gnomonicNormal p ∈ Cap.gnomonicNormal ''
      segment ℝ (K.normalSlope (D.left s).face) (K.normalSlope (D.right s).face) :=
    Set.mem_image_of_mem _ on_segment
  rw [Cap.gnomonicNormal_image_segment, K.gnomonicNormal_normalSlope,
    K.gnomonicNormal_normalSlope] at lifted
  have rotated_arc : Cap.gnomonicNormal p ∈
      L '' closedMinorArc (N.normal (C.left s.val).face) (N.normal (C.right s.val).face) := by
    rw [SpatialRotation.image_closedMinorArc_linearIsometry]
    exact lifted
  obtain ⟨n, on_arc, equal⟩ := rotated_arc
  have inverse := congrArg L.symm equal
  rw [L.symm_apply_apply] at inverse
  exact inverse ▸ on_arc

end Unfoldings.SpatialFolding.ConvexBoundary
