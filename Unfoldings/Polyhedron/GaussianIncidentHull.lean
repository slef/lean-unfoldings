module

public import Unfoldings.Polyhedron.GaussianVertexAngles

/-! In gnomonic coordinates the actual Gaussian polygon is the convex hull of
the original incident face normals. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

/-- The gnomonic images of the original face normals at the actual vertex. -/
def incidentGaussianSlopes (q : Space) (v : C.Vertex Set.univ) : Set Plane :=
  {p | ∃ f j, C.vertexOfCorner Set.univ (f, j) = v ∧
    let n := Cap.northFrame q (N.normal f)
    (n 2)⁻¹ • Cap.horizontal n = p}

include P in
/-- A view from inside the body identifies the entire Gaussian cell with the
finite convex hull of the gnomonic images of its original incident normals. -/
theorem exists_gaussianCell_eq_incidentHull (v : C.Vertex Set.univ) :
    ∃ q : Space, ‖q‖ = 1 ∧
      (∀ n ∈ F.gaussianCell (F.gaussianSiteOfVertex v), 0 < inner ℝ q n) ∧
      Cap.gnomonicRegion (Cap.northFrame q '' F.gaussianCell (F.gaussianSiteOfVertex v)) =
        convexHull ℝ (incidentGaussianSlopes N q v) := by
  obtain ⟨q, w, unit, hemisphere, internal, site, _⟩ :=
    P.exists_upperRoof_with_full_vertex_star N v
  let L := Cap.northFrame q
  let M := N.rotate L
  let PR := P.rotate L
  let K := PR.upperRoof M
  let cell := F.gaussianCell (F.gaussianSiteOfVertex v)
  have image_cell : K.sphericalNormalPolygon w = L '' cell :=
    P.sphericalNormalPolygon_eq_image_gaussianCell N v q w unit hemisphere internal site
  have corner_site (f : M.UpperFace) (j : Fin 3) :
      M.upperFolding.toSpace Set.univ (M.upperComplex.vertexPoint Set.univ
        (M.upperComplex.vertexOfCorner Set.univ (f, j))) =
        L (F.toSpace Set.univ (C.vertexPoint Set.univ (C.vertexOfCorner Set.univ (f.val, j)))) := by
    rw [M.upperFolding.toSpace_vertexOfCorner, F.toSpace_vertexOfCorner]
    rfl
  have corner_iff (f : M.UpperFace) (j : Fin 3) :
      M.upperComplex.vertexOfCorner Set.univ (f, j) = w ↔
        C.vertexOfCorner Set.univ (f.val, j) = v := by
    constructor
    · intro equal
      have same := corner_site f j
      rw [equal, site] at same
      exact C.vertexPoint_injective Set.univ (P.embedded (L.injective same.symm))
    · intro equal
      have same := corner_site f j
      rw [equal, ← site] at same
      apply M.upperComplex.vertexPoint_injective Set.univ
      exact M.upper_projection_injective PR (congrArg Cap.horizontal same)
  have slopes : K.incidentSlopes w = incidentGaussianSlopes N q v := by
    ext p
    constructor
    · rintro ⟨f, j, at_w, equal⟩
      exact ⟨f.val, j, (corner_iff f j).mp at_w, equal⟩
    · rintro ⟨f, j, at_v, equal⟩
      have in_cell := F.normal_mem_gaussianCell_of_corner N f j
      rw [at_v] at in_cell
      have up : 0 < M.normal f 2 := by
        change 0 < Cap.northFrame q (N.normal f) 2
        rw [Cap.northFrame_height q unit]
        exact hemisphere _ in_cell
      let f' : M.UpperFace := ⟨f, up⟩
      exact ⟨f', j, (corner_iff f' j).mpr at_v, equal⟩
  refine ⟨q, unit, hemisphere, ?_⟩
  change Cap.gnomonicNormal ⁻¹' (L '' cell) = _
  rw [← image_cell, ConvexRoof.sphericalNormalPolygon,
    Set.preimage_image_eq _ Cap.gnomonicNormal_injective, ConvexRoof.normalPolygon, slopes]

end Unfoldings.SpatialFolding.ConvexBoundary
