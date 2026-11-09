module

public import Unfoldings.Polyhedron.FigureEdges
public import Unfoldings.Polyhedron.GermSpatial

/-!
# Vertex-figure endpoints indexed by actual link germs

Radial projection of the other endpoint of each germ gives a point in the
constructed figure plane. Seam mates have the same point, and each original
corner section is the segment between its two germ points.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)

theorem radialGermPoint_mem_generators (p : C.LinkGerm Set.univ v) :
    radialSlicePoint V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v))
      V.level (F.germFarPoint p.val) ∈ V.spatialGenerators := by
  refine ⟨F.germFarPoint p.val, ⟨?_, ?_⟩, rfl⟩
  · exact ⟨C.germFarCorner p.val, rfl⟩
  · exact F.linkGerm_far_ne_apex Set.univ v p

theorem exists_germPoint (p : C.LinkGerm Set.univ v) :
    ∃ q : Plane, V.place q =
      radialSlicePoint V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v))
        V.level (F.germFarPoint p.val) :=
  V.spatialGenerators_subset_range (V.radialGermPoint_mem_generators p)

def germPoint (p : C.LinkGerm Set.univ v) : Plane :=
  Classical.choose (V.exists_germPoint p)

@[simp] theorem place_germPoint (p : C.LinkGerm Set.univ v) :
    V.place (V.germPoint p) =
      radialSlicePoint V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v))
        V.level (F.germFarPoint p.val) :=
  Classical.choose_spec (V.exists_germPoint p)

theorem germPoint_mem_generators (p : C.LinkGerm Set.univ v) :
    V.germPoint p ∈ V.generators := by
  change V.place (V.germPoint p) ∈ V.spatialGenerators
  rw [V.place_germPoint]
  exact V.radialGermPoint_mem_generators p

@[simp] theorem germPoint_mate (p : C.LinkGerm Set.univ v) :
    V.germPoint (C.linkMate Set.univ v p) = V.germPoint p := by
  apply V.place.injective
  rw [V.place_germPoint, V.place_germPoint]
  change radialSlicePoint V.functional _ V.level
    (F.germFarPoint (C.mateGerm Set.univ p.val)) = _
  rw [F.germFarPoint_mate]

theorem image_germ_segment (p : C.LinkGerm Set.univ v) :
    V.place '' segment ℝ (V.germPoint p) (V.germPoint (C.linkTurn Set.univ v p)) =
      radialSlice (F.faceImage p.val.1.1) V.functional
        (F.toSpace Set.univ (C.vertexPoint Set.univ v)) V.level := by
  have image : V.place '' segment ℝ (V.germPoint p)
      (V.germPoint (C.linkTurn Set.univ v p)) =
      segment ℝ (V.place (V.germPoint p))
        (V.place (V.germPoint (C.linkTurn Set.univ v p))) :=
    image_segment ℝ V.place.toAffineMap _ _
  rw [image, V.place_germPoint, V.place_germPoint,
    V.spatial_face_section_eq_segment ⟨p.val.1, p.property⟩]
  obtain ⟨⟨⟨face, i⟩, side⟩, hp⟩ := p
  cases side
  · rfl
  · exact segment_symm ℝ _ _

end Unfoldings.SpatialFolding.VertexFigure

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)

include P

theorem figure_germ_segment_subset_boundary (p : C.LinkGerm Set.univ v) :
    segment ℝ (V.germPoint p) (V.germPoint (C.linkTurn Set.univ v p)) ⊆
      frontier V.carrier := by
  intro q hq
  have spatial := P.figure_face_section_subset_boundary V ⟨p.val.1, p.property⟩
  rw [← V.image_germ_segment p] at spatial
  obtain ⟨r, hr, equal⟩ := spatial ⟨q, hq, rfl⟩
  exact V.place.injective equal ▸ hr

theorem figure_germPoint_mem_frontier (p : C.LinkGerm Set.univ v) :
    V.germPoint p ∈ frontier V.carrier :=
  P.figure_germ_segment_subset_boundary V p (left_mem_segment ℝ _ _)

end Unfoldings.SpatialFolding.ConvexBoundary
