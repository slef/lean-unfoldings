module

public import Unfoldings.Polyhedron.FigureGermIncidence
public import Unfoldings.Polyhedron.FaceIncidence
public import Unfoldings.Geometry.EdgeChordInterior

/-!
# Open figure edges lie in original face interiors

The two endpoint lifts are nonvertex points of different triangle edges.
Their open chord is therefore in the original face interior. Embeddedness
excludes every contact of an open figure edge with another original face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)

theorem germ_openSegment_subset_faceInterior (p : C.LinkGerm Set.univ v) :
    V.place '' openSegment ℝ (V.germPoint p) (V.germPoint (C.linkTurn Set.univ v p)) ⊆
      F.place p.val.1.1 '' interior (C.triangle p.val.1.1).carrier := by
  let q := C.linkTurn Set.univ v p
  let x : (C.triangle p.val.1.1).Edge (C.germEdge p.val).edge :=
    ⟨V.germCoordinate p, V.germCoordinate_mem_edge p⟩
  let y : (C.triangle p.val.1.1).Edge (C.germEdge q.val).edge :=
    ⟨V.germCoordinate q, V.germCoordinate_mem_edge q⟩
  have different : (C.germEdge p.val).edge ≠ (C.germEdge q.val).edge := by
    intro equal
    have edges : C.germEdge q.val = C.germEdge p.val :=
      congrArg (EdgeRef.mk p.val.1.1) equal.symm
    exact C.turnGerm_ne p.val (C.germ_eq_of_corner_edge rfl edges)
  have inside := (C.triangle p.val.1.1).openSegment_subset_interior_of_distinct_edges
    different x y (V.germCoordinate_not_vertex p) (V.germCoordinate_not_vertex q)
  have image : F.place p.val.1.1 '' openSegment ℝ x.val y.val =
      V.place '' openSegment ℝ (V.germPoint p) (V.germPoint q) := by
    have spatial : F.place p.val.1.1 '' openSegment ℝ x.val y.val =
        openSegment ℝ (F.place p.val.1.1 x.val) (F.place p.val.1.1 y.val) :=
      image_openSegment ℝ (F.place p.val.1.1).toAffineMap _ _
    have planar : V.place '' openSegment ℝ (V.germPoint p) (V.germPoint q) =
        openSegment ℝ (V.place (V.germPoint p)) (V.place (V.germPoint q)) :=
      image_openSegment ℝ V.place.toAffineMap _ _
    rw [spatial, planar]
    change openSegment ℝ (F.place p.val.1.1 (V.germCoordinate p))
      (F.place q.val.1.1 (V.germCoordinate q)) = _
    rw [V.place_germCoordinate, V.place_germCoordinate]
  rw [← image]
  exact Set.image_mono inside

theorem germ_openSegment_disjoint_face (embedded : F.IsEmbedded)
    (p : C.LinkGerm Set.univ v) (g : Face) (different : p.val.1.1 ≠ g) :
    Disjoint (V.place '' openSegment ℝ (V.germPoint p)
      (V.germPoint (C.linkTurn Set.univ v p))) (F.faceImage g) :=
  (F.faceImage_disjoint_spatial_interior embedded different).mono_left
    (V.germ_openSegment_subset_faceInterior p)

theorem germ_openSegment_disjoint_segment (embedded : F.IsEmbedded)
    (p q : C.LinkGerm Set.univ v) (different : p.val.1 ≠ q.val.1) :
    Disjoint (openSegment ℝ (V.germPoint p) (V.germPoint (C.linkTurn Set.univ v p)))
      (segment ℝ (V.germPoint q) (V.germPoint (C.linkTurn Set.univ v q))) := by
  have faces : p.val.1.1 ≠ q.val.1.1 := fun equal => different
    (congrArg Subtype.val (F.cornerAt_faces_injective Set.univ v
      (a₁ := ⟨p.val.1, p.property⟩) (a₂ := ⟨q.val.1, q.property⟩) equal))
  apply Set.disjoint_left.mpr
  intro z left right
  apply Set.disjoint_left.mp (V.germ_openSegment_disjoint_face embedded p q.val.1.1 faces)
    (Set.mem_image_of_mem V.place left)
  have spatial : V.place z ∈ V.place '' segment ℝ (V.germPoint q)
      (V.germPoint (C.linkTurn Set.univ v q)) := Set.mem_image_of_mem _ right
  rw [V.image_germ_segment] at spatial
  exact spatial.1

end Unfoldings.SpatialFolding.VertexFigure
