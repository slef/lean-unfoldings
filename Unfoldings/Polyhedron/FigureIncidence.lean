module

public import Unfoldings.Polyhedron.FigureBoundary
public import Unfoldings.Complex.LinkOrdering

/-!
# Which original faces meet a vertex figure

The actual image of an input triangle is the convex hull of its three
spatial corners. If none is the chosen vertex, all three have functional
height strictly above the slice, and convexity gives the same strict
inequality on the whole triangle. Every face meeting the figure therefore
has an actual corner at that retained vertex.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem faceImage_eq_convexHull (face : Face) :
    F.faceImage face = convexHull ℝ
      (Set.range (fun i : Fin 3 => F.place face ((C.triangle face).vertex i))) := by
  have mapped : F.place face '' convexHull ℝ (Set.range (C.triangle face).vertex) =
      convexHull ℝ (F.place face '' Set.range (C.triangle face).vertex) :=
    (F.place face).toAffineMap.image_convexHull _
  change F.place face '' convexHull ℝ (Set.range (C.triangle face).vertex) = _
  simpa only [← Set.range_comp'] using mapped

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)

include P

theorem figure_face_has_corner (face : Face) (p : Plane)
    (in_face : V.place p ∈ F.faceImage face) :
    ∃ i : Fin 3, C.vertexOfCorner Set.univ (face, i) = v := by
  by_contra no_corner
  have different (i : Fin 3) :
      F.place face ((C.triangle face).vertex i) ≠
        F.toSpace Set.univ (C.vertexPoint Set.univ v) := by
    intro equal
    have point_equal : C.vertexPoint Set.univ (C.vertexOfCorner Set.univ (face, i)) =
        C.vertexPoint Set.univ v := P.embedded equal
    exact no_corner ⟨i, C.vertexPoint_injective Set.univ point_equal⟩
  let g : Plane →ᵃ[ℝ] ℝ :=
    V.functional.toLinearMap.toAffineMap.comp (F.place face).toAffineMap
  let a := V.level + V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v))
  have high_corners : Set.range (C.triangle face).vertex ⊆ g ⁻¹' Set.Ioi a := by
    rintro _ ⟨i, rfl⟩
    have high := V.supported (face, i) (different i)
    rw [map_sub] at high
    change V.level + V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v)) <
      V.functional (F.place face ((C.triangle face).vertex i))
    linarith
  have high_triangle : (C.triangle face).carrier ⊆ g ⁻¹' Set.Ioi a :=
    convexHull_min high_corners ((convex_Ioi a).affine_preimage g)
  obtain ⟨q, hq, image⟩ := in_face
  have high := high_triangle hq
  change V.level + V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v)) <
    V.functional (F.place face q) at high
  have level := V.range_place.le ⟨p, rfl⟩
  change V.functional (V.place p - F.toSpace Set.univ (C.vertexPoint Set.univ v)) = V.level at level
  rw [← image, map_sub] at level
  linarith

theorem figure_boundary_has_corner (p : Plane) (boundary : p ∈ frontier V.carrier) :
    ∃ c : C.CornerAt Set.univ v, V.place p ∈ F.faceImage c.val.1 := by
  obtain ⟨face, in_face⟩ := Set.mem_iUnion.mp ((P.figure_frontier_iff_surface V p).mp boundary)
  obtain ⟨i, at_vertex⟩ := P.figure_face_has_corner V face p in_face
  exact ⟨⟨(face, i), at_vertex⟩, in_face⟩

end ConvexBoundary
end Unfoldings.SpatialFolding
