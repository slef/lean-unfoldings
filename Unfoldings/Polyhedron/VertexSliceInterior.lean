module

public import Unfoldings.Polyhedron.VertexSlice
public import Unfoldings.Geometry.SliceInterior

/-!
# Vertex slices with an actual interior center

For a convex boundary, the constructed transverse slice meets the body's
spatial interior. Such a point has a neighborhood in the level plane inside
the slice. The finite-hull description and its interior center are obtained
together from the same supporting functional and positive level.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_vertexSlice_interior (v : C.Vertex Set.univ)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ) :
    ∃ (f : Space →L[ℝ] ℝ) (h : ℝ) (q : Space), f ≠ 0 ∧ 0 < h ∧
      q ∈ interior F.vertexHull ∧ f (q - F.toSpace Set.univ (C.vertexPoint Set.univ v)) = h ∧
      radialSlice F.vertexHull f (F.toSpace Set.univ (C.vertexPoint Set.univ v)) h =
        convexHull ℝ (radialSlicePoint f (F.toSpace Set.univ (C.vertexPoint Set.univ v)) h ''
          (Set.range (fun c : Face × Fin 3 => F.place c.1 ((C.triangle c.1).vertex c.2)) \
            {F.toSpace Set.univ (C.vertexPoint Set.univ v)})) := by
  obtain ⟨f, h, nonzero, positive, _nonempty, projected⟩ := F.exists_vertexSlice v extreme
  obtain ⟨c, different⟩ := F.exists_corner_ne_vertex v
  have generator : F.place c.1 ((C.triangle c.1).vertex c.2) ∈ F.vertexHull :=
    subset_convexHull ℝ _ ⟨c, rfl⟩
  obtain ⟨q, in_section, in_interior⟩ :=
    exists_interior_radialSlice F.convex_vertexHull P.interior_nonempty f
      (F.toSpace Set.univ (C.vertexPoint Set.univ v)) h extreme.1 positive
      (F.place c.1 ((C.triangle c.1).vertex c.2)) generator (projected c different).1
  refine ⟨f, h, q, nonzero, positive, in_interior, in_section.2, ?_⟩
  apply radialSlice_convexHull_eq f _ h extreme.1 positive
  rintro y ⟨d, rfl⟩ different
  exact (projected d different).1.le

end Unfoldings.SpatialFolding.ConvexBoundary
