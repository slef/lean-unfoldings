module

public import Unfoldings.Polyhedron.FigureIncidence

/-!
# Actual vertex-figure edges from incident triangles

The complete finite-hull slice formula applies to each original triangle.
Removing its apex leaves exactly its other two corners, so its section is
the segment between their radial projections. These segments lie on the
actual figure boundary and cover it, indexed by the actual incident corners.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)

theorem spatial_face_section_eq_segment (c : C.CornerAt Set.univ v) :
    radialSlice (F.faceImage c.val.1) V.functional
        (F.toSpace Set.univ (C.vertexPoint Set.univ v)) V.level =
      segment ℝ
        (radialSlicePoint V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v))
          V.level (F.place c.val.1 ((C.triangle c.val.1).vertex (Triangle.next c.val.2))))
        (radialSlicePoint V.functional (F.toSpace Set.univ (C.vertexPoint Set.univ v))
          V.level
            (F.place c.val.1
              ((C.triangle c.val.1).vertex (Triangle.next (Triangle.next c.val.2))))) := by
  let x := F.toSpace Set.univ (C.vertexPoint Set.univ v)
  let points (i : Fin 3) := F.place c.val.1 ((C.triangle c.val.1).vertex i)
  have apex : points c.val.2 = x :=
    congrArg (fun w : C.Vertex Set.univ => F.toSpace Set.univ (C.vertexPoint Set.univ w))
      c.property
  have injective : Function.Injective points :=
    (F.place c.val.1).injective.comp (C.triangle c.val.1).vertex_injective
  have distinct_indices (i : Fin 3) :
      Triangle.next i ≠ i ∧ Triangle.next (Triangle.next i) ≠ i := by
    fin_cases i <;> decide
  have next_ne : points (Triangle.next c.val.2) ≠ x := fun equal =>
    (distinct_indices c.val.2).1 (injective (equal.trans apex.symm))
  have prev_ne : points (Triangle.next (Triangle.next c.val.2)) ≠ x := fun equal =>
    (distinct_indices c.val.2).2 (injective (equal.trans apex.symm))
  have remaining : Set.range points \ {x} =
      {points (Triangle.next c.val.2), points (Triangle.next (Triangle.next c.val.2))} := by
    ext z
    constructor
    · rintro ⟨⟨i, rfl⟩, different⟩
      rcases Triangle.corner_cases c.val.2 i with rfl | rfl | rfl
      · exact (different (Set.mem_singleton_iff.mpr apex)).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro inside
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at inside
      rcases inside with rfl | rfl
      · exact ⟨⟨_, rfl⟩, by simpa only [Set.mem_singleton_iff] using next_ne⟩
      · exact ⟨⟨_, rfl⟩, by simpa only [Set.mem_singleton_iff] using prev_ne⟩
  have equation := radialSlice_convexHull_eq V.functional x V.level
    (subset_convexHull ℝ (Set.range points) ⟨c.val.2, apex⟩) V.positive
    (fun y hy different => by
      obtain ⟨i, rfl⟩ := hy
      exact (V.supported (c.val.1, i) different).le)
  rw [remaining, Set.image_pair, convexHull_pair] at equation
  rw [F.faceImage_eq_convexHull c.val.1]
  exact equation

end Unfoldings.SpatialFolding.VertexFigure

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)

include P

theorem figure_face_section_subset_boundary (c : C.CornerAt Set.univ v) :
    radialSlice (F.faceImage c.val.1) V.functional
        (F.toSpace Set.univ (C.vertexPoint Set.univ v)) V.level ⊆
      V.place '' frontier V.carrier := by
  intro z hz
  rw [P.image_figure_frontier V]
  exact ⟨Set.mem_iUnion.mpr ⟨c.val.1, hz.1⟩, hz.2⟩

theorem figure_boundary_eq_union_face_sections :
    V.place '' frontier V.carrier =
      ⋃ c : C.CornerAt Set.univ v, radialSlice (F.faceImage c.val.1) V.functional
        (F.toSpace Set.univ (C.vertexPoint Set.univ v)) V.level := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, boundary, rfl⟩
    obtain ⟨c, in_face⟩ := P.figure_boundary_has_corner V p boundary
    exact Set.mem_iUnion.mpr ⟨c, in_face, V.range_place.le ⟨p, rfl⟩⟩
  · intro z inside
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp inside
    exact P.figure_face_section_subset_boundary V c hc

end Unfoldings.SpatialFolding.ConvexBoundary
