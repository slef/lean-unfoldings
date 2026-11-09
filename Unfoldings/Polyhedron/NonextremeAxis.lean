module

public import Unfoldings.Polyhedron.ConvexCurvature
public import Unfoldings.Geometry.SpatialPlane
public import Unfoldings.Geometry.SupportingChord

/-!
# Every nonextreme vertex has a common incident-plane direction

A nonextreme vertex lies inside a nontrivial body chord. Every incident
supporting plane must contain both ends of that chord, since its functional
attains the support level at the interior vertex. Thus all incident rigid
face planes contain one common nonzero line direction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_axis_of_nonextreme (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    ∃ d : Space, d ≠ 0 ∧ ∀ c : C.CornerAt Set.univ v,
      d ∈ LinearMap.range (F.place c.val.1).linear := by
  let z := F.toSpace Set.univ (C.vertexPoint Set.univ v)
  have member : z ∈ F.vertexHull := F.surface_subset_vertexHull
    ((F.range_toSpace Set.univ).le ⟨C.vertexPoint Set.univ v, rfl⟩)
  have chord : ∃ x ∈ F.vertexHull, ∃ y ∈ F.vertexHull,
      z ∈ openSegment ℝ x y ∧ x ≠ z := by
    by_contra none
    apply not_extreme
    refine mem_extremePoints_iff_left.mpr ⟨member, ?_⟩
    intro x hx y hy between
    by_contra different
    exact none ⟨x, hx, y, hy, between, different⟩
  obtain ⟨x, hx, y, hy, between, different⟩ := chord
  refine ⟨x - z, sub_ne_zero.mpr different, ?_⟩
  intro c
  obtain ⟨f, a, nonzero, supported, _strict, face_level⟩ := P.exists_face_support c.val.1
  have vertex_level : f z = a := by
    change f (F.toSpace Set.univ (C.vertexPoint Set.univ v)) = a
    rw [← F.tangentApex_spatial_eq Set.univ v c]
    exact face_level _
  have endpoint_levels := supporting_functional_eq_endpoints f
    (supported x hx) (supported y hy) between vertex_level
  have range_eq : LinearMap.range (F.place c.val.1).linear = f.toLinearMap.ker :=
    affineIsometry_linear_range_eq_kernel (F.place c.val.1) f nonzero a face_level
  rw [range_eq]
  change f (x - z) = 0
  rw [map_sub, endpoint_levels.1, vertex_level, sub_self]

end Unfoldings.SpatialFolding.ConvexBoundary
