module

public import Unfoldings.Polyhedron.VertexNeighborhood
public import Unfoldings.Geometry.LocalHingeBoundary

/-!
# Constructed local support hinges at nonextreme vertices

The two planes come from actual incident faces. Their supporting half-planes
describe the entire nearby spatial surface, with a positive radius. They may
coincide, retaining the locally planar case. The structure stores no metric
chart or curvature conclusion; those must be constructed from this geometry.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

structure VertexHinge (v : C.Vertex Set.univ) where
  left : C.CornerAt Set.univ v
  right : C.CornerAt Set.univ v
  leftFunctional : Space →L[ℝ] ℝ
  rightFunctional : Space →L[ℝ] ℝ
  leftLevel : ℝ
  rightLevel : ℝ
  left_nonzero : leftFunctional ≠ 0
  right_nonzero : rightFunctional ≠ 0
  left_plane : ∀ p : Plane, leftFunctional (F.place left.val.1 p) = leftLevel
  right_plane : ∀ p : Plane, rightFunctional (F.place right.val.1 p) = rightLevel
  left_supported : ∀ z ∈ F.vertexHull, leftFunctional z ≤ leftLevel
  right_supported : ∀ z ∈ F.vertexHull, rightFunctional z ≤ rightLevel
  radius : ℝ
  positive : 0 < radius
  local_surface : ∀ z, dist z (F.toSpace Set.univ (C.vertexPoint Set.univ v)) < radius →
    (z ∈ F.surface ↔ (leftFunctional z = leftLevel ∧ rightFunctional z ≤ rightLevel) ∨
      (rightFunctional z = rightLevel ∧ leftFunctional z ≤ leftLevel))

namespace VertexHinge

variable {F} {v : C.Vertex Set.univ} (H : F.VertexHinge v)

theorem left_vertex_level :
    H.leftFunctional (F.toSpace Set.univ (C.vertexPoint Set.univ v)) = H.leftLevel := by
  rw [← F.tangentApex_spatial_eq Set.univ v H.left]
  exact H.left_plane _

theorem right_vertex_level :
    H.rightFunctional (F.toSpace Set.univ (C.vertexPoint Set.univ v)) = H.rightLevel := by
  rw [← F.tangentApex_spatial_eq Set.univ v H.right]
  exact H.right_plane _

theorem left_range : Set.range (F.place H.left.val.1) = {z | H.leftFunctional z = H.leftLevel} :=
  range_affineIsometry_eq_level (F.place H.left.val.1) H.leftFunctional H.left_nonzero
    H.leftLevel H.left_plane

theorem right_range : Set.range (F.place H.right.val.1) =
    {z | H.rightFunctional z = H.rightLevel} :=
  range_affineIsometry_eq_level (F.place H.right.val.1) H.rightFunctional H.right_nonzero
    H.rightLevel H.right_plane

end VertexHinge

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary)

include P

theorem exists_vertexHinge (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    Nonempty (F.VertexHinge v) := by
  obtain ⟨left, right, r, positive, cover⟩ :=
    P.exists_nonextreme_two_plane_neighborhood v not_extreme
  obtain ⟨f, a, fne, fsupported, fstrict, fplane⟩ := P.exists_face_support left.val.1
  obtain ⟨g, b, gne, gsupported, gstrict, gplane⟩ := P.exists_face_support right.val.1
  obtain ⟨origin, inside⟩ := P.interior_nonempty
  have boundary : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ frontier F.vertexHull := by
    rw [← P.boundary]
    exact (F.range_toSpace Set.univ).le ⟨C.vertexPoint Set.univ v, rfl⟩
  have planes : ∀ z ∈ frontier F.vertexHull,
      dist z (F.toSpace Set.univ (C.vertexPoint Set.univ v)) < r → f z = a ∨ g z = b := by
    intro z hz near
    have surface : z ∈ F.surface := by rwa [P.boundary]
    rcases cover z surface near with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact Or.inl (fplane p)
    · exact Or.inr (gplane p)
  obtain ⟨δ, δpos, exact_boundary⟩ := exists_local_frontier_hinge F.convex_vertexHull
    F.compact_vertexHull inside boundary (fstrict origin inside) (gstrict origin inside)
    fsupported gsupported positive planes
  refine ⟨⟨left, right, f, g, a, b, fne, gne, fplane, gplane,
    fsupported, gsupported, δ, δpos, ?_⟩⟩
  intro z hz
  rw [P.boundary]
  exact exact_boundary z hz

def vertexHinge (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    F.VertexHinge v := Classical.choice (P.exists_vertexHinge v not_extreme)

end ConvexBoundary
end Unfoldings.SpatialFolding
