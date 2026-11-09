module

public import Unfoldings.Polyhedron.VertexHinge

/-! Construct support hinges using prescribed actual incident planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_vertexHinge_of_incident_planes {v : C.Vertex Set.univ}
    (left right : C.CornerAt Set.univ v)
    (cover : ∀ c : C.CornerAt Set.univ v,
      LinearMap.range (F.place c.val.1).linear = LinearMap.range (F.place left.val.1).linear ∨
        LinearMap.range (F.place c.val.1).linear = LinearMap.range (F.place right.val.1).linear) :
    ∃ H : F.VertexHinge v, H.left = left ∧ H.right = right := by
  obtain ⟨r, positive, star⟩ := P.exists_spatial_vertex_star_radius v
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
    obtain ⟨c, p, _hp, image⟩ := star z surface near
    have member : z ∈ Set.range (F.place c.val.1) := ⟨p, image⟩
    rcases cover c with first | second
    · rw [F.incident_plane_ranges_eq c left first] at member
      obtain ⟨q, rfl⟩ := member
      exact Or.inl (fplane q)
    · rw [F.incident_plane_ranges_eq c right second] at member
      obtain ⟨q, rfl⟩ := member
      exact Or.inr (gplane q)
  obtain ⟨δ, δpos, exact_boundary⟩ := exists_local_frontier_hinge F.convex_vertexHull
    F.compact_vertexHull inside boundary (fstrict origin inside) (gstrict origin inside)
    fsupported gsupported positive planes
  refine ⟨⟨left, right, f, g, a, b, fne, gne, fplane, gplane,
    fsupported, gsupported, δ, δpos, ?_⟩, rfl, rfl⟩
  intro z hz
  rw [P.boundary]
  exact exact_boundary z hz

end Unfoldings.SpatialFolding.ConvexBoundary
