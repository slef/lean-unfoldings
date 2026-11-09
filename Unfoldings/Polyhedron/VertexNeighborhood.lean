module

public import Unfoldings.Polyhedron.NonextremePlanes
public import Unfoldings.Geometry.AffinePlaneRange

/-!
# Actual spatial neighborhoods of convex-boundary vertices

Embeddedness forces every original face containing a spatial vertex to have
an actual corner there. The finite closed face cover excludes all other
faces on one small spatial ball. At nonextreme vertices, the proved two-plane
classification therefore contains the whole nearby spatial boundary.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem incident_plane_ranges_eq {v : C.Vertex Set.univ} (a b : C.CornerAt Set.univ v)
    (directions : LinearMap.range (F.place a.val.1).linear =
      LinearMap.range (F.place b.val.1).linear) :
    Set.range (F.place a.val.1) = Set.range (F.place b.val.1) := by
  have common := (F.tangentApex_spatial_eq Set.univ v a).trans
    (F.tangentApex_spatial_eq Set.univ v b).symm
  exact affineMap_range_eq_of_linear_range_eq (F.place a.val.1).toAffineMap
    (F.place b.val.1).toAffineMap ((C.triangle a.val.1).vertex a.val.2)
    ((C.triangle b.val.1).vertex b.val.2) common directions

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary)

include P

theorem face_has_corner_of_vertex_image (v : C.Vertex Set.univ) (face : Face)
    (member : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.faceImage face) :
    ∃ i, C.vertexOfCorner Set.univ (face, i) = v := by
  obtain ⟨p, hp, image⟩ := member
  have equal : C.faceMap Set.univ face ⟨p, hp⟩ = C.vertexPoint Set.univ v := P.embedded image
  have vertex : C.IsVertex (⟨face, ⟨p, hp⟩⟩ : C.Total) :=
    (C.mem_range_vertexPoint_iff Set.univ _).mp ⟨v, equal.symm⟩
  obtain ⟨i, coordinate⟩ := vertex
  refine ⟨i, C.vertexPoint_injective Set.univ ?_⟩
  change C.faceMap Set.univ face
    ⟨(C.triangle face).vertex i, (C.triangle face).vertex_mem i⟩ = _
  have cells : (⟨(C.triangle face).vertex i, (C.triangle face).vertex_mem i⟩ : C.Cell face) =
      ⟨p, hp⟩ := Subtype.ext coordinate
  rw [cells]
  exact equal

theorem exists_spatial_vertex_star_radius (v : C.Vertex Set.univ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ F.surface,
      dist z (F.toSpace Set.univ (C.vertexPoint Set.univ v)) < r →
      ∃ c : C.CornerAt Set.univ v, z ∈ F.faceImage c.val.1 := by
  classical
  let other : Set Space := ⋃ f : {f : Face // ¬ ∃ i, C.vertexOfCorner Set.univ (f, i) = v},
    F.faceImage f.val
  have closed : IsClosed other := isClosed_iUnion_of_finite
    (fun f => (F.compact_faceImage f.val).isClosed)
  have outside : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ other := by
    intro member
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp member
    exact f.property (P.face_has_corner_of_vertex_image v f.val hf)
  obtain ⟨r, positive, clear⟩ := Metric.isOpen_iff.mp closed.isOpen_compl _ outside
  refine ⟨r, positive, ?_⟩
  intro z surface near
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp surface
  by_cases incident : ∃ i, C.vertexOfCorner Set.univ (f, i) = v
  · obtain ⟨i, hi⟩ := incident
    exact ⟨⟨(f, i), hi⟩, hf⟩
  · exact (clear (Metric.mem_ball.mpr near) (Set.mem_iUnion.mpr ⟨⟨f, incident⟩, hf⟩)).elim

theorem exists_nonextreme_two_plane_neighborhood (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    ∃ a b : C.CornerAt Set.univ v, ∃ r : ℝ, 0 < r ∧ ∀ z ∈ F.surface,
      dist z (F.toSpace Set.univ (C.vertexPoint Set.univ v)) < r →
      z ∈ Set.range (F.place a.val.1) ∪ Set.range (F.place b.val.1) := by
  obtain ⟨a, b, planes⟩ := P.exists_two_incident_planes v not_extreme
  obtain ⟨r, positive, star⟩ := P.exists_spatial_vertex_star_radius v
  refine ⟨a, b, r, positive, ?_⟩
  intro z surface near
  obtain ⟨c, member⟩ := star z surface near
  obtain ⟨p, _hp, image⟩ := member
  have in_plane : z ∈ Set.range (F.place c.val.1) := ⟨p, image⟩
  rcases planes c with first | second
  · exact Or.inl (F.incident_plane_ranges_eq c a first ▸ in_plane)
  · exact Or.inr (F.incident_plane_ranges_eq c b second ▸ in_plane)

end ConvexBoundary
end Unfoldings.SpatialFolding
