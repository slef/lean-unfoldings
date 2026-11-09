module

public import Unfoldings.Polyhedron.PlanarPatch
public import Unfoldings.Polyhedron.VertexHinge

/-!
# Intrinsic regularity from a locally planar convex boundary

Radial projection fills a whole spatial plane patch when the nearby boundary
is contained in an original supporting plane. The proved convex-patch
isometry then supplies a whole intrinsic Euclidean metric-ball chart.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem isRegularPoint_of_locally_in_face_plane (face : Face) (p : Plane)
    (x : C.Realization Set.univ) (center : F.place face p = F.toSpace Set.univ x)
    {r : ℝ} (positive : 0 < r)
    (cover : ∀ z ∈ F.surface, dist z (F.toSpace Set.univ x) < r →
      z ∈ Set.range (F.place face)) : C.IsRegularPoint Set.univ x := by
  obtain ⟨f, a, nonzero, supported, strict, plane⟩ := P.exists_face_support face
  obtain ⟨origin, inside⟩ := P.interior_nonempty
  have boundary : F.toSpace Set.univ x ∈ frontier F.vertexHull := by
    rw [← P.boundary]
    exact (F.range_toSpace Set.univ).le ⟨x, rfl⟩
  have plane_cover : ∀ z ∈ frontier F.vertexHull, dist z (F.toSpace Set.univ x) < r →
      f z = a ∨ f z = a := by
    intro z hz near
    have surface : z ∈ F.surface := by rwa [P.boundary]
    obtain ⟨q, rfl⟩ := cover z surface near
    exact Or.inl (plane q)
  obtain ⟨δ, δpos, exact_boundary⟩ := exists_local_frontier_hinge
    (f := f) (g := f) (a := a) (b := a) F.convex_vertexHull F.compact_vertexHull
    inside boundary (strict origin inside) (strict origin inside)
    supported supported positive plane_cover
  have model (z : Space) (near : dist z (F.toSpace Set.univ x) < δ) :
      z ∈ F.surface ↔ f z = a := by
    have exact_at_z := exact_boundary z near
    rw [← P.boundary] at exact_at_z
    constructor
    · intro hz
      rcases exact_at_z.mp hz with first | second
      · exact first.1
      · exact second.1
    · intro level
      exact exact_at_z.mpr (Or.inl ⟨level, level.le⟩)
  apply P.isRegularPoint_of_planar_patch (F.place face) p x center δpos
  · rintro z ⟨q, near, rfl⟩
    apply (model _ ?_).mpr (plane q)
    rw [← center, (F.place face).isometry.dist_eq]
    exact Metric.mem_ball.mp near
  · intro z hz near
    have height := (model z (by rwa [center] at near)).mp hz
    exact (range_affineIsometry_eq_level (F.place face) f nonzero a plane).ge height

theorem isRegularPoint_of_incident_planes_eq (v : C.Vertex Set.univ)
    (a : C.CornerAt Set.univ v)
    (planes : ∀ b : C.CornerAt Set.univ v, LinearMap.range (F.place b.val.1).linear =
      LinearMap.range (F.place a.val.1).linear) :
    C.IsRegularPoint Set.univ (C.vertexPoint Set.univ v) := by
  obtain ⟨r, positive, star⟩ := P.exists_spatial_vertex_star_radius v
  apply P.isRegularPoint_of_locally_in_face_plane a.val.1
    ((C.triangle a.val.1).vertex a.val.2) (C.vertexPoint Set.univ v)
    (F.tangentApex_spatial_eq Set.univ v a) positive
  intro z surface near
  obtain ⟨b, p, _hp, image⟩ := star z surface near
  have member : z ∈ Set.range (F.place b.val.1) := ⟨p, image⟩
  rwa [F.incident_plane_ranges_eq b a (planes b)] at member

theorem isRegularPoint_of_coplanar_vertexHinge {v : C.Vertex Set.univ}
    (H : F.VertexHinge v)
    (coplanar : LinearMap.range (F.place H.left.val.1).linear =
      LinearMap.range (F.place H.right.val.1).linear) :
    C.IsRegularPoint Set.univ (C.vertexPoint Set.univ v) := by
  apply P.isRegularPoint_of_locally_in_face_plane H.left.val.1
    ((C.triangle H.left.val.1).vertex H.left.val.2) (C.vertexPoint Set.univ v)
    (F.tangentApex_spatial_eq Set.univ v H.left) H.positive
  intro z surface near
  rcases (H.local_surface z near).mp surface with first | second
  · exact H.left_range.ge first.1
  · have member := H.right_range.ge second.1
    rwa [F.incident_plane_ranges_eq H.right H.left coplanar.symm] at member

end Unfoldings.SpatialFolding.ConvexBoundary
