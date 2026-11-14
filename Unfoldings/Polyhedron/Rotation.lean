module

public import Unfoldings.Polyhedron.SupportingNormals

/-! Orthogonal changes of coordinates preserve the actual convex polyhedron. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (R : Space ≃ₗᵢ[ℝ] Space)

/-- Change spatial coordinates without changing any input triangle or seam. -/
def rotate : SpatialFolding C where
  place f := R.toLinearIsometry.toAffineIsometry.comp (F.place f)
  joined s x := congrArg R (F.joined s x)

@[simp] theorem rotate_place (f : Face) (x : Plane) :
    (F.rotate R).place f x = R (F.place f x) := rfl

theorem rotate_toSpace (retain : Set C.Seam) (x : C.Realization retain) :
    (F.rotate R).toSpace retain x = R (F.toSpace retain x) := by
  obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  rfl

theorem rotate_vertexHull : (F.rotate R).vertexHull = R '' F.vertexHull := by
  change convexHull ℝ (Set.range (fun p : Face × Fin 3 =>
    R (F.place p.1 ((C.triangle p.1).vertex p.2)))) =
      R.toLinearMap '' convexHull ℝ _
  rw [R.toLinearMap.image_convexHull]
  congr 1
  exact Set.range_comp R _

theorem rotate_surface : (F.rotate R).surface = R '' F.surface := by
  simp only [surface, faceImage, Set.image_iUnion, Set.image_image]
  rfl

namespace ConvexBoundary

variable {F R} (P : F.ConvexBoundary)

include P in
/-- The rotated input satisfies the same geometric convex-boundary conditions. -/
theorem rotate (R : Space ≃ₗᵢ[ℝ] Space) : (F.rotate R).ConvexBoundary where
  embedded := by
    intro x y same
    apply P.embedded
    apply R.injective
    simpa only [rotate_toSpace] using same
  interior_nonempty := by
    rw [rotate_vertexHull]
    change (interior (R.toHomeomorph '' F.vertexHull)).Nonempty
    rw [← R.toHomeomorph.image_interior]
    exact P.interior_nonempty.image R.toHomeomorph
  boundary := by
    rw [rotate_surface, P.boundary, rotate_vertexHull]
    exact R.toHomeomorph.image_frontier F.vertexHull

end ConvexBoundary

namespace SupportingNormals

variable {F} (N : F.SupportingNormals)

/-- Actual supporting unit normals rotate with the rigid face planes. -/
def rotate (R : Space ≃ₗᵢ[ℝ] Space) : (F.rotate R).SupportingNormals where
  normal f := R (N.normal f)
  unit f := (R.norm_map _).trans (N.unit f)
  tangent f x := by
    change inner ℝ (R (N.normal f)) (R ((F.place f).linear x)) = 0
    rw [R.inner_map_map, N.tangent]
  supporting f z hz := by
    rw [rotate_vertexHull] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    change inner ℝ (R (N.normal f)) (R y - R (F.place f 0)) ≤ 0
    rw [← map_sub, R.inner_map_map]
    exact N.supporting f y hy

end SupportingNormals
end Unfoldings.SpatialFolding
