module

public import Unfoldings.Polyhedron.Convex
public import Unfoldings.Geometry.AffineMaximum
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Supporting planes of actual input triangles

Separate the convex body at a spatial point from an original face interior.
The support functional pulls back to an affine functional with an interior
local maximum on the Euclidean triangle, hence is constant on its whole
affine plane. Thus the plane of every input face supports the actual body,
including faces subdividing a larger maximal facet.
-/

@[expose] public section

open Topology

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_face_support (face : Face) :
    ∃ (f : Space →L[ℝ] ℝ) (a : ℝ), f ≠ 0 ∧
      (∀ z ∈ F.vertexHull, f z ≤ a) ∧
      (∀ z ∈ interior F.vertexHull, f z < a) ∧
      ∀ p : Plane, f (F.place face p) = a := by
  obtain ⟨p, inside⟩ := (C.triangle face).interior_nonempty
  let z := F.place face p
  have surface : z ∈ F.surface :=
    Set.mem_iUnion.mpr ⟨face, p, interior_subset inside, rfl⟩
  have boundary : z ∈ frontier F.vertexHull := by rw [← P.boundary]; exact surface
  obtain ⟨f, nonzero, supported⟩ := geometric_hahn_banach_of_nonempty_interior_point
    F.convex_vertexHull boundary.2 P.interior_nonempty
  let g : Plane →ᵃ[ℝ] ℝ := f.toLinearMap.toAffineMap.comp (F.place face).toAffineMap
  have maximum : IsLocalMax g p := by
    change ∀ᶠ q in 𝓝 p, f (F.place face q) ≤ f (F.place face p)
    exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp inside) (fun q hq =>
      supported (F.place face q) (F.faceImage_subset_vertexHull face ⟨q, hq, rfl⟩))
  refine ⟨f, f z, nonzero, supported, ?_, ?_⟩
  · intro q hq
    exact supporting_functional_lt_on_interior f nonzero F.vertexHull (f z) supported q hq
  · intro q
    exact affine_eq_at_of_localMax g p maximum q

end Unfoldings.SpatialFolding.ConvexBoundary
