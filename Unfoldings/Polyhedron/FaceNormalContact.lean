module

public import Unfoldings.Polyhedron.SupportingNormals
public import Unfoldings.Geometry.SupportedNormalUnique

/-! A supporting plane touching an original triangular face interior has that face's normal. -/

@[expose] public section

open scoped Topology

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
theorem normal_eq_of_interior_contact (f g : Face) {x : Plane}
    (inside : x ∈ interior (C.triangle g).carrier)
    (contact : inner ℝ (N.normal f) (F.place g x - F.place f 0) = 0) :
    N.normal f = N.normal g := by
  let functional := innerSL ℝ (N.normal f)
  let A := functional.toLinearMap.toAffineMap.comp (F.place g).toAffineMap
  have maximum : IsLocalMax A x := by
    change ∀ᶠ y in 𝓝 x, inner ℝ (N.normal f) (F.place g y) ≤
      inner ℝ (N.normal f) (F.place g x)
    apply Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp inside)
    intro y hy
    have support := N.supporting f (F.place g y) (F.faceImage_subset_vertexHull g ⟨y, hy, rfl⟩)
    rw [inner_sub_right] at support contact
    calc
      inner ℝ (N.normal f) (F.place g y) ≤ inner ℝ (N.normal f) (F.place f 0) :=
        sub_nonpos.mp support
      _ = inner ℝ (N.normal f) (F.place g x) := (sub_eq_zero.mp contact).symm
  have linear_zero := affine_linear_eq_zero_of_localMax A x maximum
  have tangent_f (y : Plane) : inner ℝ (N.normal f) ((F.place g).linear y) = 0 :=
    congrArg (fun l : Plane →ₗ[ℝ] ℝ => l y) linear_zero
  have at_zero := affine_eq_at_of_localMax A x maximum 0
  change inner ℝ (N.normal f) (F.place g 0) = inner ℝ (N.normal f) (F.place g x) at at_zero
  obtain ⟨c, interior_c⟩ := P.interior_nonempty
  have strict_f := N.supporting_strict f interior_c
  have strict_g := N.supporting_strict g interior_c
  have negative_f : inner ℝ (N.normal f) (c - F.place g 0) < 0 := by
    rw [inner_sub_right] at contact strict_f ⊢
    linarith
  exact unit_normal_unique (F.place g) _ _ (N.unit f) (N.unit g) tangent_f (N.tangent g)
    c negative_f strict_g

end Unfoldings.SpatialFolding.ConvexBoundary
