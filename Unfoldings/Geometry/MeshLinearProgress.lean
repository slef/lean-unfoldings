module

public import Unfoldings.Geometry.MeshProgress
public import Unfoldings.Geometry.TriangleAffine
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Outgoing quadrant edges after any invertible planar linear change of coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem linearEquiv_affine_injective (A : Plane ≃ₗ[ℝ] Plane) :
    Function.Injective A.toLinearMap.toAffineMap := A.injective

theorem exists_mesh_linear_quadrant_edge {Face : Type*} [Finite Face]
    (triangle : Face → Triangle) (A : Plane ≃ₗ[ℝ] Plane) (region : Set Plane)
    (cover : region ⊆ ⋃ f, (triangle f).carrier) (center : Plane)
    (inside : center ∈ interior region)
    (corner : ∀ f, center ∈ (triangle f).carrier → ∃ i, (triangle f).vertex i = center)
    (acute : ∀ f i, ((triangle f).affineImage A.toAffineMap
      (linearEquiv_affine_injective A)).cornerAngle i <
      Real.pi / 2) :
    ∃ f i, (triangle f).vertex i = center ∧
      (StrictQuadrant (A ((triangle f).vertex (Triangle.next i) - center)) ∨
      StrictQuadrant (A ((triangle f).vertex (Triangle.next (Triangle.next i)) - center))) := by
  let H : Plane ≃ₜ Plane := A.toContinuousLinearEquiv.toHomeomorph
  let moved (f : Face) := (triangle f).affineImage A.toAffineMap (linearEquiv_affine_injective A)
  have covered : H '' region ⊆ ⋃ f, (moved f).carrier := by
    rintro _ ⟨p, present, rfl⟩
    obtain ⟨f, face⟩ := Set.mem_iUnion.mp (cover present)
    exact Set.mem_iUnion.mpr ⟨f,
      (Triangle.affineImage_carrier _ _ _).symm ▸ ⟨p, face, rfl⟩⟩
  have internal : H center ∈ interior (H '' region) := by
    rw [← H.image_interior]
    exact Set.mem_image_of_mem H inside
  have corner_moved (f : Face) (present : H center ∈ (moved f).carrier) :
      ∃ i, (moved f).vertex i = H center := by
    change H center ∈ ((triangle f).affineImage A.toAffineMap
      (linearEquiv_affine_injective A)).carrier at present
    have carrier := (triangle f).affineImage_carrier A.toAffineMap (linearEquiv_affine_injective A)
    have mapped : H center ∈ A.toAffineMap '' (triangle f).carrier := carrier ▸ present
    obtain ⟨p, face, equal⟩ := mapped
    have same : p = center := H.injective equal
    obtain ⟨i, vertex⟩ := corner f (same ▸ face)
    exact ⟨i, congrArg H vertex⟩
  obtain ⟨f, i, vertex, forward⟩ := exists_mesh_quadrant_edge moved (H '' region) covered
    (H center) internal corner_moved acute
  refine ⟨f, i, H.injective vertex, ?_⟩
  change StrictQuadrant (A ((triangle f).vertex (Triangle.next i)) - A center) ∨
    StrictQuadrant (A ((triangle f).vertex (Triangle.next (Triangle.next i))) - A center) at forward
  simpa only [map_sub] using forward

end Unfoldings
