module

public import Unfoldings.Roof.ProjectedRemovedSeams
public import Unfoldings.Roof.ProjectedFaces

/-! Original partial cut carriers retain exact finite segment descriptions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Removed original seams project to exactly their original closed triangle edges. -/
theorem removedProjectedSeamCarrier_eq_union_edges (retain : Set C.Seam) :
    K.removedProjectedSeamCarrier retain =
      ⋃ s : {s : C.Seam // s ∉ retain},
        (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge := by
  simp only [removedProjectedSeamCarrier, SpatialFolding.removedSeamCarrier,
    Set.image_iUnion, Set.image_image]
  simp only [projectedTriangle, Triangle.affineImage_edge]
  rfl

/-- Every removed projected seam stays inside the original closed roof footprint. -/
theorem removedProjectedSeamCarrier_subset_footprint (retain : Set C.Seam) :
    K.removedProjectedSeamCarrier retain ⊆ K.footprint := by
  rintro p ⟨z, member, rfl⟩
  exact ⟨z, K.folding.removedSeamCarrier_subset_surface retain member, rfl⟩

end Unfoldings.ConvexRoof
