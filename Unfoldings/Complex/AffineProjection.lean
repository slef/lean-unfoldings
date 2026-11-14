module

public import Unfoldings.Complex.ProjectedEmbedding
public import Unfoldings.Geometry.SharedEdgeOpening

/-!
# The projected metric complex

Compatible invertible affine face charts define new Euclidean triangles with
the same face, corner, seam and edge names. This is a separate metric complex;
projection is not asserted to preserve the original intrinsic lengths.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)

include joined in
/-- The two projected seam banks are exactly the same closed planar edge. -/
theorem affineProjected_seam_edges (s : C.Seam) :
    (C.affineProjectedTriangle A (C.left s).face).edge (C.left s).edge =
      (C.affineProjectedTriangle A (C.right s).face).edge (C.right s).edge := by
  calc
    _ = (A (C.left s).face) '' (C.triangle (C.left s).face).edge (C.left s).edge :=
      (C.triangle (C.left s).face).affineImage_edge
        (A (C.left s).face).toAffineMap (A (C.left s).face).injective (C.left s).edge
    _ = (A (C.right s).face) '' (C.triangle (C.right s).face).edge (C.right s).edge := by
      apply Set.Subset.antisymm
      · rintro p ⟨x, hx, rfl⟩
        exact ⟨(C.identify s ⟨x, hx⟩).val, (C.identify s ⟨x, hx⟩).property,
          (joined s ⟨x, hx⟩).symm⟩
      · rintro p ⟨y, hy, rfl⟩
        let x := (C.identify s).symm ⟨y, hy⟩
        refine ⟨x.val, x.property, ?_⟩
        rw [joined s x]
        exact congrArg (fun z => A (C.right s).face z.val)
          ((C.identify s).apply_symm_apply ⟨y, hy⟩)
    _ = _ := ((C.triangle (C.right s).face).affineImage_edge
      (A (C.right s).face).toAffineMap (A (C.right s).face).injective (C.right s).edge).symm

/-- Change the metric to the actual projected triangles while preserving all seam names. -/
def affineProjectionComplex : TriangleComplex.{u, v} Face where
  triangle := C.affineProjectedTriangle A
  Seam := C.Seam
  left := C.left
  right := C.right
  distinct := C.distinct
  identify s := (C.affineProjectedTriangle A (C.left s).face).sharedEdgeIdentification
    (C.affineProjectedTriangle A (C.right s).face) (C.left s).edge (C.right s).edge
    (C.affineProjected_seam_edges A joined s)
  unique := C.unique

/-- Actual projected face coordinates preserve the original tagged corner names. -/
def affineProjectionTotal (a : C.Total) : (C.affineProjectionComplex A joined).Total :=
  ⟨a.1, ⟨A a.1 a.2.val, by
    exact ((C.triangle a.1).affineImage_carrier (A a.1).toAffineMap
      (A a.1).injective).symm.subset ⟨a.2.val, a.2.property, rfl⟩⟩⟩

/-- Projected edge coordinates commute with the actual original seam identification. -/
theorem affineProjection_identify (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    ((C.affineProjectionComplex A joined).identify s
      ⟨A (C.left s).face x.val, by
        exact ((C.triangle (C.left s).face).affineImage_edge
          (A (C.left s).face).toAffineMap (A (C.left s).face).injective
          (C.left s).edge).symm.subset ⟨x.val, x.property, rfl⟩⟩).val =
      A (C.right s).face (C.identify s x).val :=
  joined s x

/-- The actual projected affine charts carry every retained seam identification to its new copy. -/
theorem affineProjection_glue (retain : Set C.Seam) {a b : C.Total}
    (related : C.glue retain a b) :
    (C.affineProjectionComplex A joined).glue retain
      (C.affineProjectionTotal A joined a) (C.affineProjectionTotal A joined b) := by
  obtain ⟨s, kept, x, rfl, rfl⟩ := related
  refine ⟨s, kept, ⟨A (C.left s).face x.val, ?_⟩, ?_, ?_⟩
  · exact ((C.triangle (C.left s).face).affineImage_edge
      (A (C.left s).face).toAffineMap (A (C.left s).face).injective
      (C.left s).edge).symm.subset ⟨x.val, x.property, rfl⟩
  · rfl
  · dsimp only [affineProjectionTotal]
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    exact Subtype.ext (joined s x).symm

end Unfoldings.TriangleComplex
