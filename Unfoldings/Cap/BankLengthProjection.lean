module

public import Unfoldings.Cap.ProjectedFaces
public import Unfoldings.Complex.GermEndpoints

/-! Actual original and projected bank lengths obey the normal-dependent contraction estimates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem face_projection_upper (f : Face) (x y : Plane) :
    dist (K.projectFace f x) (K.projectFace f y) ≤ dist x y := by
  calc
    _ = ‖Cap.horizontal (K.folding.place f x - K.folding.place f y)‖ := by
      rw [map_sub, dist_eq_norm]
      rfl
    _ ≤ ‖K.folding.place f x - K.folding.place f y‖ := Cap.horizontal_norm_le _
    _ = dist x y := by rw [← dist_eq_norm, (K.folding.place f).isometry.dist_eq]

/-- The two length comparisons concern the same original directed edge germ. -/
theorem germ_length_projection (p : C.Germ) :
    dist ((K.projectedTriangle p.1.1).vertex (C.germFarCorner p).2)
        ((K.projectedTriangle p.1.1).vertex p.1.2) ≤
      dist ((C.triangle p.1.1).vertex (C.germFarCorner p).2)
        ((C.triangle p.1.1).vertex p.1.2) ∧
    K.normal p.1.1 2 *
      dist ((C.triangle p.1.1).vertex (C.germFarCorner p).2)
        ((C.triangle p.1.1).vertex p.1.2) ≤
      dist ((K.projectedTriangle p.1.1).vertex (C.germFarCorner p).2)
        ((K.projectedTriangle p.1.1).vertex p.1.2) :=
  ⟨K.face_projection_upper p.1.1 _ _, K.face_projection_lower p.1.1 _ _⟩

end Unfoldings.ConvexCap
