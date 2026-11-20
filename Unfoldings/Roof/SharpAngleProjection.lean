module

public import Unfoldings.Cap.SharpAngleProjection
public import Unfoldings.Roof.AcuteProjection

/-! The sharp tilt correction applies to the actual projected input triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The projection of any genuine face angle differs from its original
value by at most the exact tilt correction. -/
theorem face_projection_angle_error_le {c : ℝ} (c_pos : 0 < c)
    (f : Face) (height : c ≤ K.normal f 2) (x y z : Plane) (xy : x ≠ y) (zy : z ≠ y) :
    |EuclideanGeometry.angle (K.projectFace f x) (K.projectFace f y) (K.projectFace f z) -
      EuclideanGeometry.angle x y z| ≤ 2 * Real.arcsin ((1 - c) / (1 + c)) := by
  have result := Cap.tangent_projection_angle_error (K.normal_unit f) c_pos height
    (sub_ne_zero.mpr ((K.folding.place f).injective.ne xy))
    (sub_ne_zero.mpr ((K.folding.place f).injective.ne zy))
    (K.normal_tangent_chord f x y) (K.normal_tangent_chord f z y)
  have original := (K.folding.place f).angle_map x y z
  change InnerProductGeometry.angle (K.folding.place f x - K.folding.place f y)
    (K.folding.place f z - K.folding.place f y) = _ at original
  rw [original, map_sub, map_sub] at result
  exact result

/-- A spatial input bound gives the local projected angle bound used by the
adaptive heading criterion, at the stated positive normal height. -/
theorem projected_cornerAngle_le_of_normal_height {θ c : ℝ} (c_pos : 0 < c)
    (f : Face) (height : c ≤ K.normal f 2) (i : Fin 3)
    (angle_bound : (C.triangle f).cornerAngle i ≤ θ) :
    (K.projectedTriangle f).cornerAngle i ≤ θ + 2 * Real.arcsin ((1 - c) / (1 + c)) := by
  have first : (C.triangle f).vertex (Triangle.next i) ≠ (C.triangle f).vertex i :=
    (C.triangle f).affineIndependent_vertices.injective.ne (by fin_cases i <;> decide)
  have last : (C.triangle f).vertex (Triangle.next (Triangle.next i)) ≠ (C.triangle f).vertex i :=
    (C.triangle f).affineIndependent_vertices.injective.ne (by fin_cases i <;> decide)
  have error := K.face_projection_angle_error_le c_pos f height _ _ _ first last
  change |(K.projectedTriangle f).cornerAngle i - (C.triangle f).cornerAngle i| ≤ _ at error
  linarith [(abs_le.mp error).2]

end Unfoldings.ConvexRoof
