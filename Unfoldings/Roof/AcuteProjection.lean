module

public import Unfoldings.Roof.ProjectedFaces
public import Unfoldings.Cap.AcuteProjection

/-! A uniform positive normal-tilt threshold preserves an acute mesh with half its angle margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Tangency of an actual face chord, including chords outside the triangle carrier. -/
theorem normal_tangent_chord (f : Face) (x y : Plane) :
    inner ℝ (K.normal f) (K.folding.place f x - K.folding.place f y) = 0 := by
  have linear := (K.folding.place f).toAffineMap.linear_apply_vsub x y
  change (K.folding.place f).linear (x - y) =
    K.folding.place f x - K.folding.place f y at linear
  rw [← linear]
  exact K.normal_tangent f (x - y)

/-- Projection angle distortion for a whole face follows from the universal tangent estimate. -/
theorem face_projection_angle_error {ε φ : ℝ}
    (estimate : ∀ normal a b : Space, ‖normal‖ = 1 → Real.cos φ ≤ normal 2 →
      a ≠ 0 → b ≠ 0 → inner ℝ normal a = 0 → inner ℝ normal b = 0 →
      |InnerProductGeometry.angle (Cap.horizontal a) (Cap.horizontal b) -
        InnerProductGeometry.angle a b| < ε)
    (tilt : K.TiltBound φ) (f : Face) (x y z : Plane) (xy : x ≠ y) (zy : z ≠ y) :
    |EuclideanGeometry.angle (K.projectFace f x) (K.projectFace f y) (K.projectFace f z) -
      EuclideanGeometry.angle x y z| < ε := by
  have result := estimate (K.normal f)
    (K.folding.place f x - K.folding.place f y)
    (K.folding.place f z - K.folding.place f y)
    (K.normal_unit f) (tilt f)
    (sub_ne_zero.mpr ((K.folding.place f).injective.ne xy))
    (sub_ne_zero.mpr ((K.folding.place f).injective.ne zy))
    (K.normal_tangent_chord f x y) (K.normal_tangent_chord f z y)
  have original := (K.folding.place f).angle_map x y z
  change InnerProductGeometry.angle (K.folding.place f x - K.folding.place f y)
    (K.folding.place f z - K.folding.place f y) = _ at original
  rw [original, map_sub, map_sub] at result
  exact result

/-- A single tilt threshold works simultaneously for every cap and every face of its input mesh. -/
theorem exists_acute_projection_tilt {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ K : ConvexRoof C,
      AcuteMargin (C := C) α → K.TiltBound φ → ∀ f i,
        (K.projectedTriangle f).cornerAngle i < Real.pi / 2 - α / 2 := by
  obtain ⟨φ, φbounds, estimate⟩ := Cap.exists_projection_angle_tilt (half_pos positive)
  refine ⟨φ, φbounds, fun K acute tilt f i => ?_⟩
  have first : (C.triangle f).vertex (Triangle.next i) ≠ (C.triangle f).vertex i :=
    (C.triangle f).affineIndependent_vertices.injective.ne (by fin_cases i <;> decide)
  have last : (C.triangle f).vertex (Triangle.next (Triangle.next i)) ≠
      (C.triangle f).vertex i :=
    (C.triangle f).affineIndependent_vertices.injective.ne (by fin_cases i <;> decide)
  have error := K.face_projection_angle_error estimate tilt f _ _ _ first last
  change |(K.projectedTriangle f).cornerAngle i - (C.triangle f).cornerAngle i| < α / 2 at error
  have upper := (abs_lt.mp error).2
  linarith [acute f i]

end Unfoldings.ConvexRoof
