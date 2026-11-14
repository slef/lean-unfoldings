module

public import Unfoldings.Cap.BankLengthProjection
public import Unfoldings.Cap.AngleProjection
public import Unfoldings.Geometry.LinearAngleSine
public import Unfoldings.Geometry.RelativeSineError

/-!
# Relative projection-angle error

A single positive tilt threshold makes every actual face-angle error at most a
prescribed fraction of its projected angle. Unlike an additive corner bound,
this estimate can be summed over an arbitrarily subdivided fan.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Norm contraction bounds on the actual linear face projection. -/
theorem face_projection_linear_bounds (f : Face) (x : Plane) :
    K.normal f 2 * ‖x‖ ≤ ‖(K.projectFaceEquiv f).linear x‖ ∧
      ‖(K.projectFaceEquiv f).linear x‖ ≤ ‖x‖ := by
  have chord := (K.projectFaceEquiv f).toAffineMap.linear_apply_vsub x 0
  change (K.projectFaceEquiv f).linear (x - 0) = K.projectFace f x - K.projectFace f 0 at chord
  rw [sub_zero] at chord
  rw [chord]
  simpa only [dist_eq_norm, sub_zero, projectFace_apply] using
    And.intro (K.face_projection_lower f x 0) (K.face_projection_upper f x 0)

/-- Actual linear face angles have a uniformly controlled sine ratio. -/
theorem face_projection_angle_sine_bounds {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) (f : Face) {x y : Plane} (xne : x ≠ 0) (yne : y ≠ 0) :
    c ^ 2 * Real.sin (InnerProductGeometry.angle x y) ≤
        Real.sin (InnerProductGeometry.angle ((K.projectFaceEquiv f).linear x)
          ((K.projectFaceEquiv f).linear y)) ∧
      c ^ 2 * Real.sin (InnerProductGeometry.angle ((K.projectFaceEquiv f).linear x)
          ((K.projectFaceEquiv f).linear y)) ≤ Real.sin (InnerProductGeometry.angle x y) :=
  angle_sine_bounds_of_norm_bounds (K.projectFaceEquiv f).linear positive
    (fun x => (mul_le_mul_of_nonneg_right (height f) (norm_nonneg x)).trans
      (K.face_projection_linear_bounds f x).1)
    (fun x => (K.face_projection_linear_bounds f x).2) xne yne

/-- A numerical threshold controls relative face-angle error before any mesh is specified. -/
theorem exists_uniform_height_relative_face_angle_error {ε : ℝ} (positive : 0 < ε) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), (∀ f, c ≤ K.normal f 2) →
          ∀ f (x y : Plane), x ≠ 0 → y ≠ 0 →
            |InnerProductGeometry.angle x y -
              InnerProductGeometry.angle ((K.projectFaceEquiv f).linear x)
                ((K.projectFaceEquiv f).linear y)| ≤
              ε * InnerProductGeometry.angle ((K.projectFaceEquiv f).linear x)
                ((K.projectFaceEquiv f).linear y) := by
  let r := min (ε / 8) (1 / 8)
  have rp : 0 < r := lt_min (by positivity) (by norm_num)
  have rs : r ≤ 1 / 8 := min_le_right _ _
  have rt : 4 * r ≤ ε := by
    have bound := min_le_left (ε / 8) (1 / 8)
    change r ≤ ε / 8 at bound
    linarith
  obtain ⟨d, dbounds, estimate⟩ := Cap.exists_projection_angle_height (sq_pos_of_pos rp)
  let c := max d (1 - r / 4)
  have cp : 0 < c := dbounds.1.trans_le (le_max_left _ _)
  have cs : c < 1 := max_lt dbounds.2 (by linarith)
  have square : 1 - r ≤ c ^ 2 := by
    have lower : 1 - r / 4 ≤ c := le_max_right _ _
    have base : 0 ≤ 1 - r / 4 := by linarith
    nlinarith [mul_self_le_mul_self base lower]
  refine ⟨c, ⟨cp, cs⟩, fun K height f x y xne yne => ?_⟩
  let A := (K.projectFaceEquiv f).linear
  have ax : (K.folding.place f).linear x ≠ 0 := by
    change (K.folding.place f).linearIsometry x ≠ 0
    simpa only [map_zero] using (K.folding.place f).linearIsometry.injective.ne xne
  have ay : (K.folding.place f).linear y ≠ 0 := by
    change (K.folding.place f).linearIsometry y ≠ 0
    simpa only [map_zero] using (K.folding.place f).linearIsometry.injective.ne yne
  have close := estimate (K.normal f) ((K.folding.place f).linear x)
    ((K.folding.place f).linear y) (K.normal_unit f)
    ((le_max_left d (1 - r / 4)).trans (height f)) ax ay
    (K.normal_tangent f x) (K.normal_tangent f y)
  have angle := (K.folding.place f).linearIsometry.angle_map x y
  change InnerProductGeometry.angle ((K.folding.place f).linear x)
    ((K.folding.place f).linear y) = InnerProductGeometry.angle x y at angle
  rw [angle, abs_sub_comm] at close
  change |InnerProductGeometry.angle x y - InnerProductGeometry.angle (A x) (A y)| < r ^ 2
    at close
  have sine := K.face_projection_angle_sine_bounds cp height f xne yne
  apply abs_angle_sub_le_relative_of_sine_bounds rp rs rt
    (InnerProductGeometry.angle_nonneg x y) (InnerProductGeometry.angle_nonneg _ _) close.le
  · exact (mul_le_mul_of_nonneg_right square
      (InnerProductGeometry.sin_angle_nonneg x y)).trans sine.1
  · exact (mul_le_mul_of_nonneg_right square
      (InnerProductGeometry.sin_angle_nonneg (A x) (A y))).trans sine.2

/-- Every positive relative angular tolerance admits one positive uniform tilt threshold. -/
theorem exists_uniform_tilt_relative_face_angle_error {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), K.TiltBound φ →
          ∀ f (x y : Plane), x ≠ 0 → y ≠ 0 →
            |InnerProductGeometry.angle x y -
              InnerProductGeometry.angle ((K.projectFaceEquiv f).linear x)
                ((K.projectFaceEquiv f).linear y)| ≤
              ε * InnerProductGeometry.angle ((K.projectFaceEquiv f).linear x)
                ((K.projectFaceEquiv f).linear y) := by
  obtain ⟨c, cbounds, estimate⟩ := exists_uniform_height_relative_face_angle_error.{u, v} positive
  obtain ⟨φ, pp, ps, height⟩ := Cap.exists_positive_tilt_of_height cbounds.2
  exact ⟨φ, ⟨pp, ps⟩, fun K tilt => estimate K (fun f => height.le.trans (tilt f))⟩

end Unfoldings.ConvexCap

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- A relative tolerance for each original corner, measured against its actual projected angle. -/
def RelativeCornerAngleError (ε : ℝ) : Prop :=
  ∀ f i, |(C.triangle f).cornerAngle i - (K.projectedTriangle f).cornerAngle i| ≤
    ε * (K.projectedTriangle f).cornerAngle i

/-- One positive numerical tilt threshold controls all original corners of every input mesh. -/
theorem exists_uniform_tilt_relative_corner_angle_error {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), K.TiltBound φ → K.RelativeCornerAngleError ε := by
  obtain ⟨φ, bounds, estimate⟩ := exists_uniform_tilt_relative_face_angle_error.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face' _ C' K tilt f i
  let T := C'.triangle f
  have first_ne : T.vertex (Triangle.next i) - T.vertex i ≠ 0 :=
    sub_ne_zero.mpr (T.edge_endpoints_ne i).symm
  have last_ne : T.vertex (Triangle.next (Triangle.next i)) - T.vertex i ≠ 0 := by
    apply sub_ne_zero.mpr
    apply T.vertex_injective.ne
    fin_cases i <;> decide
  have bound := estimate K tilt f _ _ first_ne last_ne
  have chord (j : Fin 3) : (K.projectFaceEquiv f).linear (T.vertex j - T.vertex i) =
      (K.projectedTriangle f).vertex j - (K.projectedTriangle f).vertex i :=
    (K.projectFaceEquiv f).toAffineMap.linear_apply_vsub (T.vertex j) (T.vertex i)
  rw [chord, chord] at bound
  exact bound

end Unfoldings.ConvexCap
