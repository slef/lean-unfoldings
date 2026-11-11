module

public import Unfoldings.Cap.CompletedProjectionCalibration
public import Unfoldings.Cap.UniformCurvature
public import Unfoldings.Cap.Tilt

/-! One numerical tilt threshold controls every completed-forest developed face direction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Choose the numerical tilt, curvature, and projection-error budgets before the whole cap. -/
theorem exists_uniform_completed_calibrated_budget {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → K.FaceDirectionAngleError (ε / 12) ∧
          2 * φ + 2 * C.totalInteriorAngularDefect Set.univ + 3 * (ε / 12) < ε := by
  obtain ⟨χ, χbounds, normal_lower, curvature_budget⟩ :=
    exists_positive_tilt_curvature_budget (show 0 < ε / 16 by positivity)
  obtain ⟨θ, θbounds, projection⟩ :=
    exists_uniform_tilt_faceDirectionAngleError (show 0 < ε / 12 by positivity)
  let φ := min χ (min θ (ε / 16))
  have φpositive : 0 < φ := lt_min χbounds.1 (lt_min θbounds.1 (by positivity))
  have φχ : φ ≤ χ := min_le_left _ _
  have φθ : φ ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have φε : φ ≤ ε / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have normal : (3 : ℝ) / 4 ≤ Real.cos φ := normal_lower.trans
    (Real.cos_le_cos_of_nonneg_of_le_pi φpositive.le
      (by linarith [χbounds.2, Real.pi_pos]) φχ)
  refine ⟨φ, ⟨φpositive, φχ.trans_lt χbounds.2⟩, normal, fun K tilt => ?_⟩
  have curvature_tilt := TiltBound.of_le K tilt φpositive.le
    (by linarith [χbounds.2, Real.pi_pos]) φχ
  have projection_tilt := TiltBound.of_le K tilt φpositive.le
    (by linarith [θbounds.2, Real.pi_pos]) φθ
  have curvature := (K.totalCurvature_le_normal_budget normal_lower curvature_tilt).trans_lt
    curvature_budget
  exact ⟨projection K projection_tilt, by linarith⟩

/-- A single threshold works for every finite cap and every completed radial cut forest whose
positive-curvature root paths have acute wedges. The actual extended construction proves these
wedges independently; arbitrary added flat branches require no angle assumption. -/
theorem exists_uniform_completed_direction_control {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ (q : Plane) (cuts : Set Plane) (R : K.RadialCutForest q cuts),
          R.CurvedPathWedges → ∀ D : FacewiseDevelopment C R.completedRetain,
            ∃ A : Plane ≃ₗᵢ[ℝ] ℂ, ∀ f (direction : Plane), direction ≠ 0 →
              InnerProductGeometry.angle (A (D.developedDirection K f direction))
                (Complex.orthonormalBasisOneI.repr.symm direction) < ε := by
  obtain ⟨φ, bounds, normal, budget⟩ := exists_uniform_completed_calibrated_budget positive
  refine ⟨φ, bounds, normal, fun K tilt q cuts R wedges D => ?_⟩
  obtain ⟨error, total_budget⟩ := budget K tilt
  let anchor := K.rimAnchor
  let reference : Plane := EuclideanSpace.single 0 1
  have nonzero : reference ≠ 0 := by
    intro zero
    have coordinate := congrArg (fun p : Plane => p 0) zero
    norm_num [reference, EuclideanSpace.single] at coordinate
  refine ⟨R.calibratedFrame D anchor reference, fun f direction different => ?_⟩
  exact (R.calibrated_face_direction_angle_le D wedges anchor reference nonzero f
    bounds.1.le bounds.2 tilt error direction different).trans_lt total_budget

end Unfoldings.ConvexCap
