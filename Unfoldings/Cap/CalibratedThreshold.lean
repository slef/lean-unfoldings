module

public import Unfoldings.Cap.ProjectionCalibration
public import Unfoldings.Cap.SectionHeadingThreshold

/-!
# Uniform calibrated direction control before the entire cap mesh

One positive threshold constructs the original-edge sector forest and makes
every actual developed face direction uniformly close to its original projected
direction in one common frame. This is direction control; global nonoverlap
requires the subsequent bank and strip separation argument.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Forest, total heading budget, and local projection error use one numerical threshold. -/
theorem exists_uniform_calibrated_budget {α ε : ℝ} (margin : 0 < α) (budget : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), AcuteMargin (C := C) α → K.TiltBound φ →
          K.FaceDirectionAngleError (ε / 12) ∧
          2 * φ + 2 * C.totalInteriorAngularDefect Set.univ + 3 * (ε / 12) < ε ∧
            ((∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) →
              ∃ origin : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ origin ∧
                Nonempty (K.SectorForest t origin)) := by
  obtain ⟨ψ, ψbounds, t, tbounds, forest⟩ :=
    exists_uniform_sectorForest_section_heading_lt margin (show 0 < ε / 4 by positivity)
  obtain ⟨χ, χbounds, projection⟩ :=
    exists_uniform_tilt_faceDirectionAngleError (show 0 < ε / 12 by positivity)
  let φ := min ψ χ
  have positive : 0 < φ := lt_min ψbounds.1 χbounds.1
  refine ⟨φ, ⟨positive, (min_le_left _ _).trans_lt ψbounds.2⟩, t, tbounds,
    fun K acute tilt => ?_⟩
  have forest_tilt := TiltBound.of_le K tilt positive.le
    (by linarith [ψbounds.2, Real.pi_pos]) (min_le_left _ _)
  have projection_tilt := TiltBound.of_le K tilt positive.le
    (by linarith [χbounds.2, Real.pi_pos]) (min_le_right _ _)
  obtain ⟨heading_budget, constructed⟩ := forest K acute forest_tilt
  have small : φ ≤ ψ := min_le_left _ _
  exact ⟨projection K projection_tilt, by linarith, constructed⟩

/-- In one common frame every actual original-face direction is uniformly close to projection. -/
theorem exists_uniform_sectorForest_direction_control {α ε : ℝ}
    (margin : 0 < α) (budget : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), AcuteMargin (C := C) α → K.TiltBound φ →
          (∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) →
          ∃ origin : C.Vertex Set.univ, ∃ M : K.SectorForest t origin,
            ∀ D : FacewiseDevelopment C M.retain, ∃ R : Plane ≃ₗᵢ[ℝ] ℂ,
              ∀ f (direction : Plane), direction ≠ 0 →
                InnerProductGeometry.angle (R (D.developedDirection K f direction))
                  (Complex.orthonormalBasisOneI.repr.symm direction) < ε := by
  obtain ⟨φ, φbounds, t, tbounds, uniform⟩ := exists_uniform_calibrated_budget margin budget
  refine ⟨φ, φbounds, t, tbounds, fun K acute tilt internal => ?_⟩
  obtain ⟨error, total_budget, forest⟩ := uniform K acute tilt
  obtain ⟨origin, _internal, ⟨M⟩⟩ := forest internal
  refine ⟨origin, M, fun D => ?_⟩
  let A := K.rimAnchor
  let reference : Plane := EuclideanSpace.single 0 1
  have reference_ne : reference ≠ 0 := by
    intro zero
    have coordinate := congrArg (fun p : Plane => p 0) zero
    norm_num [reference, EuclideanSpace.single] at coordinate
  refine ⟨M.calibratedFrame D A reference, fun f direction nonzero => ?_⟩
  exact (M.calibrated_face_direction_angle_le D tbounds.1 (by linarith [tbounds.2])
    A reference reference_ne f φbounds.1.le φbounds.2 tilt error direction nonzero).trans_lt
      total_budget

end Unfoldings.ConvexCap
