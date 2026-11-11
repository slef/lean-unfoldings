module

public import Unfoldings.Cap.ProjectedLinearError
public import Unfoldings.Cap.CompletedSectorQuadrants

/-! One uniform tilt gives bank quadrants and arbitrarily small linear error in the same frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

/-- Bank-order data and quantitative chart control use the very same actual calibration.
The margin and requested error precede the cap and both meshes. -/
theorem exists_uniform_completed_frame_linear_error (t : ℝ) (positive : 0 < t)
    (small : t < 1) {ε : ℝ} (εpositive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ (q : Plane) (cuts : Set Plane) (R : K.RadialCutForest q cuts),
          R.CurvedPathWedges → C.totalInteriorAngularDefect Set.univ < Real.pi ∧
            ∀ D : FacewiseDevelopment C R.completedRetain,
              ∃ B : R.FiveSectorFrameData positive small D,
                ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f (z : ℂ),
                  ‖(D.coordinatePlacement K (R.calibratedFrame D B.anchor B.reference)
                    frame f).linear z - z‖ ≤ ε * ‖z‖ := by
  obtain ⟨δ, δpositive, linear_control⟩ :=
    FacewiseDevelopment.exists_coordinatePlacement_linear_error_threshold.{u, v} εpositive
  let α := min δ (min (fiveSectorMargin t positive small) (Real.pi / 4))
  have αpositive : 0 < α := lt_min δpositive
    (lt_min (fiveSectorMargin_pos t positive small) (by positivity))
  have αδ : α ≤ δ := min_le_left _ _
  have αsector : α ≤ fiveSectorMargin t positive small :=
    (min_le_right _ _).trans (min_le_left _ _)
  have απ : α ≤ Real.pi / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨χ, χbounds, normal, uniform⟩ := exists_uniform_completed_calibrated_budget αpositive
  have factor : 0 < 1 + δ := by linarith
  have less_one : (1 + δ)⁻¹ < (1 : ℝ) := (inv_lt_one₀ factor).mpr (by linarith)
  have near : ∀ᶠ θ in 𝓝 (0 : ℝ), (1 + δ)⁻¹ < Real.cos θ :=
    Real.continuous_cos.continuousAt.eventually (lt_mem_nhds (by
      simpa only [Real.cos_zero] using less_one))
  obtain ⟨r, rpositive, near_bound⟩ := Metric.eventually_nhds_iff.mp near
  let φ := min χ (min (r / 2) (Real.pi / 4))
  have φpositive : 0 < φ := lt_min χbounds.1 (lt_min (by positivity) (by positivity))
  have φχ : φ ≤ χ := min_le_left _ _
  have φr : φ < r := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have φcos := near_bound (show dist φ 0 < r by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos φpositive] using φr)
  have normal_lower : (3 : ℝ) / 4 ≤ Real.cos φ := normal.trans
    (Real.cos_le_cos_of_nonneg_of_le_pi φpositive.le (by linarith [χbounds.2, Real.pi_pos]) φχ)
  refine ⟨φ, ⟨φpositive, φχ.trans_lt χbounds.2⟩, normal_lower, ?_⟩
  intro Face _ C K tilt q cuts R wedges
  have old_tilt := TiltBound.of_le K tilt φpositive.le (by linarith [χbounds.2, Real.pi_pos]) φχ
  obtain ⟨error, total_budget⟩ := uniform K old_tilt
  have curvature : C.totalInteriorAngularDefect Set.univ < Real.pi := by
    linarith [χbounds.1, Real.pi_pos]
  refine ⟨curvature, fun D => ?_⟩
  let anchor := K.rimAnchor
  let reference : Plane := EuclideanSpace.single 0 1
  have reference_ne : reference ≠ 0 := by
    intro zero
    have coordinate := congrArg (fun p : Plane => p 0) zero
    norm_num [reference, EuclideanSpace.single] at coordinate
  have close (f : Face) (direction : Plane) (nonzero : direction ≠ 0) :
      InnerProductGeometry.angle
        (R.calibratedFrame D anchor reference (D.developedDirection K f direction))
        (Complex.orthonormalBasisOneI.repr.symm direction) < α :=
    (R.calibrated_face_direction_angle_le D wedges anchor reference reference_ne f χbounds.1.le
      χbounds.2 old_tilt error direction nonzero).trans_lt total_budget
  let B : R.FiveSectorFrameData positive small D :=
    ⟨anchor, reference, reference_ne, fun i f direction inside nonzero =>
      fiveSector_quadrant_of_angle_close t positive small i inside nonzero
        ((close f direction nonzero).trans_le αsector)⟩
  refine ⟨B, ?_⟩
  exact linear_control D K (R.calibratedFrame D anchor reference)
    (fun f => φcos.le.trans (tilt f))
    (fun f direction nonzero => (close f direction nonzero).trans_le αδ)

end Unfoldings.ConvexCap
