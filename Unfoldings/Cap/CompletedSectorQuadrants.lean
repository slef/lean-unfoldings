module

public import Unfoldings.Cap.CompletedCalibratedThreshold
public import Unfoldings.Geometry.FiveSectorFrames

/-! One actual calibrated frame and five robust quadrants for the whole completed roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts) {t : ℝ}

/-- Output data keeps the calibration provenance needed for signed bank rotations. -/
structure FiveSectorFrameData (positive : 0 < t) (small : t < 1)
    (D : FacewiseDevelopment C R.completedRetain) where
  anchor : K.RimAnchor
  reference : Plane
  reference_ne : reference ≠ 0
  quadrants : ∀ (i : FiveSector) (f : Face) (direction : Plane),
    direction ∈ closedFiveSector t i → direction ≠ 0 →
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (fiveSectorFrame t positive small i).place)
          (R.calibratedFrame D anchor reference (D.developedDirection K f direction))).re ∧
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (fiveSectorFrame t positive small i).place)
          (R.calibratedFrame D anchor reference (D.developedDirection K f direction))).im

end Unfoldings.ConvexCap.RadialCutForest

namespace Unfoldings.ConvexCap

universe u v

/-- The sector parameter and one positive tolerance are fixed before the complete cap mesh.
The two forward sectors include arbitrary auxiliary vertices in the old empty gap. -/
theorem exists_uniform_completed_fiveSectorFrameData (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ (q : Plane) (cuts : Set Plane) (R : K.RadialCutForest q cuts),
          R.CurvedPathWedges → C.totalInteriorAngularDefect Set.univ < Real.pi ∧
            ∀ D : FacewiseDevelopment C R.completedRetain,
              Nonempty (R.FiveSectorFrameData positive small D) := by
  let ε := min (fiveSectorMargin t positive small) (Real.pi / 4)
  have εpositive : 0 < ε := lt_min (fiveSectorMargin_pos t positive small) (by positivity)
  obtain ⟨φ, bounds, normal, uniform⟩ := exists_uniform_completed_calibrated_budget εpositive
  refine ⟨φ, bounds, normal, ?_⟩
  intro Face _ C K tilt q cuts R wedges
  obtain ⟨error, total_budget⟩ := uniform K tilt
  have curvature : C.totalInteriorAngularDefect Set.univ < Real.pi := by
    have εsmall : ε ≤ Real.pi / 4 := min_le_right _ _
    linarith [bounds.1, Real.pi_pos]
  refine ⟨curvature, fun D => ?_⟩
  let anchor := K.rimAnchor
  let reference : Plane := EuclideanSpace.single 0 1
  have reference_ne : reference ≠ 0 := by
    intro zero
    have coordinate := congrArg (fun p : Plane => p 0) zero
    norm_num [reference, EuclideanSpace.single] at coordinate
  refine ⟨⟨anchor, reference, reference_ne, fun i f direction inside nonzero => ?_⟩⟩
  apply fiveSector_quadrant_of_angle_close t positive small i inside nonzero
  have bound := R.calibrated_face_direction_angle_le D wedges anchor reference reference_ne f
    bounds.1.le bounds.2 tilt error direction nonzero
  exact (bound.trans_lt total_budget).trans_le (min_le_left _ _)

end Unfoldings.ConvexCap
