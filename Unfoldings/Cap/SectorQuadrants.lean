module

public import Unfoldings.Cap.CalibratedThreshold
public import Unfoldings.Geometry.ThreeSectorFrames

/-!
# Actual strict sector quadrants under one mesh-independent threshold

Fix the numerical sector parameter before choosing its common positive margin.
Then choose a smaller tilt threshold. Every original direction in a closed
sector develops strictly inside that sector's one fixed open quadrant. The same
global developed frame works for all three sectors and every original face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- One global developed frame and three numerical sector frames place all actual directions. -/
def SectorQuadrantControl (positive : 0 < t) (small : t < 1)
    (D : FacewiseDevelopment C M.retain) : Prop :=
  ∃ R : Plane ≃ₗᵢ[ℝ] ℂ, ∀ (i : Fin 3) (f : Face) (direction : Plane),
    direction ∈ closedThreeSector t i → direction ≠ 0 →
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (threeSectorFrame t positive small i).place) (R (D.developedDirection K f direction))).re ∧
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (threeSectorFrame t positive small i).place) (R (D.developedDirection K f direction))).im

/-- Constructed calibration data retains the actual rotation of the common boundary frame. -/
structure SectorFrameData (positive : 0 < t) (small : t < 1)
    (D : FacewiseDevelopment C M.retain) where
  anchor : K.RimAnchor
  reference : Plane
  reference_ne : reference ≠ 0
  quadrants : ∀ (i : Fin 3) (f : Face) (direction : Plane),
    direction ∈ closedThreeSector t i → direction ≠ 0 →
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (threeSectorFrame t positive small i).place)
          (M.calibratedFrame D anchor reference (D.developedDirection K f direction))).re ∧
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (threeSectorFrame t positive small i).place)
          (M.calibratedFrame D anchor reference (D.developedDirection K f direction))).im

/-- Every selected actual parent edge has a genuine horizontal direction. -/
theorem parent_direction_ne_zero (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots) :
    K.projectedVertex (M.parents.parent e) - K.projectedVertex e ≠ 0 := by
  intro zero
  have strict := M.direction e nonroot
  rw [zero] at strict
  change 0 < threeSectorCoordinates t (K.sourceSectorLabel t origin e) 0 0 ∧ _ at strict
  simp only [map_zero, PiLp.zero_apply, lt_self_iff_false, false_and] at strict

end Unfoldings.ConvexCap.SectorForest

namespace Unfoldings.ConvexCap

universe u v

/-- One threshold depending only on the acute margin constructs actual strict quadrant control. -/
theorem exists_uniform_sectorForest_sectorFrameData {α : ℝ} (margin : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), AcuteMargin (C := C) α → K.TiltBound φ →
          (∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) →
          ∃ origin : C.Vertex Set.univ, ∃ M : K.SectorForest t origin,
            C.totalInteriorAngularDefect Set.univ < Real.pi ∧
              ∀ D : FacewiseDevelopment C M.retain,
                ∃ positive : 0 < t, ∃ small : t < 1,
                  Nonempty (M.SectorFrameData positive small D) := by
  obtain ⟨ψ, ψbounds, t, tbounds, forest⟩ := exists_uniform_tilt_sectorForest margin
  have tsmall : t < 1 := by linarith [tbounds.2]
  let ε := min (threeSectorMargin t tbounds.1 tsmall) (Real.pi / 4)
  have εpositive : 0 < ε := lt_min (threeSectorMargin_pos t tbounds.1 tsmall) (by positivity)
  obtain ⟨χ, χbounds, _other_t, _other_bounds, uniform⟩ :=
    exists_uniform_calibrated_budget margin εpositive
  let φ := min ψ χ
  have positive : 0 < φ := lt_min ψbounds.1 χbounds.1
  refine ⟨φ, ⟨positive, (min_le_left _ _).trans_lt ψbounds.2⟩, t, tbounds, ?_⟩
  intro Face inst C K acute tilt internal
  have forest_tilt := TiltBound.of_le K tilt positive.le
    (by linarith [ψbounds.2, Real.pi_pos]) (min_le_left _ _)
  have budget_tilt := TiltBound.of_le K tilt positive.le
    (by linarith [χbounds.2, Real.pi_pos]) (min_le_right _ _)
  obtain ⟨error, total_budget, _unused_forest⟩ := uniform K acute budget_tilt
  have angle_budget : 2 * φ + 2 * C.totalInteriorAngularDefect Set.univ + 3 * (ε / 12) < ε := by
    have smaller : φ ≤ χ := min_le_right _ _
    linarith
  obtain ⟨origin, _internal, ⟨M⟩⟩ := forest K acute forest_tilt internal
  have curvature_small : C.totalInteriorAngularDefect Set.univ < Real.pi := by
    have upper : ε ≤ Real.pi / 4 := min_le_right _ _
    linarith [Real.pi_pos]
  refine ⟨origin, M, curvature_small, fun D => ?_⟩
  let A := K.rimAnchor
  let reference : Plane := EuclideanSpace.single 0 1
  have reference_ne : reference ≠ 0 := by
    intro zero
    have coordinate := congrArg (fun p : Plane => p 0) zero
    norm_num [reference, EuclideanSpace.single] at coordinate
  refine ⟨tbounds.1, tsmall, ⟨⟨A, reference, reference_ne,
    fun i f direction inside nonzero => ?_⟩⟩⟩
  apply threeSector_quadrant_of_angle_close t tbounds.1 tsmall i inside nonzero
  have bound := M.calibrated_face_direction_angle_le D tbounds.1 tsmall A reference reference_ne f
    positive.le ((min_le_left _ _).trans_lt ψbounds.2) tilt error direction nonzero
  exact (bound.trans_lt angle_budget).trans_le (min_le_left _ _)

/-- One threshold depending only on the acute margin constructs actual strict quadrant control. -/
theorem exists_uniform_sectorForest_quadrants {α : ℝ} (margin : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), AcuteMargin (C := C) α → K.TiltBound φ →
          (∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) →
          ∃ origin : C.Vertex Set.univ, ∃ M : K.SectorForest t origin,
            C.totalInteriorAngularDefect Set.univ < Real.pi ∧
              ∀ D : FacewiseDevelopment C M.retain,
                ∃ positive : 0 < t, ∃ small : t < 1,
                  M.SectorQuadrantControl positive small D := by
  obtain ⟨φ, φbounds, t, tbounds, uniform⟩ :=
    exists_uniform_sectorForest_sectorFrameData margin
  refine ⟨φ, φbounds, t, tbounds, fun K acute tilt internal => ?_⟩
  obtain ⟨origin, M, curvature, frames⟩ := uniform K acute tilt internal
  refine ⟨origin, M, curvature, fun D => ?_⟩
  obtain ⟨positive, small, ⟨B⟩⟩ := frames D
  exact ⟨positive, small, M.calibratedFrame D B.anchor B.reference, B.quadrants⟩

end Unfoldings.ConvexCap
