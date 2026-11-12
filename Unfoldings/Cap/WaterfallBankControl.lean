module

public import Unfoldings.Cap.ExtendedRadialBankTraces
public import Unfoldings.Cap.WaterfallFaceError
public import Unfoldings.Cap.FacePositionMargins

/-! Retain one actual calibration's strip, bank, and all-face position control together. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1)
  (D : FacewiseDevelopment C N.retain)
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

/-- The actual approximation, injective strip maps, and radial matched bank traces share
one bank-order calibration. The uniform construction proves this property. -/
def WaterfallBankControl (ε cutoff : ℝ) : Prop :=
  let calibration := N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference
  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
    ‖(D.coordinatePlacement K calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
  ∀ i : FiveSector, ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
    ∀ S ∈ P.cells,
      let frame := (fiveSectorFrame t positive small i).place
      let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
      ∃ G : ℂ → ℂ, Continuous G ∧
        Set.EqOn (D.centeredMap K source calibration frame) G domain ∧
        Set.InjOn (D.centeredMap K source calibration frame) domain ∧
        S.RadialBankTraces G (D.centeredMap K source calibration frame 0) cutoff ∧
        N.MatchesParentBanks positive small i (N.completedDevelopment D) calibration G S cutoff ∧
        ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
          ‖(D.centeredMap K source calibration frame z -
            D.centeredMap K source calibration frame 0) - z‖ ≤ ε * (z.re + z.im)

theorem WaterfallBankControl.all_face_position_error {ε cutoff : ℝ}
    (control : N.WaterfallBankControl positive small D B ε cutoff) (nonnegative : 0 ≤ ε)
    (f : Face) {p : Plane} (member : p ∈ (K.projectedTriangle f).carrier)
    (region : p ∈ sectorSweepInterior positive small source cutoff) :
    let calibration := N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference
    ‖(calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K source)) -
      Complex.orthonormalBasisOneI.repr.symm (p - source)‖ ≤ 2 * ε * ‖p - source‖ := by
  classical
  let calibration := N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference
  have cells : ∀ i : FiveSector,
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        ∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
          ‖(D.centeredMap K source calibration (fiveSectorFrame t positive small i).place z -
            D.centeredMap K source calibration (fiveSectorFrame t positive small i).place 0) -
            z‖ ≤ ε * (z.re + z.im) := by
    intro i
    obtain ⟨P, strips⟩ := control.2 i
    refine ⟨P, fun S cell => ?_⟩
    obtain ⟨_, _, _, _, _, _, error⟩ := strips S cell
    exact error
  choose P error using cells
  exact D.projectedPlacement_source_error_of_waterfall K positive small source calibration P
    cutoff nonnegative error f member region

theorem WaterfallBankControl.all_face_distance_bounds {ε cutoff : ℝ}
    (control : N.WaterfallBankControl positive small D B ε cutoff) (nonnegative : 0 ≤ ε)
    (f : Face) {p : Plane} (member : p ∈ (K.projectedTriangle f).carrier)
    (region : p ∈ sectorSweepInterior positive small source cutoff) :
    (1 - 2 * ε) * ‖p - source‖ ≤ ‖D.projectedPlacement K f p - D.projectedMap K source‖ ∧
      ‖D.projectedPlacement K f p - D.projectedMap K source‖ ≤ (1 + 2 * ε) * ‖p - source‖ := by
  let calibration := N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference
  let w := calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K source)
  let z := Complex.orthonormalBasisOneI.repr.symm (p - source)
  have error := WaterfallBankControl.all_face_position_error N positive small D B control
    nonnegative f member region
  change ‖w - z‖ ≤ 2 * ε * ‖p - source‖ at error
  have wnorm : ‖w‖ = ‖D.projectedPlacement K f p - D.projectedMap K source‖ := by
    rw [show w = calibration (D.projectedPlacement K f p - D.projectedMap K source) from
      (calibration.map_sub _ _).symm, calibration.norm_map]
  have znorm : ‖z‖ = ‖p - source‖ := Complex.orthonormalBasisOneI.repr.symm.norm_map _
  have upper := norm_add_le (w - z) z
  have lower := norm_add_le (z - w) w
  rw [sub_add_cancel, wnorm, znorm] at upper
  rw [sub_add_cancel, norm_sub_rev, wnorm, znorm] at lower
  constructor <;> nlinarith

theorem centered_face_vector_eq (i : FiveSector) (f : Face) (p : Plane) :
    let calibration := N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference
    let frame := (fiveSectorFrame t positive small i).place
    D.centeredCoordinatePlacement K source calibration frame f (frame (p - source)) -
      D.centeredMap K source calibration frame 0 =
      B.sectorFrame i (D.projectedPlacement K f p - D.projectedMap K source) := by
  let frame := (fiveSectorFrame t positive small i).place
  let calibration := N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference
  let output := Complex.orthonormalBasisOneI.repr.trans frame
  have input : frame.symm (frame source + frame (p - source)) = p := by
    rw [← frame.map_add, frame.symm_apply_apply]
    abel
  change output (calibration (D.projectedPlacement K f
    (frame.symm (frame source + frame (p - source))))) -
    output (calibration (D.projectedMap K (source + frame.symm 0))) =
    output (calibration (D.projectedPlacement K f p - D.projectedMap K source))
  rw [input, map_zero, add_zero, calibration.map_sub, output.map_sub]

theorem WaterfallBankControl.all_face_quadrant_margin {ε cutoff μ : ℝ}
    (control : N.WaterfallBankControl positive small D B ε cutoff) (nonnegative : 0 ≤ ε)
    (margin : ∀ i : FiveSector,
      ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
        0 ≤ z.re + z.im → μ * ‖z‖ ≤ z.re ∧ μ * ‖z‖ ≤ z.im)
    (i : FiveSector) (f : Face) {p : Plane} (member : p ∈ (K.projectedTriangle f).carrier)
    (cone : p - source ∈ closedFiveSector t i)
    (region : p ∈ sectorSweepInterior positive small source cutoff) :
    (μ - 2 * ε) * ‖p - source‖ ≤
        (B.sectorFrame i (D.projectedPlacement K f p - D.projectedMap K source)).re ∧
      (μ - 2 * ε) * ‖p - source‖ ≤
        (B.sectorFrame i (D.projectedPlacement K f p - D.projectedMap K source)).im := by
  let frame := (fiveSectorFrame t positive small i).place
  let calibration := N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference
  have forward := (fiveSectorFrame t positive small i).quadrant_nonneg cone
  have coordinates := margin i (frame (p - source))
    ((fiveSectorFrame t positive small i).enclosingStrip_mem cone)
    (add_nonneg forward.1 forward.2)
  rw [frame.norm_map] at coordinates
  have error := WaterfallBankControl.all_face_position_error N positive small D B
    control nonnegative f member region
  have bounds := D.centered_face_quadrant_margin K source calibration frame f p
    coordinates.1 coordinates.2 error
  rwa [N.centered_face_vector_eq positive small D B i f p] at bounds

theorem WaterfallBankControl.face_jump_segment_quadrant_margin {ε cutoff μ : ℝ}
    (control : N.WaterfallBankControl positive small D B ε cutoff) (nonnegative : 0 ≤ ε)
    (margin : ∀ i : FiveSector,
      ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
        0 ≤ z.re + z.im → μ * ‖z‖ ≤ z.re ∧ μ * ‖z‖ ≤ z.im)
    (i : FiveSector) (f g : Face) {p : Plane}
    (first_face : p ∈ (K.projectedTriangle f).carrier)
    (last_face : p ∈ (K.projectedTriangle g).carrier)
    (cone : p - source ∈ closedFiveSector t i)
    (region : p ∈ sectorSweepInterior positive small source cutoff)
    {s : ℝ} (parameter : s ∈ Set.Icc 0 1) :
    (μ - 2 * ε) * ‖p - source‖ ≤ (B.sectorFrame i
      (AffineMap.lineMap (D.projectedPlacement K f p) (D.projectedPlacement K g p) s -
        D.projectedMap K source)).re ∧
    (μ - 2 * ε) * ‖p - source‖ ≤ (B.sectorFrame i
      (AffineMap.lineMap (D.projectedPlacement K f p) (D.projectedPlacement K g p) s -
        D.projectedMap K source)).im := by
  let r := (μ - 2 * ε) * ‖p - source‖
  let x := D.projectedPlacement K f p - D.projectedMap K source
  let y := D.projectedPlacement K g p - D.projectedMap K source
  have first := WaterfallBankControl.all_face_quadrant_margin N positive small D B
    control nonnegative margin i f first_face cone region
  have last := WaterfallBankControl.all_face_quadrant_margin N positive small D B
    control nonnegative margin i g last_face cone region
  change r ≤ (B.sectorFrame i x).re ∧ r ≤ (B.sectorFrame i x).im at first
  change r ≤ (B.sectorFrame i y).re ∧ r ≤ (B.sectorFrame i y).im at last
  have displacement :
      AffineMap.lineMap (D.projectedPlacement K f p) (D.projectedPlacement K g p) s -
        D.projectedMap K source = (1 - s) • x + s • y := by
    rw [AffineMap.lineMap_apply_module]
    dsimp only [x, y]
    module
  rw [displacement, map_add, map_smul, map_smul]
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  change r ≤ (1 - s) * (B.sectorFrame i x).re + s * (B.sectorFrame i y).re ∧
    r ≤ (1 - s) * (B.sectorFrame i x).im + s * (B.sectorFrame i y).im
  have first_re := mul_le_mul_of_nonneg_left first.1 (sub_nonneg.mpr parameter.2)
  have first_im := mul_le_mul_of_nonneg_left first.2 (sub_nonneg.mpr parameter.2)
  have last_re := mul_le_mul_of_nonneg_left last.1 parameter.1
  have last_im := mul_le_mul_of_nonneg_left last.2 parameter.1
  constructor <;> nlinarith

end Unfoldings.ConvexCap.RadialCutForest
