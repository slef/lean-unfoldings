module

public import Unfoldings.Cap.CenteredFrameError
public import Unfoldings.Cap.SectorPositionMargins

/-! Quantitative quadrant margins for every actual containing-face placement. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem centeredCoordinatePlacement_source_error_eq (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) (f : Face) (p : Plane) :
    ‖(D.centeredCoordinatePlacement K q calibration frame f (frame (p - q)) -
        D.centeredMap K q calibration frame 0) - frame (p - q)‖ =
      ‖(calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K q)) -
        Complex.orthonormalBasisOneI.repr.symm (p - q)‖ := by
  let L := Complex.orthonormalBasisOneI.repr.trans frame
  have input : frame.symm (frame q + frame (p - q)) = p := by
    rw [← frame.map_add, frame.symm_apply_apply]
    abel
  change ‖(L (calibration (D.projectedPlacement K f
      (frame.symm (frame q + frame (p - q))))) -
      L (calibration (D.projectedMap K (q + frame.symm 0)))) - frame (p - q)‖ = _
  rw [input, map_zero, add_zero]
  have vector : frame (p - q) = L (Complex.orthonormalBasisOneI.repr.symm (p - q)) := by
    change frame (p - q) = frame
      (Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm (p - q)))
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [vector, ← L.map_sub, ← L.map_sub, L.norm_map]

theorem centered_face_quadrant_margin (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (f : Face) (p : Plane) {μ ε : ℝ}
    (horizontal : μ * ‖p - q‖ ≤ (frame (p - q)).re)
    (vertical : μ * ‖p - q‖ ≤ (frame (p - q)).im)
    (error : ‖(calibration (D.projectedPlacement K f p) -
        calibration (D.projectedMap K q)) -
      Complex.orthonormalBasisOneI.repr.symm (p - q)‖ ≤ ε * ‖p - q‖) :
    (μ - ε) * ‖p - q‖ ≤
      (D.centeredCoordinatePlacement K q calibration frame f (frame (p - q)) -
        D.centeredMap K q calibration frame 0).re ∧
    (μ - ε) * ‖p - q‖ ≤
      (D.centeredCoordinatePlacement K q calibration frame f (frame (p - q)) -
        D.centeredMap K q calibration frame 0).im := by
  rw [← D.centeredCoordinatePlacement_source_error_eq K q calibration frame f p] at error
  have first := (abs_le.mp ((Complex.abs_re_le_norm _).trans error)).1
  have last := (abs_le.mp ((Complex.abs_im_le_norm _).trans error)).1
  simp only [Complex.sub_re] at first
  simp only [Complex.sub_im] at last
  constructor <;> simp only [Complex.sub_re, Complex.sub_im] <;> nlinarith

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem exists_enclosingStrip_norm_coordinate_margin :
    ∃ μ > 0, ∀ z ∈ B.enclosingStrip.carrier, 0 ≤ z.re + z.im →
      μ * ‖z‖ ≤ z.re ∧ μ * ‖z‖ ≤ z.im := by
  obtain ⟨μ, positive, bound⟩ := B.exists_enclosingStrip_coordinate_margin
  refine ⟨μ, positive, fun z member forward => ?_⟩
  have coordinates := bound z member forward
  have re : 0 ≤ z.re := (mul_nonneg positive.le forward).trans coordinates.1
  have im : 0 ≤ z.im := (mul_nonneg positive.le forward).trans coordinates.2
  have norm := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg re, abs_of_nonneg im] at norm
  have estimate := mul_le_mul_of_nonneg_left norm positive.le
  exact ⟨estimate.trans coordinates.1, estimate.trans coordinates.2⟩

end Unfoldings.AcuteWedgeFrame
