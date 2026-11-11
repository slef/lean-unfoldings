module

public import Unfoldings.Cap.DevelopmentOrientation
public import Unfoldings.Geometry.AngleAxisMargins

/-! Actual affine face maps in arbitrary strip coordinates, with derived positive axis margins. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- Use one calibrated output frame and the same orthogonal change of coordinates on both
the horizontal domain and the calibrated range. The actual face placement is unchanged. -/
def coordinatePlacement (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) (f : Face) : ℂ ≃ᵃ[ℝ] ℂ :=
  let output := calibration.trans (Complex.orthonormalBasisOneI.repr.trans frame)
  (frame.symm.toAffineIsometryEquiv.toAffineEquiv.trans (D.projectedPlacement K f)).trans
    output.toAffineIsometryEquiv.toAffineEquiv

theorem coordinatePlacement_linear (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (f : Face) (z : ℂ) :
    (D.coordinatePlacement K calibration frame f).linear z =
      (Complex.orthonormalBasisOneI.repr.trans frame)
        (calibration (D.developedDirection K f (frame.symm z))) := rfl

theorem coordinatePlacement_continuous (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) (f : Face) :
    Continuous (D.coordinatePlacement K calibration frame f) :=
  (D.coordinatePlacement K calibration frame f).continuous_of_finiteDimensional

/-- Angular calibration relative to horizontal projection is independent of strip coordinates. -/
theorem coordinatePlacement_angle {δ : ℝ} (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (close : ∀ f (direction : Plane), direction ≠ 0 →
      InnerProductGeometry.angle (calibration (D.developedDirection K f direction))
        (Complex.orthonormalBasisOneI.repr.symm direction) < δ)
    (f : Face) (z : ℂ) (nonzero : z ≠ 0) :
    InnerProductGeometry.angle z ((D.coordinatePlacement K calibration frame f).linear z) < δ :=
      by
  have genuine : frame.symm z ≠ 0 := by
    simpa only [map_zero] using frame.symm.injective.ne nonzero
  have original := close f (frame.symm z) genuine
  let L := Complex.orthonormalBasisOneI.repr.trans frame
  have transported : InnerProductGeometry.angle
      (L (calibration (D.developedDirection K f (frame.symm z))))
      (L (Complex.orthonormalBasisOneI.repr.symm (frame.symm z))) < δ :=
    (L.toLinearIsometry.angle_map _ _).trans_lt original
  have identity : L (Complex.orthonormalBasisOneI.repr.symm (frame.symm z)) = z := by
    change frame (Complex.orthonormalBasisOneI.repr
      (Complex.orthonormalBasisOneI.repr.symm (frame.symm z))) = z
    rw [LinearIsometryEquiv.apply_symm_apply, frame.apply_symm_apply]
  rw [identity, InnerProductGeometry.angle_comm] at transported
  rw [D.coordinatePlacement_linear]
  exact transported

/-- One numerical tolerance gives positive axis margins for every actual face in every
orthogonal strip frame. The cap and triangulation are quantified after that tolerance. -/
theorem exists_coordinatePlacement_axis_threshold :
    ∃ δ > 0, ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
      {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)
      (calibration : Plane ≃ₗᵢ[ℝ] ℂ),
      (∀ f (direction : Plane), direction ≠ 0 →
        InnerProductGeometry.angle (calibration (D.developedDirection K f direction))
          (Complex.orthonormalBasisOneI.repr.symm direction) < δ) →
      ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f j,
        0 < affineAxisMargins (D.coordinatePlacement K calibration frame f).toAffineMap j := by
  obtain ⟨δ, positive, tests⟩ := exists_affine_axis_angle_threshold
  refine ⟨δ, positive, fun D K calibration close frame f => ?_⟩
  exact tests _ (D.coordinatePlacement_angle K calibration frame close f 1 one_ne_zero)
    (D.coordinatePlacement_angle K calibration frame close f Complex.I Complex.I_ne_zero)

end Unfoldings.FacewiseDevelopment
