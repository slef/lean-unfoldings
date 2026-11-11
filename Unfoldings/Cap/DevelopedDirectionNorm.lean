module

public import Unfoldings.Cap.ProjectedStripMaps

/-! Exact developed-vector lengths and two-sided normal-dependent projection estimates. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem developedDirection_norm_spatial (f : Face) (direction : Plane) :
    ‖D.developedDirection K f direction‖ = ‖K.spatialDirection f direction‖ := by
  calc
    _ = ‖K.pullbackDirection f direction‖ :=
      (D.place f).toAffineIsometry.linearIsometry.norm_map _
    _ = _ := ((K.folding.place f).linearIsometry.norm_map _).symm

theorem developedDirection_norm_bounds (f : Face) (direction : Plane) :
    ‖direction‖ ≤ ‖D.developedDirection K f direction‖ ∧
      K.normal f 2 * ‖D.developedDirection K f direction‖ ≤ ‖direction‖ := by
  rw [D.developedDirection_norm_spatial]
  constructor
  · have bound := Cap.horizontal_norm_le (K.spatialDirection f direction)
    rwa [K.horizontal_spatialDirection] at bound
  · have bound := Cap.normal_tangent_projection_lower (K.normal f) (K.spatialDirection f direction)
      (K.normal_unit f) (K.normal_upward f).le (K.spatialDirection_tangent f direction)
    rwa [K.horizontal_spatialDirection] at bound

theorem coordinatePlacement_norm_bounds (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (f : Face) (z : ℂ) :
    ‖z‖ ≤ ‖(D.coordinatePlacement K calibration frame f).linear z‖ ∧
      K.normal f 2 * ‖(D.coordinatePlacement K calibration frame f).linear z‖ ≤ ‖z‖ := by
  rw [D.coordinatePlacement_linear, (Complex.orthonormalBasisOneI.repr.trans frame).norm_map,
    calibration.norm_map]
  simpa only [frame.symm.norm_map] using D.developedDirection_norm_bounds K f (frame.symm z)

end Unfoldings.FacewiseDevelopment
