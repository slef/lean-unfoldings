module

public import Unfoldings.Cap.CenteredFrameError
public import Unfoldings.Cap.ProjectedInteriorCoherence
public import Unfoldings.Cap.SectorWaterfallDensity

/-! Source-position estimates on strict strips extend to every actual face copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- The conclusion retains every containing-face value at a bank or branch point. -/
theorem projectedPlacement_source_error_of_waterfall
    {t : ℝ} (positive : 0 < t) (small : t < 1) (q : Plane)
    (calibration : Plane ≃ₗᵢ[ℝ] ℂ)
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (cutoff : ℝ) {ε : ℝ} (nonnegative : 0 ≤ ε)
    (control : ∀ i S, S ∈ (P i).cells → ∀ z ∈ S.strictCarrier,
      z.re + z.im ∈ Set.Icc 0 cutoff →
        ‖(D.centeredMap K q calibration (fiveSectorFrame t positive small i).place z -
          D.centeredMap K q calibration (fiveSectorFrame t positive small i).place 0) - z‖ ≤
            ε * (z.re + z.im))
    (f : Face) {p : Plane} (member : p ∈ (K.projectedTriangle f).carrier)
    (inside : p ∈ sectorSweepInterior positive small q cutoff) :
    ‖(calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K q)) -
        Complex.orthonormalBasisOneI.repr.symm (p - q)‖ ≤ 2 * ε * ‖p - q‖ := by
  let E := {p : Plane |
    ‖(calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K q)) -
      Complex.orthonormalBasisOneI.repr.symm (p - q)‖ ≤ 2 * ε * ‖p - q‖}
  have closed : IsClosed E := by
    apply isClosed_le
    · exact (((calibration.continuous.comp
        (D.projectedPlacement K f).continuous_of_finiteDimensional).sub continuous_const).sub
        (Complex.orthonormalBasisOneI.repr.symm.continuous.comp
          (continuous_id.sub continuous_const))).norm
    · exact continuous_const.mul (continuous_id.sub continuous_const).norm
  have near := triangle_sectorSweep_mem_closure_strict_cells positive small q P cutoff
    (K.projectedTriangle f) member inside
  apply closure_minimal (t := E) ?_ closed near
  intro x hx
  obtain ⟨i, S, cell, strict, slab⟩ := hx.2
  let frame := (fiveSectorFrame t positive small i).place
  have error := control i S cell (frame (x - q)) strict slab
  rw [D.centeredMap_source_error_eq K q calibration frame x,
    D.projectedMap_eq_on_face_interior K hx.1.2] at error
  have height : (frame (x - q)).re + (frame (x - q)).im ≤ 2 * ‖x - q‖ := by
    have first := (le_abs_self (frame (x - q)).re).trans
      (Complex.abs_re_le_norm (frame (x - q)))
    have last := (le_abs_self (frame (x - q)).im).trans
      (Complex.abs_im_le_norm (frame (x - q)))
    rw [frame.norm_map] at first last
    linarith
  exact error.trans (by nlinarith [mul_le_mul_of_nonneg_left height nonnegative])

end Unfoldings.FacewiseDevelopment
