module

public import Unfoldings.Cap.CenteredDevelopedMap

/-! Centered source-position error is independent of the chosen input frame. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem centeredMap_source_error_eq (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (p : Plane) :
    ‖(D.centeredMap K q calibration frame (frame (p - q)) -
        D.centeredMap K q calibration frame 0) - frame (p - q)‖ =
      ‖(calibration (D.projectedMap K p) - calibration (D.projectedMap K q)) -
        Complex.orthonormalBasisOneI.repr.symm (p - q)‖ := by
  have source : q + frame.symm (frame (p - q)) = p := by
    rw [frame.symm_apply_apply]
    abel
  rw [centeredMap, centeredMap, source, map_zero, add_zero]
  let L := Complex.orthonormalBasisOneI.repr.trans frame
  have vector : frame (p - q) = L (Complex.orthonormalBasisOneI.repr.symm (p - q)) := by
    change frame (p - q) = frame
      (Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm (p - q)))
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [vector, ← L.map_sub, ← L.map_sub, L.norm_map]

end Unfoldings.FacewiseDevelopment
