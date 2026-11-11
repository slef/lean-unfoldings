module

public import Unfoldings.Cap.CenteredCoherentMap
public import Unfoldings.Geometry.MonotoneStripSourceError

/-! Actual centered maps inherit mesh-independent source error from their real face charts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem centeredMap_source_error (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {c b : ℝ} (nonnegative : 0 ≤ c)
    (linear_error : ∀ f z, ‖(D.coordinatePlacement K calibration frame f).linear z - z‖ ≤ c * ‖z‖)
    (S : MonotoneStrip) (E : Set ℂ)
    (first : S.lower.coordinate 0 = 0) (last : S.upper.coordinate 0 = 0)
    (pinches : S.RecoverablePinchesIn E 0 b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc 0 b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z))
    {z : ℂ} (member : z ∈ S.strictCarrier) (slab : z.re + z.im ∈ Set.Icc 0 b) :
    ‖(D.centeredMap K q calibration frame z - D.centeredMap K q calibration frame 0) - z‖ ≤
      2 * c * (z.re + z.im) := by
  apply S.error_from_source_of_recoverable_selection
    (fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    nonnegative first last (fun f v => linear_error f v) E pinches
  · exact (D.centeredMap_continuousOn_coherent q calibration frame).mono
      (fun _ member => inside _ member.1 member.2)
  · intro z member height
    have physical := inside z member height
    obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset physical.1)
    exact ⟨f, D.centeredMap_eq_of_coherent q calibration frame physical.2 on_face⟩
  · exact member
  · exact slab

end Unfoldings.FacewiseDevelopment
