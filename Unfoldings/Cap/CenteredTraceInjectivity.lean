module

public import Unfoldings.Cap.CenteredCoherentMap
public import Unfoldings.Geometry.RecoverableStripLowerBound

/-! The actual continuous strip trace is injective through its entire approached boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- Quantitative separation on the strict slab extends to its actual trace closure.
Only coherent reopening pinches are used; permanently collapsed future tails are excluded. -/
theorem centeredMap_closed_trace_injective (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (margins : ∀ f j,
      0 < affineAxisMargins (D.coordinatePlacement K calibration frame f).toAffineMap j)
    (S : MonotoneStrip) (E : Set ℂ) (a b : ℝ) (pinches : S.RecoverablePinchesIn E a b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc a b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z))
    {G : ℂ → ℂ} (continuous : Continuous G)
    (equal : Set.EqOn (D.centeredMap K q calibration frame) G
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}) :
    Set.InjOn G (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}) := by
  apply S.injOn_closure_trace_of_recoverable_selection
    (fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    (fun f j => margins f j) E a b pinches
  · exact (D.centeredMap_continuousOn_coherent q calibration frame).mono
      (fun _ member => inside _ member.1 member.2)
  · intro z member slab
    have physical := inside z member slab
    obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset physical.1)
    exact ⟨f, D.centeredMap_eq_of_coherent q calibration frame physical.2 on_face⟩
  · exact continuous
  · exact equal

end Unfoldings.FacewiseDevelopment
