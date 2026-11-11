module

public import Unfoldings.Cap.CenteredDevelopedMap
public import Unfoldings.Cap.ProjectedCoherence
public import Unfoldings.Geometry.MonotoneStripCore
public import Unfoldings.Geometry.RecoverableStripInjective

/-! Source-centered actual strip maps extend across proved coherent pinches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem centeredMap_continuousOn_coherent (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) :
    ContinuousOn (D.centeredMap K q calibration frame)
      {z | q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z)} := by
  let L := Complex.orthonormalBasisOneI.repr.trans frame
  have input : Continuous (fun z : ℂ => q + frame.symm z) :=
    continuous_const.add frame.symm.continuous
  have along := (D.projectedMap_continuousOn_coherent K).comp input.continuousOn
    (fun _ member => member)
  exact (L.continuous.comp calibration.continuous).comp_continuousOn along

theorem centeredMap_eq_of_coherent (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {z : ℂ} (coherent : D.ProjectedCoherentAt K (q + frame.symm z))
    {f : Face} (member : q + frame.symm z ∈ (K.projectedTriangle f).carrier) :
    D.centeredMap K q calibration frame z =
      D.centeredCoordinatePlacement K q calibration frame f z := by
  rw [centeredMap, D.projectedMap_eq_of_coherent K coherent member]
  change _ = (Complex.orthonormalBasisOneI.repr.trans frame)
    (calibration (D.projectedPlacement K f (frame.symm (frame q + z))))
  rw [frame.symm.map_add, frame.symm_apply_apply]

/-- Comparisons across pinches need geometry only: actual chart compatibility and continuity
are derived once the core is in the footprint and every pinch has coherent developed values. -/
theorem centeredMap_injOn_strip_core (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (margins : ∀ f j,
      0 < affineAxisMargins (D.coordinatePlacement K calibration frame f).toAffineMap j)
    (S : MonotoneStrip) (a b : ℝ)
    (inside : ∀ z, z ∈ S.coreCarrier → z.re + z.im ∈ Set.Icc a b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z)) :
    Set.InjOn (D.centeredMap K q calibration frame)
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  apply S.injOn_strict_of_core_affine_selection
    (fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    (fun f j => margins f j) a b
  · exact (D.centeredMap_continuousOn_coherent q calibration frame).mono
      (fun _ member => inside _ member.1 member.2)
  · intro z member height
    have physical := inside z member height
    obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset physical.1)
    exact ⟨f, D.centeredMap_eq_of_coherent q calibration frame physical.2 on_face⟩

/-- Permanently merged banks need not have coherent values. Only pinches between separated
parts of the strip enter the comparison, and their coherence must come from actual geometry. -/
theorem centeredMap_injOn_strip_recoverable (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (margins : ∀ f j,
      0 < affineAxisMargins (D.coordinatePlacement K calibration frame f).toAffineMap j)
    (S : MonotoneStrip) (E : Set ℂ) (a b : ℝ)
    (pinches : S.RecoverablePinchesIn E a b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc a b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z)) :
    Set.InjOn (D.centeredMap K q calibration frame)
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  apply S.injOn_strict_of_recoverable_affine_selection
    (fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    (fun f j => margins f j) E a b pinches
  · exact (D.centeredMap_continuousOn_coherent q calibration frame).mono
      (fun _ member => inside _ member.1 member.2)
  · intro z member height
    have physical := inside z member height
    obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset physical.1)
    exact ⟨f, D.centeredMap_eq_of_coherent q calibration frame physical.2 on_face⟩

end Unfoldings.FacewiseDevelopment
