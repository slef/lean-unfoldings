module

public import Unfoldings.Cap.ProjectedDevelopedMap
public import Unfoldings.Cap.ProjectedStripMaps
public import Unfoldings.Geometry.MonotoneStripOpenInjective

/-! Actual developed maps in source-centered strip coordinates, with proved chart compatibility. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

def centeredCoordinatePlacement (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (f : Face) : ℂ ≃ᵃ[ℝ] ℂ :=
  (AffineEquiv.constVAdd ℝ ℂ (frame q)).trans (D.coordinatePlacement K calibration frame f)

theorem centeredCoordinatePlacement_linear (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) (f : Face) (z : ℂ) :
    (D.centeredCoordinatePlacement K q calibration frame f).linear z =
      (D.coordinatePlacement K calibration frame f).linear z := rfl

def centeredMap (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) (z : ℂ) : ℂ :=
  (Complex.orthonormalBasisOneI.repr.trans frame)
    (calibration (D.projectedMap K (q + frame.symm z)))

theorem centeredMap_eq {q : Plane} (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {f : Face} {z : ℂ} (member : q + frame.symm z ∈ (K.projectedTriangle f).carrier)
    (outside : q + frame.symm z ∉ K.projectedCutSet retain) :
    D.centeredMap K q calibration frame z =
      D.centeredCoordinatePlacement K q calibration frame f z := by
  rw [centeredMap, D.projectedMap_eq K member outside]
  change _ = (Complex.orthonormalBasisOneI.repr.trans frame)
    (calibration (D.projectedPlacement K f (frame.symm (frame q + z))))
  rw [frame.symm.map_add, frame.symm_apply_apply]

theorem centeredMap_continuousOn (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) :
    ContinuousOn (D.centeredMap K q calibration frame)
      {z | q + frame.symm z ∈ K.footprint \ K.projectedCutSet retain} := by
  let L := Complex.orthonormalBasisOneI.repr.trans frame
  have input : Continuous (fun z : ℂ => q + frame.symm z) :=
    continuous_const.add frame.symm.continuous
  have selected := D.projectedMap_continuousOn K
  have along := selected.comp input.continuousOn (fun _ member => member)
  exact (L.continuous.comp calibration.continuous).comp_continuousOn along

/-- The map is defined by the actual development; its chart selection is derived. -/
theorem centeredMap_selects (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {z : ℂ} (member : q + frame.symm z ∈ K.footprint \ K.projectedCutSet retain) :
    ∃ f, D.centeredMap K q calibration frame z =
      D.centeredCoordinatePlacement K q calibration frame f z := by
  obtain ⟨f, inside⟩ := Set.mem_iUnion.mp
    (K.footprint_eq_union_projectedTriangles.subset member.1)
  exact ⟨f, D.centeredMap_eq K calibration frame inside member.2⟩

/-- No continuous strip map or compatible face choices are supplied as hypotheses.
It suffices to place a bounded strip inside the regular projected region. -/
theorem centeredMap_injOn_bounded_strip (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (margins : ∀ f j,
      0 < affineAxisMargins (D.coordinatePlacement K calibration frame f).toAffineMap j)
    (S : MonotoneStrip) (a b : ℝ)
    (inside : ∀ z ∈ S.boundedCarrier a b,
      q + frame.symm z ∈ K.footprint \ K.projectedCutSet retain) :
    Set.InjOn (D.centeredMap K q calibration frame) (S.boundedCarrier a b) := by
  apply S.injOn_bounded_of_affine_selection
    (fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    (fun f j => margins f j) a b
  · exact (D.centeredMap_continuousOn K q calibration frame).mono inside
  · exact fun z member => D.centeredMap_selects K q calibration frame (inside z member)

/-- A positive-width slab of a strict strip needs no developed values on either bank. -/
theorem centeredMap_injOn_open_strip (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (margins : ∀ f j,
      0 < affineAxisMargins (D.coordinatePlacement K calibration frame f).toAffineMap j)
    (S : MonotoneStrip) (a b : ℝ)
    (width : ∀ h ∈ Set.Icc a b, S.lower.coordinate h < S.upper.coordinate h)
    (inside : ∀ z, z ∈ S.strictCarrier → z.re + z.im ∈ Set.Icc a b →
      q + frame.symm z ∈ K.footprint \ K.projectedCutSet retain) :
    Set.InjOn (D.centeredMap K q calibration frame)
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  apply S.injOn_strict_of_affine_selection
    (fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    (fun f j => margins f j) a b width
  · exact (D.centeredMap_continuousOn K q calibration frame).mono
      (fun z member => inside z member.1 member.2)
  · exact fun z member height =>
      D.centeredMap_selects K q calibration frame (inside z member height)

end Unfoldings.FacewiseDevelopment
