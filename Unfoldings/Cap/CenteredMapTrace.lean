module

public import Unfoldings.Cap.CenteredCoherentMap
public import Unfoldings.Geometry.MonotoneStripCoreLipschitz
public import Unfoldings.Topology.ComplexLipschitzExtension
public import Unfoldings.Topology.FiniteSelectionClosure

/-! Construct actual one-sided strip traces, retaining containing-face placements
at the boundary. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem centeredMap_lipschitzOn_strip (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (L : ℝ≥0)
    (linear_bound : ∀ f z, ‖(D.coordinatePlacement K calibration frame f).linear z‖ ≤ L * ‖z‖)
    (S : MonotoneStrip) (E : Set ℂ) (a b : ℝ)
    (pinches : S.RecoverablePinchesIn E a b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc a b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z)) :
    LipschitzOnWith (4 * L) (D.centeredMap K q calibration frame)
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  apply S.lipschitzOnWith_strict_of_recoverable_selection
    (fun f => (D.centeredCoordinatePlacement K q calibration frame f).toAffineMap)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    L (fun f z => linear_bound f z) E a b pinches
  · exact (D.centeredMap_continuousOn_coherent q calibration frame).mono
      (fun _ member => inside _ member.1 member.2)
  · intro z member height
    have physical := inside z member height
    obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset physical.1)
    exact ⟨f, D.centeredMap_eq_of_coherent q calibration frame physical.2 on_face⟩

/-- The trace is determined on the closure of the strict strip, including its actual one-sided
bank limits. At every boundary point it equals a containing face's real developed placement.
The chosen global continuous extension is used only to represent these unique closure values. -/
theorem centeredMap_exists_strip_trace (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (L : ℝ≥0)
    (linear_bound : ∀ f z, ‖(D.coordinatePlacement K calibration frame f).linear z‖ ≤ L * ‖z‖)
    (S : MonotoneStrip) (E : Set ℂ) (a b : ℝ)
    (pinches : S.RecoverablePinchesIn E a b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc a b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z)) :
    let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}
    ∃ G : ℂ → ℂ, Continuous G ∧ Set.EqOn (D.centeredMap K q calibration frame) G domain ∧
      ∀ z ∈ closure domain, ∃ f : Face,
        q + frame.symm z ∈ (K.projectedTriangle f).carrier ∧
          G z = D.centeredCoordinatePlacement K q calibration frame f z := by
  let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}
  obtain ⟨G, continuous, agrees⟩ := exists_continuous_complex_extension_of_lipschitzOnWith
    (D.centeredMap_lipschitzOn_strip q calibration frame L linear_bound S E a b pinches inside)
  refine ⟨G, continuous, agrees, ?_⟩
  let piece := fun f : Face => {z | q + frame.symm z ∈ (K.projectedTriangle f).carrier}
  have input : Continuous (fun z : ℂ => q + frame.symm z) :=
    continuous_const.add frame.symm.continuous
  apply finite_closed_selection_on_closure piece
    (fun f => (K.projectedTriangle f).compact_carrier.isClosed.preimage input)
    (fun f => D.centeredCoordinatePlacement K q calibration frame f)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    continuous agrees
  intro z member
  have physical := inside z (Or.inl member.1) member.2
  obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
    (K.footprint_eq_union_projectedTriangles.subset physical.1)
  exact ⟨f, on_face, D.centeredMap_eq_of_coherent q calibration frame physical.2 on_face⟩

end Unfoldings.FacewiseDevelopment
