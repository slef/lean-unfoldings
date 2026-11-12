module

public import Unfoldings.Cap.CenteredMapTrace
public import Unfoldings.Topology.FiniteSelectionVisibility

/-! Actual trace values are approached through their containing faces and match coherent copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- Retain the side from which a face contributes its actual trace value. This is stronger
than merely choosing an arbitrary face that happens to contain the boundary point. -/
def TraceVisibleAt (K : ConvexCap C) (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (G : ℂ → ℂ) (domain : Set ℂ) (z : ℂ) : Prop :=
  ∃ f : Face, q + frame.symm z ∈ (K.projectedTriangle f).carrier ∧
    z ∈ closure (domain ∩ {x | q + frame.symm x ∈ (K.projectedTriangle f).carrier}) ∧
      G z = D.centeredCoordinatePlacement K q calibration frame f z

theorem centered_trace_visible (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} (continuous : Continuous G)
    (faces : ∀ z ∈ closure domain, ∃ f : Face,
      q + frame.symm z ∈ (K.projectedTriangle f).carrier ∧
        G z = D.centeredCoordinatePlacement K q calibration frame f z) :
    ∀ z ∈ closure domain, D.TraceVisibleAt K q calibration frame G domain z := by
  let piece := fun f : Face => {z | q + frame.symm z ∈ (K.projectedTriangle f).carrier}
  have visible := finite_selection_visible_on_closure piece
    (fun f => D.centeredCoordinatePlacement K q calibration frame f)
    (fun f =>
      (D.centeredCoordinatePlacement K q calibration frame f).continuous_of_finiteDimensional)
    continuous (Set.eqOn_refl G domain) (fun z member => faces z (subset_closure member))
  intro z member
  obtain ⟨f, approach, value⟩ := visible z member
  have input : Continuous (fun z : ℂ => q + frame.symm z) :=
    continuous_const.add frame.symm.continuous
  have closed : IsClosed (piece f) :=
    (K.projectedTriangle f).compact_carrier.isClosed.preimage input
  exact ⟨f, closure_minimal Set.inter_subset_right closed approach, approach, value⟩

theorem traceVisibleAt_eq_of_coherent (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z)
    (coherent : D.ProjectedCoherentAt K (q + frame.symm z)) :
    G z = D.centeredMap K q calibration frame z := by
  obtain ⟨f, member, _, value⟩ := trace
  exact value.trans (D.centeredMap_eq_of_coherent q calibration frame coherent member).symm

end Unfoldings.FacewiseDevelopment
