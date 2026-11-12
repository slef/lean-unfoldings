module

public import Unfoldings.Cap.RadialStripTraceBounds

/-! Every approached point of the constructed strip retains an actual visible face copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- This includes terminal pinches with no later active strip height. The chosen
face is approached from this strip, rather than an arbitrary incident face. -/
theorem visible_closure (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {z : ℂ} (member : z ∈ closure data.strictDomain) :
    D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place
      data.value data.strictDomain z := by
  let frame := (fiveSectorFrame t positive small i).place
  let piece := fun f : Face => {z | source + frame.symm z ∈ (K.projectedTriangle f).carrier}
  have selection : ∀ z ∈ data.strictDomain, ∃ f : Face, z ∈ piece f ∧
      D.centeredMap K source calibration frame z =
        D.centeredCoordinatePlacement K source calibration frame f z := by
    intro z inside
    have physical := data.physical z (Or.inl inside.1) inside.2
    obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset physical.1)
    exact ⟨f, on_face, D.centeredMap_eq_of_coherent source calibration frame physical.2 on_face⟩
  obtain ⟨f, approach, value⟩ := finite_selection_visible_on_closure piece
    (fun f => D.centeredCoordinatePlacement K source calibration frame f)
    (fun f =>
      (D.centeredCoordinatePlacement K source calibration frame f).continuous_of_finiteDimensional)
    data.continuous data.equal selection z member
  have closed : IsClosed (piece f) := (K.projectedTriangle f).compact_carrier.isClosed.preimage
    (continuous_const.add frame.symm.continuous)
  exact ⟨f, closure_minimal Set.inter_subset_right closed approach, approach, value⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
