module

public import Unfoldings.Cap.RadialStripPhysicalMap
public import Unfoldings.Cap.RadialStripTraceVisibility

/-! Coherent approached traces agree in the developed plane across different sector frames. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- Even without coherence, an approached trace retains the actual face copy
seen from this strip, expressed in the common developed plane. -/
theorem exists_physical_face_of_closed
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {z : ℂ} (closed : z ∈ closure data.strictDomain) :
    ∃ f : Face,
      source + (fiveSectorFrame t positive small i).place.symm z ∈
        (K.projectedTriangle f).carrier ∧
      data.outputFrame.symm (data.value z) = D.projectedPlacement K f
        (source + (fiveSectorFrame t positive small i).place.symm z) := by
  obtain ⟨f, member, _, value⟩ := data.visible_closure closed
  refine ⟨f, member, ?_⟩
  have output : D.centeredCoordinatePlacement K source calibration
      (fiveSectorFrame t positive small i).place f z =
        data.outputFrame (D.projectedPlacement K f
          (source + (fiveSectorFrame t positive small i).place.symm z)) := by
    let frame := (fiveSectorFrame t positive small i).place
    change data.outputFrame (D.projectedPlacement K f (frame.symm (frame source + z))) = _
    rw [frame.symm.map_add, frame.symm_apply_apply]
  rw [value, output, data.outputFrame.symm_apply_apply]

/-- This extends physical trace identification to approached endpoints where
coherence is proved, including a contact approached from another sector. -/
theorem physical_value_of_closed_coherent
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    (coherent : D.ProjectedCoherentAt K
      (source + (fiveSectorFrame t positive small i).place.symm z)) :
    data.value z = data.outputFrame
      (D.projectedMap K (source + (fiveSectorFrame t positive small i).place.symm z)) :=
  D.traceVisibleAt_eq_of_coherent source calibration
    (fiveSectorFrame t positive small i).place (data.visible_closure closed) coherent

/-- Both traces are transported back to the same actual developed plane.
Their sector indices and coordinate frames may differ. -/
theorem output_values_eq_of_coherent_contact
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {otherCalibration : Plane ≃ₗᵢ[ℝ] ℂ} {j : FiveSector} {T : MonotoneStrip} {δ limit : ℝ}
    (other : N.RadialStripTraceData positive small D otherCalibration j T δ limit)
    {z w : ℂ}
    (contact : (fiveSectorFrame t positive small i).place.symm z =
      (fiveSectorFrame t positive small j).place.symm w)
    (first : z ∈ closure data.strictDomain) (last : w ∈ closure other.strictDomain)
    (coherent : D.ProjectedCoherentAt K
      (source + (fiveSectorFrame t positive small i).place.symm z)) :
    data.outputFrame.symm (data.value z) = other.outputFrame.symm (other.value w) := by
  have last_coherent : D.ProjectedCoherentAt K
      (source + (fiveSectorFrame t positive small j).place.symm w) := contact ▸ coherent
  rw [data.physical_value_of_closed_coherent first coherent,
    other.physical_value_of_closed_coherent last last_coherent,
    data.outputFrame.symm_apply_apply, other.outputFrame.symm_apply_apply, contact]

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
