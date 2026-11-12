module

public import Unfoldings.Cap.CoherentPhysicalTraceContact
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.ClosedRadialBankTrace

/-! A coherent earlier contact forces the same actual circle endpoint in either frame. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration otherCalibration : Plane ≃ₗᵢ[ℝ] ℂ} {i j : FiveSector}
  {S T : MonotoneStrip} {ε δ cutoff limit : ℝ}

theorem circle_bank_endpoint_eq_of_earlier_coherent_contact
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : N.RadialStripTraceData positive small D otherCalibration j T δ limit)
    (H : MonotoneHeightGraph) (wall : H = T.lower ∨ H = T.upper)
    {z : ℂ} {a b radius : ℝ}
    (first : z ∈ closure data.strictDomain)
    (last : H.point b ∈ closure other.strictDomain)
    (bounds : a ∈ Set.Icc 0 b) (radius_positive : 0 < radius)
    (first_radius : ‖data.value z - data.center‖ = radius)
    (last_radius : ‖other.value (H.point b) - other.center‖ = radius)
    (contact : (fiveSectorFrame t positive small i).place.symm z =
      (fiveSectorFrame t positive small j).place.symm (H.point a))
    (coherent : D.ProjectedCoherentAt K
      (source + (fiveSectorFrame t positive small i).place.symm z)) :
    a = b ∧ data.outputFrame.symm (data.value z) =
      other.outputFrame.symm (other.value (H.point b)) := by
  have earlier : H.point a ∈ closure other.strictDomain := by
    rcases wall with rfl | rfl
    · apply other.lower_bank_closed_before last
      rwa [T.lower.point_height]
    · apply other.upper_bank_closed_before last
      rwa [T.upper.point_height]
  have equal := data.output_values_eq_of_coherent_contact other contact first earlier coherent
  have size : ‖other.value (H.point a) - other.center‖ = radius := by
    rw [← other.outputFrame_symm_source_distance, ← equal, data.outputFrame_symm_source_distance]
    exact first_radius
  obtain ⟨active, member⟩ :=
    (show (closure other.strictDomain).Nonempty from ⟨H.point b, last⟩).of_closure
  have at_source : other.value (H.point 0) = other.center := by
    rcases wall with rfl | rfl
    · exact (other.source_bank_values member).1
    · exact (other.source_bank_values member).2
  have same := other.radial.closed_bank_circle_height_unique other.continuous H wall at_source
    bounds.1 (bounds.1.trans bounds.2) radius_positive earlier last size last_radius
  exact ⟨same, by simpa only [same] using equal⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
