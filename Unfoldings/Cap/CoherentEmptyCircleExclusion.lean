module

public import Unfoldings.Cap.CoherentPhysicalTraceContact
public import Unfoldings.Cap.EmptyCircleStripBounds

/-! An empty strip's approached point cannot coherently meet another frame's source circle. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration otherCalibration : Plane ≃ₗᵢ[ℝ] ℂ} {i j : FiveSector}
  {S T : MonotoneStrip} {ε δ cutoff limit : ℝ}

theorem not_coherent_of_empty_circle_contact
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : N.RadialStripTraceData positive small D otherCalibration j T δ limit)
    {q z : ℂ} (first : q ∈ closure (S.openSlab 0 cutoff))
    (last : z ∈ closure other.strictDomain)
    (contact : (fiveSectorFrame t positive small i).place.symm q =
      (fiveSectorFrame t positive small j).place.symm z)
    {radius : ℝ} (radius_positive : 0 < radius)
    (outside : radius ∉ data.emptyCircleExceptions)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {w | ‖w - data.center‖ = radius} = ∅)
    (size : ‖other.value z - other.center‖ = radius) :
    ¬ D.ProjectedCoherentAt K (source + (fiveSectorFrame t positive small i).place.symm q) := by
  intro coherent
  have included : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have equal := data.output_values_eq_of_coherent_contact other contact
    (closure_mono included first) last coherent
  have same : ‖data.value q - data.center‖ = ‖other.value z - other.center‖ := by
    rw [← data.outputFrame_symm_source_distance, equal, other.outputFrame_symm_source_distance]
  have inside := data.closed_inside_of_empty_circle radius_positive outside empty first
  rw [same, size] at inside
  exact (lt_irrefl _ inside).elim

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
