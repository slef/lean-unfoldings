module

public import Unfoldings.Cap.SharedBankCirclePrefix

/-! Actual approached trace values agree at a coherent physical contact. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S T : MonotoneStrip} {ε cutoff : ℝ}

theorem value_eq_of_coherent_contact
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration i T ε cutoff)
    {p q : ℂ} (contact : p = q)
    (first : p ∈ closure data.strictDomain) (last : q ∈ closure other.strictDomain)
    (coherent : D.ProjectedCoherentAt K
      (source + (fiveSectorFrame t positive small i).place.symm p)) :
    data.value p = other.value q := by
  subst q
  have first_value := D.traceVisibleAt_eq_of_coherent source calibration
    (fiveSectorFrame t positive small i).place (data.visible_closure first) coherent
  have last_value := D.traceVisibleAt_eq_of_coherent source calibration
    (fiveSectorFrame t positive small i).place (other.visible_closure last) coherent
  exact first_value.trans last_value.symm

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
