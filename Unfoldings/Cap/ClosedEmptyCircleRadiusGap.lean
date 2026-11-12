module

public import Unfoldings.Cap.ClosedCircleAbsenceBounds
public import Unfoldings.Cap.EmptyCircleStripBounds

/-! An absent closed circle leaves a uniform radial gap around an entire compact strip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- Compactness makes the strict enclosure of every approached point uniform. -/
theorem radiusBound_lt_of_empty_closed_circle {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' closure (S.openSlab 0 cutoff) ∩
      {z | ‖z - data.center‖ = radius} = ∅) : data.closedRadiusBound < radius := by
  have attained := (data.isCompact_closedRadii.insert 0).sSup_mem
    (Set.insert_nonempty 0 data.closedRadii)
  change data.closedRadiusBound ∈ insert 0 data.closedRadii at attained
  rcases attained with zero | ⟨z, member, equal⟩
  · simpa only [zero] using radius_positive
  · rw [← equal]
    exact data.closed_inside_of_empty_closed_circle radius_positive far empty member

/-- Every circle beyond the closed-strip radius bound is absent, with no exceptional set. -/
theorem empty_closed_circle_of_radiusBound_lt {radius : ℝ}
    (beyond : data.closedRadiusBound < radius) :
    data.value '' closure (S.openSlab 0 cutoff) ∩ {z | ‖z - data.center‖ = radius} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨⟨z, member, rfl⟩, size⟩
  have bound := data.closed_norm_le_radiusBound member
  rw [size] at bound
  exact beyond.not_ge bound

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
