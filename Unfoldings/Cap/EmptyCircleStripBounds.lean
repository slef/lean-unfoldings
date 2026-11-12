module

public import Unfoldings.Cap.RadialStripTraceBounds
public import Unfoldings.Geometry.RecoverableStripRadiusCrossing

/-! Away from finitely many radii, absent circle slices enclose the whole closed strip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

def pinchRadii : Set ℝ := (fun z => ‖data.value z - data.center‖) '' data.coherentSet

theorem finite_pinchRadii : data.pinchRadii.Finite := data.finite_coherentSet.image _

def closedRadii : Set ℝ :=
  (fun z => ‖data.value z - data.center‖) '' closure (S.openSlab 0 cutoff)

theorem isCompact_closedRadii : IsCompact data.closedRadii :=
  (S.isCompact_closure_openSlab 0 cutoff).image ((data.continuous.sub continuous_const).norm)

/-- Include zero so this bound is also defined for an entirely empty strip. -/
def closedRadiusBound : ℝ := sSup (insert 0 data.closedRadii)

theorem bddAbove_insert_closedRadii : BddAbove (insert 0 data.closedRadii) :=
  (data.isCompact_closedRadii.insert 0).bddAbove

theorem closed_norm_le_radiusBound {z : ℂ} (member : z ∈ closure (S.openSlab 0 cutoff)) :
    ‖data.value z - data.center‖ ≤ data.closedRadiusBound :=
  le_csSup data.bddAbove_insert_closedRadii (Or.inr ⟨z, member, rfl⟩)

/-- These finitely many extra radii allow comparison across strips whose circle slice is empty. -/
def emptyCircleExceptions : Set ℝ := insert data.closedRadiusBound data.pinchRadii

theorem finite_emptyCircleExceptions : data.emptyCircleExceptions.Finite :=
  data.finite_pinchRadii.insert _

theorem circle_nonempty_of_norm_ge {radius : ℝ} (radius_positive : 0 < radius)
    (outside : radius ∉ data.pinchRadii) {q : ℂ} (member : q ∈ S.openSlab 0 cutoff)
    (far : radius ≤ ‖data.value q - data.center‖) :
    (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius}).Nonempty := by
  have source_value := data.source_value_of_active
    (show q ∈ data.strictDomain from ⟨member.1, member.2.1.le, member.2.2.le⟩)
  exact S.circle_image_nonempty_of_avoiding_pinches data.lower_source data.upper_source data.pinches
    data.continuous source_value radius_positive outside member far

theorem norm_lt_of_empty_circle {radius : ℝ} (radius_positive : 0 < radius)
    (outside : radius ∉ data.pinchRadii)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {q : ℂ} (member : q ∈ S.openSlab 0 cutoff) : ‖data.value q - data.center‖ < radius := by
  by_contra not_before
  have present := data.circle_nonempty_of_norm_ge radius_positive outside member
    (le_of_not_gt not_before)
  rw [empty] at present
  exact Set.not_nonempty_empty present

theorem closed_norm_le_of_empty_circle {radius : ℝ} (radius_positive : 0 < radius)
    (outside : radius ∉ data.pinchRadii)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {q : ℂ} (member : q ∈ closure (S.openSlab 0 cutoff)) :
    ‖data.value q - data.center‖ ≤ radius := by
  have closed : IsClosed {z : ℂ | ‖data.value z - data.center‖ ≤ radius} :=
    isClosed_le ((data.continuous.sub continuous_const).norm) continuous_const
  have bound : S.openSlab 0 cutoff ⊆ {z : ℂ | ‖data.value z - data.center‖ ≤ radius} :=
    fun _ member => (data.norm_lt_of_empty_circle radius_positive outside empty member).le
  exact closure_minimal bound closed member

theorem radiusBound_le_of_empty_circle {radius : ℝ} (radius_positive : 0 < radius)
    (outside : radius ∉ data.pinchRadii)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅) :
    data.closedRadiusBound ≤ radius := by
  apply csSup_le (Set.insert_nonempty _ _)
  intro r member
  rcases member with zero | ⟨q, member, rfl⟩
  · exact zero ▸ radius_positive.le
  · exact data.closed_norm_le_of_empty_circle radius_positive outside empty member

/-- An absent nonexceptional circle leaves every approached strip point strictly
inside. In particular, a collapsed strip's terminal trace can start an exterior comparison arc. -/
theorem closed_inside_of_empty_circle {radius : ℝ} (radius_positive : 0 < radius)
    (outside : radius ∉ data.emptyCircleExceptions)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    {q : ℂ} (member : q ∈ closure (S.openSlab 0 cutoff)) :
    ‖data.value q - data.center‖ < radius := by
  have avoid_pinches : radius ∉ data.pinchRadii := fun member => outside (Or.inr member)
  have bound := data.radiusBound_le_of_empty_circle radius_positive avoid_pinches empty
  have different : data.closedRadiusBound ≠ radius := fun equal => outside (Or.inl equal.symm)
  exact (data.closed_norm_le_radiusBound member).trans_lt (lt_of_le_of_ne bound different)

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
