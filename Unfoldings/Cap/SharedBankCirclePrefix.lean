module

public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Cap.ClosedRadialBankTrace

/-! Adjacent strips have the same circle endpoint before their coherent shared prefix ends. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S T : MonotoneStrip} {ε cutoff : ℝ}

/-- Two actual traces approached on opposite sides of the same coherent physical
point have the same value. Their approached face copies need not be the same face. -/
theorem shared_bank_value_of_coherent
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration i T ε cutoff)
    (wall : S.upper = T.lower) {h : ℝ}
    (first : S.upper.point h ∈ closure data.strictDomain)
    (last : T.lower.point h ∈ closure other.strictDomain)
    (coherent : D.ProjectedCoherentAt K
      (source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h))) :
    data.value (S.upper.point h) = other.value (T.lower.point h) := by
  have first_value := D.traceVisibleAt_eq_of_coherent source calibration
    (fiveSectorFrame t positive small i).place (data.visible_closure first) coherent
  rw [wall] at coherent first_value
  have last_value := D.traceVisibleAt_eq_of_coherent source calibration
    (fiveSectorFrame t positive small i).place (other.visible_closure last) coherent
  rw [wall]
  exact first_value.trans last_value.symm

/-- Only agreement up to both tested active heights is needed. Permanently
collapsed tails outside the approached domains impose no prefix-value condition. -/
theorem circle_bank_prefix_alternative
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration i T ε cutoff)
    (prefixHeight : ℝ) {a b radius : ℝ}
    (common_prefix : ∀ h ∈ Set.Icc 0 prefixHeight, h ≤ a → h ≤ b →
      S.upper.point h ∈ closure data.strictDomain →
      T.lower.point h ∈ closure other.strictDomain →
      data.value (S.upper.point h) = other.value (T.lower.point h))
    (apositive : 0 ≤ a) (bpositive : 0 ≤ b) (radius_positive : 0 < radius)
    (first : S.upper.point a ∈ closure data.strictDomain)
    (last : T.lower.point b ∈ closure other.strictDomain)
    (first_radius : ‖data.value (S.upper.point a) - data.center‖ = radius)
    (last_radius : ‖other.value (T.lower.point b) - other.center‖ = radius) :
    (a = b ∧ data.value (S.upper.point a) = other.value (T.lower.point b)) ∨
      (prefixHeight < a ∧ prefixHeight < b) := by
  have first_carrier (h : ℝ) : S.upper.point h ∈ S.carrier := by
    change S.lower.coordinate ((S.upper.point h).re + (S.upper.point h).im) ≤
      (S.upper.point h).re ∧ (S.upper.point h).re ≤
      S.upper.coordinate ((S.upper.point h).re + (S.upper.point h).im)
    rw [S.upper.point_height]
    exact ⟨S.ordered h, le_rfl⟩
  have last_carrier (h : ℝ) : T.lower.point h ∈ T.carrier := by
    change T.lower.coordinate ((T.lower.point h).re + (T.lower.point h).im) ≤
      (T.lower.point h).re ∧ (T.lower.point h).re ≤
      T.upper.coordinate ((T.lower.point h).re + (T.lower.point h).im)
    rw [T.lower.point_height]
    exact ⟨le_rfl, T.ordered h⟩
  rcases le_total a b with ordered | ordered
  · by_cases before : a ≤ prefixHeight
    · have other_closed : T.lower.point a ∈ closure other.strictDomain :=
        other.closed_initial last (last_carrier a) (by
          rw [T.lower.point_height, T.lower.point_height]
          exact ⟨apositive, ordered⟩)
      have common := common_prefix a ⟨apositive, before⟩ le_rfl ordered first other_closed
      obtain ⟨active, member⟩ :=
        (show (closure other.strictDomain).Nonempty from ⟨T.lower.point b, last⟩).of_closure
      have other_radius : ‖other.value (T.lower.point a) - other.center‖ = radius := by
        rw [← common]
        exact first_radius
      have same := other.radial.closed_bank_circle_height_unique other.continuous T.lower
        (Or.inl rfl) (other.source_bank_values member).1 apositive bpositive radius_positive
        other_closed last other_radius last_radius
      exact Or.inl ⟨same, by simpa only [same] using common⟩
    · exact Or.inr ⟨lt_of_not_ge before, (lt_of_not_ge before).trans_le ordered⟩
  · by_cases before : b ≤ prefixHeight
    · have data_closed : S.upper.point b ∈ closure data.strictDomain :=
        data.closed_initial first (first_carrier b) (by
          rw [S.upper.point_height, S.upper.point_height]
          exact ⟨bpositive, ordered⟩)
      have common := common_prefix b ⟨bpositive, before⟩ ordered le_rfl data_closed last
      obtain ⟨active, member⟩ :=
        (show (closure data.strictDomain).Nonempty from ⟨S.upper.point a, first⟩).of_closure
      have data_radius : ‖data.value (S.upper.point b) - data.center‖ = radius := by
        rw [common]
        exact last_radius
      have same := data.radial.closed_bank_circle_height_unique data.continuous S.upper
        (Or.inr rfl) (data.source_bank_values member).2 bpositive apositive radius_positive
        data_closed first data_radius first_radius
      exact Or.inl ⟨same.symm, by simpa only [same] using common⟩
    · exact Or.inr ⟨(lt_of_not_ge before).trans_le ordered, lt_of_not_ge before⟩


/-- At equal positive source radius, adjacent endpoints either coincide at the
same prefix height or both lie beyond the coherent prefix. This includes approached
terminal points; neither strip is assumed active beyond its tested bank height. -/
theorem shared_bank_circle_prefix_alternative
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : N.RadialStripTraceData positive small D calibration i T ε cutoff)
    (wall : S.upper = T.lower) (prefixHeight : ℝ)
    (coherent : ∀ h ∈ Set.Icc 0 prefixHeight, D.ProjectedCoherentAt K
      (source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h)))
    {a b radius : ℝ} (apositive : 0 ≤ a) (bpositive : 0 ≤ b) (radius_positive : 0 < radius)
    (first : S.upper.point a ∈ closure data.strictDomain)
    (last : T.lower.point b ∈ closure other.strictDomain)
    (first_radius : ‖data.value (S.upper.point a) - data.center‖ = radius)
    (last_radius : ‖other.value (T.lower.point b) - other.center‖ = radius) :
    (a = b ∧ data.value (S.upper.point a) = other.value (T.lower.point b)) ∨
      (prefixHeight < a ∧ prefixHeight < b) := by
  exact data.circle_bank_prefix_alternative other prefixHeight
    (fun h bounds _ _ first last =>
      data.shared_bank_value_of_coherent other wall first last (coherent h bounds))
    apositive bpositive radius_positive first last first_radius last_radius

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
