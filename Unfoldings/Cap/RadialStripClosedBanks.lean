module

public import Unfoldings.Cap.RadialStripPointOrder

/-! Every earlier physical bank point is approached before an actual closed strip point. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

theorem lower_bank_closed_before {z : ℂ} (endpoint : z ∈ closure data.strictDomain)
    {h : ℝ} (height : h ∈ Set.Icc 0 (z.re + z.im)) :
    S.lower.point h ∈ closure data.strictDomain := by
  apply data.closed_initial endpoint
  · change S.lower.coordinate ((S.lower.point h).re + (S.lower.point h).im) ≤
      (S.lower.point h).re ∧ (S.lower.point h).re ≤
        S.upper.coordinate ((S.lower.point h).re + (S.lower.point h).im)
    rw [S.lower.point_height]
    exact ⟨le_rfl, S.ordered h⟩
  · rwa [S.lower.point_height]

theorem upper_bank_closed_before {z : ℂ} (endpoint : z ∈ closure data.strictDomain)
    {h : ℝ} (height : h ∈ Set.Icc 0 (z.re + z.im)) :
    S.upper.point h ∈ closure data.strictDomain := by
  apply data.closed_initial endpoint
  · change S.lower.coordinate ((S.upper.point h).re + (S.upper.point h).im) ≤
      (S.upper.point h).re ∧ (S.upper.point h).re ≤
        S.upper.coordinate ((S.upper.point h).re + (S.upper.point h).im)
    rw [S.upper.point_height]
    exact ⟨S.ordered h, le_rfl⟩
  · rwa [S.upper.point_height]

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
