module

public import Unfoldings.Cap.ClosedCircleAbsenceBounds
public import Unfoldings.Cap.RadialStripTraceVisibility
public import Unfoldings.Geometry.MonotoneStripTerminalPinch

/-! A nonempty strip absent from a controlled circle has an actual terminal trace inside it. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- The two physical banks have permanently merged by this approached height.
Its actual one-sided face value is strictly inside the comparison circle. -/
theorem exists_terminal_pinch_of_empty_closed_circle
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {radius : ℝ} (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' closure (S.openSlab 0 cutoff) ∩ {z | ‖z - data.center‖ = radius} = ∅)
    (nonempty : (S.openSlab 0 cutoff).Nonempty) :
    ∃ h ∈ Set.Ioo (0 : ℝ) cutoff,
      (∀ k ∈ Set.Icc h cutoff, S.lower.coordinate k = S.upper.coordinate k) ∧
      S.lower.point h ∈ closure (S.openSlab 0 cutoff) ∧
      S.upper.point h ∈ closure (S.openSlab 0 cutoff) ∧
      ‖data.value (S.lower.point h) - data.center‖ < radius ∧
      D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place
        data.value data.strictDomain (S.lower.point h) ∧
      ∀ z ∈ closure (S.openSlab 0 cutoff), z.re + z.im ≤ h := by
  have inside : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have no_cutoff : ∀ z ∈ closure (S.openSlab 0 cutoff), z.re + z.im ≠ cutoff := by
    intro z closed equal
    have lower := data.closed_distance_lower (closure_mono inside closed)
    rw [equal] at lower
    have near := data.closed_inside_of_empty_closed_circle radius_positive far empty closed
    exact (not_lt_of_ge lower) (near.trans far)
  obtain ⟨h, bounds, merged, lower, upper, maximum⟩ :=
    S.exists_terminal_pinch nonempty no_cutoff
  exact ⟨h, bounds, merged, lower, upper,
    data.closed_inside_of_empty_closed_circle radius_positive far empty lower,
    data.visible_closure (closure_mono inside lower), maximum⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
