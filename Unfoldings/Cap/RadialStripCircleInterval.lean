module

public import Unfoldings.Cap.RadialStripTraceBounds
public import Unfoldings.Cap.StripCircleInterval

/-! Actual radial strip data supply every hypothesis of the source-circle interval criterion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- No source values, quadrant placement, or end-level exclusions are additional inputs:
they follow from the same actual trace data and the physical sector margin. -/
theorem circle_interval (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {μ : ℝ} (small_error : ε < μ)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff) :
    S.HasBankCircleInterval data.value data.center cutoff radius := by
  classical
  by_cases active : data.strictDomain.Nonempty
  · obtain ⟨z, member⟩ := active
    exact S.exists_bank_circle_interval_of_closed_ends data.continuous data.center cutoff radius
      radius_positive data.closed_injective data.radial (data.source_bank_values member)
      (fun z member => data.strict_quadrant_of_margin small_error margin member)
      (fun z closed ends => data.end_levels_avoid_circle member radius_positive far closed ends)
  · have empty : data.strictDomain = ∅ := Set.not_nonempty_iff_eq_empty.mp active
    have closed_empty : closure data.strictDomain = ∅ := by rw [empty, closure_empty]
    have open_empty : S.openSlab 0 cutoff = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z member
      have inside : z ∈ data.strictDomain := ⟨member.1, member.2.1.le, member.2.2.le⟩
      rw [empty] at inside
      exact inside
    refine ⟨data.center, data.center, ?_, ?_, Or.inl ?_⟩
    · intro h bounds member
      change S.lower.point h ∈ closure data.strictDomain at member
      rw [closed_empty] at member
      exact member.elim
    · intro h bounds member
      change S.upper.point h ∈ closure data.strictDomain at member
      rw [closed_empty] at member
      exact member.elim
    · rw [open_empty, Set.image_empty, Set.preimage_empty]

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
