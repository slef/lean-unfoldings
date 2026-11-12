module

public import Unfoldings.Cap.ClosedCircleSectionDegeneracy
public import Unfoldings.Geometry.ClosedBankOrderLimit

/-! Actual closed sections inherit facing-bank order at vertex radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S T : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
  (other : N.RadialStripTraceData positive small D calibration i T ε cutoff)

/-- The regular-radius order extends through every exceptional circle, including sections
that collapse to a physical pinch. The conclusion uses the caller's actual closed sections. -/
theorem closed_section_facing_order_of_regular
    (first_section : S.ClosedBankCircleSection data.value data.center cutoff radius)
    (last_section : T.ClosedBankCircleSection other.value other.center cutoff radius)
    {μ : ℝ} (small_error : ε < μ)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    {exception : Set ℝ} (finite : exception.Finite)
    (regular : ∀ r ∈ Set.Ioo 0 radius, r ∉ exception →
      ∃ first : S.BankCircleSlice data.value data.center cutoff r,
      ∃ last : T.BankCircleSlice other.value other.center cutoff r,
        (data.value (S.upper.point first.upperHeight) - data.center).re ≤
          (other.value (T.lower.point last.lowerHeight) - other.center).re) :
    (data.value (S.upper.point first_section.upperHeight) - data.center).re ≤
      (other.value (T.lower.point last_section.lowerHeight) - other.center).re := by
  let A := Set.Icc 0 cutoff ∩ S.upper.point ⁻¹' closure data.strictDomain
  let B := Set.Icc 0 cutoff ∩ T.lower.point ⁻¹' closure other.strictDomain
  have compact_a : IsCompact A := isCompact_Icc.inter_right
    (isClosed_closure.preimage S.upper.point_continuous)
  have compact_b : IsCompact B := isCompact_Icc.inter_right
    (isClosed_closure.preimage T.lower.point_continuous)
  have regular_contacts : ∀ r ∈ Set.Ioo 0 radius, r ∉ exception →
      ∃ a ∈ A, ∃ b ∈ B,
        ‖data.value (S.upper.point a) - data.center‖ = r ∧
        ‖other.value (T.lower.point b) - other.center‖ = r ∧
        (data.value (S.upper.point a) - data.center).re ≤
          (other.value (T.lower.point b) - other.center).re := by
    intro r bounds outside
    obtain ⟨first, last, ordered⟩ := regular r bounds outside
    exact ⟨first.upperHeight, ⟨first.upper_bounds, first.upper_closed⟩,
      last.lowerHeight, ⟨last.lower_bounds, last.lower_closed⟩,
      first.upper_radius, last.lower_radius, ordered⟩
  obtain ⟨a, member_a, b, member_b, size_a, size_b, ordered⟩ :=
    exists_ordered_bank_contact_at_limit compact_a compact_b
      ((data.continuous.comp S.upper.point_continuous).sub continuous_const)
      ((other.continuous.comp T.lower.point_continuous).sub continuous_const)
      radius_positive finite regular_contacts
  obtain ⟨_, _, _, first_unique, _⟩ :=
    data.circle_interval small_error first_margin radius_positive far
  obtain ⟨_, _, last_unique, _, _⟩ :=
    other.circle_interval small_error last_margin radius_positive far
  have first_equal :=
    (first_unique first_section.upperHeight first_section.upper_bounds
      first_section.upper_closed first_section.upper_radius).trans
        (first_unique a member_a.1 member_a.2 size_a).symm
  have last_equal :=
    (last_unique last_section.lowerHeight last_section.lower_bounds
      last_section.lower_closed last_section.lower_radius).trans
        (last_unique b member_b.1 member_b.2 size_b).symm
  rw [first_equal, last_equal]
  exact ordered

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
