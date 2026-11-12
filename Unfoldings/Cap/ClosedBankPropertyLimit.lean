module

public import Unfoldings.Cap.ClosedRadialBankTrace
public import Unfoldings.Geometry.RecoverableStripClosure

/-! Closed predicates of actual radial bank contacts persist at exceptional radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

variable {S : MonotoneStrip} {G : ℂ → ℂ} {center : ℂ} {cutoff : ℝ}

/-- Compact bank graphs preserve any closed predicate of contact height.
The lower radius may be positive, allowing a fixed finite run to stay strictly inside. -/
theorem RadialBankTraces.closed_bank_property_at_radius_limit
    (radial : S.RadialBankTraces G center cutoff) (continuous : Continuous G)
    (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper)
    (source_value : G (H.point 0) = center)
    {h radius lower : ℝ} (nonnegative : 0 ≤ h) (positive : 0 < radius)
    (closed : H.point h ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff})
    (size : ‖G (H.point h) - center‖ = radius)
    (lower_lt : lower < radius)
    {exception : Set ℝ} (finite : exception.Finite)
    {P : Set ℝ} (property_closed : IsClosed P)
    (regular : ∀ r ∈ Set.Ioo lower radius, r ∉ exception →
      ∃ k ∈ Set.Icc 0 cutoff,
        H.point k ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ∧
        ‖G (H.point k) - center‖ = r ∧ k ∈ P) : h ∈ P := by
  let A := Set.Icc 0 cutoff ∩
    H.point ⁻¹' closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ∩ P
  let norm_value := fun k : ℝ => ‖G (H.point k) - center‖
  have norm_continuous : Continuous norm_value :=
    ((continuous.comp H.point_continuous).sub continuous_const).norm
  have compact : IsCompact A :=
    (isCompact_Icc.inter_right (isClosed_closure.preimage H.point_continuous)).inter_right
      property_closed
  have radii_closed : IsClosed (norm_value '' A) := (compact.image norm_continuous).isClosed
  have good : Set.Ioo lower radius \ exception ⊆ norm_value '' A := by
    rintro r ⟨bounds, outside⟩
    obtain ⟨k, height, approached, radius_eq, property⟩ := regular r bounds outside
    exact ⟨k, ⟨⟨height, approached⟩, property⟩, radius_eq⟩
  have approached := Icc_subset_closure_Ioo_sdiff_finite lower_lt finite
    (show radius ∈ Set.Icc lower radius from ⟨lower_lt.le, le_rfl⟩)
  obtain ⟨k, ⟨⟨height, k_closed⟩, property⟩, k_size⟩ :=
    closure_minimal good radii_closed approached
  have equal := radial.closed_bank_circle_height_unique continuous H wall source_value
    nonnegative height.1 positive closed k_closed size k_size
  exact equal.symm ▸ property

end Unfoldings.MonotoneStrip
