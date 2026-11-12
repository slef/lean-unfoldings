module

public import Unfoldings.Geometry.RecoverableStripClosure
public import Mathlib.Analysis.Complex.Basic

/-! Compact bank graphs extend circle order across finitely many exceptional radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Ordered contacts on a dense set of smaller circles have an ordered limit contact.
The admissible parameter sets are compact; neither bank needs an invertible radius map. -/
theorem exists_ordered_bank_contact_at_limit
    {A B : Set ℝ} (first_compact : IsCompact A) (last_compact : IsCompact B)
    {f g : ℝ → ℂ} (first_continuous : Continuous f) (last_continuous : Continuous g)
    {radius : ℝ} (positive : 0 < radius)
    {exception : Set ℝ} (finite : exception.Finite)
    (regular : ∀ r ∈ Set.Ioo 0 radius, r ∉ exception →
      ∃ a ∈ A, ∃ b ∈ B, ‖f a‖ = r ∧ ‖g b‖ = r ∧ (f a).re ≤ (g b).re) :
    ∃ a ∈ A, ∃ b ∈ B,
      ‖f a‖ = radius ∧ ‖g b‖ = radius ∧ (f a).re ≤ (g b).re := by
  let first : ℝ × ℝ → ℂ := fun p => f p.1
  let last : ℝ × ℝ → ℂ := fun p => g p.2
  have first_cts : Continuous first := first_continuous.comp continuous_fst
  have last_cts : Continuous last := last_continuous.comp continuous_snd
  let pairs := (A ×ˢ B) ∩ {p | ‖first p‖ = ‖last p‖} ∩
    {p | (first p).re ≤ (last p).re}
  have compact : IsCompact pairs :=
    ((first_compact.prod last_compact).inter_right
      (isClosed_eq first_cts.norm last_cts.norm)).inter_right
        (isClosed_le (Complex.continuous_re.comp first_cts)
          (Complex.continuous_re.comp last_cts))
  have radii_closed : IsClosed ((fun p => ‖first p‖) '' pairs) :=
    (compact.image first_cts.norm).isClosed
  have dense_order : Set.Ioo 0 radius \ exception ⊆
      (fun p => ‖first p‖) '' pairs := by
    rintro r ⟨inside, outside⟩
    obtain ⟨a, member_a, b, member_b, first_size, last_size, ordered⟩ :=
      regular r inside outside
    exact ⟨(a, b), ⟨⟨⟨member_a, member_b⟩, first_size.trans last_size.symm⟩, ordered⟩,
      first_size⟩
  have approached := Icc_subset_closure_Ioo_sdiff_finite positive finite
    (show radius ∈ Set.Icc 0 radius from ⟨positive.le, le_rfl⟩)
  obtain ⟨⟨a, b⟩, ⟨⟨⟨member_a, member_b⟩, equal_size⟩, ordered⟩, size⟩ :=
    closure_minimal dense_order radii_closed approached
  exact ⟨a, member_a, b, member_b, size, equal_size.symm.trans size, ordered⟩

end Unfoldings
