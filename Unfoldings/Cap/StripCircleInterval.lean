module

public import Unfoldings.Cap.ClosedRadialBankTrace
public import Unfoldings.Geometry.MonotoneStripImageFrontier
public import Unfoldings.Geometry.QuadrantCircleInterval

/-! A developed strip meets a controlled source circle in at most one angular interval. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- A source circle has at most one open strip interval, whose possible endpoints
are the unique actual values on the two approached banks. -/
def HasBankCircleInterval (G : ℂ → ℂ) (center : ℂ) (cutoff radius : ℝ) : Prop :=
  ∃ lower upper : ℂ,
    (∀ h ∈ Set.Icc 0 cutoff,
      S.lower.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} →
      ‖G (S.lower.point h) - center‖ = radius → G (S.lower.point h) = lower) ∧
    (∀ h ∈ Set.Icc 0 cutoff,
      S.upper.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} →
      ‖G (S.upper.point h) - center‖ = radius → G (S.upper.point h) = upper) ∧
    (quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) = ∅ ∨
      quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) =
        Set.Ioo (min (lower - center).re (upper - center).re)
          (max (lower - center).re (upper - center).re))

/-- The only two possible angular endpoints come from actual approached bank values.
Closure injectivity, radial bank progress, and exclusion of the physical end levels
rule out any additional component on the circle. -/
theorem exists_bank_circle_interval_of_closed_ends {G : ℂ → ℂ} (continuous : Continuous G)
    (center : ℂ) (cutoff radius : ℝ) (positive : 0 < radius)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}))
    (radial : S.RadialBankTraces G center cutoff)
    (source_values : G (S.lower.point 0) = center ∧ G (S.upper.point 0) = center)
    (quadrant : ∀ z ∈ S.openSlab 0 cutoff,
      0 < (G z - center).re ∧ 0 < (G z - center).im)
    (ends_avoid : ∀ z ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff},
      (z.re + z.im = 0 ∨ z.re + z.im = cutoff) → ‖G z - center‖ ≠ radius) :
    ∃ lower upper : ℂ,
      (∀ h ∈ Set.Icc 0 cutoff,
        S.lower.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} →
        ‖G (S.lower.point h) - center‖ = radius → G (S.lower.point h) = lower) ∧
      (∀ h ∈ Set.Icc 0 cutoff,
        S.upper.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} →
        ‖G (S.upper.point h) - center‖ = radius → G (S.upper.point h) = upper) ∧
      (quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) = ∅ ∨
        quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) =
          Set.Ioo (min (lower - center).re (upper - center).re)
            (max (lower - center).re (upper - center).re)) := by
  classical
  let domain := {z : ℂ | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
  have inside : S.openSlab 0 cutoff ⊆ domain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have single_bank (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper)
      (source_value : G (H.point 0) = center) :
      ∃ value : ℂ, ∀ h ∈ Set.Icc 0 cutoff, H.point h ∈ closure domain →
        ‖G (H.point h) - center‖ = radius → G (H.point h) = value := by
    by_cases present : ∃ h ∈ Set.Icc 0 cutoff, H.point h ∈ closure domain ∧
        ‖G (H.point h) - center‖ = radius
    · obtain ⟨h, bounds, closed, size⟩ := present
      refine ⟨G (H.point h), fun k kb kc ks => ?_⟩
      rw [radial.closed_bank_circle_height_unique continuous H wall source_value kb.1 bounds.1
        positive kc closed ks size]
    · exact ⟨center, fun h bounds closed size => (present ⟨h, bounds, closed, size⟩).elim⟩
  obtain ⟨lower, at_lower⟩ := single_bank S.lower (Or.inl rfl) source_values.1
  obtain ⟨upper, at_upper⟩ := single_bank S.upper (Or.inr rfl) source_values.2
  have open_image : IsOpen (G '' S.openSlab 0 cutoff) := by
    rw [Set.image_eq_range]
    apply PlanarTopology.isOpen_complex_range_of_continuous_injective (S.isOpen_openSlab 0 cutoff)
      ⟨fun z => G z.val, continuous.comp continuous_subtype_val⟩
    intro x y equal
    exact Subtype.ext (injective (subset_closure (inside x.property))
      (subset_closure (inside y.property)) equal)
  have image_quadrant : ∀ z ∈ G '' S.openSlab 0 cutoff,
      0 < (z - center).re ∧ 0 < (z - center).im := by
    rintro z ⟨p, member, rfl⟩
    exact quadrant p member
  refine ⟨lower, upper, at_lower, at_upper, ?_⟩
  apply quadrant_circle_preimage_interval open_image center positive image_quadrant lower upper
  intro z boundary size
  obtain ⟨p, physical_boundary, value⟩ :=
    (S.frontier_image_openSlab_eq 0 cutoff continuous injective).subset boundary
  have bounded := S.closure_openSlab_subset 0 cutoff physical_boundary.1
  have closed : p ∈ closure domain := closure_mono inside physical_boundary.1
  have physical_size : ‖G p - center‖ = radius := by rw [value]; exact size
  rcases S.frontier_openSlab_cases 0 cutoff physical_boundary with first | last | source | finish
  · left
    calc
      z = G p := value.symm
      _ = G (S.lower.point (p.re + p.im)) := congrArg G first
      _ = lower := at_lower _ bounded.2 (first ▸ closed) (first ▸ physical_size)
  · right
    calc
      z = G p := value.symm
      _ = G (S.upper.point (p.re + p.im)) := congrArg G last
      _ = upper := at_upper _ bounded.2 (last ▸ closed) (last ▸ physical_size)
  · exact (ends_avoid p closed (Or.inl source) physical_size).elim
  · exact (ends_avoid p closed (Or.inr finish) physical_size).elim


/-- The bounded-end formulation follows from the sharper approached-end criterion. -/
theorem exists_bank_circle_interval {G : ℂ → ℂ} (continuous : Continuous G)
    (center : ℂ) (cutoff radius : ℝ) (positive : 0 < radius)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}))
    (radial : S.RadialBankTraces G center cutoff)
    (source_values : G (S.lower.point 0) = center ∧ G (S.upper.point 0) = center)
    (quadrant : ∀ z ∈ S.openSlab 0 cutoff,
      0 < (G z - center).re ∧ 0 < (G z - center).im)
    (ends_avoid : ∀ z ∈ S.boundedCarrier 0 cutoff,
      (z.re + z.im = 0 ∨ z.re + z.im = cutoff) → ‖G z - center‖ ≠ radius) :
    ∃ lower upper : ℂ,
      (∀ h ∈ Set.Icc 0 cutoff,
        S.lower.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} →
        ‖G (S.lower.point h) - center‖ = radius → G (S.lower.point h) = lower) ∧
      (∀ h ∈ Set.Icc 0 cutoff,
        S.upper.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} →
        ‖G (S.upper.point h) - center‖ = radius → G (S.upper.point h) = upper) ∧
      (quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) = ∅ ∨
        quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) =
          Set.Ioo (min (lower - center).re (upper - center).re)
            (max (lower - center).re (upper - center).re)) := by
  have subset : {z : ℂ | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ⊆
      S.boundedCarrier 0 cutoff := fun _ member =>
    ⟨⟨member.1.1.le, member.1.2.le⟩, member.2⟩
  have extend := closure_minimal subset (S.isClosed_boundedCarrier 0 cutoff)
  exact S.exists_bank_circle_interval_of_closed_ends continuous center cutoff radius positive
    injective radial source_values quadrant (fun z closed ends => ends_avoid z (extend closed) ends)

end Unfoldings.MonotoneStrip
