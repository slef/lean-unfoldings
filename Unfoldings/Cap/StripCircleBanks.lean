module

public import Unfoldings.Cap.StripCircleInterval

/-! Every nonempty strip-circle interval reaches both actual approached banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- Actual physical heights and distinct developed endpoints of a nonempty circle slice. -/
structure BankCircleSlice (G : ℂ → ℂ) (center : ℂ) (cutoff radius : ℝ) where
  lowerHeight : ℝ
  upperHeight : ℝ
  lower_bounds : lowerHeight ∈ Set.Icc 0 cutoff
  upper_bounds : upperHeight ∈ Set.Icc 0 cutoff
  lower_closed : S.lower.point lowerHeight ∈ closure
    {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
  upper_closed : S.upper.point upperHeight ∈ closure
    {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
  lower_radius : ‖G (S.lower.point lowerHeight) - center‖ = radius
  upper_radius : ‖G (S.upper.point upperHeight) - center‖ = radius
  distinct : G (S.lower.point lowerHeight) ≠ G (S.upper.point upperHeight)
  interval : quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) =
    Set.Ioo
      (min (G (S.lower.point lowerHeight) - center).re
        (G (S.upper.point upperHeight) - center).re)
      (max (G (S.lower.point lowerHeight) - center).re
        (G (S.upper.point upperHeight) - center).re)

/-- Excluding the approached physical ends leaves only actual bank points on the
developed frontier. The closure membership is retained for terminal pinches. -/
theorem frontier_circle_bank_points {G : ℂ → ℂ} (continuous : Continuous G)
    (center : ℂ) (cutoff radius : ℝ)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}))
    (ends_avoid : ∀ z ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff},
      (z.re + z.im = 0 ∨ z.re + z.im = cutoff) → ‖G z - center‖ ≠ radius)
    {y : ℂ} (boundary : y ∈ frontier (G '' S.openSlab 0 cutoff))
    (size : ‖y - center‖ = radius) :
    (∃ h ∈ Set.Icc 0 cutoff,
      S.lower.point h ∈ closure
        {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ∧
      ‖G (S.lower.point h) - center‖ = radius ∧ G (S.lower.point h) = y) ∨
    (∃ h ∈ Set.Icc 0 cutoff,
      S.upper.point h ∈ closure
        {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ∧
      ‖G (S.upper.point h) - center‖ = radius ∧ G (S.upper.point h) = y) := by
  obtain ⟨z, physical, value⟩ :=
    (S.frontier_image_openSlab_eq 0 cutoff continuous injective).subset boundary
  have bounds := (S.closure_openSlab_subset 0 cutoff physical.1).2
  have inside : S.openSlab 0 cutoff ⊆
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono inside physical.1
  have physical_size : ‖G z - center‖ = radius := by rw [value]; exact size
  rcases S.frontier_openSlab_cases 0 cutoff physical with lower | upper | first | last
  · exact Or.inl ⟨z.re + z.im, bounds, lower ▸ closed, lower ▸ physical_size, lower ▸ value⟩
  · exact Or.inr ⟨z.re + z.im, bounds, upper ▸ closed, upper ▸ physical_size, upper ▸ value⟩
  · exact (ends_avoid z closed (Or.inl first) physical_size).elim
  · exact (ends_avoid z closed (Or.inr last) physical_size).elim

/-- A nonempty strip-circle slice cannot have only one bank endpoint. In particular,
an interval's two endpoints cannot be artifacts of arbitrary values on collapsed tails. -/
theorem HasBankCircleInterval.bank_points {G : ℂ → ℂ} (continuous : Continuous G)
    (center : ℂ) (cutoff radius : ℝ) (positive : 0 < radius)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}))
    (quadrant : ∀ z ∈ S.openSlab 0 cutoff,
      0 < (G z - center).re ∧ 0 < (G z - center).im)
    (ends_avoid : ∀ z ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff},
      (z.re + z.im = 0 ∨ z.re + z.im = cutoff) → ‖G z - center‖ ≠ radius)
    (interval : S.HasBankCircleInterval G center cutoff radius)
    (meets : (G '' S.openSlab 0 cutoff ∩ {z | ‖z - center‖ = radius}).Nonempty) :
    (∃ h ∈ Set.Icc 0 cutoff,
      S.lower.point h ∈ closure
        {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ∧
      ‖G (S.lower.point h) - center‖ = radius) ∧
    (∃ h ∈ Set.Icc 0 cutoff,
      S.upper.point h ∈ closure
        {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} ∧
      ‖G (S.upper.point h) - center‖ = radius) := by
  classical
  obtain ⟨lower, upper, at_lower, at_upper, _⟩ := interval
  have inside : S.openSlab 0 cutoff ⊆
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
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
  have slice_nonempty : (quadrantCirclePoint center radius ⁻¹'
      (G '' S.openSlab 0 cutoff)).Nonempty := by
    obtain ⟨z, member, size⟩ := meets
    refine ⟨(z - center).re, ?_⟩
    change quadrantCirclePoint center radius (z - center).re ∈ G '' S.openSlab 0 cutoff
    rwa [quadrantCirclePoint_eq_of_norm center
      ⟨(image_quadrant z member).1.le, (image_quadrant z member).2.le⟩ size]
  have not_single (value : ℂ) :
      ¬ (∀ z ∈ frontier (G '' S.openSlab 0 cutoff),
        ‖z - center‖ = radius → z = value) := by
    intro singleton
    have classification := quadrant_circle_preimage_interval open_image center positive
      image_quadrant value value (fun z boundary size => Or.inl (singleton z boundary size))
    have empty : quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) = ∅ := by
      rcases classification with empty | empty
      · exact empty
      · simpa only [min_self, max_self, Set.Ioo_self] using empty
    rw [empty] at slice_nonempty
    exact Set.not_nonempty_empty slice_nonempty
  constructor
  · by_contra absent
    apply not_single upper
    intro z boundary size
    rcases S.frontier_circle_bank_points continuous center cutoff radius injective ends_avoid
      boundary size with first | last
    · obtain ⟨h, bounds, closed, size, _⟩ := first
      exact (absent ⟨h, bounds, closed, size⟩).elim
    · obtain ⟨h, bounds, closed, size, value⟩ := last
      exact value.symm.trans (at_upper h bounds closed size)
  · by_contra absent
    apply not_single lower
    intro z boundary size
    rcases S.frontier_circle_bank_points continuous center cutoff radius injective ends_avoid
      boundary size with first | last
    · obtain ⟨h, bounds, closed, size, value⟩ := first
      exact value.symm.trans (at_lower h bounds closed size)
    · obtain ⟨h, bounds, closed, size, _⟩ := last
      exact (absent ⟨h, bounds, closed, size⟩).elim

/-- Realize both endpoints of a nonempty interval by actual approached bank heights. -/
theorem HasBankCircleInterval.exists_slice {G : ℂ → ℂ} (continuous : Continuous G)
    (center : ℂ) (cutoff radius : ℝ) (positive : 0 < radius)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}))
    (quadrant : ∀ z ∈ S.openSlab 0 cutoff,
      0 < (G z - center).re ∧ 0 < (G z - center).im)
    (ends_avoid : ∀ z ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff},
      (z.re + z.im = 0 ∨ z.re + z.im = cutoff) → ‖G z - center‖ ≠ radius)
    (interval : S.HasBankCircleInterval G center cutoff radius)
    (meets : (G '' S.openSlab 0 cutoff ∩ {z | ‖z - center‖ = radius}).Nonempty) :
    Nonempty (S.BankCircleSlice G center cutoff radius) := by
  obtain ⟨⟨l, lb, lc, lr⟩, ⟨u, ub, uc, ur⟩⟩ := interval.bank_points S continuous center cutoff
    radius positive injective quadrant ends_avoid meets
  obtain ⟨lower, upper, at_lower, at_upper, slice⟩ := interval
  rw [← at_lower l lb lc lr, ← at_upper u ub uc ur] at slice
  have slice_nonempty : (quadrantCirclePoint center radius ⁻¹'
      (G '' S.openSlab 0 cutoff)).Nonempty := by
    obtain ⟨z, ⟨p, member, value⟩, size⟩ := meets
    refine ⟨(z - center).re, ?_⟩
    change quadrantCirclePoint center radius (z - center).re ∈ G '' S.openSlab 0 cutoff
    have quarters := quadrant p member
    rw [value] at quarters
    rw [quadrantCirclePoint_eq_of_norm center ⟨quarters.1.le, quarters.2.le⟩ size]
    exact ⟨p, member, value⟩
  have actual_interval := slice.resolve_left (fun empty => by
    rw [empty] at slice_nonempty
    exact Set.not_nonempty_empty slice_nonempty)
  have distinct : G (S.lower.point l) ≠ G (S.upper.point u) := by
    intro equal
    rw [actual_interval, equal, min_self, max_self, Set.Ioo_self] at slice_nonempty
    exact Set.not_nonempty_empty slice_nonempty
  exact ⟨⟨l, u, lb, ub, lc, uc, lr, ur, distinct, actual_interval⟩⟩

end Unfoldings.MonotoneStrip
