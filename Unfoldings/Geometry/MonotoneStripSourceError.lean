module

public import Unfoldings.Geometry.FiniteSelectionError
public import Unfoldings.Geometry.MonotoneStripCore
public import Unfoldings.Geometry.RecoverableStripPinches

/-! Source-based position control on a whole strip, with coherent values at its pinches. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem inset_source_mem (ε : ℝ) (first : S.lower.coordinate 0 = 0)
    (last : S.upper.coordinate 0 = 0) : (0 : ℂ) ∈ (S.inset ε).carrier := by
  constructor
  · change Min.min (S.lower.coordinate (0 + 0) + ε)
      ((S.lower.coordinate (0 + 0) + S.upper.coordinate (0 + 0)) / 2) ≤ 0
    rw [zero_add, first, last]
    simpa only [zero_add, zero_div] using min_le_right ε (0 : ℝ)
  · change (0 : ℝ) ≤ Max.max (S.upper.coordinate (0 + 0) + -ε)
      ((S.lower.coordinate (0 + 0) + S.upper.coordinate (0 + 0)) / 2)
    rw [zero_add, first, last]
    simpa only [zero_add, zero_div] using le_max_right (-ε) (0 : ℝ)

theorem carrier_coordinates_nonnegative (first : S.lower.coordinate 0 = 0)
    (last : S.upper.coordinate 0 = 0) {z : ℂ} (member : z ∈ S.carrier)
    (forward : 0 ≤ z.re + z.im) : 0 ≤ z.re ∧ 0 ≤ z.im := by
  have lower := S.lower.coordinate_mono forward
  have upper := S.upper.complement_mono forward
  rw [first] at lower
  change 0 - S.upper.coordinate 0 ≤ z.re + z.im - S.upper.coordinate (z.re + z.im) at upper
  rw [last, sub_self] at upper
  exact ⟨lower.trans member.1, by linarith [member.2]⟩

/-- A uniformly small linear error of the actual affine branches gives a source-based
position estimate independent of the number of faces or branch switches. -/
theorem error_from_source_of_core_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) {c b : ℝ}
    (nonnegative : 0 ≤ c) (first : S.lower.coordinate 0 = 0)
    (last : S.upper.coordinate 0 = 0)
    (linear_error : ∀ i z, ‖(A i).linear z - z‖ ≤ c * ‖z‖)
    {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc 0 b})
    (selection : ∀ z, z ∈ S.coreCarrier → z.re + z.im ∈ Set.Icc 0 b → ∃ i, F z = A i z)
    {q : ℂ} (member : q ∈ S.strictCarrier) (slab : q.re + q.im ∈ Set.Icc 0 b) :
    ‖(F q - F 0) - q‖ ≤ 2 * c * (q.re + q.im) := by
  have coordinates := S.carrier_coordinates_nonnegative first last
    ⟨member.1.le, member.2.le⟩ slab.1
  have gap : 0 < min (q.re - S.lower.coordinate (q.re + q.im))
      (S.upper.coordinate (q.re + q.im) - q.re) :=
    lt_min (sub_pos.mpr member.1) (sub_pos.mpr member.2)
  obtain ⟨ε, positive, small⟩ := exists_between gap
  have q_inset : q ∈ (S.inset ε).carrier := S.mem_inset
    (small.le.trans (min_le_left _ _)) (small.le.trans (min_le_right _ _))
  let P := (S.inset ε).increasingPath (S.inset_source_mem ε first last) q_inset
    coordinates.1 coordinates.2
  have horizontal : Monotone (fun t => (P t).re) :=
    (S.inset ε).increasingPath_re_mono _ _ _ _
  have vertical : Monotone (fun t => (P t).im) :=
    (S.inset ε).increasingPath_im_mono _ _ _ _
  have inside (t : unitInterval) :
      P t ∈ S.coreCarrier ∧ (P t).re + (P t).im ∈ Set.Icc 0 b := by
    refine ⟨S.inset_subset_core positive
      ((S.inset ε).increasingPath_mem _ _ _ _ t), ?_⟩
    have first_re := horizontal (show (0 : unitInterval) ≤ t from t.property.1)
    have first_im := vertical (show (0 : unitInterval) ≤ t from t.property.1)
    have last_re := horizontal (show t ≤ (1 : unitInterval) from t.property.2)
    have last_im := vertical (show t ≤ (1 : unitInterval) from t.property.2)
    simp only [Path.source, Path.target] at first_re first_im last_re last_im
    simp only [Complex.zero_re, Complex.zero_im] at first_re first_im
    exact ⟨by linarith, (add_le_add last_re last_im).trans slab.2⟩
  have bound := finite_selection_error_along_path (fun i => A i) continuous c
    (fun i _ _ horizontal vertical => affine_near_identity_cone_error (A i) nonnegative
      (linear_error i) horizontal vertical) P
    (Fcontinuous.comp_continuous P.continuous inside)
    (fun t => selection (P t) (inside t).1 (inside t).2) horizontal vertical
  simp only [Complex.zero_re, Complex.zero_im, zero_add, sub_zero] at bound
  have expression : (F q - q) - F 0 = (F q - F 0) - q := by abel
  rwa [expression] at bound

/-- Permanently merged banks are excluded from the continuity hypotheses. Only the coherent
pinches preceding the chosen positive-width endpoint are used in the source comparison. -/
theorem error_from_source_of_recoverable_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) {c b : ℝ}
    (nonnegative : 0 ≤ c) (first : S.lower.coordinate 0 = 0)
    (last : S.upper.coordinate 0 = 0)
    (linear_error : ∀ i z, ‖(A i).linear z - z‖ ≤ c * ‖z‖)
    (E : Set ℂ) (pinches : S.RecoverablePinchesIn E 0 b) {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧
      z.re + z.im ∈ Set.Icc 0 b})
    (selection : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
      z.re + z.im ∈ Set.Icc 0 b → ∃ i, F z = A i z)
    {q : ℂ} (member : q ∈ S.strictCarrier) (slab : q.re + q.im ∈ Set.Icc 0 b) :
    ‖(F q - F 0) - q‖ ≤ 2 * c * (q.re + q.im) := by
  have inside : {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc 0 (q.re + q.im)} ⊆
      {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧ z.re + z.im ∈ Set.Icc 0 b} := by
    intro z hz
    have height : z.re + z.im ∈ Set.Icc 0 b := ⟨hz.2.1, hz.2.2.trans slab.2⟩
    refine ⟨?_, height⟩
    rcases hz.1.2 with strict | collapsed
    · exact Or.inl strict
    · have coherent := pinches _ height collapsed _ ⟨hz.2.2, slab.2⟩
        (member.1.trans member.2)
      have point : S.lower.point (z.re + z.im) = z := S.lower.point_eq_of_coordinate z
        (le_antisymm hz.1.1.1 (hz.1.1.2.trans_eq collapsed.symm))
      exact Or.inr (point ▸ coherent)
  exact S.error_from_source_of_core_selection A continuous nonnegative first last linear_error
    (Fcontinuous.mono inside)
    (fun z member height => selection z (inside ⟨member, height⟩).1 (inside ⟨member, height⟩).2)
    member ⟨slab.1, le_rfl⟩

end Unfoldings.MonotoneStrip
