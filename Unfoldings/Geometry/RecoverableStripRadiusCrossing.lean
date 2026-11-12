module

public import Unfoldings.Geometry.MonotoneStripCore
public import Unfoldings.Geometry.MonotoneStripSlab
public import Unfoldings.Geometry.MonotoneStripTopology
public import Unfoldings.Geometry.RecoverableStripClosure
public import Mathlib.Topology.Order.IntermediateValue

/-! A source-to-strip core path crosses every intermediate radius away from coherent pinches. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- Inset paths lie strictly inside the strip except at recoverable pinches.
An exceptional pinch radius cannot therefore hide a whole intermediate circle slice. -/
theorem circle_image_nonempty_of_avoiding_pinches {E : Set ℂ} {G : ℂ → ℂ}
    {center : ℂ} {cutoff radius : ℝ}
    (first_source : S.lower.coordinate 0 = 0) (last_source : S.upper.coordinate 0 = 0)
    (pinches : S.RecoverablePinchesIn E 0 cutoff) (continuous : Continuous G)
    (source_value : G 0 = center) (radius_positive : 0 < radius)
    (outside : radius ∉ (fun z => ‖G z - center‖) '' E)
    {q : ℂ} (member : q ∈ S.openSlab 0 cutoff) (far : radius ≤ ‖G q - center‖) :
    (G '' S.openSlab 0 cutoff ∩ {z | ‖z - center‖ = radius}).Nonempty := by
  have horizontal : 0 ≤ q.re := by
    have bound := S.lower.coordinate_mono member.2.1.le
    rw [first_source] at bound
    exact bound.trans member.1.1.le
  have vertical : 0 ≤ q.im := by
    have bound := S.upper.complement_mono member.2.1.le
    change 0 - S.upper.coordinate 0 ≤ q.re + q.im - S.upper.coordinate (q.re + q.im) at bound
    rw [last_source, sub_self] at bound
    linarith [member.1.2]
  have gap : 0 < min (q.re - S.lower.coordinate (q.re + q.im))
      (S.upper.coordinate (q.re + q.im) - q.re) :=
    lt_min (sub_pos.mpr member.1.1) (sub_pos.mpr member.1.2)
  obtain ⟨ε, εpositive, εsmall⟩ := exists_between gap
  have at_source : (0 : ℂ) ∈ (S.inset ε).carrier := by
    simp only [carrier, Set.mem_ofPred_eq, Complex.zero_re, Complex.zero_im, zero_add]
    change min (S.lower.coordinate 0 + ε)
        ((S.lower.coordinate 0 + S.upper.coordinate 0) / 2) ≤ (0 : ℝ) ∧
      (0 : ℝ) ≤ max (S.upper.coordinate 0 + -ε)
        ((S.lower.coordinate 0 + S.upper.coordinate 0) / 2)
    rw [first_source, last_source]
    simp only [zero_add, add_zero, zero_div]
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  have at_target : q ∈ (S.inset ε).carrier :=
    S.mem_inset (εsmall.le.trans (min_le_left _ _)) (εsmall.le.trans (min_le_right _ _))
  let P := (S.inset ε).increasingPath at_source at_target horizontal vertical
  have bounded (s : unitInterval) : P s ∈ (S.inset ε).boundedCarrier 0 (q.re + q.im) :=
    (S.inset ε).increasingPath_mem_bounded
      ⟨at_source, by
        simpa only [Complex.zero_re, Complex.zero_im, zero_add] using
          (show (0 : ℝ) ∈ Set.Icc 0 (q.re + q.im) from ⟨le_rfl, member.2.1.le⟩)⟩
      ⟨at_target, member.2.1.le, le_rfl⟩ horizontal vertical s
  let f := fun s : unitInterval => ‖G (P s) - center‖
  have fcontinuous : Continuous f := ((continuous.comp P.continuous).sub continuous_const).norm
  have first : f 0 = 0 := by
    change ‖G (P 0) - center‖ = 0
    rw [P.source, source_value, sub_self, norm_zero]
  have last : radius ≤ f 1 := by
    change radius ≤ ‖G (P 1) - center‖
    rw [P.target]
    exact far
  obtain ⟨s, _, size⟩ := intermediate_value_Icc
    (show (0 : unitInterval) ≤ 1 from zero_le_one) fcontinuous.continuousOn
    ⟨by rw [first]; exact radius_positive.le, last⟩
  have core := S.inset_subset_core εpositive (bounded s).1
  have strict : P s ∈ S.strictCarrier := by
    rcases core.2 with strict | collapsed
    · exact strict
    · have slab : (P s).re + (P s).im ∈ Set.Icc 0 cutoff :=
        ⟨(bounded s).2.1, (bounded s).2.2.trans member.2.2.le⟩
      have coherent := pinches _ slab collapsed (q.re + q.im)
        ⟨(bounded s).2.2, member.2.2.le⟩ (member.1.1.trans member.1.2)
      have point : S.lower.point ((P s).re + (P s).im) = P s :=
        S.lower.point_eq_of_coordinate _
          (le_antisymm core.1.1 (core.1.2.trans_eq collapsed.symm))
      exact (outside ⟨P s, point ▸ coherent, size⟩).elim
  have height : 0 < (P s).re + (P s).im :=
    S.strict_height_pos_of_source first_source last_source strict (bounded s).2.1
  exact ⟨G (P s), ⟨P s, ⟨strict, height, (bounded s).2.2.trans_lt member.2.2⟩, rfl⟩, size⟩

end Unfoldings.MonotoneStrip
