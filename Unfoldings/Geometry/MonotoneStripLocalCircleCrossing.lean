module

public import Unfoldings.Geometry.MonotoneStripTopology
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FunProp

/-! A strict radial crossing along an active bank gives an actual interior circle point. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

/-- The local positive-width hypothesis replaces any exclusion of exceptional pinch radii. -/
theorem circle_image_nonempty_of_local_bank_crossing (S : MonotoneStrip)
    {G : ℂ → ℂ} (continuous : Continuous G) (center : ℂ) (H : MonotoneHeightGraph)
    (wall : H = S.lower ∨ H = S.upper) {a b cutoff radius : ℝ}
    (ordered : a ≤ b) (positive : 0 < a) (before_end : b < cutoff)
    (width : ∀ h ∈ Set.Icc a b, S.lower.coordinate h < S.upper.coordinate h)
    (first : ‖G (H.point a) - center‖ < radius)
    (last : radius < ‖G (H.point b) - center‖) :
    (G '' S.openSlab 0 cutoff ∩ {z | ‖z - center‖ = radius}).Nonempty := by
  let blend (h weight : ℝ) : ℂ :=
    ⟨(1 - weight) * S.lower.coordinate h + weight * S.upper.coordinate h,
      h - ((1 - weight) * S.lower.coordinate h + weight * S.upper.coordinate h)⟩
  have blend_height (h weight : ℝ) : (blend h weight).re + (blend h weight).im = h := by
    dsimp only [blend]
    ring
  have lower_continuous := S.lower.continuous
  have upper_continuous := S.upper.continuous
  have blend_h_continuous (weight : ℝ) : Continuous (fun h => blend h weight) := by
    have parts : Continuous (fun h : ℝ =>
        (((1 - weight) * S.lower.coordinate h + weight * S.upper.coordinate h : ℝ) : ℂ) +
          ((h - ((1 - weight) * S.lower.coordinate h + weight * S.upper.coordinate h) : ℝ) : ℂ) *
            Complex.I) := by fun_prop
    convert parts using 1
    funext h
    apply Complex.ext <;> simp [blend]
  have blend_weight_continuous (h : ℝ) : Continuous (blend h) := by
    have parts : Continuous (fun weight : ℝ =>
        (((1 - weight) * S.lower.coordinate h + weight * S.upper.coordinate h : ℝ) : ℂ) +
          ((h - ((1 - weight) * S.lower.coordinate h + weight * S.upper.coordinate h) : ℝ) : ℂ) *
            Complex.I) := by fun_prop
    convert parts using 1
    funext weight
    apply Complex.ext <;> simp [blend]
  obtain ⟨k, approached, at_a, at_b⟩ : ∃ k ∈ closure (Set.Ioo (0 : ℝ) 1),
      blend a k = H.point a ∧ blend b k = H.point b := by
    rcases wall with rfl | rfl
    · refine ⟨0, ?_, ?_, ?_⟩
      · rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
        exact ⟨le_rfl, zero_le_one⟩
      · simp [blend, MonotoneHeightGraph.point]
      · simp [blend, MonotoneHeightGraph.point]
    · refine ⟨1, ?_, ?_, ?_⟩
      · rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
        exact ⟨zero_le_one, le_rfl⟩
      · simp [blend, MonotoneHeightGraph.point]
      · simp [blend, MonotoneHeightGraph.point]
  let V := {weight : ℝ | ‖G (blend a weight) - center‖ < radius ∧
    radius < ‖G (blend b weight) - center‖}
  have opened : IsOpen V :=
    (isOpen_lt (((continuous.comp (blend_weight_continuous a)).sub continuous_const).norm)
      continuous_const).inter
      (isOpen_lt continuous_const
        (((continuous.comp (blend_weight_continuous b)).sub continuous_const).norm))
  have at_k : k ∈ V := by
    change ‖G (blend a k) - center‖ < radius ∧ radius < ‖G (blend b k) - center‖
    rw [at_a, at_b]
    exact ⟨first, last⟩
  obtain ⟨weight, active, bounds⟩ := (mem_closure_iff.mp approached) V opened at_k
  have radial_continuous : Continuous (fun h => ‖G (blend h weight) - center‖) :=
    ((continuous.comp (blend_h_continuous weight)).sub continuous_const).norm
  obtain ⟨h, slab, size⟩ := intermediate_value_Icc ordered radial_continuous.continuousOn
    ⟨active.1.le, active.2.le⟩
  refine ⟨G (blend h weight), ⟨blend h weight, ?_, rfl⟩, size⟩
  refine ⟨?_, ?_⟩
  · change S.lower.coordinate ((blend h weight).re + (blend h weight).im) < (blend h weight).re ∧
      (blend h weight).re < S.upper.coordinate ((blend h weight).re + (blend h weight).im)
    rw [blend_height]
    have gap := width h slab
    have lower := mul_pos bounds.1 (sub_pos.mpr gap)
    have upper := mul_pos (sub_pos.mpr bounds.2) (sub_pos.mpr gap)
    dsimp only [blend]
    constructor <;> nlinarith
  · rw [blend_height]
    exact ⟨positive.trans_le slab.1, slab.2.trans_lt before_end⟩

end Unfoldings.MonotoneStrip
