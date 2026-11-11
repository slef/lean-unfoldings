module

public import Unfoldings.Geometry.StrictHeightGraphs

/-! Actual waterfall connectors progress strictly in both coordinates, even at bank targets. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem interiorConnector_strictCoordinatesOn (p : ℂ) {s : Set ℝ}
    (first : S.lower.StrictCoordinatesOn s) (last : S.upper.StrictCoordinatesOn s) :
    (S.interiorConnector p).StrictCoordinatesOn s := by
  constructor
  · intro a ha b hb ordered
    have low : Max.max (S.lower.coordinate a) (a - p.im) <
        Max.max (S.lower.coordinate b) (b - p.im) :=
      max_lt_max (first.1 ha hb ordered) (sub_lt_sub_right ordered _)
    have high : Min.min (S.upper.coordinate a) p.re ≤
        Min.min (S.upper.coordinate b) p.re :=
      min_le_min (S.upper.coordinate_mono ordered.le) le_rfl
    change (Max.max (S.lower.coordinate a) (a - p.im) +
      Min.min (S.upper.coordinate a) p.re) / 2 <
        (Max.max (S.lower.coordinate b) (b - p.im) +
          Min.min (S.upper.coordinate b) p.re) / 2
    linarith
  · intro a ha b hb ordered
    have low : Min.min (a - S.lower.coordinate a) p.im ≤
        Min.min (b - S.lower.coordinate b) p.im :=
      min_le_min (S.lower.complement_mono ordered.le) le_rfl
    have high : Max.max (a - S.upper.coordinate a) (a - p.re) <
        Max.max (b - S.upper.coordinate b) (b - p.re) :=
      max_lt_max (last.2 ha hb ordered) (sub_lt_sub_right ordered _)
    have formula (h : ℝ) : h - (S.interiorConnector p).coordinate h =
        (Min.min (h - S.lower.coordinate h) p.im +
          Max.max (h - S.upper.coordinate h) (h - p.re)) / 2 := by
      change h - (Max.max (S.lower.coordinate h) (h - p.im) +
        Min.min (S.upper.coordinate h) p.re) / 2 = _
      have left_identity : Min.min (h - S.lower.coordinate h) p.im =
          h - Max.max (S.lower.coordinate h) (h - p.im) := by
        rw [← min_sub_sub_left, sub_sub_cancel]
      rw [left_identity, max_sub_sub_left]
      ring
    change a - (S.interiorConnector p).coordinate a <
      b - (S.interiorConnector p).coordinate b
    rw [formula, formula]
    linarith

/-- Before the target, strict walls make the connector strictly internal wherever width is
positive. The target itself may lie on an exterior bank. -/
theorem interiorConnector_strict_before_target {p : ℂ} (member : p ∈ S.carrier)
    {a h : ℝ} (first : S.lower.StrictCoordinatesOn (Set.Icc a (p.re + p.im)))
    (last : S.upper.StrictCoordinatesOn (Set.Icc a (p.re + p.im)))
    (start : a ≤ h) (before : h < p.re + p.im)
    (width : S.lower.coordinate h < S.upper.coordinate h) :
    S.lower.coordinate h < (S.interiorConnector p).coordinate h ∧
      (S.interiorConnector p).coordinate h < S.upper.coordinate h := by
  have low : S.lower.coordinate h < p.re :=
    (first.1 ⟨start, before.le⟩ ⟨start.trans before.le, le_rfl⟩ before).trans_le member.1
  have high : h - p.im < S.upper.coordinate h := by
    have bound := last.2 ⟨start, before.le⟩ ⟨start.trans before.le, le_rfl⟩ before
    linarith [member.2]
  have left_low := le_max_left (S.lower.coordinate h) (h - p.im)
  have left_high := max_lt width high
  have right_low := lt_min width low
  have right_high := min_le_left (S.upper.coordinate h) p.re
  change S.lower.coordinate h <
    (Max.max (S.lower.coordinate h) (h - p.im) + Min.min (S.upper.coordinate h) p.re) / 2 ∧ _
  constructor
  · linarith
  · change (Max.max (S.lower.coordinate h) (h - p.im) +
      Min.min (S.upper.coordinate h) p.re) / 2 < S.upper.coordinate h
    linarith

theorem insertionGraph_strictCoordinatesOn (p : ℂ) (member : p ∈ S.carrier)
    (tail : MonotoneHeightGraph) (at_target : tail.coordinate (p.re + p.im) = p.re)
    {a b : ℝ} (start : a ≤ p.re + p.im) (finish : p.re + p.im ≤ b)
    (first : S.lower.StrictCoordinatesOn (Set.Icc a b))
    (last : S.upper.StrictCoordinatesOn (Set.Icc a b))
    (strict_tail : tail.StrictCoordinatesOn (Set.Icc (p.re + p.im) b)) :
    (S.insertionGraph p member tail at_target).StrictCoordinatesOn (Set.Icc a b) := by
  apply MonotoneHeightGraph.strictCoordinatesOn_splice _ _ (by
    rw [S.interiorConnector_target member]
    exact ((S.lower.clamp_eq S.upper tail
      (at_target.symm ▸ member.1) (at_target.symm ▸ member.2)).trans at_target).symm)
  · exact S.interiorConnector_strictCoordinatesOn p
      (first.mono (Set.Icc_subset_Icc_right finish))
      (last.mono (Set.Icc_subset_Icc_right finish))
  · exact MonotoneHeightGraph.strictCoordinatesOn_max _ _
      (first.mono (Set.Icc_subset_Icc_left start))
      (MonotoneHeightGraph.strictCoordinatesOn_min _ _
        (last.mono (Set.Icc_subset_Icc_left start)) strict_tail)
  · exact start
  · exact finish

end Unfoldings.MonotoneStrip
