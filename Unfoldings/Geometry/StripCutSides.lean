module

public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! Positive strip width and local cut avoidance determine the side of an approached cut. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

open Filter Topology

variable (S : MonotoneStrip) (H : MonotoneHeightGraph)

/-- A cut touching the lower wall cannot enter the strip near a positive-width point.
It may only touch the wall: coincidence of the wall with the cut is unnecessary. -/
theorem cut_below_lower_locally {a b h : ℝ} (inside : h ∈ Set.Ioo a b)
    (touch : H.coordinate h = S.lower.coordinate h)
    (width : S.lower.coordinate h < S.upper.coordinate h)
    (avoids : ∀ k ∈ Set.Ioo a b, H.point k ∉ S.strictCarrier) :
    ∃ c d, h ∈ Set.Ioo c d ∧ Set.Ioo c d ⊆ Set.Ioo a b ∧
      ∀ k ∈ Set.Ioo c d, H.coordinate k ≤ S.lower.coordinate k := by
  have before : ∀ᶠ k in 𝓝 h, H.coordinate k < S.upper.coordinate k :=
    (H.continuous.continuousAt.sub S.upper.continuous.continuousAt).eventually
      (gt_mem_nhds (show H.coordinate h - S.upper.coordinate h < 0 by rw [touch]; linarith))
      |>.mono (fun _ bound => sub_neg.mp bound)
  have near : ∀ᶠ k in 𝓝 h, k ∈ Set.Ioo a b := isOpen_Ioo.mem_nhds inside
  have side : ∀ᶠ k in 𝓝 h, k ∈ Set.Ioo a b ∧ H.coordinate k ≤ S.lower.coordinate k := by
    filter_upwards [near, before] with k member less
    refine ⟨member, le_of_not_gt ?_⟩
    intro greater
    apply avoids k member
    change S.lower.coordinate ((H.point k).re + (H.point k).im) < (H.point k).re ∧
      (H.point k).re < S.upper.coordinate ((H.point k).re + (H.point k).im)
    rw [H.point_height]
    exact ⟨greater, less⟩
  obtain ⟨r, positive, bound⟩ := Metric.eventually_nhds_iff.mp side
  have close {k : ℝ} (member : k ∈ Set.Ioo (h - r) (h + r)) : dist k h < r := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [member.1, member.2]
  exact ⟨h - r, h + r, ⟨by linarith, by linarith⟩,
    fun _ member => (bound (close member)).1, fun _ member => (bound (close member)).2⟩

theorem cut_above_upper_locally {a b h : ℝ} (inside : h ∈ Set.Ioo a b)
    (touch : H.coordinate h = S.upper.coordinate h)
    (width : S.lower.coordinate h < S.upper.coordinate h)
    (avoids : ∀ k ∈ Set.Ioo a b, H.point k ∉ S.strictCarrier) :
    ∃ c d, h ∈ Set.Ioo c d ∧ Set.Ioo c d ⊆ Set.Ioo a b ∧
      ∀ k ∈ Set.Ioo c d, S.upper.coordinate k ≤ H.coordinate k := by
  have after : ∀ᶠ k in 𝓝 h, S.lower.coordinate k < H.coordinate k :=
    (S.lower.continuous.continuousAt.sub H.continuous.continuousAt).eventually
      (gt_mem_nhds (show S.lower.coordinate h - H.coordinate h < 0 by rw [touch]; linarith))
      |>.mono (fun _ bound => sub_neg.mp bound)
  have near : ∀ᶠ k in 𝓝 h, k ∈ Set.Ioo a b := isOpen_Ioo.mem_nhds inside
  have side : ∀ᶠ k in 𝓝 h, k ∈ Set.Ioo a b ∧ S.upper.coordinate k ≤ H.coordinate k := by
    filter_upwards [near, after] with k member greater
    refine ⟨member, le_of_not_gt ?_⟩
    intro less
    apply avoids k member
    change S.lower.coordinate ((H.point k).re + (H.point k).im) < (H.point k).re ∧
      (H.point k).re < S.upper.coordinate ((H.point k).re + (H.point k).im)
    rw [H.point_height]
    exact ⟨greater, less⟩
  obtain ⟨r, positive, bound⟩ := Metric.eventually_nhds_iff.mp side
  have close {k : ℝ} (member : k ∈ Set.Ioo (h - r) (h + r)) : dist k h < r := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [member.1, member.2]
  exact ⟨h - r, h + r, ⟨by linarith, by linarith⟩,
    fun _ member => (bound (close member)).1, fun _ member => (bound (close member)).2⟩

end Unfoldings.MonotoneStrip
