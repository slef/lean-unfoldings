module

public import Unfoldings.Geometry.MonotoneStripTopology
public import Unfoldings.Geometry.SubdivisionWallContacts
public import Mathlib.Topology.Order.Compact

/-! A nonempty strip whose approached closure stops before the cutoff has a terminal pinch. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem average_point_mem_openSlab {a b h : ℝ} (height : h ∈ Set.Ioo a b)
    (width : S.lower.coordinate h < S.upper.coordinate h) :
    (S.lower.average S.upper).point h ∈ S.openSlab a b := by
  have point_height := (S.lower.average S.upper).point_height h
  constructor
  · change S.lower.coordinate _ < ((S.lower.average S.upper).point h).re ∧
      ((S.lower.average S.upper).point h).re < S.upper.coordinate _
    rw [point_height]
    change S.lower.coordinate h < (S.lower.coordinate h + S.upper.coordinate h) / 2 ∧
      (S.lower.coordinate h + S.upper.coordinate h) / 2 < S.upper.coordinate h
    constructor <;> linarith
  · rwa [point_height]

theorem exists_terminal_pinch {cutoff : ℝ} (nonempty : (S.openSlab 0 cutoff).Nonempty)
    (no_cutoff : ∀ z ∈ closure (S.openSlab 0 cutoff), z.re + z.im ≠ cutoff) :
    ∃ h ∈ Set.Ioo (0 : ℝ) cutoff,
      (∀ k ∈ Set.Icc h cutoff, S.lower.coordinate k = S.upper.coordinate k) ∧
      S.lower.point h ∈ closure (S.openSlab 0 cutoff) ∧
      S.upper.point h ∈ closure (S.openSlab 0 cutoff) ∧
      ∀ z ∈ closure (S.openSlab 0 cutoff), z.re + z.im ≤ h := by
  obtain ⟨q, closed, maximum⟩ := (S.isCompact_closure_openSlab 0 cutoff).exists_isMaxOn
    nonempty.closure (Complex.continuous_re.add Complex.continuous_im).continuousOn
  obtain ⟨p, member⟩ := nonempty
  let h := q.re + q.im
  have positive : 0 < h := member.2.1.trans_le (maximum (subset_closure member))
  have bounded := S.closure_openSlab_subset 0 cutoff closed
  have before : h < cutoff := lt_of_le_of_ne bounded.2.2 (no_cutoff q closed)
  have collapsed : S.lower.coordinate h = S.upper.coordinate h := by
    apply le_antisymm (S.ordered h)
    by_contra nonpositive
    have width : S.lower.coordinate h < S.upper.coordinate h := lt_of_not_ge nonpositive
    let m := (S.lower.average S.upper).point h
    have m_member := S.average_point_mem_openSlab ⟨positive, before⟩ width
    obtain ⟨δ, δpositive, ball⟩ := Metric.isOpen_iff.mp (S.isOpen_openSlab 0 cutoff) m m_member
    let z := m + ((δ / 2 : ℝ) : ℂ)
    have near : z ∈ Metric.ball m δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖m + ((δ / 2 : ℝ) : ℂ) - m‖ < δ
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos δpositive (by norm_num))]
      linarith
    have upper := maximum (subset_closure (ball near))
    change z.re + z.im ≤ q.re + q.im at upper
    have height : m.re + m.im = h := (S.lower.average S.upper).point_height h
    change (m + ((δ / 2 : ℝ) : ℂ)).re + (m + ((δ / 2 : ℝ) : ℂ)).im ≤ h at upper
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      add_zero] at upper
    linarith
  have after : ∀ k ∈ Set.Ioo h cutoff, S.lower.coordinate k = S.upper.coordinate k := by
    intro k within
    apply le_antisymm (S.ordered k)
    by_contra nonpositive
    have member := S.average_point_mem_openSlab ⟨positive.trans within.1, within.2⟩
      (lt_of_not_ge nonpositive)
    have upper := maximum (subset_closure member)
    change ((S.lower.average S.upper).point k).re +
      ((S.lower.average S.upper).point k).im ≤ h at upper
    rw [(S.lower.average S.upper).point_height] at upper
    exact (not_le_of_gt within.1) upper
  have all : Set.Icc h cutoff ⊆ {k | S.lower.coordinate k = S.upper.coordinate k} := by
    rw [← closure_Ioo before.ne]
    exact closure_minimal after (isClosed_eq S.lower.continuous S.upper.continuous)
  have lower_point : S.lower.point h = q := S.lower.point_eq_of_coordinate q
    (le_antisymm bounded.1.1 (bounded.1.2.trans_eq collapsed.symm))
  have upper_point : S.upper.point h = q := by
    rw [← S.lower.point_eq_of_same_coordinate S.upper collapsed]
    exact lower_point
  exact ⟨h, ⟨positive, before⟩, fun k member => all member,
    lower_point.symm ▸ closed, upper_point.symm ▸ closed, fun _ member => maximum member⟩

end Unfoldings.MonotoneStrip
