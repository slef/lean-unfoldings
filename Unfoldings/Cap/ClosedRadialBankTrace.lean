module

public import Unfoldings.Cap.RadialBankTraceProperty
public import Unfoldings.Geometry.MonotoneStripTopology
public import Mathlib.Topology.Order.DenselyOrdered

/-! Radial bank progress persists at every approached terminal bank point. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable {S : MonotoneStrip} {G : ℂ → ℂ} {center : ℂ} {cutoff : ℝ}

/-- An approached terminal height admits active strip points above every smaller
height. No active point beyond the terminal height is assumed. -/
theorem active_above_of_bank_mem_closure (H : MonotoneHeightGraph) {h d : ℝ}
    (closed : H.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff})
    (before : d < h) :
    ∃ active ∈ S.strictCarrier, active.re + active.im ∈ Set.Icc 0 cutoff ∧
      d < active.re + active.im := by
  have opened : IsOpen {z : ℂ | d < z.re + z.im} :=
    isOpen_lt continuous_const (Complex.continuous_re.add Complex.continuous_im)
  obtain ⟨active, above, strict, slab⟩ := (mem_closure_iff.mp closed)
    {z : ℂ | d < z.re + z.im} opened (by
      change d < (H.point h).re + (H.point h).im
      rw [H.point_height]
      exact before)
  exact ⟨active, strict, slab, above⟩

/-- Strict radial progress includes a terminal pinch whenever that bank point is
actually approached by the strict strip. Future collapsed tails remain outside this claim. -/
theorem RadialBankTraces.strict_before_closed_height
    (radial : S.RadialBankTraces G center cutoff) (continuous : Continuous G)
    (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper) {a b : ℝ}
    (positive : 0 < a) (before : a < b)
    (closed : H.point b ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}) :
    ‖G (H.point a) - center‖ < ‖G (H.point b) - center‖ := by
  have progress {c d : ℝ} (cpositive : 0 < c) (ordered : c < d) (dbefore : d < b) :
      ‖G (H.point c) - center‖ < ‖G (H.point d) - center‖ := by
    obtain ⟨active, strict, slab, above⟩ := active_above_of_bank_mem_closure H closed dbefore
    have bounds := radial active strict slab c d cpositive ordered above.le
    rcases wall with rfl | rfl
    · exact bounds.1
    · exact bounds.2
  let m := (a + b) / 2
  have am : a < m := by dsimp only [m]; linarith
  have mb : m < b := by dsimp only [m]; linarith
  have initial := progress positive am mb
  have closed_bound : IsClosed {d : ℝ | ‖G (H.point m) - center‖ ≤ ‖G (H.point d) - center‖} :=
    isClosed_le continuous_const
      (((continuous.comp H.point_continuous).sub continuous_const).norm)
  have inside : Set.Ioo m b ⊆ {d : ℝ | ‖G (H.point m) - center‖ ≤ ‖G (H.point d) - center‖} :=
    fun _ member => (progress (positive.trans am) member.1 member.2).le
  have at_b : b ∈ closure (Set.Ioo m b) := by
    rw [closure_Ioo mb.ne]
    exact ⟨mb.le, le_rfl⟩
  exact initial.trans_le (closure_minimal inside closed_bound at_b)

/-- A positive source circle meets the approached portion of either actual bank
at at most one height, including its terminal pinch. -/
theorem RadialBankTraces.closed_bank_circle_height_unique
    (radial : S.RadialBankTraces G center cutoff) (continuous : Continuous G)
    (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper)
    (source_value : G (H.point 0) = center) {a b radius : ℝ}
    (apositive : 0 ≤ a) (bpositive : 0 ≤ b) (positive : 0 < radius)
    (first : H.point a ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff})
    (last : H.point b ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff})
    (first_radius : ‖G (H.point a) - center‖ = radius)
    (last_radius : ‖G (H.point b) - center‖ = radius) : a = b := by
  have a_ne : a ≠ 0 := by
    intro zero
    rw [zero, source_value, sub_self, norm_zero] at first_radius
    exact (ne_of_gt positive) first_radius.symm
  have b_ne : b ≠ 0 := by
    intro zero
    rw [zero, source_value, sub_self, norm_zero] at last_radius
    exact (ne_of_gt positive) last_radius.symm
  rcases lt_trichotomy a b with before | same | after
  · have strict := radial.strict_before_closed_height continuous H wall
      (lt_of_le_of_ne apositive (Ne.symm a_ne)) before last
    rw [first_radius, last_radius] at strict
    exact (lt_irrefl _ strict).elim
  · exact same
  · have strict := radial.strict_before_closed_height continuous H wall
      (lt_of_le_of_ne bpositive (Ne.symm b_ne)) after first
    rw [first_radius, last_radius] at strict
    exact (lt_irrefl _ strict).elim

end Unfoldings.MonotoneStrip
