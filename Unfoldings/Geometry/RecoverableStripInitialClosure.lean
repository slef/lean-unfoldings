module

public import Unfoldings.Geometry.RecoverableStripClosure
public import Unfoldings.Geometry.MonotoneStripTopology

/-! The approached part of a finitely pinched strip contains every earlier carrier point. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem carrier_mem_closure_of_bank_points {z : ℂ} {a b : ℝ}
    (member : z ∈ S.carrier) (slab : z.re + z.im ∈ Set.Icc a b)
    (banks : S.lower.point (z.re + z.im) ∈ closure
        {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b} ∧
      S.upper.point (z.re + z.im) ∈ closure
        {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b}) :
    z ∈ closure {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b} := by
  rcases member.1.eq_or_lt with lower | lower
  · have point : S.lower.point (z.re + z.im) = z := by
      apply Complex.ext
      · exact lower
      · change z.re + z.im - S.lower.coordinate (z.re + z.im) = z.im
        rw [lower]
        ring
    exact point ▸ banks.1
  · rcases member.2.eq_or_lt with upper | upper
    · have point : S.upper.point (z.re + z.im) = z := by
        apply Complex.ext
        · exact upper.symm
        · change z.re + z.im - S.upper.coordinate (z.re + z.im) = z.im
          rw [← upper]
          ring
      exact point ▸ banks.2
    · exact subset_closure ⟨⟨lower, upper⟩, slab⟩

/-- Finite recoverable pinches exclude an interval of zero width before a later
active height. Consequently every carrier point before that height is approached. -/
theorem carrier_mem_closure_before_active_height {E : Set ℂ} (finite : E.Finite)
    {a k b : ℝ} (pinches : S.RecoverablePinchesIn E a b) (start : a < k) (finish : k ≤ b)
    (width : S.lower.coordinate k < S.upper.coordinate k)
    {z : ℂ} (member : z ∈ S.carrier) (slab : z.re + z.im ∈ Set.Icc a k) :
    z ∈ closure {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b} := by
  exact S.carrier_mem_closure_of_bank_points member ⟨slab.1, slab.2.trans finish⟩
    (S.bank_points_mem_closure_before_active_height finite pinches start finish width _ slab)

/-- An approached endpoint supplies all smaller heights, including when no
active strip point lies beyond the endpoint itself. -/
theorem carrier_mem_closure_before_closed_height {E : Set ℂ} (finite : E.Finite)
    {a b : ℝ} (pinches : S.RecoverablePinchesIn E a b)
    {q z : ℂ} (endpoint : q ∈ closure
      {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b})
    (member : z ∈ S.carrier) (slab : z.re + z.im ∈ Set.Icc a (q.re + q.im)) :
    z ∈ closure {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b} := by
  have bounded : closure {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b} ⊆
      S.boundedCarrier a b := closure_minimal
    (fun _ inside => ⟨⟨inside.1.1.le, inside.1.2.le⟩, inside.2⟩)
    (S.isClosed_boundedCarrier a b)
  have q_bounds := bounded endpoint
  rcases slab.2.eq_or_lt with same | before
  · by_cases width : S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im)
    · exact S.carrier_mem_closure_of_bank_points member ⟨slab.1, same.le.trans q_bounds.2.2⟩
        (S.bank_points_mem_closure_of_width ⟨slab.1, same.le.trans q_bounds.2.2⟩ width)
    · have collapsed : S.lower.coordinate (z.re + z.im) = S.upper.coordinate (z.re + z.im) :=
        le_antisymm (S.ordered _) (le_of_not_gt width)
      have q_carrier := q_bounds.1
      change S.lower.coordinate (q.re + q.im) ≤ q.re ∧
        q.re ≤ S.upper.coordinate (q.re + q.im) at q_carrier
      rw [← same, ← collapsed] at q_carrier
      have equal : z = q := by
        apply Complex.ext
        · linarith [member.1, member.2, q_carrier.1, q_carrier.2]
        · linarith [member.1, member.2, q_carrier.1, q_carrier.2]
      exact equal ▸ endpoint
  · have opened : IsOpen {w : ℂ | z.re + z.im < w.re + w.im} :=
      isOpen_lt continuous_const (Complex.continuous_re.add Complex.continuous_im)
    obtain ⟨active, above, strict, within⟩ := (mem_closure_iff.mp endpoint)
      {w : ℂ | z.re + z.im < w.re + w.im} opened before
    exact S.carrier_mem_closure_before_active_height finite pinches
      (slab.1.trans_lt above) within.2 (strict.1.trans strict.2) member ⟨slab.1, above.le⟩

end Unfoldings.MonotoneStrip
