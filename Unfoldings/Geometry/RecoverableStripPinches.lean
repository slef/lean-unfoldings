module

public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! Track only pinches that can reopen: permanently merged boundaries need no map value. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- A zero-width point followed by positive width must belong to the specified coherent set.
There is deliberately no condition on a permanently collapsed tail of the strip. -/
def RecoverablePinchesIn (E : Set ℂ) (a b : ℝ) : Prop :=
  ∀ h ∈ Set.Icc a b, S.lower.coordinate h = S.upper.coordinate h →
    ∀ k ∈ Set.Icc h b, S.lower.coordinate k < S.upper.coordinate k → S.lower.point h ∈ E

theorem recoverablePinchesIn_of_positive_width (E : Set ℂ) (a b : ℝ)
    (width : ∀ h ∈ Set.Icc a b, S.lower.coordinate h < S.upper.coordinate h) :
    S.RecoverablePinchesIn E a b := by
  intro h member same
  exact ((width h member).ne same).elim

/-- A separator cannot introduce a new reopening pinch before its target when it is strictly
internal there. After the target, permanent wall contacts prevent reopening. -/
theorem split_recoverablePinchesIn (G : MonotoneHeightGraph)
    (bounds : ∀ h, S.lower.coordinate h ≤ G.coordinate h ∧
      G.coordinate h ≤ S.upper.coordinate h)
    {E : Set ℂ} {a c b : ℝ} (old : S.RecoverablePinchesIn E a b)
    (at_target : G.point c ∈ E)
    (strict_before : ∀ h ∈ Set.Icc a b, h < c →
      S.lower.coordinate h < S.upper.coordinate h →
        S.lower.coordinate h < G.coordinate h ∧ G.coordinate h < S.upper.coordinate h)
    (left_sticks : ∀ h ∈ Set.Icc a b, c < h →
      S.lower.coordinate h = G.coordinate h →
        ∀ k ∈ Set.Icc h b, S.lower.coordinate k = G.coordinate k)
    (right_sticks : ∀ h ∈ Set.Icc a b, c < h →
      G.coordinate h = S.upper.coordinate h →
        ∀ k ∈ Set.Icc h b, G.coordinate k = S.upper.coordinate k) :
    (S.lowerSplit G bounds).RecoverablePinchesIn E a b ∧
      (S.upperSplit G bounds).RecoverablePinchesIn E a b := by
  constructor
  · intro h member same k later width
    change S.lower.coordinate h = G.coordinate h at same
    change S.lower.coordinate k < G.coordinate k at width
    change S.lower.point h ∈ E
    rcases lt_trichotomy h c with before | equal | after
    · have collapsed : S.lower.coordinate h = S.upper.coordinate h := by
        apply le_antisymm (S.ordered h)
        by_contra different
        have positive : S.lower.coordinate h < S.upper.coordinate h :=
          lt_of_not_ge different
        exact (strict_before h member before positive).1.ne same
      exact old h member collapsed k later (width.trans_le (bounds k).2)
    · subst h
      have point : S.lower.point c = G.point c := by
        apply Complex.ext
        · exact same
        · change c - S.lower.coordinate c = c - G.coordinate c
          rw [same]
      exact point.symm ▸ at_target
    · exact (width.ne (left_sticks h member after same k later)).elim
  · intro h member same k later width
    change G.coordinate h = S.upper.coordinate h at same
    change G.coordinate k < S.upper.coordinate k at width
    change G.point h ∈ E
    rcases lt_trichotomy h c with before | equal | after
    · have collapsed : S.lower.coordinate h = S.upper.coordinate h := by
        apply le_antisymm (S.ordered h)
        by_contra different
        have positive : S.lower.coordinate h < S.upper.coordinate h :=
          lt_of_not_ge different
        exact (strict_before h member before positive).2.ne same
      have point : G.point h = S.lower.point h := by
        have coordinate : G.coordinate h = S.lower.coordinate h := same.trans collapsed.symm
        apply Complex.ext
        · exact coordinate
        · change h - G.coordinate h = h - S.lower.coordinate h
          rw [coordinate]
      rw [point]
      exact old h member collapsed k later ((bounds k).1.trans_lt width)
    · exact equal ▸ at_target
    · exact (width.ne (right_sticks h member after same k later)).elim

end Unfoldings.MonotoneStrip
