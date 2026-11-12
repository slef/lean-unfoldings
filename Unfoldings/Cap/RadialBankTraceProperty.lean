module

public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! Strict radial progress of the visible bank traces before each active strip height. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

/-- Each bank progresses strictly away from the developed source before any active height. -/
def RadialBankTraces (S : MonotoneStrip) (G : ℂ → ℂ) (source : ℂ) (cutoff : ℝ) : Prop :=
  ∀ active ∈ S.strictCarrier, active.re + active.im ∈ Set.Icc 0 cutoff →
    ∀ a d : ℝ, 0 < a → a < d → d ≤ active.re + active.im →
      ‖G (S.lower.point a) - source‖ < ‖G (S.lower.point d) - source‖ ∧
      ‖G (S.upper.point a) - source‖ < ‖G (S.upper.point d) - source‖

end Unfoldings.MonotoneStrip
