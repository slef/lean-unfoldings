module

public import Unfoldings.Geometry.RecoverableStripPinches

/-! Regular points before an active strip height have positive width. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem width_pos_of_recoverable_regular {E : Set ℂ} {a b k : ℝ} {z : ℂ}
    (pinches : S.RecoverablePinchesIn E a b) (member : z ∈ S.carrier)
    (slab : z.re + z.im ∈ Set.Icc a b) (active : k ∈ Set.Icc (z.re + z.im) b)
    (width : S.lower.coordinate k < S.upper.coordinate k) (regular : z ∉ E) :
    S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im) := by
  by_contra collapsed
  have same := le_antisymm (S.ordered (z.re + z.im)) (le_of_not_gt collapsed)
  have coordinate : S.lower.coordinate (z.re + z.im) = z.re :=
    le_antisymm member.1 (same.symm ▸ member.2)
  have point := S.lower.point_eq_of_coordinate z coordinate
  exact regular (point ▸ pinches (z.re + z.im) slab same k active width)

end Unfoldings.MonotoneStrip
