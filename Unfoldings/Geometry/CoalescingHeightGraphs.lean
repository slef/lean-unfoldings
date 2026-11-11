module

public import Unfoldings.Geometry.MonotoneHeightGraph
public import Mathlib.Topology.Order.IntermediateValue

/-! Once two monotone path graphs merge, they cannot exchange their left-to-right order. -/

@[expose] public section

namespace Unfoldings.MonotoneHeightGraph

variable (G H J : MonotoneHeightGraph) (a b : ℝ)

/-- After the paths meet in the specified interval, their entire later tails coincide. -/
def CoalescesOn : Prop :=
  ∀ x ∈ Set.Icc a b, G.coordinate x = H.coordinate x →
    ∀ y ∈ Set.Icc x b, G.coordinate y = H.coordinate y

theorem CoalescesOn.symm (coalesces : G.CoalescesOn H a b) : H.CoalescesOn G a b :=
  fun x member same y later => (coalesces x member same.symm y later).symm

/-- Continuity supplies an intervening meeting point if an order reversal were to occur. -/
theorem CoalescesOn.le_of_start_le (coalesces : G.CoalescesOn H a b)
    (start : G.coordinate a ≤ H.coordinate a) {y : ℝ} (member : y ∈ Set.Icc a b) :
    G.coordinate y ≤ H.coordinate y := by
  by_contra reversed
  have later : 0 ≤ G.coordinate y - H.coordinate y := (sub_pos.mpr (lt_of_not_ge reversed)).le
  obtain ⟨x, between, equal⟩ :=
    intermediate_value_Icc member.1 (G.continuous.sub H.continuous).continuousOn
      (show 0 ∈ Set.Icc (G.coordinate a - H.coordinate a)
        (G.coordinate y - H.coordinate y) from ⟨sub_nonpos.mpr start, later⟩)
  have meet : G.coordinate x = H.coordinate x := sub_eq_zero.mp equal
  have same := coalesces x ⟨between.1, between.2.trans member.2⟩ meet y ⟨between.2, member.2⟩
  exact reversed same.le

/-- Any two such tails have one consistent weak order on their entire common height interval. -/
theorem CoalescesOn.order_total (coalesces : G.CoalescesOn H a b) :
    (∀ y ∈ Set.Icc a b, G.coordinate y ≤ H.coordinate y) ∨
      (∀ y ∈ Set.Icc a b, H.coordinate y ≤ G.coordinate y) := by
  rcases le_total (G.coordinate a) (H.coordinate a) with first | last
  · exact Or.inl (fun _ member => coalesces.le_of_start_le G H a b first member)
  · exact Or.inr (fun _ member => coalesces.symm.le_of_start_le H G a b last member)

/-- If the tails are still distinct at a later height, their earlier weak order is strict. -/
theorem CoalescesOn.lt_before_distinct (coalesces : G.CoalescesOn H a b)
    (start : G.coordinate a ≤ H.coordinate a) {x y : ℝ}
    (first : x ∈ Set.Icc a b) (later : y ∈ Set.Icc x b)
    (different : G.coordinate y ≠ H.coordinate y) : G.coordinate x < H.coordinate x := by
  apply lt_of_le_of_ne (coalesces.le_of_start_le G H a b start first)
  intro same
  exact different (coalesces x first same y later)

/-- A new tail starting between its two neighbors remains there until the common cutoff. -/
theorem tail_between_of_coalesces
    (left : G.CoalescesOn J a b) (right : J.CoalescesOn H a b)
    (start_left : G.coordinate a ≤ J.coordinate a) (start_right : J.coordinate a ≤ H.coordinate a)
    {y : ℝ} (member : y ∈ Set.Icc a b) :
    G.coordinate y ≤ J.coordinate y ∧ J.coordinate y ≤ H.coordinate y :=
  ⟨left.le_of_start_le G J a b start_left member, right.le_of_start_le J H a b start_right member⟩

end Unfoldings.MonotoneHeightGraph
