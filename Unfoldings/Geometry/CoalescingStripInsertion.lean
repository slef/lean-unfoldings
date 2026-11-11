module

public import Unfoldings.Geometry.CoalescingHeightGraphs
public import Unfoldings.Geometry.MonotoneStripInsertion

/-! A monotone strip insertion preserves a tail ordered by the proved coalescence relation. -/

@[expose] public section

namespace Unfoldings

namespace MonotoneHeightGraph

variable {G H G' H' : MonotoneHeightGraph} {a b : ℝ}

/-- Completing paths below their starting height does not affect later coalescence. -/
theorem CoalescesOn.congr (coalesces : G.CoalescesOn H a b)
    (first : ∀ h ∈ Set.Icc a b, G'.coordinate h = G.coordinate h)
    (last : ∀ h ∈ Set.Icc a b, H'.coordinate h = H.coordinate h) : G'.CoalescesOn H' a b := by
  intro x member same y later
  have y_member : y ∈ Set.Icc a b := ⟨member.1.trans later.1, later.2⟩
  rw [first x member, last x member] at same
  rw [first y y_member, last y y_member]
  exact coalesces x member same y later

end MonotoneHeightGraph

namespace MonotoneStrip

variable (S : MonotoneStrip)

/-- Starting between two coalescing neighbors traps the whole tail up to the common cutoff.
The inserted graph therefore preserves the actual tail without clipping any of its points. -/
theorem insertionGraph_preserves_coalescing_tail (p : ℂ) (member : p ∈ S.carrier)
    (tail : MonotoneHeightGraph) (at_target : tail.coordinate (p.re + p.im) = p.re)
    (cutoff : ℝ) (left : S.lower.CoalescesOn tail (p.re + p.im) cutoff)
    (right : tail.CoalescesOn S.upper (p.re + p.im) cutoff)
    {h : ℝ} (inside : h ∈ Set.Icc (p.re + p.im) cutoff) :
    (S.insertionGraph p member tail at_target).coordinate h = tail.coordinate h := by
  have first : S.lower.coordinate (p.re + p.im) ≤ tail.coordinate (p.re + p.im) := by
    rw [at_target]
    exact member.1
  have last : tail.coordinate (p.re + p.im) ≤ S.upper.coordinate (p.re + p.im) := by
    rw [at_target]
    exact member.2
  have bounds := MonotoneHeightGraph.tail_between_of_coalesces S.lower S.upper tail
    (p.re + p.im) cutoff left right first last inside
  exact S.insertionGraph_preserves_tail p member tail at_target inside.1 bounds.1 bounds.2

end MonotoneStrip
end Unfoldings
