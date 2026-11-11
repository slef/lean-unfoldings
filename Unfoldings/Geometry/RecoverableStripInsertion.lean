module

public import Unfoldings.Geometry.StrictStripInsertion
public import Unfoldings.Geometry.RecoverableStripPinches

/-! The actual connector-and-tail insertion preserves coherent reopening pinches. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem insertionGraph_recoverablePinchesIn (p : ℂ) (member : p ∈ S.carrier)
    (tail : MonotoneHeightGraph) (at_target : tail.coordinate (p.re + p.im) = p.re)
    {E : Set ℂ} {a b : ℝ} (old : S.RecoverablePinchesIn E a b)
    (target_coherent : p ∈ E) (finish : p.re + p.im ≤ b)
    (first : S.lower.StrictCoordinatesOn (Set.Icc a b))
    (last : S.upper.StrictCoordinatesOn (Set.Icc a b))
    (trapped : ∀ h ∈ Set.Icc (p.re + p.im) b,
      S.lower.coordinate h ≤ tail.coordinate h ∧ tail.coordinate h ≤ S.upper.coordinate h)
    (left_sticks : ∀ h ∈ Set.Ioc (p.re + p.im) b,
      S.lower.coordinate h = tail.coordinate h →
        ∀ k ∈ Set.Icc h b, S.lower.coordinate k = tail.coordinate k)
    (right_sticks : ∀ h ∈ Set.Ioc (p.re + p.im) b,
      tail.coordinate h = S.upper.coordinate h →
        ∀ k ∈ Set.Icc h b, tail.coordinate k = S.upper.coordinate k) :
    let G := S.insertionGraph p member tail at_target
    let bounds := S.insertionGraph_bounds p member tail at_target
    (S.lowerSplit G bounds).RecoverablePinchesIn E a b ∧
      (S.upperSplit G bounds).RecoverablePinchesIn E a b := by
  let G := S.insertionGraph p member tail at_target
  have agrees {h : ℝ} (slab : h ∈ Set.Icc (p.re + p.im) b) :
      G.coordinate h = tail.coordinate h :=
    S.insertionGraph_preserves_tail p member tail at_target slab.1
      (trapped h slab).1 (trapped h slab).2
  apply S.split_recoverablePinchesIn G (S.insertionGraph_bounds p member tail at_target) old
  · have point : G.point (p.re + p.im) = p :=
      G.point_eq_of_coordinate p ((agrees ⟨le_rfl, finish⟩).trans at_target)
    exact point.symm ▸ target_coherent
  · intro h slab before width
    rw [show G.coordinate h = (S.interiorConnector p).coordinate h from
      (ite_eq_left before.le)]
    exact S.interiorConnector_strict_before_target member
      (first.mono (Set.Icc_subset_Icc_right finish))
      (last.mono (Set.Icc_subset_Icc_right finish)) slab.1 before width
  · intro h slab after same k later
    rw [agrees ⟨after.le, slab.2⟩] at same
    rw [agrees ⟨after.le.trans later.1, later.2⟩]
    exact left_sticks h ⟨after, slab.2⟩ same k later
  · intro h slab after same k later
    rw [agrees ⟨after.le, slab.2⟩] at same
    rw [agrees ⟨after.le.trans later.1, later.2⟩]
    exact right_sticks h ⟨after, slab.2⟩ same k later

end Unfoldings.MonotoneStrip
