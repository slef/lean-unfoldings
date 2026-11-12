module

public import Unfoldings.Geometry.AffineGraphPinches

/-! Strict prefixes and locally affine actual tails preserve the approached-pinch invariant. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem split_approachedPinchesIn (G : MonotoneHeightGraph)
    (bounds : ∀ h, S.lower.coordinate h ≤ G.coordinate h ∧
      G.coordinate h ≤ S.upper.coordinate h)
    {V : Set ℂ} {a c b : ℝ} (old : S.ApproachedPinchesIn V a b)
    (at_target : G.point c ∈ V)
    (strict_before : ∀ h ∈ Set.Ioo a b, h < c →
      S.lower.coordinate h < S.upper.coordinate h →
        S.lower.coordinate h < G.coordinate h ∧ G.coordinate h < S.upper.coordinate h)
    (first_affine : ∀ h ∈ Set.Ioo c b, S.lower.point h ∉ V → S.lower.AffineAt h)
    (last_affine : ∀ h ∈ Set.Ioo c b, S.upper.point h ∉ V → S.upper.AffineAt h)
    (new_affine : ∀ h ∈ Set.Ioo c b, G.point h ∉ V → G.AffineAt h) :
    (S.lowerSplit G bounds).ApproachedPinchesIn V a b ∧
      (S.upperSplit G bounds).ApproachedPinchesIn V a b := by
  have first_subset : (S.lowerSplit G bounds).strictCarrier ⊆ S.strictCarrier :=
    fun z member => ⟨member.1, member.2.trans_le (bounds _).2⟩
  have last_subset : (S.upperSplit G bounds).strictCarrier ⊆ S.strictCarrier :=
    fun z member => ⟨(bounds _).1.trans_lt member.1, member.2⟩
  constructor
  · intro h member same approached
    change S.lower.coordinate h = G.coordinate h at same
    change S.lower.point h ∈ V
    have equal := S.lower.point_eq_of_same_coordinate G same
    rcases lt_trichotomy h c with before | rfl | after
    · have collapsed : S.lower.coordinate h = S.upper.coordinate h := by
        apply le_antisymm (S.ordered h)
        by_contra different
        exact (strict_before h member before (lt_of_not_ge different)).1.ne same
      exact old h member collapsed (closure_mono first_subset approached)
    · exact equal.symm ▸ at_target
    · by_contra outside
      exact (S.lowerSplit G bounds).not_mem_closure_strictCarrier_of_affine_pinch
        (first_affine h ⟨after, member.2⟩ outside)
        (new_affine h ⟨after, member.2⟩ (fun inside => outside (equal.symm ▸ inside)))
        same approached
  · intro h member same approached
    change G.coordinate h = S.upper.coordinate h at same
    change G.point h ∈ V
    change G.point h ∈ closure (S.upperSplit G bounds).strictCarrier at approached
    have equal := G.point_eq_of_same_coordinate S.upper same
    rcases lt_trichotomy h c with before | rfl | after
    · have collapsed : S.lower.coordinate h = S.upper.coordinate h := by
        apply le_antisymm (S.ordered h)
        by_contra different
        exact (strict_before h member before (lt_of_not_ge different)).2.ne same
      have first_equal := G.point_eq_of_same_coordinate S.lower (same.trans collapsed.symm)
      rw [first_equal] at approached ⊢
      exact old h member collapsed (closure_mono last_subset approached)
    · exact at_target
    · by_contra outside
      exact (S.upperSplit G bounds).not_mem_closure_strictCarrier_of_affine_pinch
        (new_affine h ⟨after, member.2⟩ outside)
        (last_affine h ⟨after, member.2⟩ (fun inside => outside (equal.symm ▸ inside)))
        same approached

end Unfoldings.MonotoneStrip
