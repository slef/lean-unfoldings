module

public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! A target outside all recorded separators lies in a positive-width cell. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : S.Subdivision)

theorem cell_positive_width_of_avoids_separators {R : MonotoneStrip} (cell : R ∈ P.cells)
    {p : ℂ} (member : p ∈ R.carrier)
    (width : S.lower.coordinate (p.re + p.im) < S.upper.coordinate (p.re + p.im))
    (avoids : ∀ G ∈ P.separators, G.coordinate (p.re + p.im) ≠ p.re) :
    R.lower.coordinate (p.re + p.im) < R.upper.coordinate (p.re + p.im) := by
  by_contra not_positive
  have equal : R.lower.coordinate (p.re + p.im) = R.upper.coordinate (p.re + p.im) :=
    le_antisymm (R.ordered _) (le_of_not_gt not_positive)
  have lower : R.lower.coordinate (p.re + p.im) = p.re :=
    le_antisymm member.1 (member.2.trans_eq equal.symm)
  have upper : R.upper.coordinate (p.re + p.im) = p.re := equal.symm.trans lower
  obtain ⟨first, last⟩ := P.cell_wall_provenance cell
  rcases first with first | first
  · rcases last with last | last
    · rw [first] at lower
      rw [last] at upper
      exact width.ne (lower.trans upper.symm)
    · exact avoids R.upper last upper
  · exact avoids R.lower first lower

end Unfoldings.MonotoneStrip.Subdivision

namespace Unfoldings.MonotoneStrip

theorem positive_width_of_wall_provenance (S R : MonotoneStrip) {p : ℂ}
    (old : MonotoneHeightGraph → Prop)
    (first : R.lower = S.lower ∨ old R.lower) (last : R.upper = S.upper ∨ old R.upper)
    (member : p ∈ R.carrier)
    (width : S.lower.coordinate (p.re + p.im) < S.upper.coordinate (p.re + p.im))
    (avoids : ∀ G, old G → G.coordinate (p.re + p.im) ≠ p.re) :
    R.lower.coordinate (p.re + p.im) < R.upper.coordinate (p.re + p.im) := by
  by_contra not_positive
  have equal : R.lower.coordinate (p.re + p.im) = R.upper.coordinate (p.re + p.im) :=
    le_antisymm (R.ordered _) (le_of_not_gt not_positive)
  have lower : R.lower.coordinate (p.re + p.im) = p.re :=
    le_antisymm member.1 (member.2.trans_eq equal.symm)
  have upper : R.upper.coordinate (p.re + p.im) = p.re := equal.symm.trans lower
  rcases first with first | first
  · rcases last with last | last
    · rw [first] at lower
      rw [last] at upper
      exact width.ne (lower.trans upper.symm)
    · exact avoids R.upper last upper
  · exact avoids R.lower first lower

end Unfoldings.MonotoneStrip
