module

public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! Positive cells meeting at one physical level meet strictly inside the root strip. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : Subdivision S) {A B : MonotoneStrip}

theorem bank_contact_mem_strictCarrier (first : A ∈ P.cells) (last : B ∈ P.cells)
    {h : ℝ} (contact : A.upper.point h = B.lower.point h)
    (first_width : A.lower.coordinate h < A.upper.coordinate h)
    (last_width : B.lower.coordinate h < B.upper.coordinate h) :
    A.upper.point h ∈ S.strictCarrier := by
  have coordinate : A.upper.coordinate h = B.lower.coordinate h := congrArg Complex.re contact
  change S.lower.coordinate ((A.upper.point h).re + (A.upper.point h).im) <
      (A.upper.point h).re ∧ (A.upper.point h).re <
        S.upper.coordinate ((A.upper.point h).re + (A.upper.point h).im)
  rw [A.upper.point_height]
  refine ⟨(P.cell_bounds first h).1.trans_lt first_width, ?_⟩
  change A.upper.coordinate h < S.upper.coordinate h
  rw [coordinate]
  exact last_width.trans_le (P.cell_bounds last h).2

theorem upper_bank_separator_of_contact (first : A ∈ P.cells) (last : B ∈ P.cells)
    {h : ℝ} (contact : A.upper.point h = B.lower.point h)
    (last_width : B.lower.coordinate h < B.upper.coordinate h) : A.upper ∈ P.separators := by
  rcases (P.cell_wall_provenance first).2 with exterior | separator
  · have coordinate : A.upper.coordinate h = B.lower.coordinate h := congrArg Complex.re contact
    have bound := last_width.trans_le (P.cell_bounds last h).2
    rw [← coordinate, exterior] at bound
    exact (lt_irrefl _ bound).elim
  · exact separator

theorem lower_bank_separator_of_contact (first : A ∈ P.cells) (last : B ∈ P.cells)
    {h : ℝ} (contact : A.upper.point h = B.lower.point h)
    (first_width : A.lower.coordinate h < A.upper.coordinate h) : B.lower ∈ P.separators := by
  rcases (P.cell_wall_provenance last).1 with exterior | separator
  · have coordinate : A.upper.coordinate h = B.lower.coordinate h := congrArg Complex.re contact
    have bound := (P.cell_bounds first h).1.trans_lt first_width
    rw [coordinate, exterior] at bound
    exact (lt_irrefl _ bound).elim
  · exact separator

end Unfoldings.MonotoneStrip.Subdivision
