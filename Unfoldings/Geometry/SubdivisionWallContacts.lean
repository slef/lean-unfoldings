module

public import Unfoldings.Geometry.RecoverableStripPinches

/-! Contacts between subdivision walls can reopen only at the recorded coherent points. -/

@[expose] public section

namespace Unfoldings

theorem MonotoneHeightGraph.point_eq_of_same_coordinate
    (G H : MonotoneHeightGraph) {h : ℝ} (same : G.coordinate h = H.coordinate h) :
    G.point h = H.point h := by
  apply Complex.ext
  · exact same
  · change h - G.coordinate h = h - H.coordinate h
    rw [same]

namespace MonotoneStrip.Subdivision

variable {S : MonotoneStrip}

theorem wall_bounds (P : Subdivision S) {G : MonotoneHeightGraph} (member : G ∈ P.walls) (h : ℝ) :
    S.lower.coordinate h ≤ G.coordinate h ∧ G.coordinate h ≤ S.upper.coordinate h := by
  induction P with
  | leaf S =>
    change G = S.lower ∨ G = S.upper at member
    rcases member with rfl | rfl
    · exact ⟨le_rfl, S.ordered h⟩
    · exact ⟨S.ordered h, le_rfl⟩
  | split H bounds left right first last =>
    rcases member with member | member
    · exact ⟨(first member).1, (first member).2.trans (bounds h).2⟩
    · exact ⟨(bounds h).1.trans (last member).1, (last member).2⟩

/-- If two actual walls meet and later differ, some intervening final cell
reopens at their contact. Its recoverable-pinch invariant identifies that point. -/
theorem wall_contact_reopening_mem (P : Subdivision S) {E : Set ℂ} {a b : ℝ}
    (good : ∀ R ∈ P.cells, R.RecoverablePinchesIn E a b)
    {G H : MonotoneHeightGraph} (first : G ∈ P.walls) (last : H ∈ P.walls)
    {h k : ℝ} (height : h ∈ Set.Icc a b) (same : G.coordinate h = H.coordinate h)
    (later : k ∈ Set.Icc h b) (different : G.coordinate k ≠ H.coordinate k) :
    G.point h ∈ E := by
  induction P generalizing G H with
  | leaf S =>
    change G = S.lower ∨ G = S.upper at first
    change H = S.lower ∨ H = S.upper at last
    rcases first with rfl | rfl <;> rcases last with rfl | rfl
    · exact (different rfl).elim
    · exact good S (List.mem_singleton_self S) h height same k later
        (lt_of_le_of_ne (S.ordered k) different)
    · rw [S.upper.point_eq_of_same_coordinate S.lower same]
      exact good S (List.mem_singleton_self S) h height same.symm k later
        (lt_of_le_of_ne (S.ordered k) (Ne.symm different))
    · exact (different rfl).elim
  | @split S J bounds left right ih_left ih_right =>
    have good_left : ∀ R ∈ left.cells, R.RecoverablePinchesIn E a b :=
      fun R member => good R (List.mem_append_left _ member)
    have good_right : ∀ R ∈ right.cells, R.RecoverablePinchesIn E a b :=
      fun R member => good R (List.mem_append_right _ member)
    have across {G H : MonotoneHeightGraph} (first : G ∈ left.walls) (last : H ∈ right.walls)
        (same : G.coordinate h = H.coordinate h) (different : G.coordinate k ≠ H.coordinate k) :
        G.point h ∈ E := by
      have first_bound : G.coordinate h ≤ J.coordinate h := (left.wall_bounds first h).2
      have last_bound : J.coordinate h ≤ H.coordinate h := (right.wall_bounds last h).1
      have first_contact : G.coordinate h = J.coordinate h := by linarith
      have last_contact : J.coordinate h = H.coordinate h := first_contact.symm.trans same
      by_cases before : G.coordinate k ≠ J.coordinate k
      · exact ih_left good_left first left.exterior_walls.2 first_contact before
      · have after : J.coordinate k ≠ H.coordinate k := by
          intro equal
          exact different ((not_not.mp before).trans equal)
        rw [G.point_eq_of_same_coordinate J first_contact]
        exact ih_right good_right right.exterior_walls.1 last last_contact after
    rcases first with first | first <;> rcases last with last | last
    · exact ih_left good_left first last same different
    · exact across first last same different
    · rw [G.point_eq_of_same_coordinate H same]
      exact across last first same.symm (Ne.symm different)
    · exact ih_right good_right first last same different

end MonotoneStrip.Subdivision
end Unfoldings
