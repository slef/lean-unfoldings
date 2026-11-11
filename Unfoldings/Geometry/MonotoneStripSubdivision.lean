module

public import Unfoldings.Geometry.MonotoneStripInsertion
public import Mathlib.Data.List.Pairwise

/-! Finite strip subdivisions retain boundaries, cover exactly, and have disjoint interiors. -/

@[expose] public section

namespace Unfoldings

namespace MonotoneStrip

def strictCarrier (S : MonotoneStrip) : Set ℂ :=
  {z | S.lower.coordinate (z.re + z.im) < z.re ∧
    z.re < S.upper.coordinate (z.re + z.im)}

/-- A finite subdivision records the actual successive separating graphs, including contacts. -/
inductive Subdivision : MonotoneStrip → Type
  | leaf (S : MonotoneStrip) : Subdivision S
  | split {S : MonotoneStrip} (G : MonotoneHeightGraph)
      (bounds : ∀ h, S.lower.coordinate h ≤ G.coordinate h ∧
        G.coordinate h ≤ S.upper.coordinate h)
      (left : Subdivision (S.lowerSplit G bounds))
      (right : Subdivision (S.upperSplit G bounds)) : Subdivision S

namespace Subdivision

variable {S : MonotoneStrip}

def cells : {S : MonotoneStrip} → Subdivision S → List MonotoneStrip
  | _, .leaf S => [S]
  | _, .split _ _ left right => left.cells ++ right.cells

/-- Include the exterior walls as well as every inserted separator. -/
def walls : {S : MonotoneStrip} → Subdivision S → Set MonotoneHeightGraph
  | S, .leaf _ => {S.lower, S.upper}
  | _, .split _ _ left right => left.walls ∪ right.walls

def separators : {S : MonotoneStrip} → Subdivision S → Set MonotoneHeightGraph
  | _, .leaf _ => ∅
  | _, .split G _ left right => insert G (left.separators ∪ right.separators)

/-- Exterior walls retain their side; an internal cell wall is a recorded separator. -/
theorem cell_wall_provenance (T : Subdivision S) {R : MonotoneStrip}
    (member : R ∈ T.cells) :
    (R.lower = S.lower ∨ R.lower ∈ T.separators) ∧
      (R.upper = S.upper ∨ R.upper ∈ T.separators) := by
  induction T with
  | leaf S =>
    have equal : R = S := List.mem_singleton.mp member
    subst R
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  | split G bounds left right first last =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨lower, upper⟩ := first member
      refine ⟨lower.imp_right (fun old => Or.inr (Or.inl old)), Or.inr ?_⟩
      exact upper.elim Or.inl (fun old => Or.inr (Or.inl old))
    · obtain ⟨lower, upper⟩ := last member
      refine ⟨Or.inr ?_, upper.imp_right (fun old => Or.inr (Or.inr old))⟩
      exact lower.elim Or.inl (fun old => Or.inr (Or.inr old))

theorem exterior_walls (T : Subdivision S) : S.lower ∈ T.walls ∧ S.upper ∈ T.walls := by
  induction T with
  | leaf S => exact ⟨Or.inl rfl, Or.inr rfl⟩
  | split G bounds left right first last => exact ⟨Or.inl first.1, Or.inr last.2⟩

theorem separators_walls (T : Subdivision S) : T.separators ⊆ T.walls := by
  induction T with
  | leaf S => exact Set.empty_subset _
  | split G bounds left right first last =>
    intro H member
    rcases member with equal | (member | member)
    · subst H
      exact Or.inl left.exterior_walls.2
    · exact Or.inl (first member)
    · exact Or.inr (last member)

theorem cell_walls (T : Subdivision S) {R : MonotoneStrip} (member : R ∈ T.cells) :
    R.lower ∈ T.walls ∧ R.upper ∈ T.walls := by
  induction T with
  | leaf S =>
    have equal : R = S := List.mem_singleton.mp member
    subst R
    exact ⟨Or.inl rfl, Or.inr rfl⟩
  | split G bounds left right first last =>
    rcases List.mem_append.mp member with member | member
    · exact ⟨Or.inl (first member).1, Or.inl (first member).2⟩
    · exact ⟨Or.inr (last member).1, Or.inr (last member).2⟩

theorem cell_bounds (T : Subdivision S) {R : MonotoneStrip} (member : R ∈ T.cells) (h : ℝ) :
    S.lower.coordinate h ≤ R.lower.coordinate h ∧
      R.upper.coordinate h ≤ S.upper.coordinate h := by
  induction T with
  | leaf S =>
    have equal : R = S := List.mem_singleton.mp member
    subst R
    exact ⟨le_rfl, le_rfl⟩
  | split G bounds left right first last =>
    rcases List.mem_append.mp member with member | member
    · exact ⟨(first member).1, (first member).2.trans (bounds h).2⟩
    · exact ⟨(bounds h).1.trans (last member).1, (last member).2⟩

theorem cover (T : Subdivision S) (z : ℂ) :
    z ∈ S.carrier ↔ ∃ R ∈ T.cells, z ∈ R.carrier := by
  induction T with
  | leaf S => simp only [cells, List.mem_singleton, exists_eq_left]
  | @split S G bounds left right first last =>
    rw [← S.split_cover G bounds]
    change (z ∈ (S.lowerSplit G bounds).carrier ∨ z ∈ (S.upperSplit G bounds).carrier) ↔ _
    rw [first, last]
    simp only [cells, List.mem_append, or_and_right, exists_or]

theorem interiors_disjoint (T : Subdivision S) :
    T.cells.Pairwise (fun R Q => Disjoint R.strictCarrier Q.strictCarrier) := by
  induction T with
  | leaf S => exact List.pairwise_singleton _ _
  | split G bounds left right first last =>
    apply List.pairwise_append.mpr
    refine ⟨first, last, ?_⟩
    intro R first Q last
    apply Set.disjoint_left.mpr
    intro z in_first in_last
    have before := (left.cell_bounds first (z.re + z.im)).2
    have after := (right.cell_bounds last (z.re + z.im)).1
    exact (in_first.2.trans_le before).not_ge (after.trans_lt in_last.1).le

theorem separator_bounds (T : Subdivision S) {G : MonotoneHeightGraph}
    (member : G ∈ T.separators) (h : ℝ) :
    S.lower.coordinate h ≤ G.coordinate h ∧ G.coordinate h ≤ S.upper.coordinate h := by
  induction T with
  | leaf S => exact member.elim
  | split H bounds left right first last =>
    rcases member with equal | (member | member)
    · subst G
      exact bounds h
    · exact ⟨(first member).1, (first member).2.trans (bounds h).2⟩
    · exact ⟨(bounds h).1.trans (last member).1, (last member).2⟩

/-- Every recorded separator stays out of every final cell's strict interior. -/
theorem separator_avoids_cells (T : Subdivision S) {G : MonotoneHeightGraph}
    (wall : G ∈ T.separators) {R : MonotoneStrip} (cell : R ∈ T.cells) (h : ℝ) :
    G.point h ∉ R.strictCarrier := by
  induction T with
  | leaf S => exact wall.elim
  | split H bounds left right first last =>
    intro inside
    change R.lower.coordinate ((G.point h).re + (G.point h).im) < G.coordinate h ∧
      G.coordinate h < R.upper.coordinate ((G.point h).re + (G.point h).im) at inside
    rw [G.point_height] at inside
    rcases List.mem_append.mp cell with cell | cell
    · have bound := (left.cell_bounds cell h).2
      rcases wall with equal | (wall | wall)
      · subst G
        exact (inside.2.trans_le bound).false
      · exact first wall cell (by
          change R.lower.coordinate ((G.point h).re + (G.point h).im) < G.coordinate h ∧
            G.coordinate h < R.upper.coordinate ((G.point h).re + (G.point h).im)
          rwa [G.point_height])
      · exact ((right.separator_bounds wall h).1.trans_lt (inside.2.trans_le bound)).false
    · have bound := (right.cell_bounds cell h).1
      rcases wall with equal | (wall | wall)
      · subst G
        exact (bound.trans_lt inside.1).false
      · exact ((left.separator_bounds wall h).2.trans_lt (bound.trans_lt inside.1)).false
      · exact last wall cell (by
          change R.lower.coordinate ((G.point h).re + (G.point h).im) < G.coordinate h ∧
            G.coordinate h < R.upper.coordinate ((G.point h).re + (G.point h).im)
          rwa [G.point_height])

/-- Insert in a cell containing the target. Every previous wall is retained.
The caller supplies only the local construction, not a partition or a safe-path certificate. -/
theorem exists_insert (T : Subdivision S) (p : ℂ) (member : p ∈ S.carrier)
    (P : MonotoneHeightGraph → Prop)
    (make : ∀ R ∈ T.cells, p ∈ R.carrier →
      ∃ G : MonotoneHeightGraph,
        (∀ h, R.lower.coordinate h ≤ G.coordinate h ∧
          G.coordinate h ≤ R.upper.coordinate h) ∧ P G) :
    ∃ (U : Subdivision S) (G : MonotoneHeightGraph),
      P G ∧ G ∈ U.walls ∧ T.walls ⊆ U.walls ∧ U.walls ⊆ insert G T.walls := by
  induction T with
  | leaf S =>
    obtain ⟨G, bounds, good⟩ := make S (by simp [cells]) member
    refine ⟨.split G bounds (.leaf _) (.leaf _), G, good, ?_, ?_, ?_⟩
    · exact Or.inl (Or.inr rfl)
    · intro H old
      rcases old with equal | equal
      · exact Or.inl (Or.inl equal)
      · exact Or.inr (Or.inr equal)
    · intro H added
      rcases added with (equal | equal) | (equal | equal)
      · exact Or.inr (Or.inl equal)
      · exact Or.inl equal
      · exact Or.inl equal
      · exact Or.inr (Or.inr equal)
  | @split S G bounds left right first last =>
    have split_member := (S.split_cover G bounds).symm.subset member
    rcases split_member with in_left | in_right
    · obtain ⟨U, H, good, wall, retained, added⟩ := first in_left
        (fun R member inside => make R (List.mem_append_left _ member) inside)
      refine ⟨.split G bounds U right, H, good, Or.inl wall, ?_, ?_⟩
      · intro J old
        exact old.elim (fun member => Or.inl (retained member)) Or.inr
      · intro J new
        rcases new with new | old
        · exact (added new).elim Or.inl (fun member => Or.inr (Or.inl member))
        · exact Or.inr (Or.inr old)
    · obtain ⟨U, H, good, wall, retained, added⟩ := last in_right
        (fun R member inside => make R (List.mem_append_right _ member) inside)
      refine ⟨.split G bounds left U, H, good, Or.inr wall, ?_, ?_⟩
      · intro J old
        exact old.elim Or.inl (fun member => Or.inr (retained member))
      · intro J new
        rcases new with old | new
        · exact Or.inr (Or.inl old)
        · exact (added new).elim Or.inl (fun member => Or.inr (Or.inr member))

/-- The separator version records provenance without confusing the two exterior walls. -/
theorem exists_insert_separator (T : Subdivision S) (p : ℂ) (member : p ∈ S.carrier)
    (P : MonotoneHeightGraph → Prop)
    (make : ∀ R ∈ T.cells, p ∈ R.carrier →
      ∃ G : MonotoneHeightGraph,
        (∀ h, R.lower.coordinate h ≤ G.coordinate h ∧
          G.coordinate h ≤ R.upper.coordinate h) ∧ P G) :
    ∃ (U : Subdivision S) (G : MonotoneHeightGraph),
      P G ∧ G ∈ U.separators ∧ T.separators ⊆ U.separators ∧
        U.separators ⊆ insert G T.separators := by
  induction T with
  | leaf S =>
    obtain ⟨G, bounds, good⟩ := make S (by simp [cells]) member
    refine ⟨.split G bounds (.leaf _) (.leaf _), G, good, Or.inl rfl, Set.empty_subset _, ?_⟩
    intro H member
    rcases member with equal | (member | member)
    · exact Or.inl equal
    · exact member.elim
    · exact member.elim
  | @split S G bounds left right first last =>
    have split_member := (S.split_cover G bounds).symm.subset member
    rcases split_member with in_left | in_right
    · obtain ⟨U, H, good, wall, retained, added⟩ := first in_left
        (fun R member inside => make R (List.mem_append_left _ member) inside)
      refine ⟨.split G bounds U right, H, good, Or.inr (Or.inl wall), ?_, ?_⟩
      · intro J old
        rcases old with equal | (old | old)
        · exact Or.inl equal
        · exact Or.inr (Or.inl (retained old))
        · exact Or.inr (Or.inr old)
      · intro J new
        rcases new with equal | (new | old)
        · exact Or.inr (Or.inl equal)
        · exact (added new).elim Or.inl (fun old => Or.inr (Or.inr (Or.inl old)))
        · exact Or.inr (Or.inr (Or.inr old))
    · obtain ⟨U, H, good, wall, retained, added⟩ := last in_right
        (fun R member inside => make R (List.mem_append_right _ member) inside)
      refine ⟨.split G bounds left U, H, good, Or.inr (Or.inr wall), ?_, ?_⟩
      · intro J old
        rcases old with equal | (old | old)
        · exact Or.inl equal
        · exact Or.inr (Or.inl old)
        · exact Or.inr (Or.inr (retained old))
      · intro J new
        rcases new with equal | (old | new)
        · exact Or.inr (Or.inl equal)
        · exact Or.inr (Or.inr (Or.inl old))
        · exact (added new).elim Or.inl (fun old => Or.inr (Or.inr (Or.inr old)))

end Subdivision
end MonotoneStrip
end Unfoldings
