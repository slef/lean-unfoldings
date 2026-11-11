module

public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! Carry a proved cell invariant through a constructed finite strip insertion. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip}

/-- The new separator is built in one actual cell. Its two child invariants suffice to
preserve the invariant on every final cell, while retaining separator provenance. -/
theorem exists_insert_separator_preserving (T : Subdivision S) (p : ℂ)
    (member : p ∈ S.carrier) (P : MonotoneHeightGraph → Prop)
    (Q : MonotoneStrip → Prop) (good : ∀ R ∈ T.cells, Q R)
    (make : ∀ R ∈ T.cells, p ∈ R.carrier → Q R →
      ∃ (G : MonotoneHeightGraph)
        (bounds : ∀ h, R.lower.coordinate h ≤ G.coordinate h ∧
          G.coordinate h ≤ R.upper.coordinate h),
        P G ∧ Q (R.lowerSplit G bounds) ∧ Q (R.upperSplit G bounds)) :
    ∃ (U : Subdivision S) (G : MonotoneHeightGraph),
      P G ∧ G ∈ U.separators ∧ T.separators ⊆ U.separators ∧
        U.separators ⊆ insert G T.separators ∧ ∀ R ∈ U.cells, Q R := by
  induction T with
  | leaf S =>
    have cell : S ∈ (Subdivision.leaf S).cells := List.mem_singleton_self S
    obtain ⟨G, bounds, property, first, last⟩ := make S cell member (good S cell)
    refine ⟨.split G bounds (.leaf _) (.leaf _), G, property, Or.inl rfl,
      Set.empty_subset _, ?_, ?_⟩
    · intro H member
      rcases member with same | (member | member)
      · exact Or.inl same
      · exact member.elim
      · exact member.elim
    · intro R member
      rcases List.mem_append.mp member with member | member
      · exact List.mem_singleton.mp member ▸ first
      · exact List.mem_singleton.mp member ▸ last
  | @split S G bounds left right ih_left ih_right =>
    have split_member := (S.split_cover G bounds).symm.subset member
    rcases split_member with in_left | in_right
    · obtain ⟨U, H, property, new, retained, added, preserved⟩ := ih_left in_left
        (fun R cell => good R (List.mem_append_left _ cell))
        (fun R cell inside valid => make R (List.mem_append_left _ cell) inside valid)
      refine ⟨.split G bounds U right, H, property, Or.inr (Or.inl new), ?_, ?_, ?_⟩
      · intro J old
        rcases old with same | (old | old)
        · exact Or.inl same
        · exact Or.inr (Or.inl (retained old))
        · exact Or.inr (Or.inr old)
      · intro J wall
        rcases wall with same | (wall | old)
        · exact Or.inr (Or.inl same)
        · exact (added wall).elim Or.inl (fun old => Or.inr (Or.inr (Or.inl old)))
        · exact Or.inr (Or.inr (Or.inr old))
      · intro R cell
        rcases List.mem_append.mp cell with cell | cell
        · exact preserved R cell
        · exact good R (List.mem_append_right _ cell)
    · obtain ⟨U, H, property, new, retained, added, preserved⟩ := ih_right in_right
        (fun R cell => good R (List.mem_append_right _ cell))
        (fun R cell inside valid => make R (List.mem_append_right _ cell) inside valid)
      refine ⟨.split G bounds left U, H, property, Or.inr (Or.inr new), ?_, ?_, ?_⟩
      · intro J old
        rcases old with same | (old | old)
        · exact Or.inl same
        · exact Or.inr (Or.inl old)
        · exact Or.inr (Or.inr (retained old))
      · intro J wall
        rcases wall with same | (old | wall)
        · exact Or.inr (Or.inl same)
        · exact Or.inr (Or.inr (Or.inl old))
        · exact (added wall).elim Or.inl (fun old => Or.inr (Or.inr (Or.inr old)))
      · intro R cell
        rcases List.mem_append.mp cell with cell | cell
        · exact good R (List.mem_append_left _ cell)
        · exact preserved R cell

end Unfoldings.MonotoneStrip.Subdivision
