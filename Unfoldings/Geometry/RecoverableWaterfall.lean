module

public import Unfoldings.Geometry.FiniteWaterfall
public import Unfoldings.Geometry.CoalescingStripInsertion
public import Unfoldings.Geometry.RecoverableStripInsertion
public import Unfoldings.Geometry.StripSubdivisionInvariant

/-! Construct finite waterfall strips with strict walls and controlled reopening pinches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

/-- Construct the subdivision rather than assuming a collection of safe strips.
Tails merge permanently after the later starting height. Exterior contacts need persist only
strictly after the target: a bank target itself may be a coherent reopening leaf pinch. -/
theorem exists_finite_waterfall_recoverable (S : MonotoneStrip) (n : ℕ) (p : Fin n → ℂ)
    (tail : Fin n → MonotoneHeightGraph) (cutoff : ℝ)
    (first_source : S.lower.coordinate 0 = 0) (last_source : S.upper.coordinate 0 = 0)
    (nonnegative : ∀ j, 0 ≤ (p j).re ∧ 0 ≤ (p j).im)
    (heights : Monotone (fun j => (p j).re + (p j).im))
    (below : ∀ j, (p j).re + (p j).im ≤ cutoff)
    (at_target : ∀ j, (tail j).coordinate ((p j).re + (p j).im) = (p j).re)
    (outer_bounds : ∀ j h, h ∈ Set.Icc ((p j).re + (p j).im) cutoff →
      S.lower.coordinate h ≤ (tail j).coordinate h ∧
        (tail j).coordinate h ≤ S.upper.coordinate h)
    (coalesces : ∀ j k : Fin n, j < k →
      (tail j).CoalescesOn (tail k) ((p k).re + (p k).im) cutoff)
    (E : Set ℂ)
    (initial : S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
      S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ S.RecoverablePinchesIn E 0 cutoff)
    (target_coherent : ∀ j, p j ∈ E)
    (strict_tails : ∀ j,
      (tail j).StrictCoordinatesOn (Set.Icc ((p j).re + (p j).im) cutoff))
    (outer_left_sticks : ∀ j h, h ∈ Set.Ioc ((p j).re + (p j).im) cutoff →
      S.lower.coordinate h = (tail j).coordinate h →
        ∀ k ∈ Set.Icc h cutoff, S.lower.coordinate k = (tail j).coordinate k)
    (outer_right_sticks : ∀ j h, h ∈ Set.Ioc ((p j).re + (p j).im) cutoff →
      (tail j).coordinate h = S.upper.coordinate h →
        ∀ k ∈ Set.Icc h cutoff, (tail j).coordinate k = S.upper.coordinate k) :
    ∃ T : S.Subdivision,
      (∀ G ∈ T.separators, ∃ j, CompletesTail (p j) (tail j) cutoff G) ∧
      (∀ j, ∃ G ∈ T.separators, CompletesTail (p j) (tail j) cutoff G) ∧
      ∀ R ∈ T.cells, R.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
        R.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ R.RecoverablePinchesIn E 0 cutoff := by
  let Good := fun R : MonotoneStrip => R.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
    R.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ R.RecoverablePinchesIn E 0 cutoff
  let height := fun j : Fin n => (p j).re + (p j).im
  have stages : ∀ k : ℕ, k ≤ n → ∃ T : S.Subdivision,
      (∀ G ∈ T.separators, ∃ j : Fin n,
        j.val < k ∧ CompletesTail (p j) (tail j) cutoff G) ∧
      (∀ j : Fin n, j.val < k →
        ∃ G ∈ T.separators, CompletesTail (p j) (tail j) cutoff G) ∧
      ∀ R ∈ T.cells, Good R := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨.leaf S, ?_, ?_, ?_⟩
      · intro G member
        exact member.elim
      · intro j before
        exact (Nat.not_lt_zero _ before).elim
      · intro R member
        exact List.mem_singleton.mp member ▸ initial
    | succ k ih =>
      intro within
      obtain ⟨T, provenance, represented, good⟩ := ih (Nat.le_of_succ_le within)
      let j : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) within⟩
      have target_member : p j ∈ S.carrier := by
        have bounds := outer_bounds j (height j) ⟨le_rfl, below j⟩
        rwa [at_target j] at bounds
      have make : ∀ R ∈ T.cells, p j ∈ R.carrier → Good R →
          ∃ (G : MonotoneHeightGraph)
            (bounds : ∀ h, R.lower.coordinate h ≤ G.coordinate h ∧
              G.coordinate h ≤ R.upper.coordinate h),
            CompletesTail (p j) (tail j) cutoff G ∧
              Good (R.lowerSplit G bounds) ∧ Good (R.upperSplit G bounds) := by
        intro R in_cells member valid
        obtain ⟨left_wall, right_wall⟩ := T.cell_wall_provenance in_cells
        have left_source : R.lower.coordinate 0 = 0 := by
          rcases left_wall with equal | old
          · rw [equal]
            exact first_source
          · obtain ⟨a, _, completion⟩ := provenance R.lower old
            exact completion.1
        have right_source : R.upper.coordinate 0 = 0 := by
          rcases right_wall with equal | old
          · rw [equal]
            exact last_source
          · obtain ⟨a, _, completion⟩ := provenance R.upper old
            exact completion.1
        have trapped : ∀ h ∈ Set.Icc (height j) cutoff,
            R.lower.coordinate h ≤ (tail j).coordinate h ∧
              (tail j).coordinate h ≤ R.upper.coordinate h := by
          intro h inside
          constructor
          · rcases left_wall with equal | old
            · rw [equal]
              exact (outer_bounds j h inside).1
            · obtain ⟨a, earlier, completion⟩ := provenance R.lower old
              have ordered : a < j := earlier
              have before : height a ≤ height j := heights ordered.le
              have start_match := completion.2 (height j) ⟨before, below j⟩
              have start : (tail a).coordinate (height j) ≤
                  (tail j).coordinate (height j) := by
                rw [← start_match, at_target j]
                exact member.1
              rw [completion.2 h ⟨before.trans inside.1, inside.2⟩]
              exact (coalesces a j ordered).le_of_start_le _ _ _ _ start inside
          · rcases right_wall with equal | old
            · rw [equal]
              exact (outer_bounds j h inside).2
            · obtain ⟨a, earlier, completion⟩ := provenance R.upper old
              have ordered : a < j := earlier
              have before : height a ≤ height j := heights ordered.le
              have start_match := completion.2 (height j) ⟨before, below j⟩
              have start : (tail j).coordinate (height j) ≤
                  (tail a).coordinate (height j) := by
                rw [← start_match, at_target j]
                exact member.2
              rw [completion.2 h ⟨before.trans inside.1, inside.2⟩]
              exact (coalesces a j ordered).symm.le_of_start_le _ _ _ _ start inside
        have left_sticks : ∀ h ∈ Set.Ioc (height j) cutoff,
            R.lower.coordinate h = (tail j).coordinate h →
              ∀ k ∈ Set.Icc h cutoff, R.lower.coordinate k = (tail j).coordinate k := by
          intro h slab same k later
          rcases left_wall with equal | old
          · rw [equal] at same ⊢
            exact outer_left_sticks j h slab same k later
          · obtain ⟨a, earlier, completion⟩ := provenance R.lower old
            have ordered : a < j := earlier
            have before : height a ≤ height j := heights ordered.le
            rw [completion.2 h ⟨before.trans slab.1.le, slab.2⟩] at same
            rw [completion.2 k ⟨before.trans (slab.1.le.trans later.1), later.2⟩]
            exact coalesces a j ordered h ⟨slab.1.le, slab.2⟩ same k later
        have right_sticks : ∀ h ∈ Set.Ioc (height j) cutoff,
            (tail j).coordinate h = R.upper.coordinate h →
              ∀ k ∈ Set.Icc h cutoff, (tail j).coordinate k = R.upper.coordinate k := by
          intro h slab same k later
          rcases right_wall with equal | old
          · rw [equal] at same ⊢
            exact outer_right_sticks j h slab same k later
          · obtain ⟨a, earlier, completion⟩ := provenance R.upper old
            have ordered : a < j := earlier
            have before : height a ≤ height j := heights ordered.le
            rw [completion.2 h ⟨before.trans slab.1.le, slab.2⟩] at same
            rw [completion.2 k ⟨before.trans (slab.1.le.trans later.1), later.2⟩]
            exact (coalesces a j ordered h ⟨slab.1.le, slab.2⟩ same.symm k later).symm
        have increasing := R.insertionGraph_strictCoordinatesOn (p j) member (tail j)
          (at_target j) (add_nonneg (nonnegative j).1 (nonnegative j).2) (below j)
          valid.1 valid.2.1 (strict_tails j)
        have pinches := R.insertionGraph_recoverablePinchesIn (p j) member (tail j)
          (at_target j) valid.2.2 (target_coherent j) (below j) valid.1 valid.2.1
          trapped left_sticks right_sticks
        refine ⟨R.insertionGraph (p j) member (tail j) (at_target j),
          R.insertionGraph_bounds _ _ _ _, ⟨?_, ?_⟩,
          ⟨valid.1, increasing, pinches.1⟩, ⟨increasing, valid.2.1, pinches.2⟩⟩
        · exact R.insertionGraph_source _ _ _ _ left_source right_source
            (nonnegative j).1 (nonnegative j).2
        · intro h inside
          exact R.insertionGraph_preserves_tail _ _ _ _ inside.1
            (trapped h inside).1 (trapped h inside).2
      obtain ⟨U, G, completion, new, retained, added, preserved⟩ :=
        T.exists_insert_separator_preserving (p j) target_member
          (CompletesTail (p j) (tail j) cutoff) Good good make
      refine ⟨U, ?_, ?_, preserved⟩
      · intro H member
        rcases added member with equal | old
        · subst H
          exact ⟨j, Nat.lt_succ_self k, completion⟩
        · obtain ⟨a, before, good⟩ := provenance H old
          exact ⟨a, Nat.lt_succ_of_lt before, good⟩
      · intro a before
        by_cases earlier : a.val < k
        · obtain ⟨H, old, good⟩ := represented a earlier
          exact ⟨H, retained old, good⟩
        · have same : a = j := Fin.ext (show a.val = k by omega)
          subst a
          exact ⟨G, new, completion⟩
  obtain ⟨T, provenance, represented, good⟩ := stages n le_rfl
  refine ⟨T, ?_, (fun j => represented j j.isLt), good⟩
  intro G member
  obtain ⟨j, _, good⟩ := provenance G member
  exact ⟨j, good⟩

end Unfoldings.MonotoneStrip
