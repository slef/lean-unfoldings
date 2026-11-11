module

public import Unfoldings.Geometry.MonotoneStripSubdivision
public import Unfoldings.Geometry.CoalescingStripInsertion

/-! Insert a finite height-ordered family of coalescing tails, preserving every actual tail. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

/-- A source connector followed by the prescribed tail throughout the physical height slab. -/
def CompletesTail (p : ℂ) (tail : MonotoneHeightGraph) (cutoff : ℝ)
    (G : MonotoneHeightGraph) : Prop :=
  G.coordinate 0 = 0 ∧
    ∀ h ∈ Set.Icc (p.re + p.im) cutoff, G.coordinate h = tail.coordinate h

theorem insertionGraph_source (S : MonotoneStrip) (p : ℂ) (member : p ∈ S.carrier)
    (tail : MonotoneHeightGraph) (at_target : tail.coordinate (p.re + p.im) = p.re)
    (first : S.lower.coordinate 0 = 0) (last : S.upper.coordinate 0 = 0)
    (horizontal : 0 ≤ p.re) (vertical : 0 ≤ p.im) :
    (S.insertionGraph p member tail at_target).coordinate 0 = 0 := by
  simp only [insertionGraph, MonotoneHeightGraph.splice,
    ite_eq_left (add_nonneg horizontal vertical)]
  exact S.interiorConnector_source first last horizontal vertical

/-- Construct the subdivision rather than assuming a collection of safe strips.
Tails need coalescence only after the later starting height. Exterior walls need only bound
the prescribed tails; they need not belong to the cut network or coalesce with it. -/
theorem exists_finite_waterfall (S : MonotoneStrip) (n : ℕ) (p : Fin n → ℂ)
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
      (tail j).CoalescesOn (tail k) ((p k).re + (p k).im) cutoff) :
    ∃ T : S.Subdivision,
      (∀ G ∈ T.separators, ∃ j, CompletesTail (p j) (tail j) cutoff G) ∧
      ∀ j, ∃ G ∈ T.separators, CompletesTail (p j) (tail j) cutoff G := by
  let height := fun j : Fin n => (p j).re + (p j).im
  have stages : ∀ k : ℕ, k ≤ n → ∃ T : S.Subdivision,
      (∀ G ∈ T.separators, ∃ j : Fin n,
        j.val < k ∧ CompletesTail (p j) (tail j) cutoff G) ∧
      ∀ j : Fin n, j.val < k →
        ∃ G ∈ T.separators, CompletesTail (p j) (tail j) cutoff G := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨.leaf S, ?_, ?_⟩
      · intro G member
        exact member.elim
      · intro j before
        exact (Nat.not_lt_zero _ before).elim
    | succ k ih =>
      intro within
      obtain ⟨T, provenance, represented⟩ := ih (Nat.le_of_succ_le within)
      let j : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) within⟩
      have target_member : p j ∈ S.carrier := by
        have bounds := outer_bounds j (height j) ⟨le_rfl, below j⟩
        rwa [at_target j] at bounds
      have make : ∀ R ∈ T.cells, p j ∈ R.carrier →
          ∃ G : MonotoneHeightGraph,
            (∀ h, R.lower.coordinate h ≤ G.coordinate h ∧
              G.coordinate h ≤ R.upper.coordinate h) ∧
            CompletesTail (p j) (tail j) cutoff G := by
        intro R in_cells member
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
        refine ⟨R.insertionGraph (p j) member (tail j) (at_target j),
          R.insertionGraph_bounds _ _ _ _, ?_, ?_⟩
        · exact R.insertionGraph_source _ _ _ _ left_source right_source
            (nonnegative j).1 (nonnegative j).2
        · intro h inside
          exact R.insertionGraph_preserves_tail _ _ _ _ inside.1
            (trapped h inside).1 (trapped h inside).2
      obtain ⟨U, G, completion, new, retained, added⟩ :=
        T.exists_insert_separator (p j) target_member
          (CompletesTail (p j) (tail j) cutoff) make
      refine ⟨U, ?_, ?_⟩
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
  obtain ⟨T, provenance, represented⟩ := stages n le_rfl
  refine ⟨T, ?_, fun j => represented j j.isLt⟩
  intro G member
  obtain ⟨j, _, good⟩ := provenance G member
  exact ⟨j, good⟩

end Unfoldings.MonotoneStrip
