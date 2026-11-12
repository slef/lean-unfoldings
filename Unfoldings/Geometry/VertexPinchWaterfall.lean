module

public import Unfoldings.Geometry.RecoverableWaterfall
public import Unfoldings.Geometry.ApproachedStripInsertion

/-! Construct finite actual waterfall subdivisions whose approached pinches are vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

theorem exists_finite_waterfall_vertex_pinches (S : MonotoneStrip) (n : ℕ) (p : Fin n → ℂ)
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
        ∀ k ∈ Set.Icc h cutoff, (tail j).coordinate k = S.upper.coordinate k)
    (V : Set ℂ) (initial_pinches : S.ApproachedPinchesIn V 0 cutoff)
    (target_vertex : ∀ j, p j ∈ V)
    (first_affine : ∀ h ∈ Set.Ioo (0 : ℝ) cutoff, S.lower.point h ∉ V → S.lower.AffineAt h)
    (last_affine : ∀ h ∈ Set.Ioo (0 : ℝ) cutoff, S.upper.point h ∉ V → S.upper.AffineAt h)
    (tail_affine : ∀ j h, h ∈ Set.Ioo ((p j).re + (p j).im) cutoff →
      (tail j).point h ∉ V → (tail j).AffineAt h) :
    ∃ T : S.Subdivision,
      (∀ G ∈ T.separators, ∃ j, CompletesTail (p j) (tail j) cutoff G) ∧
      (∀ j, ∃ G ∈ T.separators, CompletesTail (p j) (tail j) cutoff G) ∧
      ∀ R ∈ T.cells, (R.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
        R.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ R.RecoverablePinchesIn E 0 cutoff) ∧
          R.ApproachedPinchesIn V 0 cutoff := by
  apply S.exists_finite_waterfall_recoverable_preserving n p tail cutoff first_source last_source
    nonnegative heights below at_target outer_bounds coalesces E initial target_coherent
    strict_tails outer_left_sticks outer_right_sticks
    (fun R => R.ApproachedPinchesIn V 0 cutoff) initial_pinches
  intro j R member left_wall right_wall trapped first_strict last_strict old
  let c := (p j).re + (p j).im
  let G := R.insertionGraph (p j) member (tail j) (at_target j)
  let bounds := R.insertionGraph_bounds (p j) member (tail j) (at_target j)
  have agrees : Set.EqOn G.coordinate (tail j).coordinate (Set.Icc c cutoff) := by
    intro h within
    exact R.insertionGraph_preserves_tail _ _ _ _ within.1
      (trapped h within).1 (trapped h within).2
  have target : G.point c = p j :=
    G.point_eq_of_coordinate (p j) ((agrees ⟨le_rfl, below j⟩).trans (at_target j))
  apply R.split_approachedPinchesIn G bounds old (target.symm ▸ target_vertex j)
  · intro h within before width
    have equal : G.coordinate h = (R.interiorConnector (p j)).coordinate h := ite_eq_left before.le
    rw [equal]
    exact R.interiorConnector_strict_before_target member
      (first_strict.mono (Set.Icc_subset_Icc_right (below j)))
      (last_strict.mono (Set.Icc_subset_Icc_right (below j))) within.1.le before width
  · intro h within outside
    rcases left_wall with equal | ⟨k, earlier, completion⟩
    · rw [equal] at outside ⊢
      exact first_affine h ⟨(add_nonneg (nonnegative j).1 (nonnegative j).2).trans_lt within.1,
        within.2⟩ outside
    · have start : (p k).re + (p k).im < h := (heights earlier.le).trans_lt within.1
      have at_point := R.lower.point_eq_of_same_coordinate (tail k)
        (completion.2 h ⟨start.le, within.2.le⟩)
      have regular : (tail k).point h ∉ V := fun inside => outside (at_point.symm ▸ inside)
      exact (tail_affine k h ⟨start, within.2⟩ regular).congr_on_Ioo
        (fun _ bounds => completion.2 _ ⟨bounds.1.le, bounds.2.le⟩) ⟨start, within.2⟩
  · intro h within outside
    rcases right_wall with equal | ⟨k, earlier, completion⟩
    · rw [equal] at outside ⊢
      exact last_affine h ⟨(add_nonneg (nonnegative j).1 (nonnegative j).2).trans_lt within.1,
        within.2⟩ outside
    · have start : (p k).re + (p k).im < h := (heights earlier.le).trans_lt within.1
      have at_point := R.upper.point_eq_of_same_coordinate (tail k)
        (completion.2 h ⟨start.le, within.2.le⟩)
      have regular : (tail k).point h ∉ V := fun inside => outside (at_point.symm ▸ inside)
      exact (tail_affine k h ⟨start, within.2⟩ regular).congr_on_Ioo
        (fun _ bounds => completion.2 _ ⟨bounds.1.le, bounds.2.le⟩) ⟨start, within.2⟩
  · intro h within outside
    have at_point := G.point_eq_of_same_coordinate (tail j)
      (agrees ⟨within.1.le, within.2.le⟩)
    have regular : (tail j).point h ∉ V := fun inside => outside (at_point.symm ▸ inside)
    exact (tail_affine j h within regular).congr_on_Ioo
      (fun _ bounds => agrees ⟨bounds.1.le, bounds.2.le⟩) within

end Unfoldings.MonotoneStrip
