module

public import Unfoldings.Cap.CompletedBankChainOrder
public import Unfoldings.Geometry.OrientedInnerBarriers

/-! Actual parent-bank progress supplies inner terminal barriers across different sector frames. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem inner_barrier_point_exclusion (i l : FiveSector) (center m p : Plane)
    (first_barrier : 0 < (B.sectorFrame i (m - center)).re ∧
      0 < (B.sectorFrame i (m - center)).im)
    (last_barrier : 0 < (B.sectorFrame l (m - center)).re ∧
      0 < (B.sectorFrame l (m - center)).im)
    (first : 0 ≤ (B.sectorFrame i (p - center)).re ∧
      0 < (B.sectorFrame i (p - center)).im)
    (last : 0 ≤ (B.sectorFrame l (p - center)).re ∧
      0 < (B.sectorFrame l (p - center)).im)
    (horizontal : (B.sectorFrame i (p - center)).re ≤ (B.sectorFrame i (m - center)).re)
    (vertical : (B.sectorFrame l (p - center)).im ≤ (B.sectorFrame l (m - center)).im)
    (outside : ‖m - center‖ < ‖p - center‖) : False := by
  let calibration := N.calibratedFrame D B.anchor B.reference
  let F := Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place
  let G := Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small l).place
  exact oriented_inner_barrier_point_exclusion F G
    (fiveSectorFrame_commutes_mul t positive small i)
    (fiveSectorFrame_commutes_mul t positive small l)
    (m := calibration (m - center)) (z := calibration (p - center))
    first_barrier last_barrier first last horizontal vertical
    (by simpa only [calibration.norm_map] using outside)

theorem inner_barrier_point_exclusion_of_norm_le (i l : FiveSector) (center m p : Plane)
    (first_barrier : 0 < (B.sectorFrame i (m - center)).re ∧
      0 < (B.sectorFrame i (m - center)).im)
    (last_barrier : 0 < (B.sectorFrame l (m - center)).re ∧
      0 < (B.sectorFrame l (m - center)).im)
    (first : 0 ≤ (B.sectorFrame i (p - center)).re ∧
      0 < (B.sectorFrame i (p - center)).im)
    (last : 0 ≤ (B.sectorFrame l (p - center)).re ∧
      0 < (B.sectorFrame l (p - center)).im)
    (horizontal : (B.sectorFrame i (p - center)).re < (B.sectorFrame i (m - center)).re)
    (vertical : (B.sectorFrame l (p - center)).im < (B.sectorFrame l (m - center)).im)
    (outside : ‖m - center‖ ≤ ‖p - center‖) : False := by
  let calibration := N.calibratedFrame D B.anchor B.reference
  let F := Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place
  let G := Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small l).place
  exact oriented_inner_barrier_point_exclusion_of_norm_le F G
    (fiveSectorFrame_commutes_mul t positive small i)
    (fiveSectorFrame_commutes_mul t positive small l)
    (m := calibration (m - center)) (z := calibration (p - center))
    first_barrier last_barrier first last horizontal vertical
    (by simpa only [calibration.norm_map] using outside)

variable {n : ℕ}
  (i l : FiveSector)
  (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
  (parents : ∀ j k : Fin n, k.val = j.val + 1 →
    N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
  (first_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
  (last_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) l (chain j))
  (first_directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
    K.projectedVertex (chain j).val ∈ closedFiveSector t i)
  (last_directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
    K.projectedVertex (chain j).val ∈ closedFiveSector t l)
  (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)

include parents first_sectors last_sectors first_directions last_directions budget

theorem chain_points_cross_frame_alternative (j k : Fin n) (s r : unitInterval)
    (center : Plane) :
    (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ≤
        (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re ∨
      (B.sectorFrame l (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im ≤
        (B.sectorFrame l (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im := by
  have ordered : (j < k ∨ j = k ∧ s ≤ r) ∨ (k < j ∨ k = j ∧ r ≤ s) := by
    rcases lt_trichotomy j k with before | rfl | after
    · exact Or.inl (Or.inl before)
    · exact (le_total s r).imp (fun h => Or.inr ⟨rfl, h⟩) (fun h => Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl after)
  rcases ordered with before | after
  · have along := B.chain_entrance_horizontal_order i chain parents first_sectors first_directions
      budget j k s r before
    have matched := (B.matched_bank_points_order i (chain j) (first_sectors j) (1 - (s : ℝ))
      (by linarith [s.property.1]) budget).1
    left
    simpa only [map_sub, Complex.sub_re] using
      sub_le_sub_right (matched.trans along) (B.sectorFrame i center).re
  · have along := B.chain_exit_vertical_order l chain parents last_sectors last_directions
      budget k j r s after
    have matched := (B.matched_bank_points_order l (chain k) (last_sectors k) (1 - (r : ℝ))
      (by linarith [r.property.1]) budget).2
    right
    simpa only [map_sub, Complex.sub_im] using
      sub_le_sub_right (matched.trans along) (B.sectorFrame l center).im

/-- Compare actual terminal parent endpoints. The useful coordinate is selected
in its own sector frame by their order along the genuine fine parent path. -/
theorem chain_terminal_cross_frame_alternative (j k : Fin n) (center : Plane) :
    (B.sectorFrame i (N.parentExitPoint D (chain j) 0 - center)).re ≤
        (B.sectorFrame i (N.parentEntrancePoint D (chain k) 0 - center)).re ∨
      (B.sectorFrame l (N.parentEntrancePoint D (chain k) 0 - center)).im ≤
        (B.sectorFrame l (N.parentExitPoint D (chain j) 0 - center)).im := by
  have one : ((1 : unitInterval) : ℝ) = 1 := rfl
  rcases le_or_gt j k with before | after
  · have along := B.chain_entrance_horizontal_order i chain parents first_sectors first_directions
      budget j k 1 1 (before.lt_or_eq.imp id (fun equal => ⟨equal, le_rfl⟩))
    have matched := (B.matched_bank_points_order i (chain j) (first_sectors j) 0
      (by norm_num) budget).1
    rw [one, sub_self] at along
    left
    simpa only [map_sub, Complex.sub_re] using
      sub_le_sub_right (matched.trans along) (B.sectorFrame i center).re
  · have along := B.chain_exit_vertical_order l chain parents last_sectors last_directions
      budget k j 1 1 (Or.inl after)
    have matched := (B.matched_bank_points_order l (chain k) (last_sectors k) 0
      (by norm_num) budget).2
    rw [one, sub_self] at along
    right
    simpa only [map_sub, Complex.sub_im] using
      sub_le_sub_right (matched.trans along) (B.sectorFrame l center).im

/-- Both circle arcs cross before their own maximal terminal. Their terminal
copies may have different physical heights and use different quadrant frames.
Actual bank-chain progress chooses one of those two inner points as a separator. -/
theorem chain_terminal_early_circle_separation (j k : Fin n) (center : Plane) {radius : ℝ}
    (exit_inside : ‖N.parentExitPoint D (chain j) 0 - center‖ < radius)
    (entrance_inside : ‖N.parentEntrancePoint D (chain k) 0 - center‖ < radius)
    (first_exit : 0 < (B.sectorFrame i (N.parentExitPoint D (chain j) 0 - center)).re ∧
      0 < (B.sectorFrame i (N.parentExitPoint D (chain j) 0 - center)).im)
    (last_exit : 0 < (B.sectorFrame l (N.parentExitPoint D (chain j) 0 - center)).re ∧
      0 < (B.sectorFrame l (N.parentExitPoint D (chain j) 0 - center)).im)
    (first_entrance : 0 < (B.sectorFrame i (N.parentEntrancePoint D (chain k) 0 - center)).re ∧
      0 < (B.sectorFrame i (N.parentEntrancePoint D (chain k) 0 - center)).im)
    (last_entrance : 0 < (B.sectorFrame l (N.parentEntrancePoint D (chain k) 0 - center)).re ∧
      0 < (B.sectorFrame l (N.parentEntrancePoint D (chain k) 0 - center)).im)
    {A E : Set Plane}
    (first : ∀ p ∈ A, 0 ≤ (B.sectorFrame i (p - center)).re ∧
      0 < (B.sectorFrame i (p - center)).im ∧
      (B.sectorFrame i (p - center)).re ≤
        (B.sectorFrame i (N.parentExitPoint D (chain j) 0 - center)).re)
    (last : ∀ p ∈ E, 0 ≤ (B.sectorFrame l (p - center)).re ∧
      0 < (B.sectorFrame l (p - center)).im ∧
      (B.sectorFrame l (p - center)).im ≤
        (B.sectorFrame l (N.parentEntrancePoint D (chain k) 0 - center)).im)
    (first_radius : ∀ p ∈ A, ‖p - center‖ = radius)
    (last_radius : ∀ p ∈ E, ‖p - center‖ = radius) : Disjoint A E := by
  apply Set.disjoint_left.mpr
  intro p member other_member
  have first_bounds := first p member
  have last_bounds := last p other_member
  rcases B.chain_terminal_cross_frame_alternative i l chain parents first_sectors last_sectors
    first_directions last_directions budget j k center with horizontal | vertical
  · exact B.inner_barrier_point_exclusion i l center (N.parentEntrancePoint D (chain k) 0) p
      first_entrance last_entrance ⟨first_bounds.1, first_bounds.2.1⟩
      ⟨last_bounds.1, last_bounds.2.1⟩ (first_bounds.2.2.trans horizontal) last_bounds.2.2
      (entrance_inside.trans_eq (first_radius p member).symm)
  · exact B.inner_barrier_point_exclusion i l center (N.parentExitPoint D (chain j) 0) p
      first_exit last_exit ⟨first_bounds.1, first_bounds.2.1⟩
      ⟨last_bounds.1, last_bounds.2.1⟩ first_bounds.2.2 (last_bounds.2.2.trans vertical)
      (exit_inside.trans_eq (last_radius p other_member).symm)

/-- Each bounding bank point may be either an inner terminal or an actual
circle crossing. Strict open-arc coordinate bounds therefore cover all four
early/late combinations with one bank-chain comparison. -/
theorem chain_points_circle_separation (j k : Fin n) (s r : unitInterval)
    (center : Plane) {radius : ℝ}
    (exit_inside : ‖N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center‖ ≤ radius)
    (entrance_inside : ‖N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center‖ ≤ radius)
    (first_exit :
      0 < (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ∧
      0 < (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im)
    (last_exit :
      0 < (B.sectorFrame l (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ∧
      0 < (B.sectorFrame l (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im)
    (first_entrance :
      0 < (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re ∧
      0 < (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im)
    (last_entrance :
      0 < (B.sectorFrame l (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re ∧
      0 < (B.sectorFrame l (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im)
    {A E : Set Plane}
    (first : ∀ p ∈ A, 0 ≤ (B.sectorFrame i (p - center)).re ∧
      0 < (B.sectorFrame i (p - center)).im ∧
      (B.sectorFrame i (p - center)).re <
        (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re)
    (last : ∀ p ∈ E, 0 ≤ (B.sectorFrame l (p - center)).re ∧
      0 < (B.sectorFrame l (p - center)).im ∧
      (B.sectorFrame l (p - center)).im <
        (B.sectorFrame l (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im)
    (first_radius : ∀ p ∈ A, ‖p - center‖ = radius)
    (last_radius : ∀ p ∈ E, ‖p - center‖ = radius) : Disjoint A E := by
  apply Set.disjoint_left.mpr
  intro p member other_member
  have first_bounds := first p member
  have last_bounds := last p other_member
  rcases B.chain_points_cross_frame_alternative i l chain parents first_sectors last_sectors
    first_directions last_directions budget j k s r center with horizontal | vertical
  · exact B.inner_barrier_point_exclusion_of_norm_le i l center
      (N.parentEntrancePoint D (chain k) (1 - (r : ℝ))) p
      first_entrance last_entrance ⟨first_bounds.1, first_bounds.2.1⟩
      ⟨last_bounds.1, last_bounds.2.1⟩ (first_bounds.2.2.trans_le horizontal) last_bounds.2.2
      (entrance_inside.trans_eq (first_radius p member).symm)
  · exact B.inner_barrier_point_exclusion_of_norm_le i l center
      (N.parentExitPoint D (chain j) (1 - (s : ℝ))) p
      first_exit last_exit ⟨first_bounds.1, first_bounds.2.1⟩
      ⟨last_bounds.1, last_bounds.2.1⟩ first_bounds.2.2 (last_bounds.2.2.trans_le vertical)
      (exit_inside.trans_eq (last_radius p other_member).symm)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
