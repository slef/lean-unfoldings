module

public import Unfoldings.Cap.ClosedBarrierContact
public import Unfoldings.Cap.CompletedBankClosedContact
public import Unfoldings.Cap.CompletedBankCoordinateContact

/-! Weak circle contacts on a completed chain identify the same physical point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- The named comparison banks may lie strictly inside the circle. Equality in their
ordered coordinates still forces matching parameters or a shared branch endpoint. -/
theorem chain_weak_circle_caps_contact_same_projected_point {n : ℕ} (i l : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (first_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (last_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) l (chain j))
    (first_directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) -
        K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (last_directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) -
        K.projectedVertex (chain j).val ∈ closedFiveSector t l)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (j k : Fin n) (s r : unitInterval) (center : Plane) {radius first_bound last_bound : ℝ}
    (exit_inside : ‖N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center‖ ≤ radius)
    (entrance_inside : ‖N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center‖ ≤ radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im) ∧
      (0 < (B.sectorFrame a (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im))
    (first_bound_le : first_bound ≤
      (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re)
    (last_bound_le : last_bound ≤
      (B.sectorFrame l (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im)
    {p : Plane} (member : p ∈ weakCircleUpperCap (B.sectorFrame i) center radius first_bound ∩
      weakCircleLowerCap (B.sectorFrame l) center radius last_bound) :
    AffineMap.lineMap (K.projectedVertex (chain j).val)
      (K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val)) (s : ℝ) =
    AffineMap.lineMap (K.projectedVertex (chain k).val)
      (K.projectedVertex (N.spanningCompletion.parents.parent (chain k).val)) (r : ℝ) := by
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
    have horizontal : (B.sectorFrame i
        (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ≤
        (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re := by
      simpa only [map_sub, Complex.sub_re] using
        sub_le_sub_right (matched.trans along) (B.sectorFrame i center).re
    have contact : p = N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) :=
      B.inner_barrier_point_eq_of_norm_le i l center _ p
        (quadrants i (Or.inl rfl)).2 (quadrants l (Or.inr rfl)).2
        ⟨member.1.1, member.1.2.1⟩ ⟨member.2.1, member.2.2.1⟩
        ((member.1.2.2.1.trans first_bound_le).trans horizontal)
        (member.2.2.2.1.trans last_bound_le) (entrance_inside.trans_eq member.1.2.2.2.symm)
    let F := fun j (s : unitInterval) =>
      (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (s : ℝ)))).re
    have reverse : F k r ≤ F j s := by
      have bound := member.1.2.2.1.trans first_bound_le
      rw [contact] at bound
      simp only [map_sub, Complex.sub_re] at bound
      dsimp only [F]
      linarith
    rcases before with before | ⟨rfl, before⟩
    · have jumps : ∀ j k : Fin n, k.val = j.val + 1 → F j 1 ≤ F k 0 := by
        intro j k adjacent
        have jump := (B.parent_child_bank_jump_order i (chain k) (chain j)
          (parents j k adjacent) (first_sectors k) budget).1.1
        simpa [F] using jump
      obtain ⟨adjacent, rfl, rfl, _⟩ := finite_strict_pieces_contact F
        (fun j => B.chain_entrance_piece_strict i (chain j) (first_directions j)) jumps
        j k s r before reverse
      change AffineMap.lineMap _ _ (1 : ℝ) = AffineMap.lineMap _ _ (0 : ℝ)
      rw [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, parents j k adjacent]
    · have parameters : r = s := le_antisymm
        ((B.chain_entrance_piece_strict i (chain j) (first_directions j)).le_iff_le.mp reverse)
        before
      subst r
      rfl
  · have along := B.chain_exit_vertical_order l chain parents last_sectors last_directions
      budget k j r s after
    have matched := (B.matched_bank_points_order l (chain k) (last_sectors k) (1 - (r : ℝ))
      (by linarith [r.property.1]) budget).2
    have vertical : (B.sectorFrame l
        (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im ≤
        (B.sectorFrame l (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im := by
      simpa only [map_sub, Complex.sub_im] using
        sub_le_sub_right (matched.trans along) (B.sectorFrame l center).im
    have contact : p = N.parentExitPoint D (chain j) (1 - (s : ℝ)) :=
      B.inner_barrier_point_eq_of_norm_le i l center _ p
        (quadrants i (Or.inl rfl)).1 (quadrants l (Or.inr rfl)).1
        ⟨member.1.1, member.1.2.1⟩ ⟨member.2.1, member.2.2.1⟩
        (member.1.2.2.1.trans first_bound_le)
        ((member.2.2.2.1.trans last_bound_le).trans vertical)
        (exit_inside.trans_eq member.2.2.2.2.symm)
    let F := fun j (s : unitInterval) =>
      (B.sectorFrame l (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).im
    have reverse : F j s ≤ F k r := by
      have bound := member.2.2.2.1.trans last_bound_le
      rw [contact] at bound
      simp only [map_sub, Complex.sub_im] at bound
      dsimp only [F]
      linarith
    rcases after with after | ⟨rfl, after⟩
    · have jumps : ∀ j k : Fin n, k.val = j.val + 1 → F j 1 ≤ F k 0 := by
        intro j k adjacent
        have jump := (B.parent_child_bank_jump_order l (chain k) (chain j)
          (parents j k adjacent) (last_sectors k) budget).2.2
        simpa [F] using jump
      obtain ⟨adjacent, rfl, rfl, _⟩ := finite_strict_pieces_contact F
        (fun j => B.chain_exit_piece_strict l (chain j) (last_directions j)) jumps
        k j r s after reverse
      change AffineMap.lineMap _ _ (0 : ℝ) = AffineMap.lineMap _ _ (1 : ℝ)
      rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, parents k j adjacent]
    · have parameters : s = r := le_antisymm
        ((B.chain_exit_piece_strict l (chain k) (last_directions k)).le_iff_le.mp reverse)
        after
      subst s
      rfl

/-- With curvature strictly below a half turn, contact identifies both bank values,
even when the comparison points were allowed to lie inside the circle. -/
theorem chain_weak_circle_caps_contact_values {n : ℕ} (i l : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (first_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (last_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) l (chain j))
    (first_directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) -
        K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (last_directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) -
        K.projectedVertex (chain j).val ∈ closedFiveSector t l)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (j k : Fin n) (s r : unitInterval) (center : Plane) {radius first_bound last_bound : ℝ}
    (exit_inside : ‖N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center‖ ≤ radius)
    (entrance_inside : ‖N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center‖ ≤ radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im) ∧
      (0 < (B.sectorFrame a (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im))
    (first_bound_le : first_bound ≤
      (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re)
    (last_bound_le : last_bound ≤
      (B.sectorFrame l (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im)
    {p : Plane} (member : p ∈ weakCircleUpperCap (B.sectorFrame i) center radius first_bound ∩
      weakCircleLowerCap (B.sectorFrame l) center radius last_bound) :
    p = N.parentExitPoint D (chain j) (1 - (s : ℝ)) ∧
      N.parentExitPoint D (chain j) (1 - (s : ℝ)) =
        N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) := by
  have ordered : (j < k ∨ j = k ∧ s ≤ r) ∨ (k < j ∨ k = j ∧ r ≤ s) := by
    rcases lt_trichotomy j k with before | rfl | after
    · exact Or.inl (Or.inl before)
    · exact (le_total s r).imp (fun h => Or.inr ⟨rfl, h⟩) (fun h => Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl after)
  rcases ordered with before | after
  · have along := B.chain_entrance_horizontal_order i chain parents first_sectors first_directions
      budget.le j k s r before
    have matched := (B.matched_bank_points_order i (chain j) (first_sectors j) (1 - (s : ℝ))
      (by linarith [s.property.1]) budget.le).1
    have horizontal : (B.sectorFrame i
        (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ≤
        (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re := by
      simpa only [map_sub, Complex.sub_re] using
        sub_le_sub_right (matched.trans along) (B.sectorFrame i center).re
    have contact : p = N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) :=
      B.inner_barrier_point_eq_of_norm_le i l center _ p
        (quadrants i (Or.inl rfl)).2 (quadrants l (Or.inr rfl)).2
        ⟨member.1.1, member.1.2.1⟩ ⟨member.2.1, member.2.2.1⟩
        ((member.1.2.2.1.trans first_bound_le).trans horizontal)
        (member.2.2.2.1.trans last_bound_le) (entrance_inside.trans_eq member.1.2.2.2.symm)
    have reverse : (B.sectorFrame i
        (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)))).re ≤
        (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).re := by
      have bound := member.1.2.2.1.trans first_bound_le
      rw [contact] at bound
      simpa only [map_sub, Complex.sub_re, sub_le_sub_iff_right] using bound
    have banks := B.chain_entrance_reversed_contact i chain parents first_sectors first_directions
      budget j k s r before reverse
    exact ⟨contact.trans banks.symm, banks⟩
  · have along := B.chain_exit_vertical_order l chain parents last_sectors last_directions
      budget.le k j r s after
    have matched := (B.matched_bank_points_order l (chain k) (last_sectors k) (1 - (r : ℝ))
      (by linarith [r.property.1]) budget.le).2
    have vertical : (B.sectorFrame l
        (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im ≤
        (B.sectorFrame l (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im := by
      simpa only [map_sub, Complex.sub_im] using
        sub_le_sub_right (matched.trans along) (B.sectorFrame l center).im
    have contact : p = N.parentExitPoint D (chain j) (1 - (s : ℝ)) :=
      B.inner_barrier_point_eq_of_norm_le i l center _ p
        (quadrants i (Or.inl rfl)).1 (quadrants l (Or.inr rfl)).1
        ⟨member.1.1, member.1.2.1⟩ ⟨member.2.1, member.2.2.1⟩
        (member.1.2.2.1.trans first_bound_le)
        ((member.2.2.2.1.trans last_bound_le).trans vertical)
        (exit_inside.trans_eq member.2.2.2.2.symm)
    have reverse : (B.sectorFrame l
        (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).im ≤
        (B.sectorFrame l (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)))).im := by
      have bound := member.2.2.2.1.trans last_bound_le
      rw [contact] at bound
      simpa only [map_sub, Complex.sub_im, sub_le_sub_iff_right] using bound
    have banks := B.chain_exit_reversed_contact l chain parents last_sectors last_directions
      budget k j r s after reverse
    exact ⟨contact, banks.symm⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
