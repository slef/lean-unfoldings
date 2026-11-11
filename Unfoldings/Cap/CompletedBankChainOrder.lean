module

public import Unfoldings.Cap.CompletedBranchJumpOrder
public import Unfoldings.Topology.FiniteMonotonePieces

/-! Whole actual bank chains retain their order across every sibling displacement at a branch. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem parent_vectors_quadrant (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i) :
    (0 < (B.sectorFrame i (N.parentEntryVector D e)).re ∧
      0 < (B.sectorFrame i (N.parentEntryVector D e)).im) ∧
    (0 < (B.sectorFrame i (N.parentExitVector D e)).re ∧
      0 < (B.sectorFrame i (N.parentExitVector D e)).im) :=
  ⟨B.quadrants i (N.parentBankOpening D e).entranceFace _ inside
      (N.completed_parent_direction_ne_zero e.val e.property),
    B.quadrants i (N.parentBankOpening D e).exitFace _ inside
      (N.completed_parent_direction_ne_zero e.val e.property)⟩

/-- The right bank progresses horizontally even at branches, where it may jump downwards. -/
theorem chain_entrance_horizontal_order {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
      K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (j k : Fin n) (s r : unitInterval) (before : j < k ∨ j = k ∧ s ≤ r) :
    (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (s : ℝ)))).re ≤
      (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)))).re := by
  let F := fun j (s : unitInterval) =>
    (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (s : ℝ)))).re
  apply finite_monotone_pieces F ?_ ?_ j k s r before
  · intro j a b ordered
    have quadrant := (B.parent_vectors_quadrant i (chain j) (directions j)).1.1
    have product := mul_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ b from ordered)) quadrant.le
    change (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (a : ℝ)))).re ≤
      (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (b : ℝ)))).re
    simp only [parentEntrancePoint, map_sub, map_smul, Complex.sub_re, Complex.smul_re,
      smul_eq_mul]
    linarith
  · intro j k adjacent
    have jump := (B.parent_child_bank_jump_order i (chain k) (chain j)
      (parents j k adjacent) (sectors k) budget).1.1
    simpa [F] using jump

/-- The left bank progresses vertically even at branches, where it may jump leftwards. -/
theorem chain_exit_vertical_order {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
      K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (j k : Fin n) (s r : unitInterval) (before : j < k ∨ j = k ∧ s ≤ r) :
    (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).im ≤
      (B.sectorFrame i (N.parentExitPoint D (chain k) (1 - (r : ℝ)))).im := by
  let F := fun j (s : unitInterval) =>
    (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).im
  apply finite_monotone_pieces F ?_ ?_ j k s r before
  · intro j a b ordered
    have quadrant := (B.parent_vectors_quadrant i (chain j) (directions j)).2.2
    have product := mul_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ b from ordered)) quadrant.le
    change (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (a : ℝ)))).im ≤
      (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (b : ℝ)))).im
    simp only [parentExitPoint, map_sub, map_smul, Complex.sub_im, Complex.smul_im,
      smul_eq_mul]
    linarith
  · intro j k adjacent
    have jump := (B.parent_child_bank_jump_order i (chain k) (chain j)
      (parents j k adjacent) (sectors k) budget).2.2
    simpa [F] using jump

/-- Whole edges on different levels of a branching path have the same left-or-above order.
The proof uses the derived sibling jumps; it never treats a branching bank as continuous. -/
theorem chain_left_or_above {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
      K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (j k : Fin n) (s r : unitInterval) :
    (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).re ≤
        (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)))).re ∨
      (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)))).im ≤
        (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).im := by
  have ordered : (j < k ∨ j = k ∧ s ≤ r) ∨ (k < j ∨ k = j ∧ r ≤ s) := by
    rcases lt_trichotomy j k with before | rfl | after
    · exact Or.inl (Or.inl before)
    · exact (le_total s r).imp (fun h => Or.inr ⟨rfl, h⟩) (fun h => Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl after)
  rcases ordered with before | after
  · exact Or.inl ((B.matched_bank_points_order i (chain j) (sectors j) (1 - (s : ℝ))
      (by linarith [s.property.1]) budget).1.trans
      (B.chain_entrance_horizontal_order i chain parents sectors directions budget j k s r before))
  · exact Or.inr ((B.matched_bank_points_order i (chain k) (sectors k) (1 - (r : ℝ))
      (by linarith [r.property.1]) budget).2.trans
      (B.chain_exit_vertical_order i chain parents sectors directions budget k j r s after))

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
