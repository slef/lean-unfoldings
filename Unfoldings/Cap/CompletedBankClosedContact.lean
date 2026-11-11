module

public import Unfoldings.Cap.CompletedBankChainContact
public import Unfoldings.Topology.FiniteStrictPieces

/-! Closed opposite-bank contacts include branch endpoints, with an exact flatness criterion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem matched_bank_strict_vertical (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sectors : N.CurvedSubtreeInSector (t := t) i e) {s : ℝ} (before_child : s < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (curved : 0 < N.completedSubtreeCurvature e.val) :
    (B.sectorFrame i (N.parentEntrancePoint D e s)).im <
      (B.sectorFrame i (N.parentExitPoint D e s)).im := by
  classical
  let frame := B.sectorFrame i
  have proper : 0 ≤
      (frame (∑ v ∈ Finset.univ.erase e, if N.spanningCompletion.parents.Ancestor v.val e.val then
        N.parentExitVector D v - N.parentEntryVector D v else 0)).im := by
    simp only [map_sum, Complex.im_sum]
    apply Finset.sum_nonneg
    intro v _
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order i e sectors budget.le v reaches).2
    · simp only [map_zero, Complex.zero_im, le_refl]
  have top := (B.parent_vector_strict_order i e inside budget curved).2
  have positive_gap := add_pos_of_nonneg_of_pos proper
    (mul_pos (sub_pos.mpr before_child) top)
  have gap : frame (N.parentExitPoint D e s) - frame (N.parentEntrancePoint D e s) =
      frame (∑ v ∈ Finset.univ.erase e, if N.spanningCompletion.parents.Ancestor v.val e.val then
        N.parentExitVector D v - N.parentEntryVector D v else 0) +
      (1 - s) • frame (N.parentExitVector D e - N.parentEntryVector D e) := by
    rw [← map_sub, N.matched_bank_gap_eq D e s, map_add, map_smul]
  have imaginary := congrArg Complex.im gap
  simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul] at imaginary
  change (frame _).im < (frame _).im
  linarith

theorem chain_entrance_piece_strict (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i) :
    StrictMono (fun s : unitInterval =>
      (B.sectorFrame i (N.parentEntrancePoint D e (1 - (s : ℝ)))).re) := by
  intro s r ordered
  have quadrant := (B.parent_vectors_quadrant i e inside).1.1
  have product := mul_pos (sub_pos.mpr (show (s : ℝ) < r from ordered)) quadrant
  simp only [parentEntrancePoint, map_sub, map_smul, Complex.sub_re, Complex.smul_re,
    smul_eq_mul]
  linarith

theorem chain_exit_piece_strict (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i) :
    StrictMono (fun s : unitInterval =>
      (B.sectorFrame i (N.parentExitPoint D e (1 - (s : ℝ)))).im) := by
  intro s r ordered
  have quadrant := (B.parent_vectors_quadrant i e inside).2.2
  have product := mul_pos (sub_pos.mpr (show (s : ℝ) < r from ordered)) quadrant
  simp only [parentExitPoint, map_sub, map_smul, Complex.sub_im, Complex.smul_im,
    smul_eq_mul]
  linarith

include B in
/-- Different closed edges can meet only at a shared physical branch endpoint, and the
earlier subtree is flat. A matched contact is flat except possibly at its own child endpoint. -/
theorem chain_closed_contact {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
      K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (j k : Fin n) (s r : unitInterval)
    (same : N.parentExitPoint D (chain j) (1 - (s : ℝ)) =
      N.parentEntrancePoint D (chain k) (1 - (r : ℝ))) :
    (j = k ∧ s = r ∧ (s = 0 ∨ N.completedSubtreeCurvature (chain j).val = 0)) ∨
      (k.val = j.val + 1 ∧ s = 1 ∧ r = 0 ∧ N.completedSubtreeCurvature (chain j).val = 0) ∨
      (j.val = k.val + 1 ∧ s = 0 ∧ r = 1 ∧ N.completedSubtreeCurvature (chain k).val = 0) := by
  rcases lt_trichotomy j k with before | equal | after
  · let F := fun j (s : unitInterval) =>
      (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (s : ℝ)))).re
    have jumps : ∀ j k : Fin n, k.val = j.val + 1 → F j 1 ≤ F k 0 := by
      intro j k adjacent
      have jump := (B.parent_child_bank_jump_order i (chain k) (chain j)
        (parents j k adjacent) (sectors k) budget.le).1.1
      simpa [F] using jump
    have reversed : F k r ≤ F j s := by
      have matched := (B.matched_bank_points_order i (chain j) (sectors j) (1 - (s : ℝ))
        (by linarith [s.property.1]) budget.le).1
      rwa [same] at matched
    obtain ⟨adjacent, first, last, _⟩ := finite_strict_pieces_contact F
      (fun j => B.chain_entrance_piece_strict i (chain j) (directions j)) jumps j k s r
      before reversed
    refine Or.inr (Or.inl ⟨adjacent, first, last, ?_⟩)
    apply le_antisymm _ (N.completedSubtreeCurvature_nonneg (chain j).val)
    by_contra curved
    have spositive : 0 < (s : ℝ) := by rw [first]; norm_num
    have strict := B.matched_bank_strict_horizontal i (chain j) (directions j) (sectors j)
      (show 1 - (s : ℝ) < 1 by linarith) budget (lt_of_not_ge curved)
    have later := B.chain_entrance_horizontal_order i chain parents sectors directions budget.le
      j k s r (Or.inl before)
    have gap := strict.trans_le later
    rw [same] at gap
    exact (lt_irrefl _ gap).elim
  · subst k
    have parameters := B.bank_intersection_parameter_eq i (chain j) (directions j) (sectors j)
      (show 1 - (r : ℝ) ≤ 1 by linarith [r.property.1])
      (show 1 - (s : ℝ) ≤ 1 by linarith [s.property.1]) budget.le same.symm
    have matched : s = r := Subtype.ext (by linarith)
    refine Or.inl ⟨rfl, matched, ?_⟩
    by_cases zero : s = 0
    · exact Or.inl zero
    · have spositive : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1
        (fun equal => zero (Subtype.ext equal.symm))
      have rpositive : 0 < (r : ℝ) := matched ▸ spositive
      exact Or.inr (B.parent_bank_contact_flat i (chain j) (directions j) (sectors j)
        (show 1 - (r : ℝ) < 1 by linarith) (show 1 - (s : ℝ) < 1 by linarith)
        budget same.symm)
  · let F := fun j (s : unitInterval) =>
      (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).im
    have jumps : ∀ j k : Fin n, k.val = j.val + 1 → F j 1 ≤ F k 0 := by
      intro j k adjacent
      have jump := (B.parent_child_bank_jump_order i (chain k) (chain j)
        (parents j k adjacent) (sectors k) budget.le).2.2
      simpa [F] using jump
    have reversed : F j s ≤ F k r := by
      have matched := (B.matched_bank_points_order i (chain k) (sectors k) (1 - (r : ℝ))
        (by linarith [r.property.1]) budget.le).2
      rwa [← same] at matched
    obtain ⟨adjacent, first, last, _⟩ := finite_strict_pieces_contact F
      (fun j => B.chain_exit_piece_strict i (chain j) (directions j)) jumps k j r s after reversed
    refine Or.inr (Or.inr ⟨adjacent, last, first, ?_⟩)
    apply le_antisymm _ (N.completedSubtreeCurvature_nonneg (chain k).val)
    by_contra curved
    have rpositive : 0 < (r : ℝ) := by rw [first]; norm_num
    have strict := B.matched_bank_strict_vertical i (chain k) (directions k) (sectors k)
      (show 1 - (r : ℝ) < 1 by linarith) budget (lt_of_not_ge curved)
    have later := B.chain_exit_vertical_order i chain parents sectors directions budget.le
      k j r s (Or.inl after)
    have gap := strict.trans_le later
    rw [same] at gap
    exact (lt_irrefl _ gap).elim

include B in
/-- Even a closed-edge bank contact identifies the same projected surface point. In particular,
contacts between different edge names at a branch do not create false point identifications. -/
theorem chain_contact_same_projected_point {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
      K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (j k : Fin n) (s r : unitInterval)
    (same : N.parentExitPoint D (chain j) (1 - (s : ℝ)) =
      N.parentEntrancePoint D (chain k) (1 - (r : ℝ))) :
    AffineMap.lineMap (K.projectedVertex (chain j).val)
      (K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val)) (s : ℝ) =
    AffineMap.lineMap (K.projectedVertex (chain k).val)
      (K.projectedVertex (N.spanningCompletion.parents.parent (chain k).val)) (r : ℝ) := by
  rcases B.chain_closed_contact i chain parents sectors directions budget j k s r same with
    ⟨rfl, rfl, _⟩ | ⟨adjacent, rfl, rfl, _⟩ | ⟨adjacent, rfl, rfl, _⟩
  · rfl
  · change AffineMap.lineMap _ _ (1 : ℝ) = AffineMap.lineMap _ _ (0 : ℝ)
    rw [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, parents j k adjacent]
  · change AffineMap.lineMap _ _ (0 : ℝ) = AffineMap.lineMap _ _ (1 : ℝ)
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, parents k j adjacent]

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
