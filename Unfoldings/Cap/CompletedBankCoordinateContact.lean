module

public import Unfoldings.Cap.CompletedBankClosedContact
public import Unfoldings.Cap.CompletedExcursionStrictOrder
public import Unfoldings.Cap.CompletedFlatBanks

/-! Equality in a controlling coordinate identifies the actual completed bank values. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem matched_bank_horizontal_eq_iff (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    {a : ℝ} (before_child : a ≤ 1) :
    (B.sectorFrame i (N.parentExitPoint D e a)).re =
        (B.sectorFrame i (N.parentEntrancePoint D e a)).re ↔
      N.parentExitPoint D e a = N.parentEntrancePoint D e a := by
  refine ⟨?_, fun same => congrArg (fun p => (B.sectorFrame i p).re) same⟩
  intro equal
  by_cases child : a = 1
  · subst a
    have criterion := B.vertex_entrance_horizontal_eq_iff i e sectors budget
      (N.parentBankOpening D e).leave (N.parentBankOpening D e).exit_vertex
    rw [← N.parentExitPoint_child_index D e] at criterion
    apply criterion.mp
    rw [map_sub, Complex.sub_re, equal, sub_self]
  · have flat : N.completedSubtreeCurvature e.val = 0 := by
      apply le_antisymm _ (N.completedSubtreeCurvature_nonneg e.val)
      by_contra curved
      have strict := B.matched_bank_strict_horizontal i e inside sectors
        (lt_of_le_of_ne before_child child) budget (lt_of_not_ge curved)
      exact strict.ne equal
    exact N.completed_parent_points_eq_of_flat D e flat a

theorem matched_bank_vertical_eq_iff (i : FiveSector)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (inside : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
      K.projectedVertex e.val ∈ closedFiveSector t i)
    (sectors : N.CurvedSubtreeInSector (t := t) i e)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    {a : ℝ} (before_child : a ≤ 1) :
    (B.sectorFrame i (N.parentExitPoint D e a)).im =
        (B.sectorFrame i (N.parentEntrancePoint D e a)).im ↔
      N.parentExitPoint D e a = N.parentEntrancePoint D e a := by
  refine ⟨?_, fun same => congrArg (fun p => (B.sectorFrame i p).im) same⟩
  intro equal
  by_cases child : a = 1
  · subst a
    have criterion := B.vertex_exit_vertical_eq_iff i e sectors budget
      (finRotate (N.completedContour.length + 1) (N.parentBankOpening D e).enter)
      (N.parentBankOpening D e).entrance_next_vertex
    rw [← N.parentEntrancePoint_child_index D e] at criterion
    exact (criterion.mp (by rw [map_sub, Complex.sub_im, equal, sub_self])).symm
  · have flat : N.completedSubtreeCurvature e.val = 0 := by
      apply le_antisymm _ (N.completedSubtreeCurvature_nonneg e.val)
      by_contra curved
      have strict := B.matched_bank_strict_vertical i e inside sectors
        (lt_of_le_of_ne before_child child) budget (lt_of_not_ge curved)
      exact strict.ne equal.symm
    exact N.completed_parent_points_eq_of_flat D e flat a

theorem chain_entrance_reversed_contact {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) -
        K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (j k : Fin n) (s r : unitInterval) (before : j < k ∨ j = k ∧ s ≤ r)
    (reverse : (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)))).re ≤
      (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).re) :
    N.parentExitPoint D (chain j) (1 - (s : ℝ)) =
      N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) := by
  let F := fun j (s : unitInterval) =>
    (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (s : ℝ)))).re
  have matched := (B.matched_bank_points_order i (chain j) (sectors j) (1 - (s : ℝ))
    (by linarith [s.property.1]) budget.le).1
  have along := B.chain_entrance_horizontal_order i chain parents sectors directions
    budget.le j k s r before
  have coordinate : (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).re =
      (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)))).re :=
    le_antisymm (matched.trans along) reverse
  rcases before with before | ⟨rfl, before⟩
  · have jumps : ∀ j k : Fin n, k.val = j.val + 1 → F j 1 ≤ F k 0 := by
      intro j k adjacent
      have jump := (B.parent_child_bank_jump_order i (chain k) (chain j)
        (parents j k adjacent) (sectors k) budget.le).1.1
      simpa [F] using jump
    obtain ⟨adjacent, rfl, rfl, _⟩ := finite_strict_pieces_contact F
      (fun j => B.chain_entrance_piece_strict i (chain j) (directions j)) jumps
      j k s r before (reverse.trans matched)
    simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_self, sub_zero] at coordinate ⊢
    have criterion := B.vertex_entrance_horizontal_eq_iff i (chain k) (sectors k) budget
      (finRotate (N.completedContour.length + 1) (N.parentBankOpening D (chain j)).leave)
      ((N.parentBankOpening D (chain j)).exit_next_vertex.trans (parents j k adjacent))
    rw [← N.parentExitPoint_parent_index D (chain j)] at criterion
    exact criterion.mp (by rw [map_sub, Complex.sub_re, coordinate, sub_self])
  · have parameters : r = s := le_antisymm
      ((B.chain_entrance_piece_strict i (chain j) (directions j)).le_iff_le.mp
        (reverse.trans matched)) before
    subst r
    exact (B.matched_bank_horizontal_eq_iff i (chain j) (directions j) (sectors j) budget
      (by linarith [s.property.1])).mp coordinate

theorem chain_exit_reversed_contact {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) -
        K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (j k : Fin n) (s r : unitInterval) (before : j < k ∨ j = k ∧ s ≤ r)
    (reverse : (B.sectorFrame i (N.parentExitPoint D (chain k) (1 - (r : ℝ)))).im ≤
      (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (s : ℝ)))).im) :
    N.parentEntrancePoint D (chain j) (1 - (s : ℝ)) =
      N.parentExitPoint D (chain k) (1 - (r : ℝ)) := by
  let F := fun j (s : unitInterval) =>
    (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)))).im
  have matched := (B.matched_bank_points_order i (chain j) (sectors j) (1 - (s : ℝ))
    (by linarith [s.property.1]) budget.le).2
  have along := B.chain_exit_vertical_order i chain parents sectors directions
    budget.le j k s r before
  have coordinate : (B.sectorFrame i (N.parentEntrancePoint D (chain j) (1 - (s : ℝ)))).im =
      (B.sectorFrame i (N.parentExitPoint D (chain k) (1 - (r : ℝ)))).im :=
    le_antisymm (matched.trans along) reverse
  rcases before with before | ⟨rfl, before⟩
  · have jumps : ∀ j k : Fin n, k.val = j.val + 1 → F j 1 ≤ F k 0 := by
      intro j k adjacent
      have jump := (B.parent_child_bank_jump_order i (chain k) (chain j)
        (parents j k adjacent) (sectors k) budget.le).2.2
      simpa [F] using jump
    obtain ⟨adjacent, rfl, rfl, _⟩ := finite_strict_pieces_contact F
      (fun j => B.chain_exit_piece_strict i (chain j) (directions j)) jumps
      j k s r before (reverse.trans matched)
    simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_self, sub_zero] at coordinate ⊢
    have criterion := B.vertex_exit_vertical_eq_iff i (chain k) (sectors k) budget
      (N.parentBankOpening D (chain j)).enter
      ((N.parentBankOpening D (chain j)).entrance_vertex.trans (parents j k adjacent))
    rw [← N.parentEntrancePoint_parent_index D (chain j)] at criterion
    exact criterion.mp (by rw [map_sub, Complex.sub_im, coordinate, sub_self])
  · have parameters : r = s := le_antisymm
      ((B.chain_exit_piece_strict i (chain j) (directions j)).le_iff_le.mp
        (reverse.trans matched)) before
    subst r
    exact ((B.matched_bank_vertical_eq_iff i (chain j) (directions j) (sectors j) budget
      (by linarith [s.property.1])).mp coordinate.symm).symm

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
