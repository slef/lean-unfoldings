module

public import Unfoldings.Complex.ContourGapStacks
public import Unfoldings.Complex.ContourParentBanks

/-! Each child contributes a contiguous block of its parent's actual saved gap stack. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

private theorem descending_interval_blocks {A : Type*} (rank : A → ℕ) (lo hi : ℕ)
    (bounds : lo ≤ hi) (l : List A) (ordered : l.Pairwise fun a b => rank b < rank a) :
    l = (l.filter fun a => hi < rank a) ++
      (l.filter fun a => lo < rank a ∧ rank a ≤ hi) ++ (l.filter fun a => rank a ≤ lo) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have head := List.pairwise_cons.mp ordered
    by_cases high : hi < rank a
    · have not_middle : ¬ (lo < rank a ∧ rank a ≤ hi) := fun h => (not_le_of_gt high) h.2
      have not_low : ¬ rank a ≤ lo := not_le_of_gt (bounds.trans_lt high)
      simp only [List.filter_cons, high, not_middle, not_low, decide_true, decide_false,
        ite_true, Bool.false_eq_true, ite_false, List.cons_append, List.cons.injEq, true_and]
      exact ih head.2
    · by_cases above : lo < rank a
      · have mid : lo < rank a ∧ rank a ≤ hi := ⟨above, le_of_not_gt high⟩
        have empty : (l.filter fun x => hi < rank x) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b member
          simpa only [decide_eq_true_eq] using (not_lt_of_ge ((head.1 b member).le.trans mid.2))
        simp only [List.filter_cons, high, mid, not_le_of_gt above, decide_true, decide_false,
          ite_true, Bool.false_eq_true, ite_false, empty, List.nil_append, List.cons_append,
          List.cons.injEq, true_and]
        simpa only [empty, List.nil_append] using ih head.2
      · have below : rank a ≤ lo := le_of_not_gt above
        have not_middle (x : A) (h : rank x ≤ lo) :
            ¬ (lo < rank x ∧ rank x ≤ hi) := fun both => (not_lt_of_ge h) both.1
        have all_low (x : A) (member : x ∈ a :: l) : rank x ≤ lo := by
          rcases List.mem_cons.mp member with rfl | later
          · exact below
          · exact (head.1 x later).le.trans below
        have no_high : ((a :: l).filter fun x => hi < rank x) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b member
          simpa only [decide_eq_true_eq] using (not_lt_of_ge ((all_low b member).trans bounds))
        have no_mid : ((a :: l).filter fun x => lo < rank x ∧ rank x ≤ hi) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b member
          simpa only [decide_eq_true_eq] using (not_middle b (all_low b member))
        have all : ((a :: l).filter fun x => rank x ≤ lo) = a :: l :=
          List.filter_eq_self.mpr (fun b member => decide_eq_true_eq.mpr (all_low b member))
        simp only [no_high, no_mid, all, List.nil_append]

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

open Classical in
/-- The parent stack restricted to one child's original subtree is exactly that child's stack. -/
theorem contourSavedGapStack_filter_child (child : C.Vertex Set.univ) :
    ((C.contourSavedGapStack S Q (P.parent child)).filter
      fun event => P.Ancestor (C.positiveContourVertex S Q event) child) =
        C.contourSavedGapStack S Q child := by
  unfold contourSavedGapStack contourEdgeGapStack
  rw [List.filter_reverse, List.filter_filter]
  apply congrArg List.reverse
  apply congrArg (fun p => (C.positiveContourSources S Q).filter p)
  funext event
  by_cases h : P.Ancestor (C.positiveContourVertex S Q event) child
  · have parent := h.trans P (P.ancestor_parent child)
    simp [h, parent]
  · simp [h]

/-- The actual cyclic contour makes each child's stack a consecutive block of the
parent stack, with the surrounding blocks retaining their original order. -/
theorem contourSavedGapStack_child_block
    (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
    (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
    (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots) :
    ∃ before after, C.contourSavedGapStack S Q (P.parent child) =
      before ++ C.contourSavedGapStack S Q child ++ after := by
  classical
  let interval := C.contourParentInterval S Q roots starts child nonroot
  let stack := C.contourSavedGapStack S Q (P.parent child)
  let rank (event : C.PositiveContourSource S Q) := event.val.val
  have order : stack.Pairwise fun a b => rank b < rank a :=
    (C.contourEdgeGapStack_ordered S Q (P.parent child)).reverse
  have blocks := descending_interval_blocks rank interval.enter.val interval.leave.val
    interval.ordered.le stack order
  have middle : (stack.filter fun g => interval.enter.val < rank g ∧
      rank g ≤ interval.leave.val) = C.contourSavedGapStack S Q child := by
    rw [← C.contourSavedGapStack_filter_child S Q child]
    apply congrArg (List.filter · stack)
    funext g
    have named : P.Ancestor (C.positiveContourVertex S Q g) child ↔
        interval.enter.val < rank g ∧ rank g ≤ interval.leave.val :=
      interval.subtree g.val.castSucc
    by_cases member : P.Ancestor (C.positiveContourVertex S Q g) child
    · exact (decide_eq_true_eq.mpr (named.mp member)).trans (decide_eq_true_eq.mpr member).symm
    · have outside : ¬ (interval.enter.val < rank g ∧ rank g ≤ interval.leave.val) :=
        fun h => member (named.mpr h)
      exact (decide_eq_false outside).trans (decide_eq_false member).symm
  rw [middle] at blocks
  exact ⟨_, _, blocks⟩

end Unfoldings.TriangleComplex
