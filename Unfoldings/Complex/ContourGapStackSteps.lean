module

public import Unfoldings.Complex.ContourGapStacks

/-! Prefixes of the saved gap stack record exactly the staged ray insertions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

open Classical in
private theorem filter_before_succ {α : Type*} (rank : α → ℕ) (l : List α) (e : α)
    [DecidableEq α] (injective : Function.Injective rank)
    (sorted : l.Pairwise fun a b => rank b < rank a) :
    (l.filter fun a => rank a < rank e + 1) =
      if e ∈ l then e :: (l.filter fun a => rank a < rank e)
      else (l.filter fun a => rank a < rank e) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at sorted
    rcases lt_trichotomy (rank a) (rank e) with before | same | after
    · have not_mem : e ∉ a :: l := by
        simp only [List.mem_cons]
        rintro (rfl | member)
        · exact lt_irrefl _ before
        · exact (not_lt_of_ge before.le) (sorted.1 e member)
      simp only [List.filter_cons, decide_eq_true_eq, before,
        before.trans (Nat.lt_succ_self _), ite_true, not_mem, ite_false]
      rw [ih sorted.2, ite_eq_right (fun h => not_mem (List.mem_cons_of_mem _ h))]
    · obtain rfl := injective same
      have not_tail : a ∉ l := fun h => lt_irrefl _ (sorted.1 a h)
      have tails := ih sorted.2
      rw [ite_eq_right not_tail] at tails
      rw [ite_eq_left List.mem_cons_self]
      simpa [List.filter_cons, Nat.lt_succ_self] using congrArg (List.cons a) tails
    · have same : e ∈ a :: l ↔ e ∈ l := by
        have different : e ≠ a := fun eq => lt_irrefl _ (eq ▸ after)
        simp [different]
      simp only [List.filter_cons, decide_eq_true_eq, not_lt_of_ge after.le,
        not_lt_of_ge (Nat.succ_le_iff.mpr after), ite_false, same]
      exact ih sorted.2

/-- The active saved-frontier stack keeps exactly the already inserted descendant gaps,
in reverse contour order. -/
def contourSavedGapStackBefore (vertex : C.Vertex Set.univ) (stage : ℕ) :
    List (C.PositiveContourSource S Q) :=
  (C.contourSavedGapStack S Q vertex).filter (fun event => event.val.val < stage)

open Classical in
/-- A positive source adds one head gap exactly along its original ancestor path.
Every attachment on that path saves all its former consecutive seams below the new gap. -/
theorem contourSavedGapStackBefore_succ (vertex : C.Vertex Set.univ)
    (event : C.PositiveContourSource S Q) :
    C.contourSavedGapStackBefore S Q vertex (event.val.val + 1) =
      if P.Ancestor (C.positiveContourVertex S Q event) vertex then
        event :: C.contourSavedGapStackBefore S Q vertex event.val.val
      else C.contourSavedGapStackBefore S Q vertex event.val.val := by
  classical
  unfold contourSavedGapStackBefore
  have ordered : (C.contourSavedGapStack S Q vertex).Pairwise
      (fun (a b : C.PositiveContourSource S Q) => b.val.val < a.val.val) :=
    (C.contourEdgeGapStack_ordered S Q vertex).reverse
  refine (filter_before_succ (fun e => e.val.val) _ event
    (fun _ _ same => Subtype.ext (Fin.ext same)) ordered).trans ?_
  by_cases reaches : P.Ancestor (C.positiveContourVertex S Q event) vertex
  · rw [ite_eq_left reaches,
      ite_eq_left ((C.mem_contourSavedGapStack S Q vertex event).mpr reaches)]
  · rw [ite_eq_right reaches, ite_eq_right
      (fun h => reaches ((C.mem_contourSavedGapStack S Q vertex event).mp h))]

/-- The final stage recovers the full original saved-gap stack. -/
theorem contourSavedGapStackBefore_length (vertex : C.Vertex Set.univ) :
    C.contourSavedGapStackBefore S Q vertex Q.length = C.contourSavedGapStack S Q vertex := by
  exact List.filter_eq_self.mpr (fun event _ => decide_eq_true_eq.mpr event.val.isLt)

end Unfoldings.TriangleComplex
