module

public import Mathlib.Data.List.Chain

/-! Consecutive survivors are separated by a finite run of removed list entries. -/

@[expose] public section

namespace Unfoldings

variable {α : Type*} {R : α → α → Prop} (keep : α → Bool)

/-- To order a filtered list, it suffices to bridge each consecutive pair
separated by a run consisting entirely of removed entries. -/
theorem isChain_filter_of_removed_runs (pieces : List α)
    (bridge : ∀ (before : List α) (a : α) (middle : List α) (b : α) (after : List α),
      pieces = before ++ a :: (middle ++ b :: after) → keep a → keep b →
      (∀ x ∈ middle, ¬ keep x) → R a b) :
    (pieces.filter keep).IsChain R := by
  induction pieces with
  | nil => exact List.isChain_nil
  | cons a pieces ih =>
    have remaining : (pieces.filter keep).IsChain R := by
      apply ih
      intro before x middle y after equal kept_x kept_y removed
      exact bridge (a :: before) x middle y after (congrArg (List.cons a) equal)
        kept_x kept_y removed
    cases kept_a : keep a with
    | false =>
      simpa only [List.filter_cons, kept_a, Bool.false_eq_true, ↓reduceIte] using remaining
    | true =>
      simp only [List.filter_cons, kept_a, ↓reduceIte]
      cases next : pieces.filter keep with
      | nil => exact List.isChain_singleton _
      | cons b rest =>
        obtain ⟨middle, after, equal, removed, kept_b, _⟩ := List.filter_eq_cons_iff.mp next
        apply List.isChain_cons_cons.mpr
        refine ⟨?_, by simpa only [next] using remaining⟩
        exact bridge [] a middle b after (congrArg (List.cons a) equal) kept_a kept_b removed

/-- Two increasing list positions give a pair sublist, retaining the
occurrences even when values in the list repeat. -/
theorem pair_getElem_sublist (pieces : List α) (a b : ℕ) (ordered : a < b)
    (inside : b < pieces.length) :
    List.Sublist [pieces[a]'(by omega), pieces[b]] pieces := by
  induction pieces generalizing a b with
  | nil => simp only [List.length_nil] at inside; omega
  | cons x pieces ih =>
    cases a with
    | zero =>
      cases b with
      | zero => omega
      | succ b =>
        exact List.Sublist.cons_cons x
          (List.singleton_sublist.mpr (List.getElem_mem (by simpa using inside)))
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        exact (ih a b (by omega) (by simpa using inside)).cons x

end Unfoldings
