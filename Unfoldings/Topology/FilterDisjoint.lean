module

public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Set.Disjoint

/-! Empty set entries can be removed from pairwise separation checks. -/

@[expose] public section

namespace Unfoldings

variable {α β : Type*}

theorem pairwise_disjoint_of_filter (images : α → Set β) (keep : α → Bool) (pieces : List α)
    (separated : (pieces.filter keep).Pairwise (fun a b => Disjoint (images a) (images b)))
    (removed : ∀ a ∈ pieces, keep a = false → images a = ∅) :
    pieces.Pairwise (fun a b => Disjoint (images a) (images b)) := by
  induction pieces with
  | nil => exact List.Pairwise.nil
  | cons a pieces ih =>
    have remaining : ∀ b ∈ pieces, keep b = false → images b = ∅ :=
      fun b member => removed b (List.mem_cons_of_mem _ member)
    cases active : keep a with
    | false =>
      have tail : (pieces.filter keep).Pairwise (fun a b => Disjoint (images a) (images b)) := by
        simpa only [List.filter_cons, active, Bool.false_eq_true, ↓reduceIte] using separated
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih tail remaining⟩
      intro b _
      rw [removed a (List.mem_cons_self ..) active]
      exact Set.empty_disjoint _
    | true =>
      have kept : (a :: pieces.filter keep).Pairwise
          (fun a b => Disjoint (images a) (images b)) := by
        simpa only [List.filter_cons, active, ↓reduceIte] using separated
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih kept.tail remaining⟩
      intro b member
      cases kept_b : keep b with
      | false => rw [remaining b member kept_b]; exact Set.disjoint_empty _
      | true => exact (List.pairwise_cons.mp kept).1 b (List.mem_filter.mpr ⟨member, kept_b⟩)

end Unfoldings
