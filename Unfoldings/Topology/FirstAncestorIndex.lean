module

public import Unfoldings.Topology.AscendingForest
public import Mathlib.Data.Finset.Max

/-! The first shared ancestor on a finite ordered parent path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V) {n : ℕ} (path : Fin (n + 1) → V)

open Classical in
/-- The first actual path vertex that is an ancestor of the named original source. -/
def firstAncestorIndex (source : V) (reaches : ∃ i, P.Ancestor source (path i)) : Fin (n + 1) :=
  (Finset.univ.filter (fun i => P.Ancestor source (path i))).min' (by
    obtain ⟨i, member⟩ := reaches
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, member⟩⟩)

open Classical in
/-- The chosen index is an actual common ancestor. -/
theorem firstAncestorIndex_ancestor (source : V) (reaches : ∃ i, P.Ancestor source (path i)) :
    P.Ancestor source (path (P.firstAncestorIndex path source reaches)) := by
  unfold firstAncestorIndex
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun i : Fin (n + 1) => P.Ancestor source (path i))) _)).2

open Classical in
/-- Along an ancestor-ordered path, a source affects exactly the suffix after its first contact. -/
theorem firstAncestorIndex_le_iff
    (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j))
    (source : V) (reaches : ∃ i, P.Ancestor source (path i)) (i : Fin (n + 1)) :
    P.firstAncestorIndex path source reaches ≤ i ↔ P.Ancestor source (path i) := by
  constructor
  · intro after
    exact (P.firstAncestorIndex_ancestor path source reaches).trans P
      (ordered _ _ after)
  · intro member
    unfold firstAncestorIndex
    exact Finset.min'_le
      (Finset.univ.filter (fun k : Fin (n + 1) => P.Ancestor source (path k))) i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, member⟩)

/-- Contact at the initial path vertex has literal hinge index zero. -/
theorem firstAncestorIndex_eq_zero
    (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j))
    (source : V) (reaches : ∃ i, P.Ancestor source (path i))
    (initial : P.Ancestor source (path 0)) : P.firstAncestorIndex path source reaches = 0 :=
  le_antisymm ((P.firstAncestorIndex_le_iff path ordered source reaches 0).mpr initial)
    (Fin.zero_le _)

end Unfoldings.AscendingParents
