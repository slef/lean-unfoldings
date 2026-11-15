module

public import Unfoldings.Topology.ParentFrontierHistory
public import Unfoldings.Topology.SelectedSubtree

/-! Exact edge-end incidence in an ancestor-closed processed descendant subtree. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.ParentFrontier

variable {V : Type*} [Fintype V] {P : AscendingParents V} (S : P.ParentFrontier)

/-- Original processed descendants, retaining their original vertex labels. -/
def processedDescendants (vertex : V) : Finset V := by
  classical
  exact (P.descendants vertex).filter (fun w => w ∈ S.processed)

@[simp] theorem mem_processedDescendants (vertex w : V) :
    w ∈ S.processedDescendants vertex ↔ w ∈ S.processed ∧ P.Ancestor w vertex := by
  classical
  simp only [processedDescendants, Finset.mem_filter, P.mem_descendants, and_comm]

open Classical in
/-- The actual partial subtree has one outgoing parent edge, so its incidence is twice
its number of processed original vertices minus one. Fresh descendants are not counted. -/
theorem sum_processed_descendant_incidence (vertex : V) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ S.processed) :
    (∑ w : V, ((if w ∈ S.processed ∧ P.Ancestor w vertex then (1 : ℝ) else 0) +
      (if w ∈ S.processed ∧ P.Ancestor (P.parent w) vertex then (1 : ℝ) else 0))) =
      2 * (S.processedDescendants vertex).card - 1 := by
  classical
  have top : vertex ∈ S.processedDescendants vertex :=
    (S.mem_processedDescendants vertex vertex).mpr ⟨processed, P.ancestor_refl vertex⟩
  have first_set : Finset.univ.filter (fun w => w ∈ S.processed ∧ P.Ancestor w vertex) =
      S.processedDescendants vertex := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S.mem_processedDescendants]
  have second_set : Finset.univ.filter (fun w =>
      w ∈ S.processed ∧ P.Ancestor (P.parent w) vertex) =
        (S.processedDescendants vertex).erase vertex := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      S.mem_processedDescendants, P.ancestor_parent_iff_descendant_ne nonroot]
    tauto
  have first : (∑ w : V, if w ∈ S.processed ∧ P.Ancestor w vertex then (1 : ℝ) else 0) =
      (S.processedDescendants vertex).card := by rw [Finset.sum_boole, first_set]
  have second : (∑ w : V,
      if w ∈ S.processed ∧ P.Ancestor (P.parent w) vertex then (1 : ℝ) else 0) =
        (S.processedDescendants vertex).card - 1 := by
    rw [Finset.sum_boole, second_set, Finset.card_erase_of_mem top,
      Nat.cast_sub (Finset.card_pos.mpr ⟨vertex, top⟩), Nat.cast_one]
  rw [Finset.sum_add_distrib, first, second]
  ring

end Unfoldings.AscendingParents.ParentFrontier
