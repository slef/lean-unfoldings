module

public import Unfoldings.Topology.ProcessedDescendantIncidence
public import Unfoldings.Topology.ParentFrontierNeighbor

/-! A singleton fresh step changes original subtree weights by exactly its own source weight. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.ParentFrontier

variable {V : Type*} [Fintype V] {P : AscendingParents V} (S : P.ParentFrontier)

/-- Sum a weight over actual processed original descendants. -/
def processedDescendantWeight (weight : V → ℝ) (vertex : V) : ℝ :=
  ∑ w ∈ S.processedDescendants vertex, weight w

open Classical in
/-- Original source labels are retained: only ancestor subtrees receive the new source charge. -/
theorem processedDescendantWeight_single_step (weight : V → ℝ) (vertex seed : V)
    (fresh : seed ∉ S.processed) (single : S.contactTime seed = 1) :
    (S.process seed).processedDescendantWeight weight vertex =
      S.processedDescendantWeight weight vertex +
        (if P.Ancestor seed vertex then weight seed else 0) := by
  classical
  have not_mem : seed ∉ S.processedDescendants vertex :=
    fun member => fresh ((S.mem_processedDescendants vertex seed).mp member).1
  by_cases inside : P.Ancestor seed vertex
  · have copies : (S.process seed).processedDescendants vertex =
        insert seed (S.processedDescendants vertex) := by
      ext w
      rw [(S.process seed).mem_processedDescendants, S.process_processed_eq_insert single,
        Set.mem_insert_iff, Finset.mem_insert, S.mem_processedDescendants]
      constructor
      · rintro ⟨same | old, ancestor⟩
        · exact Or.inl same
        · exact Or.inr ⟨old, ancestor⟩
      · rintro (same | ⟨old, ancestor⟩)
        · exact ⟨Or.inl same, same.symm ▸ inside⟩
        · exact ⟨Or.inr old, ancestor⟩
    simp only [processedDescendantWeight, copies, Finset.sum_insert not_mem,
      ite_eq_left inside, add_comm]
  · have copies : (S.process seed).processedDescendants vertex = S.processedDescendants vertex := by
      ext w
      rw [(S.process seed).mem_processedDescendants, S.process_processed_eq_insert single,
        Set.mem_insert_iff, S.mem_processedDescendants]
      constructor
      · rintro ⟨same | old, ancestor⟩
        · exact (inside (same ▸ ancestor)).elim
        · exact ⟨old, ancestor⟩
      · exact fun both => ⟨Or.inr both.1, both.2⟩
    simp only [processedDescendantWeight, copies, ite_eq_right inside, add_zero]

end Unfoldings.AscendingParents.ParentFrontier
