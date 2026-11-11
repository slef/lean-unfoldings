module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Separation.Hausdorff

/-! A continuous extension of a finite closed-piece selection retains its actual branch values. -/

@[expose] public section

namespace Unfoldings

theorem finite_closed_selection_on_closure {ι α β : Type*} [Finite ι]
    [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    (piece : ι → Set α) (closed : ∀ i, IsClosed (piece i))
    (branch : ι → α → β) (continuous : ∀ i, Continuous (branch i))
    {F G : α → β} {s : Set α} (Gcontinuous : Continuous G) (agrees : Set.EqOn F G s)
    (selection : ∀ x ∈ s, ∃ i, x ∈ piece i ∧ F x = branch i x) :
    ∀ x ∈ closure s, ∃ i, x ∈ piece i ∧ G x = branch i x := by
  let covered := ⋃ i, piece i ∩ {x | G x = branch i x}
  have covered_closed : IsClosed covered := isClosed_iUnion_of_finite
    (fun i => (closed i).inter (isClosed_eq Gcontinuous (continuous i)))
  have subset : s ⊆ covered := by
    intro x member
    obtain ⟨i, inside, equal⟩ := selection x member
    exact Set.mem_iUnion.mpr ⟨i, inside, (agrees member).symm.trans equal⟩
  intro x member
  exact Set.mem_iUnion.mp (closure_minimal subset covered_closed member)

end Unfoldings
