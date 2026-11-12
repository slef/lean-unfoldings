module

public import Unfoldings.Topology.FiniteSelectionClosure

/-! A trace branch is approached through its own actual piece. -/

@[expose] public section

namespace Unfoldings

theorem finite_selection_visible_on_closure {ι α β : Type*} [Finite ι]
    [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    (piece : ι → Set α) (branch : ι → α → β) (continuous : ∀ i, Continuous (branch i))
    {F G : α → β} {s : Set α} (Gcontinuous : Continuous G) (agrees : Set.EqOn F G s)
    (selection : ∀ x ∈ s, ∃ i, x ∈ piece i ∧ F x = branch i x) :
    ∀ x ∈ closure s, ∃ i, x ∈ closure (s ∩ piece i) ∧ G x = branch i x := by
  let visible := fun i => closure (s ∩ piece i)
  apply finite_closed_selection_on_closure visible (fun _ => isClosed_closure) branch continuous
    Gcontinuous agrees
  intro x member
  obtain ⟨i, inside, equal⟩ := selection x member
  exact ⟨i, subset_closure ⟨member, inside⟩, equal⟩

end Unfoldings
