module

public import Mathlib.Topology.LocallyFinite

/-! Finitely many closed cells determine neighborhoods from the cells incident at their center. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

/-- Including all incident cells makes an interior ambient point interior to the region. -/
theorem interior_of_incident_closed_cells {X I : Type*} [TopologicalSpace X] [Finite I]
    (cells : I → Set X) (closed : ∀ i, IsClosed (cells i)) {ambient region : Set X}
    (cover : ambient ⊆ ⋃ i, cells i) {x : X} (inside : x ∈ interior ambient)
    (included : ∀ i, x ∈ cells i → cells i ⊆ region) : x ∈ interior region := by
  have exclude (i : I) : ∀ᶠ y in 𝓝 x, y ∈ cells i → x ∈ cells i := by
    by_cases incident : x ∈ cells i
    · exact Eventually.of_forall (fun _ _ => incident)
    · filter_upwards [(closed i).isOpen_compl.mem_nhds incident] with y outside
      exact fun member => (outside member).elim
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [Filter.eventually_all.mpr exclude, mem_interior_iff_mem_nhds.mp inside]
    with y near member
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (cover member)
  exact included i (near i hi) hi

end Unfoldings
