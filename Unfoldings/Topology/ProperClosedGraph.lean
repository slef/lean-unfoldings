module

public import Mathlib.Topology.Maps.Proper.Basic

/-! A closed graph is continuous when its image has a continuous proper coordinate. -/

@[expose] public section

namespace Unfoldings

/-- A proper coordinate prevents escape along a closed graph. No compactness of the whole
codomain or local compactness of the parameter space is needed. -/
theorem continuous_of_isClosed_graph_of_proper_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} (graph : IsClosed f.graph) (h : Y → Z) (proper : IsProperMap h)
    (coordinate : Continuous (h ∘ f)) : Continuous f := by
  rw [continuous_iff_isClosed]
  intro C closed
  have image_closed := (isProperMap_id.prodMap proper).isClosedMap _
    (graph.inter (isClosed_univ.prod closed))
  have preimage_closed := image_closed.preimage (continuous_id.prodMk coordinate)
  convert preimage_closed using 1
  ext x
  constructor
  · intro member
    exact ⟨(x, f x), ⟨rfl, ⟨Set.mem_univ _, member⟩⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨on_graph, _, member⟩, equal⟩
    have first : a = x := congrArg Prod.fst equal
    have second : f a = b := on_graph
    change f x ∈ C
    rw [← second, first] at member
    exact member

end Unfoldings
