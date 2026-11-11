module

public import Mathlib.Topology.Continuous
public import Mathlib.Order.Filter.Finite

/-! Near a point, a finite closed cover can use only pieces already containing that point. -/

@[expose] public section

namespace Unfoldings

open Filter Topology

theorem finite_closed_cover_eventually_active {X Y ι : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (piece : ι → Set Y) (closed : ∀ i, IsClosed (piece i))
    (f : X → Y) (continuous : Continuous f) (x : X) :
    ∀ᶠ y in 𝓝 x, ∀ i, f y ∈ piece i → f x ∈ piece i := by
  rw [Filter.eventually_all]
  intro i
  by_cases active : f x ∈ piece i
  · exact Filter.Eventually.of_forall (fun _ _ => active)
  · have avoid : ∀ᶠ y in 𝓝 x, f y ∉ piece i :=
      ((closed i).isOpen_compl.preimage continuous).mem_nhds active
    exact avoid.mono (fun _ outside member => (outside member).elim)

end Unfoldings
