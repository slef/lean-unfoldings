module

public import Mathlib.Topology.Perfect

/-!
# A perfect boundary cannot have finitely many uniquely projected exceptions

Outside a closed set, an injective projection of a perfect space cannot take
only finitely many values. Otherwise that closed-set complement would give a
finite open neighborhood. This applies to the source net's boundary circle.
-/

@[expose] public section

open scoped Topology

namespace Unfoldings

theorem range_subset_closed_of_perfect {Z X : Type*}
    [TopologicalSpace Z] [T1Space Z] [PerfectSpace Z] [TopologicalSpace X]
    (f : Z → X) (continuous : Continuous f) {K S : Set X} (closed : IsClosed K)
    (finite : S.Finite) (range_subset : Set.range f ⊆ K ∪ S)
    (unique : ∀ a b, f a ∉ K → f a = f b → a = b) : Set.range f ⊆ K := by
  rintro _ ⟨z, rfl⟩
  by_contra outside
  let T : Set Z := f ⁻¹' Kᶜ
  have open_T : IsOpen T := closed.isOpen_compl.preimage continuous
  have in_T : z ∈ T := outside
  have maps : Set.MapsTo f T S := by
    intro a ha
    exact (range_subset ⟨a, rfl⟩).resolve_left ha
  have injective : Set.InjOn f T := fun a ha b _hb equal => unique a b ha equal
  have finite_T := finite.of_injOn maps injective
  exact infinite_of_mem_nhds z (open_T.mem_nhds in_T) finite_T

end Unfoldings
