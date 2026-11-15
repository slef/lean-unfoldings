module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-! Strict order propagates across connected parameters when contacts are impossible. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

/-- Ordered limits fix the order everywhere in a connected noncrossing family. -/
theorem lt_of_continuous_noncontact_of_tendsto
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {l : Filter X} [NeBot l]
    {f g : X → ℝ} (first : Continuous f) (last : Continuous g)
    (noncontact : ∀ x, f x ≠ g x) {a b : ℝ}
    (limit_first : Tendsto f l (𝓝 a)) (limit_last : Tendsto g l (𝓝 b))
    (ordered : a < b) (x : X) : f x < g x := by
  by_contra wrong
  have eventually_ordered : f ≤ᶠ[l] g := by
    filter_upwards [limit_first.eventually_lt_const (show a < (a + b) / 2 by linarith),
      limit_last.eventually_const_lt (show (a + b) / 2 < b by linarith)] with y left right
    exact (left.trans right).le
  obtain ⟨y, equal⟩ := intermediate_value_univ₂_eventually₁ last first
    (le_of_not_gt wrong) eventually_ordered
  exact noncontact y equal.symm

end Unfoldings
